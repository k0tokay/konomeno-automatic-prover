import predicate_logic_ast as pla
import pegtree as pg
import itertools
import json
import networkx as nx

'''
_skolem_counter = itertools.count(1)  # Skolem関数名用カウンタ
_var_counter = itertools.count(1)      # 変数名カウンタ
_alpha_var_counter = itertools.count(1)   # α変換用変数名カウンタ'''
_node_counter = itertools.count(1)  # ノード名用カウンタ

class AST:
    pass

class Discourse(AST):
    __match_args__ = ('sentences',)
    def __init__(self, sentences):
        self.sentences = sentences
    def __repr__(self):
        return f"Discourse({self.sentences})"

class Sentence(AST):
    __match_args__ = ('content', 'situation', 'action')
    def __init__(self, sentence, situation=None, action=None):
        self.content = sentence
        self.situation = situation
        self.action = action
    def __repr__(self):
        #return f"Sentence({self.content}, situation={self.situation}, action={self.action})"
        return f"{self.content}"

class Situation(AST):
    __match_args__ = ('speaker', 'listener', 'time', 'place')
    def __init__(self, speaker, listener, time, place):
        self.speaker = speaker
        self.listener = listener
        self.time = time
        self.place = place
    def __repr__(self):
        return f"Situation({self.speaker}, {self.listener}, {self.time}, {self.place})"

class Graph(AST):
    __match_args__ = ('nodes', 'edges')
    # KGに相当する．KGはtriplesで定義されることが多いが，ここではnodesとedgesで定義する
    def __init__(self, nodes, edges):
        self.nodes = nodes
        self.edges = edges
    def __repr__(self):
        # あとでちゃんと書く
        return f"Graph({self.nodes}, {self.edges})"

class Node(AST):
    __match_args__ = ('concept', 'modifier')
    def __init__(self, concept, modifier=None, label=None):
        self.concept = concept
        self.modifier = modifier # 雑多な情報を入れるので1つのdictにまとめておく
        self.modifier["id"] = next(_node_counter)
    def __repr__(self):
        #return f"Node({self.concept}, modifier={self.modifier})"
        return f"{self.concept}_{self.modifier['id']}"
    
class Edge(AST):
    __match_args__ = ('relation', 'modifier')
    def __init__(self, relation, modifier=None, label=None):
        self.relation = relation
        self.modifier = modifier
    def __repr__(self):
        #return f"Edge({self.relation}, modifier={self.modifier})"
        return f"{self.relation}({self.modifier['source']}, {self.modifier['target']})"

class Concept(AST):
    __match_args__ = ('name',)
    def __init__(self, name):
        self.name = name
    def __repr__(self):
        #return f"Concept({self.name})"
        return f"{self.name}"

class Relation(AST):
    __match_args__ = ('name',)
    def __init__(self, name):
        self.name = name
    def __repr__(self):
        #return f"Relation({self.name})"
        return f"{self.name}"

class Quantifier(AST):
    __match_args__ = ('name', 'concepts')
    def __init__(self, name, concepts):
        self.name = name
        self.concepts = concepts
    def __repr__(self):
        return f"{self.name} {self.concepts}."
    
class Quantified(AST):
    __match_args__ = ('quantifier', 'content')
    def __init__(self, quantifier, content):
        self.quantifier = quantifier
        self.content = content
    def __repr__(self):
        return f"{self.quantifier} {self.content}"
    
def kono_to_ast(tree, dict):
    scopes = []  # スコープ(というか量化子)のリスト
    scopes.append(Quantifier("kostafe", []))  # デフォルトで文脈による集合化の存在量化がある
    # 発話状況にとりあえずデフォルト値を設定
    # 今後色々追加する
    default_situation = Situation(
        pla.Constant("default_speaker"), 
        pla.Constant("default_listener"),
        pla.Constant("default_time"),
        pla.Constant("default_place")
    )
    # Conceptを同値類で割るためのグラフ(Labelだけ)
    same_label = {}

    all_concepts = {}

    def rec(tree):
        nonlocal scopes, same_label, all_concepts
        tag = tree.getTag()
    
        if tag == "Discourse":
            sentences = []
            for s in tree:
                action = s.getTag()
                sentences.append(Sentence(rec(s), default_situation, action))
            return Discourse(sentences)
    
        elif tag == "Sentence" or tag == "Question":
            # 論理式と同じように処理する
            children = list(tree)
    
            if len(children) == 1:
                return rec(children[0])
            
            left = rec(children[0])
            op = children[1].getToken()
            right = rec(children[2])
    
            if op == "lite":
                return pla.And(left, right)
            elif op == "liko":
                return pla.Or(left, right)
            elif op == "lista":
                return pla.Imp(left, right)
            elif op == "kalista":
                return pla.Iff(left, right)
            else:
                return None
        
        elif tag == "Not":
            result = rec(tree[-1])
            for _ in range(len(tree) - 1):
                result = pla.Not(result)
            return result
        
        elif tag == "Quantified":
            quant = tree[0]
            labels = [label.getToken() for label in tree if label.getTag() == "Label"]
            name = quant.getToken()
            concepts = [Node(None, modifier={"label": label}) for label in labels]
            all_concepts.update({concept.modifier["id"]: concept for concept in concepts})
            for concept in concepts:
                # same_label[concept.modifier["label"]]は空であるはず
                same_label[concept.modifier["label"]] = [concept.modifier["id"]]
            quant_comp = Quantifier(name, concepts)
            scopes.append(quant_comp)
            content = rec(tree[-1])
            scopes.pop()
            return Quantified(quant_comp, content)
    
        elif tag == "Graph":
            graph_nodes = []
            graph_edges = []
            for line in list(tree):
                line_nodes, line_edges = rec(line)
                graph_nodes.extend(line_nodes)
                graph_edges.extend(line_edges)
            return Graph(graph_nodes, graph_edges)
        
        elif tag == "Line":
                # Lineの処理
                line_nodes = []
                line_edges = []
                for child in list(tree):
                    if child.getTag() == "Node":
                        line_nodes.append(rec(child))
                    else:
                        edge = rec(child)
                        if line_edges:
                            line_edges[-1].modifier["target"] = line_nodes[-1]
                        edge.modifier["source"] = line_nodes[-1]
                        line_edges.append(edge)
                line_edges[-1].modifier["target"] = line_nodes[-1]
                return line_nodes, line_edges

        elif tag == "Node":
            modifier = {}
    
            children = list(tree)
            i = 0
            modifier["pos"] = 0
            while children[i].getTag() == "Prefix":
                prefix = children[i][0]
                if prefix.getTag() == "LeftDemon":
                    print("Left demon", prefix.getToken())
                    demon = prefix.getToken()
                    ld_dict = {"sen": -1, "tan": -2, "seton": -3}
                    if demon in ld_dict:
                        pos = ld_dict[demon]
                    else:
                        pos = -int(demon.split("-")[0])
                    modifier["pos"] = pos
                elif prefix.getTag() == "RightDemon":
                    demon = prefix.getToken()
                    rd_dict = {"lon": 1, "con": 2, "colun": 3}
                    if demon in rd_dict:
                        pos = rd_dict[demon]
                    else:
                        pos = int(demon.split("-")[0])
                    modifier["pos"] = pos
                elif prefix.getTag() == "Interrogative":
                    if "interrogative" not in modifier:
                        modifier["interrogative"] = []
                    modifier["interrogative"].append(prefix.getToken())
                elif prefix.getTag() == "PreNodeQ":
                    modifier["node_q"] = prefix.getToken()
                elif prefix.getTag() == "PreNodePDQ":
                    modifier["node_pdq"] = prefix.getToken()
                i += 1
    
            concept = rec(tree[i])
            i += 1
    
            while i < len(children) and children[i].getTag() == "Suffix":
                suffix = children[i][0]
                if suffix.getTag() == "Abbrev":
                    abbrev = suffix[0]
                    if abbrev.getTag() == "Tense":
                        if "tense" in modifier:
                            raise Exception("Multiple tense modifiers")
                        modifier["tense"] = abbrev.getToken()
                elif suffix.getTag() == "PostNodeQ":
                    modifier["node_q"] = suffix.getToken()
                i += 1
            while i < len(children) and children[i].getTag() == "Label":
                modifier["label"] = children[i].getToken()
                i += 1
            
            result = Node(concept, modifier)
            if "label" in modifier:
                if modifier["label"] not in same_label:
                    same_label[modifier["label"]] = []
                same_label[modifier["label"]].append(modifier["id"])
        
            # スコープの検索
            for scope in reversed(scopes):
                node_q = "fe" if scope.name == "kostafe" else scope.name.split("-")[0]
                if "node_q" not in modifier:
                    modifier["node_q"] = "fe"
                if node_q == modifier["node_q"]:
                    scope.concepts.append(result)
                    break
            all_concepts[modifier["id"]] = result
            return result
    
        elif tag == "Edge":
            modifier = {}
            i = 0
            children = list(tree)
            neg_num = 0
            while children[i].getTag() == "Neg":
                neg_num += 1
                i += 1
            modifier["neg"] = neg_num
            relation = rec(children[i])
            
            while children[i].getTag() == "Label":
                modifier["label"] = children[i].getToken()
                i += 1

            return Edge(relation, modifier)
    
        elif tag == "Concept":
            return Concept(tree.getToken())
    
        elif tag == "Relation":
            return Relation(tree.getToken())
        
    result = rec(tree)
    result = Quantified(scopes[0], result)

    return result, same_label, all_concepts

def find_same_concept(ast, same_label):
    #posを消化する
    same_concept = []
    scopes = []
    def rec(ast):
        match ast:
            case Discourse(sentences):
                for sentence in sentences:
                    rec(sentence)
            case Sentence(content, situation, action):
                rec(content)
            case pla.And(left, right) | pla.Or(left, right) | pla.Imp(left, right) | pla.Iff(left, right):
                rec(left)
                rec(right)
            case pla.Not(content):
                rec(content)
            case Quantified(quantifier, content):
                scopes.append(quantifier)
                rec(content)
                scopes.pop()
            case Graph(nodes, edges):
                for node in nodes:
                    # scopeを見つける
                    for scope in reversed(scopes):
                        node_q = "fe" if scope.name == "kostafe" else scope.name.split("-")[0]
                        if node_q == node.modifier["node_q"]:
                            same_name = [v for v in scope.concepts if (v.concept is not None) and v.concept.name == node.concept.name]
                            if len(same_name) < abs(node.modifier["pos"]):
                                raise Exception("Invalid position")
                            target = same_name[node.modifier["pos"]]
                            same_concept.append((node.modifier["id"], target.modifier["id"]))
                            break
                return
    rec(ast)
    # labelの情報を統合
    same_concept.extend([(v[0], vi) for v in same_label.values() for vi in v])

    return same_concept

                

def flip_edge(graph, dict):
    pass

def modify_ast(ast, same_concept, all_concepts):
    # 同値類をまとめる(連結成分を求める)
    G = nx.Graph()
    G.add_edges_from(same_concept)
    connect = nx.connected_components(G)
    connect = [comp for comp in connect]
    print("Connected components:", connect)
    # 代表元
    repr_dict = {}
    for comp in connect:
        for id in comp:
            if all_concepts[id].concept is not None:
                rep = all_concepts[id].modifier["id"]
                break
            
        for id in comp:
            repr_dict[id] = rep


    def rec(ast):
        nonlocal repr_dict, all_concepts
        match ast:
            case Discourse(sentences):
                return Discourse([rec(sentence) for sentence in sentences])
            case Sentence(content, situation, action):
                return Sentence(rec(content), situation, action)
            case pla.And(left, right) | pla.Or(left, right) | pla.Imp(left, right) | pla.Iff(left, right):
                return type(ast)(rec(left), rec(right))
            case pla.Not(content):
                return pla.Not(rec(content))
            case Quantified(quantifier, content):
                return Quantified(rec(quantifier), rec(content))
            case Quantifier(name, concepts):
                return Quantifier(name, list(set([rec(concept) for concept in concepts])))
            case Graph(nodes, edges):
                new_nodes = list(set([rec(node) for node in nodes]))
                return Graph(new_nodes, edges)
            case Node(concept, modifier):
                return all_concepts[repr_dict[modifier["id"]]]
            
    result = rec(ast)
    return result
    
"""
def kono_to_logic(ast):
    env = {}
    def rec(ast):
        match ast:
            case Discourse(sentences):
                return [rec(sentence) for sentence in sentences if sentence.action == "Sentence"]
            case Sentence(content, situation, action):
                # 指標詞はあとで処理する
                return rec(content)
            case pla.And(left, right) | pla.Or(left, right) | pla.Imp(left, right) | pla.Iff(left, right):
                return type(ast)(rec(left), rec(right))
            case Graph(nodes, edges):
                atoms = []
                for edge in edges:
                    edge_name, source, target = edge
                    rel = edge_name.relation
                    neg_num = edge_name.modifier["neg"]
                    pred_name = rel.name
                    pred = pla.Predicate(pred_name, [nodes[source].concept, nodes[target].concept])
                    for _ in range(neg_num):
                        pred = pla.Not(pred)
                    atoms.append(pred)
                
                result = atoms[0]
                for atom in atoms[1:]:
                    result = pla.And(result, atom)
                return result
    result = rec(ast)
    return result"""
    
def test_01():
    peg = pg.grammar("konomeno.tpeg")
    parser = pg.generate(peg)
    code = "kon-lilee-α-β waka ja lon-hamin-ik ke kalam-kon-α, hamin-ik-γ ke mikan-kon-β tos"
    tree = parser(code)
    print("Tree:", repr(tree))
    ast, same_label, all_concepts = kono_to_ast(tree, None)
    print("AST:", ast)
    same_concept = find_same_concept(ast, same_label)
    print("Same concept:", same_concept)
    ast = modify_ast(ast, same_concept, all_concepts)
    print("Modified AST:", ast)
    # logic = kono_to_logic(ast)
    # print("Logic:", logic)
    # cnf = pla.cnf_convert(logic)
    # print("CNF:", cnf)
    # clauses = pla.cnf_to_clause(cnf)
    # print("Clauses:", clauses)


if __name__ == '__main__':
    test_01()