import predicate_logic_ast as pla
import resolution as res
import pegtree as pg
import itertools
import json
import networkx as nx

'''
_skolem_counter = itertools.count(1)  # Skolem関数名用カウンタ
_var_counter = itertools.count(1)      # 変数名カウンタ
_alpha_var_counter = itertools.count(1)   # α変換用変数名カウンタ'''
_node_counter = itertools.count(1)  # ノード名用カウンタ
_pd_counter = itertools.count(1)  # PD変数名用カウンタ

class AST:
    pass

class Discourse(AST):
    __match_args__ = ('sentences',)
    def __init__(self, sentences):
        self.sentences = sentences
    def __repr__(self):
        return "; ".join([f"{sentence}" for sentence in self.sentences])

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
        return f"Graph({', '.join(map(str, self.edges))})"

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
    # Nodeを同値類で割るためのグラフ(Labelだけ)
    same_label = {}

    # Nodeの一覧
    all_nodes = {}

    def rec(tree):
        nonlocal scopes, same_label, all_nodes
        tag = tree.getTag()
    
        if tag == "Discourse":
            sentences = []
            for s in tree:
                action = s.getTag()
                sentences.append(Sentence(rec(s), default_situation, action))
            return Discourse(sentences)
    
        elif tag == "Sentence" or tag == "Question":
            # questionの場合は，enaを閉じるためのena-lileeを追加する
            if tag == "Question":
                scopes.append(Quantifier("ena-lilee", []))
            
            # 論理式と同じように処理する
            children = list(tree)
    
            if len(children) == 1:
                result = rec(children[0])

            else:
                left = rec(children[0])
                op = children[1].getToken()
                right = rec(children[2])
    
                if op == "lite":
                    result = pla.And(left, right)
                elif op == "liko":
                    result = pla.Or(left, right)
                elif op == "lista":
                    result = pla.Imp(left, right)
                elif op == "kalista":
                    result = pla.Iff(left, right)
            
            if tag == "Question":
                scope = scopes.pop()
                result = Quantified(scope, result)
            
            return result
        
        elif tag == "Not":
            result = rec(tree[-1])
            for _ in range(len(tree) - 1):
                result = pla.Not(result)
            return result
        
        elif tag == "Quantified" or tag == "PullDown":
            quant = tree[0]
            labels = [label.getToken() for label in tree if label.getTag() == "Label"]
            name = quant.getToken()
            # concepts = [Node(None, modifier={"label": label}) for label in labels]
            # all_nodes.update({concept.modifier["id"]: concept for concept in concepts})
            # for concept in concepts:
            #     # same_label[concept.modifier["label"]]は空であるはず
            #     same_label[concept.modifier["label"]] = [concept.modifier["id"]]
            # quant_comp = Quantifier(name, concepts)
            quant_comp = Quantifier(name, labels)
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
                    # if "interrogative" not in modifier:
                    #     modifier["interrogative"] = []
                    # modifier["interrogative"].append(prefix.getToken())
                    modifier["node_q"] = prefix.getToken()
                elif prefix.getTag() == "PreNodeQ" or prefix.getTag() == "PreNodePDQ":
                    modifier["node_q"] = prefix.getToken()
                # elif prefix.getTag() == "PreNodePDQ":
                #     modifier["node_pdq"] = prefix.getToken()
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
                elif suffix.getTag() == "PostNodeQ" or suffix.getTag() == "PostNodePDQ":
                    modifier["node_q"] = suffix.getToken()
                # elif suffix.getTag() == "PostNodePDQ":
                #     modifier["node_pdq"] = suffix.getToken()
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
            # ラベルがあるものを優先的に検索する
            scope = None if "label" not in modifier else [scope for scope in reversed(scopes) if modifier["label"] in scope.concepts]

            if scope is not None and len(scope) > 0:
                scope = scope[0]
                i = scope.concepts.index(modifier["label"])
                scope.concepts[i] = result
                result.modifier["scope"] = scope
            else:
                for scope in reversed(scopes):
                    q_map = {
                        "kostafe": "fe",
                        "ceja": "le",
                        "lesta": "laf",
                    }
                    node_q = q_map[scope.name] if scope.name in q_map else scope.name.split("-")[0]
                    if "node_q" not in modifier:
                        modifier["node_q"] = "fe"
                    if node_q == modifier["node_q"]:
                        scope.concepts.append(result)
                        result.modifier["scope"] = scope
                        break

            all_nodes[modifier["id"]] = result
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
    # return result, same_label, all_nodes
    same_node = find_same_node(result, same_label)
    ast = modify_ast(result, same_node, all_nodes)

    return ast

def find_same_node(ast, same_label):
    #posを消化する
    same_node = []
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
                rec(content)
            case Graph(nodes, edges):
                for node in nodes:
                    scope = node.modifier["scope"]
                    if not isinstance(node.concept, Concept):
                        rec(node.concept)
                        continue
                    same_name = [v for v in scope.concepts if isinstance(v.concept, Concept) and v.concept.name == node.concept.name]
                    if len(same_name) <= abs(node.modifier["pos"]):
                        raise Exception("Invalid position")
                    idx = [i for i, v in enumerate(same_name) if v.modifier["id"] == node.modifier["id"]][0]
                    target = same_name[node.modifier["pos"] + idx]
                    same_node.append((node.modifier["id"], target.modifier["id"]))
                return
    rec(ast)
    # labelの情報を統合
    same_node.extend([(v[0], vi) for v in same_label.values() for vi in v])

    return same_node

def flip_edge(graph, dict):
    pass

def rec_template(func):
    def rec(ast):
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
                return func(ast)
            case Graph(nodes, edges):
                return func(ast)
            case Node(concept, modifier):
                return func(ast)
            case Edge(relation, modifier):
                return func(ast)
    return rec

def modify_ast(ast, same_node, all_nodes):
    # 同値類をまとめる(連結成分を求める)
    G = nx.Graph()
    G.add_edges_from(same_node)
    connect = nx.connected_components(G)
    connect = [comp for comp in connect]
    # 代表元
    repr_dict = {}
    for comp in connect:
        for id in comp:
            if all_nodes[id].concept is not None:
                rep = all_nodes[id].modifier["id"]
                break
            
        for id in comp:
            repr_dict[id] = rep
    
    @rec_template
    def rec(ast):
        nonlocal repr_dict, all_nodes
        match ast:
            case Node(concept, modifier):
                return  all_nodes[repr_dict[modifier["id"]]]
            case Edge(relation, modifier):
                modifier["source"] = all_nodes[repr_dict[modifier["source"].modifier["id"]]]
                modifier["target"] = all_nodes[repr_dict[modifier["target"].modifier["id"]]]
                return Edge(relation, modifier)
            case Graph(nodes, edges):
                new_nodes = list(set([rec(node) for node in nodes]))
                new_edges = list(set([rec(edge) for edge in edges]))
                return Graph(new_nodes, edges)
            case Quantifier(name, concepts):
                concepts = [rec(concept) for concept in concepts]
                concepts = list(set(concepts))
                return Quantifier(name, concepts)
            
    result = rec(ast)
    return result


def expand_abbrev(ast):
    # 最上位がkostafeのQunatifiedのはず
    kostafe = ast.quantifier
    # 今
    kans = Node(Concept("kans"), modifier={"id": next(_node_counter), "scope": kostafe})
    kostafe.concepts.append(kans)
    @rec_template
    def rec(ast):
        match ast:
            case Node(concept, modifier):  
                nodes = []
                edges = []
                if "tense" in modifier:
                    if modifier["tense"] == "en": # 現在
                        # A-ik -> A aki kans
                        nodes += [ast, kans]
                        edges += [Edge(Relation("aki"), {"source": ast, "target": kans})]
                    elif modifier["tense"] == "ik": # 過去
                        # A-ik -> A aki t* liimes kans
                        t = Node(Concept("t"), modifier={"id": next(_node_counter), "scope": ast.modifier["scope"]})
                        ast.modifier["scope"].concepts.append(t)
                        nodes += [ast, t, kans]
                        edges += [Edge(Relation("aki"), {"source": ast, "target": t}), Edge(Relation("liimes"), {"source": t, "target": kans})]
                    elif modifier["tense"] == "as": # 未来
                        # A-ik -> A aki t* sammes kans
                        t = Node(Concept("t"), modifier={"id": next(_node_counter), "scope": ast.modifier["scope"]})
                        ast.modifier["scope"].concepts.append(t)
                        nodes += [ast, t, kans]
                        edges += [Edge(Relation("aki"), {"source": ast, "target": t}), Edge(Relation("sammes"), {"source": t, "target": kans})]
                return Graph(nodes, edges)
                    
            case Graph(nodes, edges):
                new_nodes = nodes.copy()
                new_edges = edges.copy()
                for node in nodes:
                    result = rec(node)
                    new_nodes.extend(result.nodes)
                    new_edges.extend(result.edges)

                new_nodes = list(set(new_nodes))
                new_edges = list(set(new_edges))
                return Graph(new_nodes, new_edges)
        
            case _:
                return ast
    
    result = rec(ast)
    return result   

def kono_to_logic(ast):
    kostafe = ast.quantifier
    # 追加で必要になる公理
    var_map = {}
    ax = []
    def rec(ast):
        match ast:
            case Discourse(sentences):
                result = {}
                result["sentence"] = [rec(sentence) for sentence in sentences if sentence.action == "Sentence"]
                result["question"] = [rec(sentence) for sentence in sentences if sentence.action == "Question"]
                return result
            case Sentence(content, situation, action):
                # 指標詞の処理はあとで考える
                return rec(content)
            case pla.And(left, right) | pla.Or(left, right) | pla.Imp(left, right) | pla.Iff(left, right):
                return type(ast)(rec(left), rec(right))
            case Quantified(quantifier, content):
                # 最上位だけ事前にスコーレム化する
                if quantifier == kostafe:
                    atoms = []
                    for concept in quantifier.concepts:
                        category = concept.concept.name
                        const = pla.Constant(str(concept))
                        var_map[concept] = const
                        domain = pla.Predicate(category, [var_map[concept]])
                        atoms.append(domain)
                    ax.extend(atoms)
                    return rec(content)

                name = quantifier.name
                # とりあえず∀と∃のみ
                for concept in quantifier.concepts:
                    var = pla.Var(str(concept))
                    var_map[concept] = var
                result = rec(content)
                if name in {"kostafe", "kon-lilee", "ena-lilee"}:
                    for concept in quantifier.concepts:
                        category = concept.concept.name
                        domain = pla.Predicate(category, [var_map[concept]])
                        result = pla.Exists([var_map[concept]], pla.And(domain, result))
                    return result
                elif name in {"san-lilee"}:
                    for concept in quantifier.concepts:
                        category = concept.concept.name
                        domain = pla.Predicate(category, [var_map[concept]])
                        result = pla.Forall([var_map[concept]], pla.And(domain, result))
                    return result

            case Graph(nodes, edges):
                atoms = []
                nodes = [var_map[node] for node in nodes]
                for edge in edges:
                    name, source, target = edge.relation, edge.modifier["source"], edge.modifier["target"]
                    neg_num = edge.modifier["neg"]
                    pred_name = name.name
                    pred = pla.Predicate(pred_name, [var_map[source],var_map[target]])
                    for _ in range(neg_num):
                        pred = pla.Not(pred)
                    atoms.append(pred)
                
                result = atoms[0]
                for atom in atoms[1:]:
                    result = pla.And(result, atom)
                return result
            case Concept(name):
                return pla.Constant(name)
    result = rec(ast)
    result["axioms"] = ax
    return result

def hierarchy(dictionary):
    if isinstance(dictionary, str):
        with open(dictionary) as f:
            dictionary = json.load(f) 

    # 一意化
    words = dictionary["words"]
    entries_map = {}
    for i, w in enumerate(words):
        if w == None:
            continue
        if w["entry"] not in entries_map:
            entries_map[w["entry"]] = []
        entries_map[w["entry"]].append(i)
    if entries_map["造語待ち"]:
        del entries_map["造語待ち"]
    for k, v in entries_map.items():
        if len(v) > 1:
            for i in range(len(v)):
                words[v[i]]["entry"] = f"{k}{i}"
                # print(f"Renamed {k} to {words[v[i]]['entry']}")

    ax_clause = []
    def rec(w):
        if "造語待ち" == w["entry"] or "children" not in w:
            return
        w["entry"] = w["entry"].replace(" ", "_")
        if len(w["children"]) == 0:
            # hierarchy.append(f"{w['entry']}({w['entry']}_0).")
            const = pla.Constant(f"{w['entry']}_default")
            positive = [pla.Predicate(w["entry"], [const])]
            ax_clause.append(pla.Clause(positive, []))
            return
        for cid in w["children"]:
            c = words[cid]
            if "造語待ち" == c["entry"]:
                continue
            else:
                positive = [pla.Predicate(w["entry"], [pla.Var("X")])]
                negative = [pla.Predicate(c["entry"], [pla.Var("X")])]
                ax_clause.append(pla.Clause(positive, negative))
            rec(c)
    rec(words[6])

    return ax_clause

    
def test_01():
    peg = pg.grammar("konomeno.tpeg")
    parser = pg.generate(peg)
    # code = "kon-lilee-α-β waka ja lon-hamin-ik ke ceja fylam ansa le-kalam tos-kon-α, hamin-ik-γ ke lesta kasa ansa mikam-laf tos-kon-β tos; hato waka ja sen-hamin-ik ke ena-nato no"
    code = "waka ja hamin ke kalam; hato sen-hamin-ik ke ena-nato no"
    tree = parser(code)
    print("Tree:", tree)
    ast = kono_to_ast(tree, None)
    print("AST:", ast)
    exp_ast = expand_abbrev(ast)
    print("Expanded AST:", exp_ast)
    logic = kono_to_logic(ast)
    print("Logic:", logic)
    cnf = pla.cnf_convert(logic["sentence"] + logic["axioms"])
    print("CNF:", cnf)
    clauses = pla.cnfs_to_clause(cnf)
    hierarchy_ax = hierarchy("dict/konomeno-v5.json")
    clauses = hierarchy_ax + clauses
    # clauses = clauses + hierarchy_ax
    query = pla.cnf_convert(pla.Not(logic["question"][0]))
    query = pla.cnf_to_clause(query)[0]
    print("Clauses:", clauses)
    with open("test.pl", "w") as f:
        for clause in clauses:
            f.write(f"{clause}.\n")
    result = res.SLD_resolution(clauses, query)
    print("Resolution:", result)


if __name__ == '__main__':
    test_01()