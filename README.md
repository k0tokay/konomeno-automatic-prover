# コノメノによる自動証明器
コノメノを論理型プログラミング言語，自動定理証明器として実装する試み．参考のためにPrologのインタプリタも実装する．

- **resolution.py**  代入，単一化，SLD導出など
- **prolog.tpeg**  Prologの(基礎的な部分の)解析表現文法による文法
- **prolog_interpreter.py**  Prologの(基礎的な部分の)インタプリタ

## 参考文献
[1] 倉光 君郎．Pythonで学ぶ解析表現文法と構文解析．森北出版．2022．
[2] 萩野 達也．知識処理論．産業図書．1995．
[3] 小野 寛晰．情報科学における論理．日本評論社．1994．