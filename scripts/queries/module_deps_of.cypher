// Every Geometry module transitively required by a target module's decls.
// Pass the target as a `just q` arg: `just q module_deps_of Geometry.Ch3.Prop.P5`.
// Useful when shaking imports: anything the term-graph reaches must be in
// the import closure; anything else *may* be droppable (caveat: this is a
// term-level reachability, so syntax/notation/tactic providers are not
// listed here — treat the result as a lower bound and cross-check with
// `lake build`).
MATCH (root:Decl)-[:DECLARED_IN]->(rm:Module {name: '$1'})
MATCH (root)-[:USES*1..]->(d:Decl)-[:DECLARED_IN]->(m:Module)
WHERE m.name STARTS WITH 'Geometry' AND m.name <> '$1'
RETURN DISTINCT m.name AS module
ORDER BY module;
