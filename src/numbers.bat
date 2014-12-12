echo "Domain library:"
coqwc  Categories.v NSetoid.v PredomCore.v PredomFix.v PredomKleisli.v PredomLift.v PredomRec.v PredomSum.v PredomAll.v

echo "Typed PCF:"
coqwc typedadequacy.v typeddensem.v typedlambda.v typedopsem.v typedsoundness.v typedsubst.v

echo "Uni-Typed CVB Lambda Calculus:"
coqwc uniiop.v unii.v uniirec.v uniisem.v uniisound.v uniiade.v KnasterTarski.v

echo "Metric library:"
coqwc MetricCore.v MetricRec.v

echo "Kitchen Sink:"
coqwc mpremet.v KSSem.v Finmap.v FinmapMetric.v KSOp.v KSTyping.v KSTm.v KSTy.v Fin.v








