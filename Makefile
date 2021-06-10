.PHONY: test Everything.agda clean

OTHEROPTS=

RTSARGS = +RTS -M6G -A128M ${OTHEROPTS} -RTS

test: Everything.agda
	agda ${RTSARGS} -i. Everything.agda

html: Everything.agda
	agda ${RTSARGS} --html -i. Everything.agda

Everything.agda:
	git ls-tree --full-tree -r --name-only HEAD | grep '^src/[^\.]*.agda' | sed -e 's|^src/[/]*|import |' -e 's|/|.|g' -e 's/.agda//' -e '/import Everything/d' | LC_COLLATE='C' sort > Everything.agda

tex: Trivial.lagda src/Fragment/Algebra/Signature.lagda src/Fragment/Algebra/Algebra.lagda src/Fragment/Equational/Theory/Bundles.lagda
	agda -i. --latex Trivial.lagda
	agda --latex src/Fragment/Algebra/Signature.lagda
	agda --latex src/Fragment/Algebra/Algebra.lagda
	agda --latex src/Fragment/Algebra/Homomorphism/Base.lagda
	agda --latex src/Fragment/Algebra/Homomorphism/Definitions.lagda
	agda --latex src/Fragment/Algebra/Quotient.lagda
	agda --latex src/Fragment/Algebra/Free/Atoms.lagda
	agda --latex src/Fragment/Algebra/Free/Base.lagda
	agda --latex src/Fragment/Algebra/Free/Evaluation.lagda
	agda --latex src/Fragment/Equational/Theory/Base.lagda
	agda --latex src/Fragment/Equational/Theory/Laws.lagda
	agda --latex src/Fragment/Equational/Theory/Bundles.lagda
	agda --latex src/Fragment/Equational/Model/Base.lagda
	agda --latex src/Fragment/Equational/Model/Satisfaction.lagda
	agda --latex src/Fragment/Equational/Model/Synthetic.lagda
	agda --latex src/Fragment/Equational/Coproduct.lagda
	agda --latex src/Fragment/Equational/FreeExtension/Base.lagda
	agda --latex src/Fragment/Equational/FreeExtension/Properties.lagda
	agda --latex src/Fragment/Examples/CSemigroup/Arith/Functions.lagda
	agda --latex src/Fragment/Examples/Semigroup/Arith/Reasoning.lagda
	agda --latex src/Fragment/Examples/Semigroup/Types.lagda

clean:
	$(RM) -r latex/
	find . -name '*.agdai' -exec rm \{\} \;

profile: Everything.agda
	agda ${RTSARGS} -v profile:7 -v profile.definitions:15 -i. Everything.agda
