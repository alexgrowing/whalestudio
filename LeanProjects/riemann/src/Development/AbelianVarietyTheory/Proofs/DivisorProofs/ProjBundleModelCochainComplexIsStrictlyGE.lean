import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem cochain_chains_subsingleton {R : Type} [CommRing R] (E : Spc) (I : Cx R) (hI : I.IsStrictlyGE 0) (n : ℤ)
    (hn : n < 0) : Subsingleton (Cochain ((chains R).obj E) I n) := by
  constructor
  intro a b
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : 0 < p
  · have hz : IsZero (((chains R).obj E).X p) :=
      HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat p (fun i hi => by
        change -(i : ℤ) = p at hi
        omega)
    exact hz.eq_of_src _ _
  · have hz : IsZero (I.X q) := I.isZero_of_isStrictlyGE 0 q (by omega)
    exact hz.eq_of_tgt _ _

theorem Jcx_isStrictlyGE (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (hI : I.IsStrictlyGE 0) :
    (Jcx R q N I).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have hpre : IsZero (cotPre R q N I n) := by
    refine Functor.isZero _ (fun U => ?_)
    have h := cochain_chains_subsingleton (sch.obj U.unop ⨯ fibQ q N) I hI n hn
    letI : Subsingleton ((cotPre R q N I n).obj U) := h
    exact ModuleCat.isZero_of_subsingleton _
  exact (presheafToSheaf Scheme.etaleTopology.{0} _).map_isZero hpre

end GlobalTheory.EtC

end
