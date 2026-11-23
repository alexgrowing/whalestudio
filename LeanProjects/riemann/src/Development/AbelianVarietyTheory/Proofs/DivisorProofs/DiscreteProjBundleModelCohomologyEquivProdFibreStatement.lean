import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteProjBundleModelCohomologyEquivProdFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_projBundleModel_cohomology_equiv_prod_fibre : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ), ∃ e : CohomologyClass ((chains R).obj (disc.obj F)) (Jcx R q N I) n ≃+ CohomologyClass ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, ∀ (β : Cocycle ((chains R).obj (disc.obj F)) (Jcx R q N I) n) (γ : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n), (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), β.1.v (-(p : ℤ)) s h = 0) → (∀ (U : Scheme.{0}) (x : F.obj (op U)), ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n, ev β.1 0 n (by simp) U x = Jsec c ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + n = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) k V), ev c k s hs V y = ev γ.1 k s hs V (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y)) → e (CohomologyClass.mk β) = CohomologyClass.mk γ := by
  first | (exact @GlobalTheory.EtC.DiscCoch.model) | (exact GlobalTheory.EtC.DiscCoch.model) | (intros; apply GlobalTheory.EtC.DiscCoch.model <;> assumption)
