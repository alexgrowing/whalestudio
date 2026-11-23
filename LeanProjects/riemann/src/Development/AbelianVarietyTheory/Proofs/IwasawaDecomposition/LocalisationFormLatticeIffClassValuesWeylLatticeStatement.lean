import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationFormLatticeIffClassValuesWeylLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisation_formLattice_iff_classValues_weylLattice : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (Pl : Rows.Places K) (w : Pl.Pl) (p : ℕ) [Fact p.Prime] (iL : K →+* ℂ_[p]), (∀ x, x ∈ intW Pl w ↔ ‖iL x‖ ≤ 1) → ∀ x : S.FormsK emb lam h, x ∈ locW Pl w (S.latOf emb lam h fun c => delAtr emb lam (S.Lsh c.1 (S.rep c))) ↔ ∀ c, x.1 c ∈ locW Pl w (delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
  first | exact @GlobalTheory.Mem.Col2.GStep.locW_latOf_iff | exact GlobalTheory.Mem.Col2.GStep.locW_latOf_iff | (intros; apply GlobalTheory.Mem.Col2.GStep.locW_latOf_iff <;> assumption)
