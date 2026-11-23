import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportQuotientSpanIffOfIsPushout
import Mathlib
open CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_support_quotient_span_iff_of_isPushout' : ∀ (R S R' S' : CommRingCat.{0}) (qa : R ⟶ S) (ba : R ⟶ R') (ga : S ⟶ S') (qa' : R' ⟶ S'), IsPushout qa ba ga qa' → qa.hom.Finite → ∀ {ι : Type} (s : ι → S) (p : PrimeSpectrum R'), ((letI := qa'.hom.toAlgebra; p ∈ Module.support R' (S' ⧸ Submodule.span R' (Set.range (fun i => ga.hom (s i))))) ↔ (letI := qa.hom.toAlgebra; PrimeSpectrum.comap ba.hom p ∈ Module.support R (S ⧸ Submodule.span R (Set.range s)))) := by
  first | (exact @GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout) | (exact GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout) | (intros; apply GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout  <;> assumption)
