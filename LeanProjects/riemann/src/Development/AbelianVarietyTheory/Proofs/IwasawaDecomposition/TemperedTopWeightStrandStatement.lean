import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedTopWeightStrand
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_top_weight_strand : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (m : ℕ) (hS : ∀ σ, ∀ v ∈ wtSpace a (-(m : ℤ)), a.ρ σ v ∈ wtSpace a (-(m : ℤ))) (hB : IsSubWD a (strand a.N (wtSpace a (-(m : ℤ))) m)), a.Tempered → (∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥) → WD.mk (restrict a _ hB) = ((WD.mk (restrictρ a _ hS)).lpTw ((m : ℝ) / 2)).lpChar (WD.lpSp h (m + 1)) := by
  first | exact @GlobalTheory.WeilDeligne.PrimDecomp.mk_restrict_strand_eq | exact GlobalTheory.WeilDeligne.PrimDecomp.mk_restrict_strand_eq | (intros; apply GlobalTheory.WeilDeligne.PrimDecomp.mk_restrict_strand_eq <;> assumption)
