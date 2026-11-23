import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorMemAdelicForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upwardOperator_mem_adelicForms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ (res : 𝓞 E →+* k) (t : 𝓞 E) (lam : ι → DomWeight n), ∀ g ∈ AdForms S emb lam, upAd res t v p g ∈ AdForms S emb lam := by
  first | exact @GlobalTheory.LevelHecke.UpKeeps.upAd_mem_adForms | exact GlobalTheory.LevelHecke.UpKeeps.upAd_mem_adForms | (intros; apply GlobalTheory.LevelHecke.UpKeeps.upAd_mem_adForms <;> assumption)
