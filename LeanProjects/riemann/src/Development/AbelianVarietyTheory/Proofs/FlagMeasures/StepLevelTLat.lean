import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in

theorem _root_.GlobalTheory.St.G.stepLevel_tLat : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : _root_.Formalism.L2.Forms.StepLevel F E σ J T f bad),
    _root_.GlobalTheory.St.G.TLat σ J T f S.Lb := by
  intro F E _ _ _ _ _ n σ J T f bad S
  refine ⟨⟨S.Lb_fin, S.Lb_span⟩, S.Lb_int, S.Lb_dual, S.Lb_index, fun v hv => ?_⟩
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (S.fT_ne v hv)
  exact ⟨x, x.2, fun hmem => hx (S.fT_L v hv x hmem)⟩

end GlobalTheory.St.G
