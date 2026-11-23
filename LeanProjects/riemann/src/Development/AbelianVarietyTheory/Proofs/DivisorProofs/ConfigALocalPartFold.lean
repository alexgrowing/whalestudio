import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF.InfMove

theorem weil_moves_rho_inf : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ g ∈ UAt σ G.V (evI F), ∀ (w : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)) (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))),
      locOpInf (om (g, 1)) (locOpInf (G.M.co.rho B.ψ (partInf F w)) f) =
        locOpInf (G.M.co.rho B.ψ (partInf F (actAB (cA σ) ((g, 1) : UA σ G.V.J × UA σ G.W.J) w))) (locOpInf (om (g, 1)) f) := by
  intro hP F E _ _ _ _ _ σ B b a' G G₁ H H' _ e _ ei ev _ X om om' om₁ om₁' hT _ g hg w f
  have hS := IsUWeilPair.isUSplitting hT.weil
  obtain ⟨r, h0, hr⟩ := exists_rest_inf F (Fin (b + 2) × Fin (b + 2 + a'))
  have hA : ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')), ∃ f₁ : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
      Acts (evI F) (om (g, 1)) f f₁ := fun f =>
    GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ (b + 2) (b + 2 + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om
      hT.base.cm hT.base.std hT.weil g hg f
  have hact : actAB (cA σ) ((g, 1) : UA σ G.V.J × UA σ G.W.J) (partInf F w) =
      partInf F (actAB (cA σ) ((g, 1) : UA σ G.V.J × UA σ G.W.J) w) := by
    change mat g * (realAd F 1 • w) * (mat (1 : UA σ G.W.J))ᵀ = realAd F 1 • (mat g * w * (mat (1 : UA σ G.W.J))ᵀ)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  set f' := locOpInf (G.M.co.rho B.ψ (partInf F w)) f
  set f1 := locOpInf (om (g, 1)) f
  have e1 := (locOpInf_rho G.M.co hT.base.std w f).1 r (hr f)
  have e2 := acts_locOpInf (hA f') r (hr f')
  have e3 := acts_locOpInf (hA f) r (hr f)
  have e4 := (locOpInf_rho G.M.co hT.base.std (actAB (cA σ) ((g, 1) : UA σ G.V.J × UA σ G.W.J) w) f1).1 r (hr f1)
  have himpl := hS.impl ((g, 1) : UA σ G.V.J × UA σ G.W.J) (partInf F w) _ (hr f).2
  rw [hact, e1, e2, e3, e4] at himpl
  exact DFunLike.coe_injective (eq_of_tens_inf h0 (hr f).1 himpl)

end GlobalTheory.ThK.LemF.InfMove
