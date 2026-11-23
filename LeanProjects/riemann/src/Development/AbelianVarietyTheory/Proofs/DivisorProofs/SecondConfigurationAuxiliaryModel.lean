import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneRestriction

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
noncomputable section

namespace GlobalTheory.ThK

theorem exists_isLevi_herm_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ l : (AE F E)ˣ, ∃ m₀ : UA σ G.V.J, IsLevi (W₁ := X₁) H₀ l 1 m₀ := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' _ X om om' om₁ om₁' hT _ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hH hA _ _ t
  have hσ := GlobalTheory.LeviTorusH.sigma_invol hT.base.cm
  have hc : ∀ a : AE F E, (cA σ).toRingHom ((cA σ).toRingHom a) = a := GlobalTheory.LeviTorusH.cA_invol hσ
  have hJ : ∀ i j, (cA σ).toRingHom (incM F G.V.J j i) = incM F G.V.J i j := by
    intro i j
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, incM, Matrix.map_apply, GlobalTheory.LeviTorusH.cA_incl]
    exact congrArg _ (hH.herm i j)
  have hXX : incV F H₀.x ⬝ᵥ incM F G.V.J *ᵥ (fun i => (cA σ).toRingHom (incV F H₀.x i)) = 0 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H₀.x i)) = fun i => cA σ (incV F H₀.x i) from rfl,
      GlobalTheory.LeviTorusH.form_incl]
    exact (congrArg _ hA.xx).trans (map_zero _)
  have hYY : incV F H₀.y ⬝ᵥ incM F G.V.J *ᵥ (fun i => (cA σ).toRingHom (incV F H₀.y i)) = 0 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H₀.y i)) = fun i => cA σ (incV F H₀.y i) from rfl,
      GlobalTheory.LeviTorusH.form_incl]
    exact (congrArg _ hA.yy).trans (map_zero _)
  have hXY : incV F H₀.x ⬝ᵥ incM F G.V.J *ᵥ (fun i => (cA σ).toRingHom (incV F H₀.y i)) = 1 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H₀.y i)) = fun i => cA σ (incV F H₀.y i) from rfl,
      GlobalTheory.LeviTorusH.form_incl]
    exact (congrArg _ hA.xy).trans (map_one _)
  have h01 := GlobalTheory.LeviTorusH.torus_mul_inv hc hJ hXY t hXX hYY
  have h10 : GlobalTheory.LeviTorusH.torusMat (cA σ).toRingHom (incM F G.V.J) (incV F H₀.x) (incV F H₀.y) t⁻¹ *
      GlobalTheory.LeviTorusH.torusMat (cA σ).toRingHom (incM F G.V.J) (incV F H₀.x) (incV F H₀.y) t = 1 :=
    by simpa only [inv_inv] using GlobalTheory.LeviTorusH.torus_mul_inv hc hJ hXY t⁻¹ hXX hYY
  refine ⟨⟨⟨GlobalTheory.LeviTorusH.torusMat (cA σ).toRingHom (incM F G.V.J) (incV F H₀.x) (incV F H₀.y) t, _, h01, h10⟩, ?_⟩, ?_, ?_, ?_⟩
  · exact GlobalTheory.LeviTorusH.torus_unitary hc hJ hXY t hXX hYY
  · exact GlobalTheory.LeviTorusH.torus_mulVec_x hXY t hXX
  · exact GlobalTheory.LeviTorusH.torus_mulVec_y hc hJ hXY t hYY
  · have hu : (incM F G.V.J *ᵥ fun i => (cA σ).toRingHom (incV F H₀.y i)) ᵥ* incM F H₀.ι = 0 := by
      rw [show (fun i => (cA σ).toRingHom (incV F H₀.y i)) = fun i => cA σ (incV F H₀.y i) from rfl,
        GlobalTheory.LeviTorusH.vecMul_incM]
      funext j
      exact (congrArg _ (hA.orth (Pi.single j 1)).2).trans (map_zero _)
    have hw : (incM F G.V.J *ᵥ fun i => (cA σ).toRingHom (incV F H₀.x i)) ᵥ* incM F H₀.ι = 0 := by
      rw [show (fun i => (cA σ).toRingHom (incV F H₀.x i)) = fun i => cA σ (incV F H₀.x i) from rfl,
        GlobalTheory.LeviTorusH.vecMul_incM]
      funext j
      exact (congrArg _ (hA.orth (Pi.single j 1)).1).trans (map_zero _)
    show GlobalTheory.LeviTorusH.torusMat (cA σ).toRingHom (incM F G.V.J) (incV F H₀.x) (incV F H₀.y) t * incM F H₀.ι =
      incM F H₀.ι * 1
    rw [Matrix.mul_one]
    exact GlobalTheory.LeviTorusH.torus_mul_of t _ hu hw

end GlobalTheory.ThK

end
