import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleSeesawIdentityStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixVPlaneRescaled

theorem twist_heis_inv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (hT : IsTriple B G X om om') (V₂ : Spc F E a) (n₁ d₁ : ℕ) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H₀ : Plane E a n₁)
    (H' : Plane E (a + a') d₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁) (e₂ : Fn F a (a + a') →ₗ[ℂ] Fn F n₁ d₁)
    (hH₀ : H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁) (he : IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂)
    (k : UA σ G.V.J) (c : AE F E) (hx : mat k *ᵥ incV F H₀.x = c • incV F H₀.x)
    (hι : ∀ z : Fin n₁ → AE F E, ∃ d : AE F E, mat k *ᵥ (incM F H₀.ι *ᵥ z) = incM F H₀.ι *ᵥ z + d • incV F H₀.x) :
    (∀ z, ∀ Φ ∈ schA F (Fin a × Fin (a + a')),
      e₂ (om (k, 1) (G.M.co.rho B.ψ (incM F H₀.ι * z * (incM F H'.ι)ᵀ) Φ)) = M₂.co.rho B.ψ z (e₂ (om (k, 1) Φ))) ∧
    ∀ u ∈ isoA (F := F) H₀ H', ∀ Φ ∈ schA F (Fin a × Fin (a + a')), e₂ (om (k, 1) (G.M.co.rho B.ψ u Φ)) = e₂ (om (k, 1) Φ) := by
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hs := IsUWeilPair.isUSplitting hP.weil
  have hstd : IsStd B.ψ := hP.base.std
  have hc : ∀ t : E, cA σ (inclR (F := F) (AF F) t) = inclR (F := F) (AF F) (σ t) := fun t => rfl
  have hact : ∀ w, actAB (cA σ) ((k, 1) : UA σ G.V.J × UA σ G.W.J) w = mat k * w := by
    intro w; simp [actAB, mat]
  have hcomp : ∀ w w' Φ, symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) w w' = 0 →
      G.M.co.rho B.ψ w (G.M.co.rho B.ψ w' Φ) = G.M.co.rho B.ψ (w + w') Φ := by
    intro w w' Φ h0
    simp only [Darboux.rho]
    have hlaw : ∀ (v v' : (Fin a × Fin (a + a') → AF F) × (Fin a × Fin (a + a') → AF F))
        (φ : (Fin a × Fin (a + a') → AF F) → ℂ),
        schr B.ψ v (schr B.ψ v' φ) = B.ψ (⅟(2 : AF F) * (v.1 ⬝ᵥ v'.2 - v'.1 ⬝ᵥ v.2)) • schr B.ψ (v + v') φ := by
      intro v v' φ
      funext x
      simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add,
        add_assoc, add_dotProduct, dotProduct_add]
      congr 2
      linear_combination (-(v.1 ⬝ᵥ v'.2)) * invOf_mul_self (2 : AF F)
    rw [hlaw, ← G.M.co.form, h0, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add]
  have hcol : ∀ m, ∑ i, ∑ j, H₀.ι i m * (G.V.J i j * σ (H₀.x j)) = 0 := by
    intro m
    have h := (hH₀.orth (Pi.single m 1)).1
    simp only [form, reS, Matrix.mulVec_single_one, dotProduct, Matrix.mulVec] at h
    simpa [Finset.mul_sum, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_mul] using h
  have hperp : ∀ (z : Matrix (Fin n₁) (Fin (a + a')) (AE F E)) (q : Fin (a + a') → AE F E),
      symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (incM F H₀.ι * z) (Matrix.vecMulVec (incV F H₀.x) q) = 0 := by
    intro z q
    have hinner : ∀ j, ∑ i, ∑ l, (incM F H₀.ι * z) i j * incM F G.V.J i l * cA σ (incV F H₀.x l) = 0 := by
      intro j
      have e1 : ∀ i l, (incM F H₀.ι * z) i j * incM F G.V.J i l * cA σ (incV F H₀.x l) =
          ∑ m, z m j * inclR (F := F) (AF F) (H₀.ι i m * (G.V.J i l * σ (H₀.x l))) := by
        intro i l
        rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [incM, incV, Matrix.map_apply, hc, map_mul]
        ring
      simp_rw [e1]
      calc _ = ∑ i, ∑ m, ∑ l, z m j * inclR (F := F) (AF F) (H₀.ι i m * (G.V.J i l * σ (H₀.x l))) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ m, ∑ i, ∑ l, z m j * inclR (F := F) (AF F) (H₀.ι i m * (G.V.J i l * σ (H₀.x l))) := Finset.sum_comm
        _ = ∑ m, z m j * inclR (F := F) (AF F) (∑ i, ∑ l, H₀.ι i m * (G.V.J i l * σ (H₀.x l))) := by
            simp [map_sum, Finset.mul_sum]
        _ = 0 := Finset.sum_eq_zero fun m _ => by rw [hcol m, map_zero, mul_zero]
    have hTn : hTens (cA σ) (incM F G.V.J) (incM F G.W.J) (incM F H₀.ι * z) (Matrix.vecMulVec (incV F H₀.x) q) = 0 := by
      unfold hTens
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have e2 : ∀ i l, ∑ r, (incM F H₀.ι * z) i j * incM F G.V.J i l * incM F G.W.J j r *
          cA σ (Matrix.vecMulVec (incV F H₀.x) q l r) =
          ((incM F H₀.ι * z) i j * incM F G.V.J i l * cA σ (incV F H₀.x l)) * ∑ r, incM F G.W.J j r * cA σ (q r) := by
        intro i l
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp only [Matrix.vecMulVec_apply, map_mul]
        ring
      simp_rw [e2, ← Finset.sum_mul, hinner j, zero_mul]
    simp [symp, hTn]
  choose β hβ using fun j : Fin n₁ => hι (Pi.single j 1)
  have hgι : mat k * incM F H₀.ι = incM F H₀.ι + Matrix.vecMulVec (incV F H₀.x) β := by
    ext i j
    have h := congrFun (hβ j) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    simpa [Matrix.vecMulVec_apply, mul_comm] using h
  refine ⟨fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩
  · have hΨ := hs.pres (k, 1) Φ hΦ
    rw [hs.impl (k, 1) _ Φ hΦ, hact]
    have hw : mat k * (incM F H₀.ι * z * (incM F H'.ι)ᵀ) =
        incM F H₀.ι * (z * (incM F H'.ι)ᵀ) + Matrix.vecMulVec (incV F H₀.x) (incM F H'.ι *ᵥ (β ᵥ* z)) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc, hgι, Matrix.add_mul]
      congr 1
      rw [Matrix.vecMulVec_mul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]
    have hh := he.Heisenberg₂ z _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd
      (Matrix.vecMulVec (incV F H₀.x) (incM F H'.ι *ᵥ (β ᵥ* z))) _ hΨ)
    rw [hw, ← hcomp _ _ _ (hperp _ _), ← Matrix.mul_assoc, hh, he.inv _ (Or.inr ⟨_, rfl⟩) _ hΨ]
  · have hΨ := hs.pres (k, 1) Φ hΦ
    rw [hs.impl (k, 1) _ Φ hΦ, hact]
    rcases hu with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · rw [Matrix.mul_vecMulVec]
      exact he.inv _ (Or.inl ⟨_, rfl⟩) _ hΨ
    · rw [Matrix.mul_vecMulVec, hx]
      refine he.inv _ (Or.inr ⟨c • z, ?_⟩) _ hΨ
      rw [Matrix.mulVec_smul]
      ext i j
      simp [Matrix.vecMulVec_apply]
      ring

section
open scoped Classical

theorem proj_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (y : κ → AF F) :
    (LinearMap.proj y : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (y i).2) • ((BoundedContinuousFunction.evalCLM ℂ (fun i => evI F (y i))).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp only [LinearMap.coe_proj, Function.eval, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, smul_eq_mul, pureA]
  rw [mul_comm]
  rfl

end

theorem twist_scalar : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ →
    ∀ (k : UA σ G.V.J) (c : AE F E), mat k *ᵥ incV F H₀.x = c • incV F H₀.x →
    (∀ z : Fin n₁ → AE F E, ∃ d : AE F E, mat k *ᵥ (incM F H₀.ι *ᵥ z) = incM F H₀.ι *ᵥ z + d • incV F H₀.x) →
    ∃ s : ℂ, ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (k, 1) Ψ) = s • e₂ Ψ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ he k c hx hι
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hS := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨h1, h2⟩ := twist_heis_inv F E σ B a (b + 2) G X om om' hT V₂ n₁ (a + b) X₁ G₁.W H₀ H' j₀ j₁ M₂ e₂ hH₀ he k c hx hι
  refine GlobalTheory.T.config_b_triple_seesaw_identity hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ he
    (e₂ ∘ₗ om (k, 1)) h1 h2 fun y => ?_
  have := hS.adm (k, 1) _ (GlobalTheory.T.eigen_intertwiner_good_models F E σ B _ _ _ _ G.V G.W X₁ G₁.W G.M M₂ H₀.ι H'.ι _ e₂ hP.good hM₂ he _
    (proj_adm F _ y))
  rwa [LinearMap.comp_assoc] at this

end GlobalTheory.MixVPlaneRescaled

end
