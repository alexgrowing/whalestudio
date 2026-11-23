import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingVectorPreserves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleSeesawStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKNInvB

open GlobalTheory.PlaneLevi in

theorem levi_scale {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
    {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {j₀ j₁ r s : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hX : X.IsHerm σ B r s) (hσ : ∀ e : E, σ (σ e) = e) (t : ℕ) (ht : t ≠ 0) :
    ∃ m : UA σ X.J, mat m *ᵥ incV F H.x = (t : AE F E) • incV F H.x ∧
        (t : AE F E) • (mat m *ᵥ incV F H.y) = incV F H.y ∧ ∀ z : Fin n₁ → AE F E, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by
  have hyp : Hyp (σ := σ) (J := X.J) H.x H.y :=
    ⟨hH.xx, hH.yy, hH.xy, by rw [← form_swap hσ hX.herm, hH.xy, map_one]⟩
  have hs : (t : E) ≠ 0 := Nat.cast_ne_zero.2 ht
  have hσs : σ (t : E) = t := map_natCast σ t
  have hinv : levi σ X.J H.x H.y (t : E)⁻¹ * levi σ X.J H.x H.y (t : E) = 1 := by
    have := levi_mul_levi hyp (inv_ne_zero hs); rwa [inv_inv] at this
  let g : GL (Fin n) E := ⟨levi σ X.J H.x H.y t, levi σ X.J H.x H.y (t : E)⁻¹, levi_mul_levi hyp hs, hinv⟩
  refine ⟨toUA σ g (levi_unitary hσ hX.herm hyp hs hσs), ?_, ?_, ?_⟩
  · rw [mat_toUA]
    ext i
    change ((levi σ X.J H.x H.y t).map (inclR (F := F) (AF F)) *ᵥ ((inclR (F := F) (AF F)) ∘ H.x)) i = _
    rw [← RingHom.map_mulVec, levi_mulVec_of_hyp hyp]
    simp [incV, map_natCast]
  · rw [mat_toUA]
    ext i
    change (t : AE F E) * ((levi σ X.J H.x H.y t).map (inclR (F := F) (AF F)) *ᵥ ((inclR (F := F) (AF F)) ∘ H.y)) i = _
    rw [← RingHom.map_mulVec, levi_mulVec_y hyp, ← map_natCast (inclR (F := F) (AF F)) t, ← map_mul]
    simp only [incV, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  · intro z
    rw [mat_toUA, Matrix.mulVec_mulVec]
    congr 1
    change (levi σ X.J H.x H.y t).map (inclR (F := F) (AF F)) * H.ι.map (inclR (F := F) (AF F)) =
      H.ι.map (inclR (F := F) (AF F))
    rw [← Matrix.map_mul, levi_mul_of_orth _ hH.orth]

theorem unip_inv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ Φ ∈ PolData B G.M, ∀ h, ∀ n ∈ unip σ G.V H₀, ∀ g, thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (n * g, h) Φ))) = thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, h) Φ))) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ he Φ hΦ h n hn g
  have hs := IsUWeilPair.isUSplitting hT.weil
  have hstd : IsStd B.ψ := hT.base.std
  have hσσ : ∀ x : E, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    apply τ.injective
    rw [hT.base.cm.2.2.2 τ, hT.base.cm.2.2.2 τ, star_star]
  have hom : ∀ (x y : UA σ G.V.J) Ψ, om (x * y, 1) Ψ = om (x, 1) (om (y, 1) Ψ) := by
    intro x y Ψ
    rw [show ((x * y, 1) : UA σ G.V.J × UA σ G.W.J) = (x, 1) * (y, 1) by simp, map_mul]
    rfl
  have hsc := GlobalTheory.T.config_b_triple_seesaw hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ he
  have hmulS : ∀ (x y : UA σ G.V.J) (c₁ c₂ : ℂ), (∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (x, 1) Ψ) = c₁ • e₂ Ψ) →
      (∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (y, 1) Ψ) = c₂ • e₂ Ψ) →
      ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (x * y, 1) Ψ) = (c₁ * c₂) • e₂ Ψ := by
    intro x y c₁ c₂ hx hy Ψ hΨ
    rw [hom, hx _ (hs.pres _ _ hΨ), hy _ hΨ, smul_smul]
  have key : ∀ k ∈ unip σ G.V H₀, mat k *ᵥ incV F H₀.x = incV F H₀.x ∧
      ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (k, 1) Ψ) = e₂ Ψ := by
    have om11 : ∀ Ψ, om (1, 1) Ψ = Ψ := by
      intro Ψ
      rw [show ((1 : UA σ G.V.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one]
      rfl
    have gen : ∀ u : UA σ G.V.J, mat u *ᵥ incV F H₀.x = incV F H₀.x →
        (∀ z : Fin n₁ → AE F E, ∃ d : AE F E, mat u *ᵥ (incM F H₀.ι *ᵥ z) = incM F H₀.ι *ᵥ z + d • incV F H₀.x) →
        ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (u, 1) Ψ) = e₂ Ψ := by
      intro u hu1 hu2
      by_cases h0 : ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ Ψ = 0
      · intro Ψ hΨ
        rw [h0 _ (hs.pres _ _ hΨ), h0 _ hΨ]
      push_neg at h0
      obtain ⟨Ψ₀, hΨ₀, hne⟩ := h0
      obtain ⟨y, hy⟩ := Function.ne_iff.mp hne
      have ext : ∀ c c' : ℂ, c • e₂ Ψ₀ = c' • e₂ Ψ₀ → c = c' := by
        intro c c' hcc
        have h1 := congrFun hcc y
        simp only [Pi.smul_apply, smul_eq_mul] at h1
        exact mul_right_cancel₀ hy h1
      have hinvS : ∀ (x : UA σ G.V.J) (c : ℂ), (∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (x, 1) Ψ) = c • e₂ Ψ) →
          c ≠ 0 ∧ ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (x⁻¹, 1) Ψ) = c⁻¹ • e₂ Ψ := by
        intro x c hx
        have hrec : ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ Ψ = c • e₂ (om (x⁻¹, 1) Ψ) := by
          intro Ψ hΨ
          rw [← hx _ (hs.pres _ _ hΨ), ← hom, mul_inv_cancel, om11]
        have hc : c ≠ 0 := by
          rintro rfl
          apply hne
          rw [hrec _ hΨ₀, zero_smul]
        refine ⟨hc, fun Ψ hΨ => ?_⟩
        rw [hrec _ hΨ, smul_smul, inv_mul_cancel₀ hc, one_smul]
      have hpowS : ∀ (x : UA σ G.V.J) (c : ℂ), (∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (x, 1) Ψ) = c • e₂ Ψ) →
          ∀ k : ℕ, ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (x ^ k, 1) Ψ) = (c ^ k) • e₂ Ψ := by
        intro x c hx k
        induction k with
        | zero => intro Ψ _; rw [pow_zero, pow_zero, om11, one_smul]
        | succ k ih => intro Ψ hΨ; rw [pow_succ, pow_succ]; exact hmulS _ _ _ _ ih hx Ψ hΨ
      obtain ⟨m2, hm2x, hm2y, hm2ι⟩ : ∃ m : UA σ G.V.J, mat m *ᵥ incV F H₀.x = ((2 : ℕ) : AE F E) • incV F H₀.x ∧
          ((2 : ℕ) : AE F E) • (mat m *ᵥ incV F H₀.y) = incV F H₀.y ∧ ∀ z : Fin n₁ → AE F E, mat m *ᵥ (incM F H₀.ι *ᵥ z) = incM F H₀.ι *ᵥ z :=
        levi_scale hH₀ hV₂ hσσ 2 two_ne_zero
      obtain ⟨m3, hm3x, hm3y, hm3ι⟩ : ∃ m : UA σ G.V.J, mat m *ᵥ incV F H₀.x = ((3 : ℕ) : AE F E) • incV F H₀.x ∧
          ((3 : ℕ) : AE F E) • (mat m *ᵥ incV F H₀.y) = incV F H₀.y ∧ ∀ z : Fin n₁ → AE F E, mat m *ᵥ (incM F H₀.ι *ᵥ z) = incM F H₀.ι *ᵥ z :=
        levi_scale hH₀ hV₂ hσσ 3 (by norm_num)
      obtain ⟨cu, hcu⟩ := hsc u 1 (by rw [one_smul]; exact hu1) hu2
      obtain ⟨c2, hc2⟩ := hsc m2 _ hm2x (fun z => ⟨0, by rw [zero_smul, add_zero, hm2ι]⟩)
      obtain ⟨c3, hc3⟩ := hsc m3 _ hm3x (fun z => ⟨0, by rw [zero_smul, add_zero, hm3ι]⟩)
      obtain ⟨hcu0, hcuI⟩ := hinvS u cu hcu
      obtain ⟨hc20, hc2I⟩ := hinvS m2 c2 hc2
      obtain ⟨hc30, hc3I⟩ := hinvS m3 c3 hc3
      have hvS : ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (u⁻¹ * u⁻¹ * (m2 * u * m2⁻¹), 1) Ψ) = cu⁻¹ • e₂ Ψ := by
        intro Ψ hΨ
        have h1 := hmulS _ _ _ _ (hmulS _ _ _ _ hcuI hcuI) (hmulS _ _ _ _ (hmulS _ _ _ _ hc2 hcu) hc2I) Ψ hΨ
        rwa [show cu⁻¹ * cu⁻¹ * (c2 * cu * c2⁻¹) = cu⁻¹ by field_simp] at h1
      have hconj : ∀ (m : UA σ G.V.J) (c : ℂ), (∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (m, 1) Ψ) = c • e₂ Ψ) →
          (∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (m⁻¹, 1) Ψ) = c⁻¹ • e₂ Ψ) → c ≠ 0 →
          ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (m * (u⁻¹ * u⁻¹ * (m2 * u * m2⁻¹)) * m⁻¹, 1) Ψ) = cu⁻¹ • e₂ Ψ := by
        intro m c hm hmI hc Ψ hΨ
        have h1 := hmulS _ _ _ _ (hmulS _ _ _ _ hm hvS) hmI Ψ hΨ
        rwa [show c * cu⁻¹ * c⁻¹ = cu⁻¹ by field_simp] at h1
      have hm2x' : mat m2 *ᵥ incV F H₀.x = (2 : AE F E) • incV F H₀.x := by rw [hm2x, Nat.cast_ofNat]
      have hm2y' : (2 : AE F E) • (mat m2 *ᵥ incV F H₀.y) = incV F H₀.y := by
        have h1 := hm2y
        rwa [Nat.cast_ofNat] at h1
      obtain ⟨cy, z₀, huy⟩ : ∃ (c : AE F E) (z₀ : Fin n₁ → AE F E), mat u *ᵥ incV F H₀.y = incV F H₀.y + c • incV F H₀.x + incM F H₀.ι *ᵥ z₀ :=
        GlobalTheory.UnipLine.mulVec_y hH₀ hV₂ u hu1
      have hspan : ∀ w : Fin a → AE F E, ∃ (c d : AE F E) (z : Fin n₁ → AE F E), w = c • incV F H₀.x + incM F H₀.ι *ᵥ z + d • incV F H₀.y :=
        GlobalTheory.UnipLine.span_A hH₀ hV₂
      have hcen2 := GlobalTheory.UnipLine.conj_eq_pow hspan u hu1 hu2 cy z₀ huy m2 m2 2 hm2x' hm2y' hm2ι hm2x hm2y hm2ι
      have hcen3 := GlobalTheory.UnipLine.conj_eq_pow hspan u hu1 hu2 cy z₀ huy m2 m3 3 hm2x' hm2y' hm2ι hm3x hm3y hm3ι
      have e4 : cu⁻¹ = cu⁻¹ ^ (2 ^ 2) := by
        refine ext _ _ ?_
        rw [← hconj m2 c2 hc2 hc2I hc20 _ hΨ₀, hcen2, hpowS _ _ hvS _ _ hΨ₀]
      have e9 : cu⁻¹ = cu⁻¹ ^ (3 ^ 2) := by
        refine ext _ _ ?_
        rw [← hconj m3 c3 hc3 hc3I hc30 _ hΨ₀, hcen3, hpowS _ _ hvS _ _ hΨ₀]
      have hw0 : cu⁻¹ ≠ 0 := inv_ne_zero hcu0
      have h3 : cu⁻¹ ^ 3 = 1 := by
        have h4 : cu⁻¹ * cu⁻¹ ^ 3 = cu⁻¹ * 1 := by rw [mul_one, ← pow_succ']; norm_num at e4 ⊢; exact e4.symm
        exact mul_left_cancel₀ hw0 h4
      have h1 : cu⁻¹ = 1 := by
        rw [e9, show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul, h3, one_pow]
      have hcu1 : cu = 1 := inv_eq_one.mp h1
      intro Ψ hΨ
      rw [hcu _ hΨ, hcu1, one_smul]
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem u hu => exact ⟨hu.1, gen u hu.1 hu.2⟩
    | one => exact ⟨by rw [GlobalTheory.UnipLine.mat_one, Matrix.one_mulVec], fun Ψ _ => by rw [om11]⟩
    | mul x y _ _ hx hy =>
      exact ⟨by rw [GlobalTheory.UnipLine.mulVec_mul, hy.1, hx.1], fun Ψ hΨ => by rw [hom, hx.2 _ (hs.pres _ _ hΨ), hy.2 _ hΨ]⟩
    | inv x _ hx =>
      refine ⟨GlobalTheory.UnipLine.inv_mulVec_of_mulVec hx.1, fun Ψ hΨ => ?_⟩
      have h1 := hx.2 _ (hs.pres (x⁻¹, 1) Ψ hΨ)
      rw [← hom, mul_inv_cancel, om11] at h1
      exact h1.symm
  have hΦs : Φ ∈ schA F (Fin a × Fin (a + (b + 2))) := by
    refine (Submodule.span_le.2 ?_) hΦ
    rintro Φ ⟨f, -, φ, hSB, hev, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2)
  have hΨ := hs.pres (g, h) Φ hΦs
  obtain ⟨hx, hinv⟩ := key n hn
  have hact : actAB (cA σ) ((n, 1) : UA σ G.V.J × UA σ G.W.J) (shiftA H₀ H' 1) = shiftA H₀ H' 1 := by
    unfold actAB shiftA
    rw [Units.val_one, one_smul, Matrix.mul_vecMulVec]
    erw [hx]
    simp
  rw [show ((n * g, h) : UA σ G.V.J × UA σ G.W.J) = (n, 1) * (g, h) by simp, map_mul, Module.End.mul_apply]
  rw [← hact, ← hs.impl (n, 1) _ _ hΨ, hact, hinv _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd _ _ hΨ)]

end GlobalTheory.ThKNInvB
