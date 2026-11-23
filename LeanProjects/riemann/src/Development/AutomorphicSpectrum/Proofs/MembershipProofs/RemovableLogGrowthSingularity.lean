import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibility

noncomputable section

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct ContDiff Classical

namespace GlobalTheory.CompanionTheory.ThetaBox

section Schwartz

variable {E A B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem decay_comp (f : SchwartzMap A ℂ) (p : E →L[ℝ] A) (k n : ℕ) :
    ∃ C : ℝ, ∀ x, ‖p x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f (p y)) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := f.decay' k n
  refine ⟨C * ‖p‖ ^ n, fun x => ?_⟩
  have e := p.iteratedFDeriv_comp_right f.smooth' x (i := n) (by exact_mod_cast le_top)
  have h1 : ‖iteratedFDeriv ℝ n (fun y => f (p y)) x‖ ≤ ‖iteratedFDeriv ℝ n f.toFun (p x)‖ * ‖p‖ ^ n := by
    rw [show (fun y => f (p y)) = f.toFun ∘ ⇑p from rfl, e]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ‖p x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f (p y)) x‖
        ≤ ‖p x‖ ^ k * (‖iteratedFDeriv ℝ n f.toFun (p x)‖ * ‖p‖ ^ n) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (‖p x‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun (p x)‖) * ‖p‖ ^ n := by ring
    _ ≤ C * ‖p‖ ^ n := mul_le_mul_of_nonneg_right (hC (p x)) (by positivity)

def schwartzBox (f : SchwartzMap A ℂ) (g : SchwartzMap B ℂ) (p : E →L[ℝ] A) (q : E →L[ℝ] B)
    (h : ∀ x, ‖x‖ ≤ max ‖p x‖ ‖q x‖) : SchwartzMap E ℂ where
  toFun x := f (p x) * g (q x)
  smooth' := (f.smooth'.comp p.contDiff).mul (g.smooth'.comp q.contDiff)
  decay' k n := by
    choose C hC using decay_comp f p
    choose D hD using decay_comp g q
    refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (C k i * D 0 (n - i) + C 0 i * D k (n - i)), fun x => ?_⟩
    have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := ∞) (f := fun y => f (p y)) (g := fun y => g (q y))
      (f.smooth'.comp p.contDiff) (g.smooth'.comp q.contDiff) x (n := n) (by exact_mod_cast le_top)
    have h2 : ‖x‖ ^ k ≤ ‖p x‖ ^ k + ‖q x‖ ^ k := by
      rcases le_max_iff.1 (h x) with h' | h'
      · exact (pow_le_pow_left₀ (norm_nonneg _) h' k).trans (le_add_of_nonneg_right (by positivity))
      · exact (pow_le_pow_left₀ (norm_nonneg _) h' k).trans (le_add_of_nonneg_left (by positivity))
    refine (mul_le_mul h2 h1 (norm_nonneg _) (by positivity)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have a1 := hC k i x
    have a2 := hC 0 i x
    have b1 := hD k (n - i) x
    have b2 := hD 0 (n - i) x
    set u := ‖iteratedFDeriv ℝ i (fun y => f (p y)) x‖
    set v := ‖iteratedFDeriv ℝ (n - i) (fun y => g (q y)) x‖
    have hu : 0 ≤ u := norm_nonneg _
    have hv : 0 ≤ v := norm_nonneg _
    rw [pow_zero, one_mul] at a2 b2
    calc _ = (n.choose i : ℝ) * ((‖p x‖ ^ k * u) * v + u * (‖q x‖ ^ k * v)) := by ring
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (Nat.cast_nonneg _)
        · exact mul_le_mul a1 b2 hv (le_trans (by positivity) a1)
        · exact mul_le_mul a2 b1 (by positivity) (hu.trans a2)

theorem exists_schwartz_box {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ → A) ℂ)
    (g : SchwartzMap (κ' → A) ℂ) :
    ∃ h : SchwartzMap (κ ⊕ κ' → A) ℂ, ∀ x, h x = f (x ∘ Sum.inl) * g (x ∘ Sum.inr) := by
  let P : (κ ⊕ κ' → A) →L[ℝ] (κ → A) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Sum.inl j)
  let Q : (κ ⊕ κ' → A) →L[ℝ] (κ' → A) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Sum.inr j)
  have hPQ : ∀ x, ‖x‖ ≤ max ‖P x‖ ‖Q x‖ := by
    intro x
    refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun i => ?_
    rcases i with j | j
    · exact (norm_le_pi_norm (P x) j).trans (le_max_left _ _)
    · exact (norm_le_pi_norm (Q x) j).trans (le_max_right _ _)
  exact ⟨schwartzBox f g P Q hPQ, fun x => rfl⟩

end Schwartz

theorem box_mem_SB {R : Type} [TopologicalSpace R] [T2Space R] {κ κ' : Type} {φ₁ : (κ → R) → ℂ}
    {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ∈ SB (κ → R)) (h₂ : φ₂ ∈ SB (κ' → R)) : boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → R) := by
  have h₁' : IsLocallyConstant φ₁ ∧ HasCompactSupport φ₁ := h₁
  have h₂' : IsLocallyConstant φ₂ ∧ HasCompactSupport φ₂ := h₂
  obtain ⟨hl1, hc1⟩ := h₁'
  obtain ⟨hl2, hc2⟩ := h₂'
  show IsLocallyConstant (boxFun φ₁ φ₂) ∧ HasCompactSupport (boxFun φ₁ φ₂)
  refine ⟨?_, ?_⟩
  · exact (hl1.comp_continuous (continuous_pi fun j => continuous_apply (Sum.inl j))).mul
      (hl2.comp_continuous (continuous_pi fun j => continuous_apply (Sum.inr j)))
  · let e : (κ ⊕ κ' → R) ≃ₜ (κ → R) × (κ' → R) := Homeomorph.sumArrowHomeomorphProdArrow
    refine HasCompactSupport.intro ((hc1.isCompact.prod hc2.isCompact).image e.symm.continuous) ?_
    intro x hx
    have hx' : ¬ (x ∘ Sum.inl ∈ tsupport φ₁ ∧ x ∘ Sum.inr ∈ tsupport φ₂) := by
      rintro ⟨k1, k2⟩
      exact hx ⟨e x, ⟨k1, k2⟩, e.symm_apply_apply x⟩
    show φ₁ (x ∘ Sum.inl) * φ₂ (x ∘ Sum.inr) = 0
    rcases not_and_or.1 hx' with k | k
    · rw [image_eq_zero_of_notMem_tsupport k, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport k, mul_zero]

variable (F : Type) [Field F] [NumberField F]

theorem box_mem_schA {κ κ' : Type} [Fintype κ] [Fintype κ'] {φ₁ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    {φ₂ : (κ' → AdeleRing (𝓞 F) F) → ℂ} (h₁ : φ₁ ∈ schA F κ) (h₂ : φ₂ ∈ schA F κ') :
    boxFun φ₁ φ₂ ∈ schA F (κ ⊕ κ') := by
  let B : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ' → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ]
      ((κ ⊕ κ' → AdeleRing (𝓞 F) F) → ℂ) :=
    LinearMap.mk₂ ℂ boxFun
      (fun a b c => by funext x; simp only [GlobalTheory.WeilM.boxFun, Pi.add_apply]; ring)
      (fun s a c => by funext x; simp only [GlobalTheory.WeilM.boxFun, Pi.smul_apply, smul_eq_mul]; ring)
      (fun a b c => by funext x; simp only [GlobalTheory.WeilM.boxFun, Pi.add_apply]; ring)
      (fun s a c => by funext x; simp only [GlobalTheory.WeilM.boxFun, Pi.smul_apply, smul_eq_mul]; ring)
  have hmem : B φ₁ φ₂ ∈ Submodule.map₂ B (schA F κ) (schA F κ') := Submodule.apply_mem_map₂ B h₁ h₂
  have hle : Submodule.map₂ B (schA F κ) (schA F κ') ≤ schA F (κ ⊕ κ') := by
    unfold GlobalTheory.WeilM.schA
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨Φ₁, ⟨f1, g1, hg1, rfl⟩, Φ₂, ⟨f2, g2, hg2, rfl⟩, rfl⟩
    obtain ⟨h, hh⟩ := exists_schwartz_box f1 f2
    refine Submodule.subset_span ⟨h, boxFun g1 g2, box_mem_SB hg1 hg2, ?_⟩
    funext x
    simp only [B, LinearMap.mk₂_apply, GlobalTheory.WeilM.boxFun, GlobalTheory.WeilM.pureA, hh, Function.comp_def]
    ring
  exact hle hmem

theorem thetaSum_box {κ κ' : Type} [Fintype κ] [Fintype κ'] {φ₁ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    {φ₂ : (κ' → AdeleRing (𝓞 F) F) → ℂ} (h₁ : φ₁ ∈ schA F κ) (h₂ : φ₂ ∈ schA F κ') :
    thetaSum F (boxFun φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  have s1 := GlobalTheory.CompanionTheory.ThetaAdm.summable_schA F h₁
  have s2 := GlobalTheory.CompanionTheory.ThetaAdm.summable_schA F h₂
  unfold GlobalTheory.WeilM.thetaSum
  rw [tsum_mul_tsum_of_summable_norm s1 s2, ← (Equiv.sumArrowEquivProdArrow κ κ' F).tsum_eq]
  exact tsum_congr (fun ξ => rfl)

theorem theta_box : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ κ' : Type)
    [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ',
    boxFun φ₁ φ₂ ∈ schA F (κ ⊕ κ') ∧ thetaSum F (boxFun φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  intro F _ _ _ κ κ' _ _ φ₁ h₁ φ₂ h₂
  exact ⟨box_mem_schA F h₁ h₂, thetaSum_box F h₁ h₂⟩

end GlobalTheory.CompanionTheory.ThetaBox

end
