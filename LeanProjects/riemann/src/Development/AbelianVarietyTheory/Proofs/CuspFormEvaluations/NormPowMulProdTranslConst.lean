import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsProportionalOfSqLaw

open NumberField Matrix Complex
open scoped ComplexConjugate Real
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (thetaChar omegaStd hermForm)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory.CanTh (canTh canMult translConst)

namespace GlobalTheory.ThFr

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
  (idx : Fin g ≃ X.Ψ × Fin r)

section Coord

variable (bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)

def ratPt : (Fin g ⊕ Fin g → ℚ) →ₗ[ℚ] (Fin r → E) :=
  Fintype.linearCombination ℚ fun s => (bas (Pi.single s 1) : Fin r → E)

theorem coe_bas_eq_sum (m : Fin g ⊕ Fin g → ℤ) :
    (bas m : Fin r → E) = ∑ s, m s • (bas (Pi.single s 1) : Fin r → E) := by
  have hm : m = ∑ s, m s • (Pi.single s 1 : Fin g ⊕ Fin g → ℤ) := by
    ext t; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hm]
  rw [map_sum]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_zsmul]
  push_cast
  rfl

theorem ratPt_bijective : Function.Bijective (ratPt bas) := by
  set v : Fin g ⊕ Fin g → (Fin r → E) := fun s => (bas (Pi.single s 1) : Fin r → E) with hv
  have hΛ : ∀ l ∈ X.Λ, l ∈ Submodule.span ℚ (Set.range v) := by
    intro l hl
    have h := coe_bas_eq_sum bas (bas.symm ⟨l, hl⟩)
    rw [LinearEquiv.apply_symm_apply] at h
    have key : ((⟨l, hl⟩ : X.Λ) : Fin r → E) ∈ Submodule.span ℚ (Set.range v) := by
      rw [h]
      exact Submodule.sum_mem _ fun s _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self s)) _
    exact key
  refine ⟨?_, ?_⟩
  · have h1 : LinearIndependent ℤ v := by
      have hb := ((Pi.basisFun ℤ (Fin g ⊕ Fin g)).map bas).linearIndependent
      have h2 := hb.map' (X.Λ.subtype.restrictScalars ℤ)
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
      have hfun : v = ⇑(X.Λ.subtype.restrictScalars ℤ) ∘
          ⇑((Pi.basisFun ℤ (Fin g ⊕ Fin g)).map bas) := by
        ext s; simp [v]
      rw [hfun]
      exact h2
    have h3 : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
    exact linearIndependent_iff_injective_fintypeLinearCombination.mp h3
  · rw [← LinearMap.range_eq_top]
    show LinearMap.range (Fintype.linearCombination ℚ v) = ⊤
    rw [Fintype.range_linearCombination]
    have hsmul : ∀ (e : E) (w : Fin r → E), w ∈ Submodule.span ℚ (Set.range v) →
        e • w ∈ Submodule.span ℚ (Set.range v) := by
      intro e w hw
      obtain ⟨d, o, hd, hdo⟩ :=
        (IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ e)).exists_nsmul_eq (𝓞 E)
      induction hw using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨s, rfl⟩ := hy
        have h1 : o • v s ∈ X.Λ := X.Λ.smul_mem o (bas (Pi.single s 1)).2
        have h2 : (o • v s : Fin r → E) = ((d : ℚ) • e) • v s := by
          rw [Nat.cast_smul_eq_nsmul ℚ, hdo, algebraMap_smul]
        have h3 : e • v s = ((d : ℚ)⁻¹) • (o • v s) := by
          rw [h2, smul_assoc, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hd), one_smul]
        rw [h3]
        exact Submodule.smul_mem _ _ (hΛ _ h1)
      | zero => simp
      | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
      | smul q y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ q hy
    let S : Submodule E (Fin r → E) :=
      { toAddSubmonoid := (Submodule.span ℚ (Set.range v)).toAddSubmonoid
        smul_mem' := fun e w hw => hsmul e w hw }
    have hS : S = ⊤ := by
      rw [eq_top_iff, ← X.Λ_span, Submodule.span_le]
      intro l hl
      exact hΛ l hl
    rw [eq_top_iff]
    intro w _
    have hw : w ∈ S := hS ▸ Submodule.mem_top
    exact hw

def ratCoord : (Fin r → E) ≃ₗ[ℚ] (Fin g ⊕ Fin g → ℚ) :=
  (LinearEquiv.ofBijective (ratPt bas) (ratPt_bijective bas)).symm

def realCoord (y : Fin r → E) : Fin g ⊕ Fin g → ℝ := fun s => (ratCoord bas y s : ℝ)

def thPt {q0 : ℕ} (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)
    (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (a₀ b₀ : Fin g → ℝ) (y : Fin n → Fin r → E)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) : Frame X.Ψ r → ℂ :=
  thFr X hr bas idx n (fun k => a₀ + realCoord bas (y k) ∘ Sum.inr)
    (fun k => b₀ + realCoord bas (y k) ∘ Sum.inl) P

end Coord

section Series

variable {idx} {bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {q0 : ℕ} (hr : X.p0 + q0 = r) {n : ℕ}

theorem polyDeriv_prod_canFn_eq_mul (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    {a b a' b' : Fin n → Fin g → ℝ} {c : Fin n → ℂ}
    (h : ∀ k z, canFn X bas' idx (a' k) (b' k) x z = c k * canFn X bas idx (a k) (b k) x z)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    polyDeriv P (letterDir X hr idx) (fun z => ∏ k, canFn X bas' idx (a' k) (b' k) x (z k)) 0 =
      (∏ k, c k) *
        polyDeriv P (letterDir X hr idx) (fun z => ∏ k, canFn X bas idx (a k) (b k) x (z k)) 0 := by
  have hF : (fun z : Fin n → Fin g → ℂ => ∏ k, canFn X bas' idx (a' k) (b' k) x (z k)) =
      fun z => (∏ k, c k) * ∏ k, canFn X bas idx (a k) (b k) x (z k) := by
    funext z
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => h k (z k)
  have hd : Differentiable ℂ
      (fun z : Fin n → Fin g → ℂ => ∏ k, canFn X bas idx (a k) (b k) x (z k)) := by
    have he : (fun z : Fin n → Fin g → ℂ => ∏ k, canFn X bas idx (a k) (b k) x (z k)) =
        ∏ k, fun z : Fin n → Fin g → ℂ => canFn X bas idx (a k) (b k) x (z k) := by
      funext z; simp [Finset.prod_apply]
    rw [he]
    exact Finset.prod_induction _ (fun f => Differentiable ℂ f) (fun f1 f2 h1 h2 => h1.mul h2)
      (differentiable_const 1)
      fun k _ => (canFn_entire idx hs hx (a k) (b k)).comp (differentiable_apply k)
  rw [hF]
  exact GlobalTheory.CanTh.polyDeriv_const_mul P _ isOpen_univ hd.differentiableOn _ (Set.mem_univ _)

variable (hs : IsSympl X bas) (hs' : IsSympl X bas') (hn : Even n)
include hs hs' hn

theorem IsProportional.thFr_eq {κ : ℂ} {a₀ b₀ a₀' b₀' : Fin g → ℝ}
    (h : IsProportional X idx κ bas a₀ b₀ bas' a₀' b₀') {u u' : Fin n → Fin g ⊕ Fin g → ℝ}
    (hu : ∀ k, IsSamePt X bas bas' (u k) (u' k)) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    thFr X hr bas' idx n (fun k => a₀' + u' k ∘ Sum.inr) (fun k => b₀' + u' k ∘ Sum.inl) P x =
      κ ^ (n / 2) * (∏ k, translConst b₀ (u k ∘ Sum.inr) (u k ∘ Sum.inl) /
        translConst b₀' (u' k ∘ Sum.inr) (u' k ∘ Sum.inl)) *
      thFr X hr bas idx n (fun k => a₀ + u k ∘ Sum.inr) (fun k => b₀ + u k ∘ Sum.inl) P x := by
  obtain ⟨μ, hμ, hμz⟩ := h x hx
  have hc : ∀ k z, canFn X bas' idx (a₀' + u' k ∘ Sum.inr) (b₀' + u' k ∘ Sum.inl) x z =
      (translConst b₀ (u k ∘ Sum.inr) (u k ∘ Sum.inl) /
        translConst b₀' (u' k ∘ Sum.inr) (u' k ∘ Sum.inl) * μ) *
        canFn X bas idx (a₀ + u k ∘ Sum.inr) (b₀ + u k ∘ Sum.inl) x z := fun k z =>
    canFn_translate_eq_mul hs hs' hx hμz (hu k) z
  have halg : ∀ {A B D : ℂ} (t : Fin n → ℂ), μ ^ 2 * A = κ * B →
      A ^ (n / 2) * ((∏ k, (t k * μ)) * D) = κ ^ (n / 2) * (∏ k, t k) * (B ^ (n / 2) * D) := by
    intro A B D t hAB
    obtain ⟨m, rfl⟩ := hn
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show (m + m) / 2 = m by omega]
    have key : (μ ^ 2 * A) ^ m = (κ * B) ^ m := by rw [hAB]
    linear_combination (∏ k, t k) * D * key
  simp only [thFr]
  rw [polyDeriv_prod_canFn_eq_mul hr hs hx hc P]
  exact halg _ hμ

omit hs hs' hn in

theorem norm_pow_mul_prod_translConst {κ : ℂ} (hκ : ‖κ‖ = 1) (j : ℕ) (b b' : Fin g → ℝ)
    (s t s' t' : Fin n → Fin g → ℝ) :
    ‖κ ^ j * ∏ k, translConst b (s k) (t k) / translConst b' (s' k) (t' k)‖ = 1 := by
  rw [norm_mul, norm_pow, hκ, one_pow, one_mul, norm_prod]
  exact Finset.prod_eq_one fun k _ => by
    rw [norm_div, GlobalTheory.CanTh.norm_translConst, GlobalTheory.CanTh.norm_translConst, div_one]

variable (idx) in

theorem exists_thFr_eq_mul (a b : Fin n → Fin g → ℝ) :
    ∃ (a' b' : Fin n → Fin g → ℝ) (c : ℂ), ‖c‖ = 1 ∧
      ((∀ k i, a k i ∈ Set.range (Rat.cast : ℚ → ℝ)) → (∀ k i, b k i ∈ Set.range (Rat.cast : ℚ → ℝ)) →
        (∀ k i, a' k i ∈ Set.range (Rat.cast : ℚ → ℝ)) ∧
          ∀ k i, b' k i ∈ Set.range (Rat.cast : ℚ → ℝ)) ∧
      ∀ (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), ∀ x ∈ X.dom,
        thFr X hr bas idx n a b P x = c * thFr X hr bas' idx n a' b' P x := by
  obtain ⟨k, k', hk⟩ := exists_isProportional idx hs' hs
  obtain ⟨κ, hκ, hprop⟩ := hk 0 0 (Matrix.mulVec_zero _).symm
  set w' : Fin n → Fin g ⊕ Fin g → ℝ := fun j =>
    Sum.elim (b j - fun i => (k' i : ℝ) / 2) (a j - fun i => (k i : ℝ) / 2) with hw'
  set w : Fin n → Fin g ⊕ Fin g → ℝ := fun j =>
    (chgMat X bas' bas).map (Int.cast : ℤ → ℝ) *ᵥ w' j with hw
  have hu : ∀ j, IsSamePt X bas' bas (w j) (w' j) := fun j => rfl
  refine ⟨fun j => (0 : Fin g ⊕ Fin g → ℝ) ∘ Sum.inr + w j ∘ Sum.inr,
    fun j => (0 : Fin g ⊕ Fin g → ℝ) ∘ Sum.inl + w j ∘ Sum.inl,
    κ ^ (n / 2) * ∏ j, translConst ((0 : Fin g ⊕ Fin g → ℝ) ∘ Sum.inl) (w j ∘ Sum.inr)
      (w j ∘ Sum.inl) / translConst ((fun i => (k' i : ℝ) / 2) + (0 : Fin g ⊕ Fin g → ℝ) ∘ Sum.inl)
      (w' j ∘ Sum.inr) (w' j ∘ Sum.inl),
    norm_pow_mul_prod_translConst hκ _ _ _ _ _ _ _, ?_, ?_⟩
  · intro ha hb
    have hw'r : ∀ j s, w' j s ∈ Set.range (Rat.cast : ℚ → ℝ) := by
      intro j s
      rcases s with i | i
      · obtain ⟨q, hq⟩ := hb j i
        exact ⟨q - (k' i : ℚ) / 2, by simp [hw', hq]⟩
      · obtain ⟨q, hq⟩ := ha j i
        exact ⟨q - (k i : ℚ) / 2, by simp [hw', hq]⟩
    have hwr : ∀ j s, w j s ∈ Set.range (Rat.cast : ℚ → ℝ) := by
      intro j s
      choose q hq using hw'r j
      refine ⟨((chgMat X bas' bas).map (Int.cast : ℤ → ℚ) *ᵥ q) s, ?_⟩
      simp [hw, Matrix.mulVec, dotProduct, hq]
    exact ⟨fun j i => by simpa using hwr j (Sum.inr i), fun j i => by simpa using hwr j (Sum.inl i)⟩
  · intro P x hx
    have h := IsProportional.thFr_eq hr hs' hs hn hprop hu P hx
    convert h using 2 <;> funext j <;> simp [hw']

end Series

end

end GlobalTheory.ThFr
