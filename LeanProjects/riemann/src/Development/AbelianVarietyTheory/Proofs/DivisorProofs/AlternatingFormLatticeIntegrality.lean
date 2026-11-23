import Mathlib
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem alternating_pairing_expand {F V : Type} [Field F] [NumberField F] [AddCommGroup V]
    [Module F V] (L : Set V)
    (hadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hsm : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (Q : V → V → F)
    (halt : ∀ x ∈ L, ∀ x' ∈ L, Q x x' = -Q x' x)
    (hQadd : ∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, Q (x₁ + x₂) x' = Q x₁ x' + Q x₂ x')
    (hQsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, Q ((a : F) • x) x' = (a : F) * Q x x')
    {x x' : V} (hx : x ∈ L) (hx' : x' ∈ L) (r₀ r₁ s₀ s₁ : 𝓞 F) :
    Q ((r₀ : F) • x + (r₁ : F) • x') ((s₀ : F) • x + (s₁ : F) • x') =
      ((r₀ : F) * s₁ - (r₁ : F) * s₀) * Q x x' := by
  have hself : ∀ y ∈ L, Q y y = 0 := by
    intro y hy
    have h := halt y hy y hy
    have h2 : (2 : F) * Q y y = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hadd2 : ∀ y ∈ L, ∀ y₁ ∈ L, ∀ y₂ ∈ L, Q y (y₁ + y₂) = Q y y₁ + Q y y₂ := by
    intro y hy y₁ hy₁ y₂ hy₂
    have e1 := halt y hy _ (hadd _ hy₁ _ hy₂)
    have e2 := hQadd _ hy₁ _ hy₂ _ hy
    have e3 := halt y hy y₁ hy₁
    have e4 := halt y hy y₂ hy₂
    linear_combination e1 - e2 - e3 - e4
  have hsmul2 : ∀ y ∈ L, ∀ (a : 𝓞 F), ∀ y' ∈ L, Q y ((a : F) • y') = (a : F) * Q y y' := by
    intro y hy a y' hy'
    have e1 := halt y hy _ (hsm a y' hy')
    have e2 := hQsmul a y' hy' y hy
    have e3 := halt y hy y' hy'
    linear_combination e1 - e2 - (a : F) * e3
  have hu := hsm r₀ x hx
  have hv := hsm r₁ x' hx'
  have hp := hsm s₀ x hx
  have hq := hsm s₁ x' hx'
  rw [hQadd _ hu _ hv _ (hadd _ hp _ hq), hadd2 _ hu _ hp _ hq, hadd2 _ hv _ hp _ hq,
    hQsmul r₀ x hx _ hp, hQsmul r₀ x hx _ hq, hQsmul r₁ x' hx' _ hp, hQsmul r₁ x' hx' _ hq,
    hsmul2 x hx s₀ x hx, hsmul2 x hx s₁ x' hx', hsmul2 x' hx' s₀ x hx, hsmul2 x' hx' s₁ x' hx',
    hself x hx, hself x' hx', halt x' hx' x hx]
  ring

theorem exists_int_of_isInteger_smul {F : Type} [Field F] [NumberField F] (d : 𝓞 F) (y : F)
    (h : IsLocalization.IsInteger (𝓞 F) (d • y)) : ∃ n : 𝓞 F, (n : F) = (d : F) * y := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap, hn, Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap]

theorem exists_alternating_bilinForm_eq_pairing : ∀ {F V : Type} [Field F] [NumberField F]
    [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (L : Set V),
    (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) → ∀ (P : V → V → F),
    (∀ x ∈ L, ∀ x' ∈ L, P x x' = -P x' x) →
    (∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, P ((a : F) • x) x' = (a : F) * P x x') →
    ∀ {x x' : V}, x ∈ L → x' ∈ L → P x x' ≠ 0 →
    ∃ B : LinearMap.BilinForm F V, (∀ z, B z z = 0) ∧ ∀ z ∈ L, ∀ w ∈ L, P z w = B z w := by
  intro F V _ _ _ _ hfin L hadd hsm P halt hPadd hPsmul x x' hx hx' hne
  have hP0 : ∀ y ∈ L, P 0 y = 0 := by
    intro y hy
    simpa using hPsmul 0 x hx y hy
  have hP0' : ∀ y ∈ L, P y 0 = 0 := by
    intro y hy
    have h0 : (0 : V) ∈ L := by simpa using hsm 0 x hx
    rw [halt y hy 0 h0, hP0 y hy, neg_zero]
  have hdne : ∀ d : (𝓞 F)⁰, ((d : 𝓞 F) : F) ≠ 0 := by
    intro d
    exact_mod_cast nonZeroDivisors.coe_ne_zero d
  have hli : LinearIndependent F ![x, x'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 F)⁰ ![s, t]
    obtain ⟨n₀, hn₀⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) s (hd 0)
    obtain ⟨n₁, hn₁⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) t (hd 1)
    have hrel : (n₀ : F) • x + (n₁ : F) • x' = 0 := by
      rw [hn₀, hn₁, ← smul_smul, ← smul_smul, ← smul_add, hst, smul_zero]
    have e₀ := alternating_pairing_expand L hadd hsm P halt hPadd hPsmul hx hx' n₀ n₁ 0 1
    have e₁ := alternating_pairing_expand L hadd hsm P halt hPadd hPsmul hx hx' 1 0 n₀ n₁
    rw [hrel, hP0 _ (hadd _ (hsm 0 x hx) _ (hsm 1 x' hx'))] at e₀
    rw [hrel, hP0' _ (hadd _ (hsm 1 x hx) _ (hsm 0 x' hx'))] at e₁
    push_cast at e₀ e₁
    simp only [mul_one, mul_zero, sub_zero, one_mul, zero_mul] at e₀ e₁
    have h0 : (n₀ : F) = 0 := by
      rcases mul_eq_zero.mp e₀.symm with h | h
      · exact h
      · exact absurd h hne
    have h1 : (n₁ : F) = 0 := by
      rcases mul_eq_zero.mp e₁.symm with h | h
      · exact h
      · exact absurd h hne
    rw [hn₀] at h0
    rw [hn₁] at h1
    exact ⟨(mul_eq_zero.mp h0).resolve_left (hdne d), (mul_eq_zero.mp h1).resolve_left (hdne d)⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank F V := by simp [hfin]
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 2) F V, ⇑b = ![x, x'] :=
    ⟨_, coe_basisOfLinearIndependentOfCardEqFinrank hli hcard⟩
  have hb0 : b 0 = x := by rw [hb]; rfl
  have hb1 : b 1 = x' := by rw [hb]; rfl
  let B : LinearMap.BilinForm F V := LinearMap.mk₂ F
    (fun z w => P x x' * (b.repr z 0 * b.repr w 1 - b.repr z 1 * b.repr w 0))
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
  have hB : ∀ z w, B z w = P x x' * (b.repr z 0 * b.repr w 1 - b.repr z 1 * b.repr w 0) :=
    fun _ _ => rfl
  have hBxx' : B x x' = P x x' := by
    rw [hB, ← hb0, ← hb1, b.repr_self, b.repr_self]
    simp
  refine ⟨B, fun z => by rw [hB]; ring, ?_⟩
  intro z hz w hw
  have hsum : ∀ v : V, v = b.repr v 0 • x + b.repr v 1 • x' := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    rw [Fin.sum_univ_two, hb0, hb1]
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 F)⁰
    ![b.repr z 0, b.repr z 1, b.repr w 0, b.repr w 1]
  obtain ⟨r₀, hr₀⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr z 0) (hd 0)
  obtain ⟨r₁, hr₁⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr z 1) (hd 1)
  obtain ⟨s₀, hs₀⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr w 0) (hd 2)
  obtain ⟨s₁, hs₁⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr w 1) (hd 3)
  set e : 𝓞 F := (d : 𝓞 F) with he
  have hez : (e : F) • z = (r₀ : F) • x + (r₁ : F) • x' := by
    calc (e : F) • z = (e : F) • (b.repr z 0 • x + b.repr z 1 • x') := congrArg _ (hsum z)
      _ = _ := by rw [smul_add, smul_smul, smul_smul, hr₀, hr₁]
  have hew : (e : F) • w = (s₀ : F) • x + (s₁ : F) • x' := by
    calc (e : F) • w = (e : F) • (b.repr w 0 • x + b.repr w 1 • x') := congrArg _ (hsum w)
      _ = _ := by rw [smul_add, smul_smul, smul_smul, hs₀, hs₁]
  have hPe : P ((e : F) • z) ((e : F) • w) = (e : F) * ((e : F) * P z w) := by
    have a1 := hPsmul e z hz _ (hsm e w hw)
    have a2 := halt z hz _ (hsm e w hw)
    have a3 := hPsmul e w hw z hz
    have a4 := halt w hw z hz
    linear_combination a1 + (e : F) * a2 - (e : F) * a3 - (e : F) * (e : F) * a4
  have hBe : B ((e : F) • z) ((e : F) • w) = (e : F) * ((e : F) * B z w) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have eP := alternating_pairing_expand L hadd hsm P halt hPadd hPsmul hx hx' r₀ r₁ s₀ s₁
  have eB := alternating_pairing_expand L hadd hsm (fun u v => B u v)
    (fun u _ v _ => by simp only [hB]; ring) (fun u₁ _ u₂ _ v _ => by rw [map_add, LinearMap.add_apply])
    (fun a u _ v _ => by rw [map_smul, LinearMap.smul_apply, smul_eq_mul]) hx hx' r₀ r₁ s₀ s₁
  rw [← hez, ← hew, hPe] at eP
  rw [← hez, ← hew, hBe, hBxx'] at eB
  have hee : (e : F) * (e : F) ≠ 0 := mul_ne_zero (hdne d) (hdne d)
  apply mul_left_cancel₀ hee
  linear_combination eP - eB

end GlobalTheory
