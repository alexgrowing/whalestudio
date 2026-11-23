import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqLift.DPStep

variable {R : Type} [CommRing R] {I : Ideal R}

def prods (κ : DividedPowers I) (m : ℕ) : Set R :=
  {x | ∃ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) ∧ m ≤ (l.map Prod.fst).sum ∧
    x = (l.map fun p ↦ κ.dpow p.1 p.2).prod}

theorem prod_mem (κ : DividedPowers I) : ∀ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) →
    1 ≤ (l.map Prod.fst).sum → (l.map fun p ↦ κ.dpow p.1 p.2).prod ∈ I := by
  intro l
  induction l with
  | nil => simp
  | cons p l ih =>
    intro hl hs
    have hp : p.2 ∈ I := hl p (by simp)
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · rw [h] at hs
      exact I.mul_mem_left _ (ih (fun q hq ↦ hl q (by simp [hq])) (by omega))
    · exact I.mul_mem_right _ (κ.dpow_mem (by omega) hp)

theorem dpow_prod_eq_zero (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    ∀ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) → N + 1 ≤ (l.map Prod.fst).sum →
      ∀ n, 2 ≤ n → κ.dpow n (l.map fun p ↦ κ.dpow p.1 p.2).prod = 0 := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons p l ih =>
    intro hl hs n hn
    have hp : p.2 ∈ I := hl p (by simp)
    have hl' : ∀ q ∈ l, q.2 ∈ I := fun q hq ↦ hl q (by simp [hq])
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · rw [h, κ.dpow_zero hp, _root_.one_mul]
      exact ih hl' (by omega) n hn
    · set P := (l.map fun p ↦ κ.dpow p.1 p.2).prod
      have hm : κ.dpow p.1 p.2 ∈ I := κ.dpow_mem (by omega) hp
      have hz : P * κ.dpow (n * p.1) p.2 = 0 := by
        have := hN ((n * p.1, p.2) :: l) (by
          intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact hp
          · exact hl' q hq) (by
          have : 2 * p.1 ≤ n * p.1 := Nat.mul_le_mul_right _ hn
          simp only [List.map_cons, List.sum_cons]
          omega)
        simpa [List.map_cons, List.prod_cons, mul_comm] using this
      rw [mul_comm, κ.dpow_mul hm, κ.dpow_comp (by omega) hp]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, mul_left_comm, _root_.mul_assoc, hz, mul_zero, mul_zero]

end GlobalTheory.SqLift.DPStep

namespace GlobalTheory.SqLift.DPStep

variable {R : Type} [CommRing R] {I : Ideal R}

def idl (κ : DividedPowers I) (m : ℕ) : Ideal R := Ideal.span (prods κ m)

theorem idl_le (κ : DividedPowers I) (N : ℕ) : idl κ (N + 1) ≤ I := by
  refine Ideal.span_le.2 ?_
  rintro x ⟨l, hl, hs, rfl⟩
  exact prod_mem κ l hl (by omega)

theorem mul_idl_eq_zero (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) {a : R} (ha : a ∈ I) :
    ∀ b ∈ idl κ (N + 1), a * b = 0 := by
  intro b hb
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hs, rfl⟩ := hx
    have := hN ((1, a) :: l) (by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ha
      · exact hl q hq) (by simp only [List.map_cons, List.sum_cons]; omega)
    simpa [κ.dpow_one ha] using this
  | zero => exact mul_zero a
  | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]

theorem idl_sq (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) : idl κ (N + 1) ^ 2 = 0 := by
  rw [Ideal.zero_eq_bot, eq_bot_iff, pow_two]
  refine Ideal.mul_le.2 fun a ha b hb ↦ ?_
  rw [Ideal.mem_bot]
  exact mul_idl_eq_zero κ hN (idl_le κ N ha) b hb

theorem dpow_idl (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    ∀ x ∈ idl κ (N + 1), ∀ n, 2 ≤ n → κ.dpow n x = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hs, rfl⟩ := hx
    exact dpow_prod_eq_zero κ hN l hl hs
  | zero => intro n hn; exact κ.dpow_eval_zero (by omega)
  | add x y hxm hym hx hy =>
    intro n hn
    have hxI := idl_le κ N hxm
    have hyI := idl_le κ N hym
    rw [κ.dpow_add hxI hyI]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
    by_cases h1 : 2 ≤ k.1
    · rw [hx _ h1, MulZeroClass.zero_mul]
    by_cases h2 : 2 ≤ k.2
    · rw [hy _ h2, mul_zero]
    obtain ⟨a, b⟩ := k
    simp only at h1 h2 hk
    obtain rfl : a = 1 := by omega
    obtain rfl : b = 1 := by omega
    rw [κ.dpow_one hxI, κ.dpow_one hyI]
    exact mul_idl_eq_zero κ hN hxI y hym
  | smul r x hxm hx =>
    intro n hn
    rw [smul_eq_mul, κ.dpow_mul (idl_le κ N hxm), hx n hn, mul_zero]

theorem isSubDPIdeal (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    IsSubDPIdeal κ (idl κ (N + 1) ⊓ I) where
  isSubideal := inf_le_right
  dpow_mem n hn j hj := by
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      rw [κ.dpow_one hj.2]; exact hj
    · rw [dpow_idl κ hN j hj.1 n h]; exact Submodule.zero_mem _

end GlobalTheory.SqLift.DPStep

open GlobalTheory.SqLift.DPStep in

theorem GlobalTheory.SqLift.exists_isStep_nilExp :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → ∀ N : ℕ, NilExp κ (N + 2) →
    ∃ (R₁ : Type) (_ : CommRing R₁) (J : Ideal R) (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (I₁ : Ideal R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀),
      IsStep κ π hJ ρ κ₁ π₁ ∧ NilExp κ₁ (N + 1) := by
  intro R R₀ _ _ I κ π hπ hker N hN
  set J := idl κ (N + 1)
  have hJI : J ≤ I := idl_le κ N
  have hsub := isSubDPIdeal κ hN
  have hz : ∀ a ∈ J, π a = 0 := fun a ha ↦ by rw [← RingHom.mem_ker, hker]; exact hJI ha
  let π₁ : R ⧸ J →+* R₀ := Ideal.Quotient.lift J π hz
  have hnil1 : NilExp (DividedPowers.Quotient.dividedPowers κ hsub) (N + 1) := by
    intro l hl hs
    have key : ∀ l : List (ℕ × (R ⧸ J)), (∀ p ∈ l, p.2 ∈ I.map (Ideal.Quotient.mk J)) →
        ∃ l' : List (ℕ × R), (∀ p ∈ l', p.2 ∈ I) ∧ l'.map Prod.fst = l.map Prod.fst ∧
          (l.map fun p ↦ (DividedPowers.Quotient.dividedPowers κ hsub).dpow p.1 p.2).prod =
            Ideal.Quotient.mk J (l'.map fun p ↦ κ.dpow p.1 p.2).prod := by
      intro l
      induction l with
      | nil => intro _; exact ⟨[], by simp, by simp, by simp⟩
      | cons p l ih =>
        intro hl
        obtain ⟨l', hl', he, hp⟩ := ih fun q hq ↦ hl q (by simp [hq])
        obtain ⟨a, ha, hae⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
          (hl p (by simp))
        refine ⟨(p.1, a) :: l', ?_, by simp [he], ?_⟩
        · intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact ha
          · exact hl' q hq
        · simp only [List.map_cons, List.prod_cons, map_mul, hp, ← hae]
          rw [DividedPowers.Quotient.dpow_apply κ hsub ha]
    obtain ⟨l', hl', he, hp⟩ := key l hl
    rw [hp, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨l', hl', by rw [he]; exact hs, rfl⟩
  refine ⟨R ⧸ J, inferInstance, J, idl_sq κ hN, Ideal.Quotient.mk J, I.map (Ideal.Quotient.mk J),
    DividedPowers.Quotient.dividedPowers κ hsub, π₁, ?_, hnil1⟩
  refine
    { nil := ⟨N + 2, hN⟩
      nil₁ := ⟨N + 1, hnil1⟩
      surj := Ideal.Quotient.mk_surjective
      surj₁ := ?_
      comp := Ideal.Quotient.lift_comp_mk J π hz
      ker := hker
      kerJ := Ideal.mk_ker
      ker₁ := ?_
      dp := DividedPowers.Quotient.isDPMorphism κ hsub
      dpJ := ?_ }
  · intro y
    obtain ⟨a, rfl⟩ := hπ y
    exact ⟨Ideal.Quotient.mk J a, Ideal.Quotient.lift_mk J π hz⟩
  · ext y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker, Ideal.Quotient.lift_mk, ← RingHom.mem_ker, hker, Ideal.mem_quotient_iff_mem hJI]
  · refine (isDPMorphism_iff _ _ _).2 ⟨by rw [Ideal.map_id]; exact hJI, fun n hn a ha ↦ ?_⟩
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      rw [RingHom.id_apply, RingHom.id_apply, κ.dpow_one (hJI ha), (divided₂ _).dpow_one ha]
    · rw [RingHom.id_apply, RingHom.id_apply, squareZeroDividedPowers_dpow _ h, dpow_idl κ hN a ha n h]
