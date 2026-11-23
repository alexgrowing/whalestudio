import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.TriBasis

noncomputable def revLex : MonomialOrder.{0, 0} ℕ :=
  (MonomialOrder.lex (σ := ℕᵒᵈ) : MonomialOrder ℕᵒᵈ)

theorem revLex_lt {β γ : ℕ →₀ ℕ} (i : ℕ) (h1 : ∀ j, i < j → β j = γ j) (h2 : β i < γ i) :
    revLex.toSyn β < revLex.toSyn γ := by
  exact ⟨OrderDual.toDual i, fun j hj => h1 (OrderDual.ofDual j) hj, h2⟩

variable {σ : Type} {R : Type} [CommRing R]

def Led (m : MonomialOrder.{0, 0} σ) (p : MvPolynomial σ R) (γ : σ →₀ ℕ) : Prop :=
  IsUnit (MvPolynomial.coeff γ p) ∧ m.toSyn (m.degree p) ≤ m.toSyn γ

theorem Led.mul {m : MonomialOrder.{0, 0} σ} {p q : MvPolynomial σ R} {γ δ : σ →₀ ℕ}
    (hp : Led m p γ) (hq : Led m q δ) : Led m (p * q) (γ + δ) := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  refine ⟨?_, ?_⟩
  · rw [MonomialOrder.coeff_mul_of_add_of_degree_le hp2 hq2]
    exact hp1.mul hq1
  · calc m.toSyn (m.degree (p * q)) ≤ m.toSyn (m.degree p + m.degree q) :=
          MonomialOrder.degree_mul_le
      _ = m.toSyn (m.degree p) + m.toSyn (m.degree q) := map_add _ _ _
      _ ≤ m.toSyn γ + m.toSyn δ := add_le_add hp2 hq2
      _ = m.toSyn (γ + δ) := (map_add _ _ _).symm

theorem Led.monomial (m : MonomialOrder.{0, 0} σ) (γ : σ →₀ ℕ) :
    Led m (MvPolynomial.monomial γ (1 : R)) γ := by
  classical
  refine ⟨?_, MonomialOrder.degree_monomial_le _⟩
  rw [MvPolynomial.coeff_monomial, if_pos rfl]
  exact isUnit_one

theorem Led.one (m : MonomialOrder.{0, 0} σ) : Led m (1 : MvPolynomial σ R) 0 := by
  have h := Led.monomial (R := R) m 0
  rwa [← MvPolynomial.C_apply, MvPolynomial.C_1] at h

theorem Led.pow {m : MonomialOrder.{0, 0} σ} {p : MvPolynomial σ R} {γ : σ →₀ ℕ}
    (hp : Led m p γ) (n : ℕ) : Led m (p ^ n) (n • γ) := by
  induction n with
  | zero =>
    have e : (0 : ℕ) • γ = 0 := by ext; simp
    rw [pow_zero, e]
    exact Led.one m
  | succ n ih =>
    have e : (n + 1) • γ = n • γ + γ := by ext; simp [add_mul]
    rw [pow_succ, e]
    exact ih.mul hp

theorem Led.prod {ι : Type} {m : MonomialOrder.{0, 0} σ} (s : Finset ι)
    {p : ι → MvPolynomial σ R} {γ : ι → σ →₀ ℕ}
    (hp : ∀ i, Led m (p i) (γ i)) : Led m (∏ i ∈ s, p i) (∑ i ∈ s, γ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact Led.one m
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact (hp j).mul ih

theorem apply_eq_zero_of_supported {i : ℕ} {a : MvPolynomial ℕ R}
    (ha : a ∈ MvPolynomial.supported R (Set.Iio i)) {β : ℕ →₀ ℕ} (hβ : β ∈ a.support)
    {j : ℕ} (hj : i ≤ j) : β j = 0 := by
  by_contra h
  have hv : j ∈ a.vars :=
    (MvPolynomial.mem_vars_iff_mem_support j).2 ⟨β, hβ, Finsupp.mem_support_iff.2 h⟩
  have hlt : j < i := MvPolynomial.mem_supported.1 ha hv
  omega

theorem led_tri {l : ℕ} (hl : 2 ≤ l) (i : ℕ) (v : Rˣ) {a b : MvPolynomial ℕ R}
    (ha : a ∈ MvPolynomial.supported R (Set.Iio i))
    (hb : b ∈ MvPolynomial.supported R (Set.Iio i)) :
    Led revLex (MvPolynomial.C (v : R) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b)
      (Finsupp.single i l) := by
  classical
  have hmon : MvPolynomial.C (v : R) * MvPolynomial.X i ^ l =
      MvPolynomial.monomial (Finsupp.single i l) (v : R) := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  have hsmall : ∀ c : ℕ →₀ ℕ, (∀ j, i < j → c j = 0) → c i < l →
      revLex.toSyn c < revLex.toSyn (Finsupp.single i l) := by
    intro c h1 h2
    refine revLex_lt i (fun j hj => ?_) (by simpa using h2)
    rw [h1 j hj]
    simp [hj.ne]
  have hb0 : ∀ c, b.coeff c ≠ 0 → ∀ j, i ≤ j → c j = 0 := fun c hc j hj =>
    apply_eq_zero_of_supported hb (MvPolynomial.mem_support_iff.2 hc) hj
  have ha0 : ∀ c, (a * MvPolynomial.X i).coeff c ≠ 0 → (∀ j, i < j → c j = 0) ∧ c i ≤ 1 := by
    intro c hc
    rw [MvPolynomial.coeff_mul_X'] at hc
    split_ifs at hc with hci
    · have hd : ∀ j, i ≤ j → (c - Finsupp.single i 1 : ℕ →₀ ℕ) j = 0 := fun j hj =>
        apply_eq_zero_of_supported ha (MvPolynomial.mem_support_iff.2 hc) hj
      refine ⟨fun j hj => ?_, ?_⟩
      · have h := hd j hj.le
        rwa [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hj.ne, Nat.sub_zero] at h
      · have h := hd i le_rfl
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same] at h
        omega
    · exact absurd rfl hc
  refine ⟨?_, ?_⟩
  · have h1 : (a * MvPolynomial.X i).coeff (Finsupp.single i l) = 0 := by
      by_contra h
      have h' := (ha0 _ h).2
      rw [Finsupp.single_eq_same] at h'
      omega
    have h2 : b.coeff (Finsupp.single i l) = 0 := by
      by_contra h
      have h' := hb0 _ h i le_rfl
      rw [Finsupp.single_eq_same] at h'
      omega
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, hmon, MvPolynomial.coeff_monomial, if_pos rfl,
      h1, h2, add_zero, add_zero]
    exact v.isUnit
  · rw [MonomialOrder.degree_le_iff]
    intro c hc
    by_cases hce : c = Finsupp.single i l
    · rw [hce]
    · have hc' := MvPolynomial.mem_support_iff.1 hc
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, hmon, MvPolynomial.coeff_monomial,
        if_neg (Ne.symm hce), zero_add] at hc'
      by_cases hA : (a * MvPolynomial.X i).coeff c = 0
      · rw [hA, zero_add] at hc'
        have h := hb0 c hc'
        refine (hsmall c (fun j hj => h j hj.le) ?_).le
        rw [h i le_rfl]
        omega
      · have h := ha0 c hA
        exact (hsmall c h.1 (by omega)).le

theorem bij (l : ℕ) [hl : Fact l.Prime] :
    Function.Bijective (fun x : Digits l × (ℕ →₀ ℕ) => x.1.1 + l • x.2) := by
  have hl0 : 0 < l := hl.out.pos
  constructor
  · rintro ⟨⟨α, hα⟩, γ⟩ ⟨⟨α', hα'⟩, γ'⟩ h
    have h' : α + l • γ = α' + l • γ' := h
    have hk : ∀ k, α k = α' k ∧ γ k = γ' k := by
      intro k
      have e := DFunLike.congr_fun h' k
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at e
      have e1 : α k = α' k := by
        have h2 := congrArg (· % l) e
        simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hα k), Nat.mod_eq_of_lt (hα' k)] at h2
        exact h2
      refine ⟨e1, ?_⟩
      rw [e1] at e
      exact Nat.eq_of_mul_eq_mul_left hl0 (Nat.add_left_cancel e)
    have e1 : α = α' := Finsupp.ext fun k => (hk k).1
    have e2 : γ = γ' := Finsupp.ext fun k => (hk k).2
    subst e1
    subst e2
    rfl
  · intro β
    refine ⟨(⟨Finsupp.mapRange (· % l) (Nat.zero_mod l) β, fun k => ?_⟩,
      Finsupp.mapRange (· / l) (Nat.zero_div l) β), ?_⟩
    · rw [Finsupp.mapRange_apply]
      exact Nat.mod_lt _ hl0
    · ext k
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
      exact Nat.mod_add_div (β k) l

theorem tri_basis : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (t : ℕ → MvPolynomial ℕ R), (∀ i, ∃ (v : Rˣ) (a b : MvPolynomial ℕ R), a ∈ MvPolynomial.supported R (Set.Iio i) ∧ b ∈ MvPolynomial.supported R (Set.Iio i) ∧ t i = MvPolynomial.C (v : R) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) → LinearIndependent R (fun x : Digits l × (ℕ →₀ ℕ) => MvPolynomial.monomial x.1.1 (1 : R) * x.2.prod fun i n => t i ^ n) ∧ Submodule.span R (Set.range fun x : Digits l × (ℕ →₀ ℕ) => MvPolynomial.monomial x.1.1 (1 : R) * x.2.prod fun i n => t i ^ n) = ⊤ := by
  intro l hlp R _ t ht
  classical
  choose v a b ha hb hteq using ht
  have hl : 2 ≤ l := hlp.out.two_le
  set F : Digits l × (ℕ →₀ ℕ) → MvPolynomial ℕ R :=
    fun x => MvPolynomial.monomial x.1.1 (1 : R) * x.2.prod fun i n => t i ^ n with hF
  have hLed : ∀ x : Digits l × (ℕ →₀ ℕ), Led revLex (F x) (x.1.1 + l • x.2) := by
    intro x
    refine (Led.monomial revLex x.1.1).mul ?_
    have ht' : ∀ i, Led revLex (t i ^ x.2 i) (x.2 i • Finsupp.single i l) := fun i => by
      rw [hteq i]
      exact (led_tri hl i (v i) (ha i) (hb i)).pow _
    have hsum : (∑ i ∈ x.2.support, x.2 i • Finsupp.single i l) = l • x.2 := by
      ext j
      rw [Finsupp.finsetSum_apply]
      by_cases hj : j ∈ x.2.support
      · rw [Finset.sum_eq_single j]
        · simp [mul_comm]
        · intro k _ hk
          simp [hk]
        · intro h
          exact absurd hj h
      · rw [Finset.sum_eq_zero]
        · have h0 : x.2 j = 0 := by simpa using hj
          simp [h0]
        · intro k hk
          have hkj : k ≠ j := fun e => hj (e ▸ hk)
          simp [hkj]
    rw [Finsupp.prod, ← hsum]
    exact Led.prod x.2.support ht'
  constructor
  · rw [linearIndependent_iff']
    intro s g hg i0 hi0s
    by_contra hi0
    have hs' : (s.filter fun x => g x ≠ 0).Nonempty := ⟨i0, Finset.mem_filter.2 ⟨hi0s, hi0⟩⟩
    obtain ⟨x, hx, hxmax⟩ := Finset.exists_max_image _
      (fun x : Digits l × (ℕ →₀ ℕ) => revLex.toSyn (x.1.1 + l • x.2)) hs'
    rw [Finset.mem_filter] at hx
    have hc := congrArg (MvPolynomial.coeff (x.1.1 + l • x.2)) hg
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero, Finset.sum_eq_single x] at hc
    · rw [MvPolynomial.coeff_smul, smul_eq_mul] at hc
      obtain ⟨hu, _⟩ := hLed x
      exact hx.2 ((hu.mul_left_eq_zero).1 hc)
    · intro y hy hyx
      rw [MvPolynomial.coeff_smul, smul_eq_mul]
      by_cases hgy : g y = 0
      · rw [hgy, zero_mul]
      · have hle := hxmax y (Finset.mem_filter.2 ⟨hy, hgy⟩)
        have hne : y.1.1 + l • y.2 ≠ x.1.1 + l • x.2 := fun e => hyx ((bij l).1 e)
        have hlt : revLex.toSyn (y.1.1 + l • y.2) < revLex.toSyn (x.1.1 + l • x.2) :=
          lt_of_le_of_ne hle (fun e => hne (revLex.toSyn.injective e))
        obtain ⟨_, hdeg⟩ := hLed y
        rw [MonomialOrder.coeff_eq_zero_of_lt (lt_of_le_of_lt hdeg hlt), mul_zero]
    · intro h
      exact absurd hx.1 h
  · rw [Submodule.eq_top_iff']
    have key : ∀ s : revLex.syn, ∀ q : MvPolynomial ℕ R,
        revLex.toSyn (revLex.degree q) = s → q ∈ Submodule.span R (Set.range F) := by
      intro s
      induction s using WellFoundedLT.induction with
      | ind s ih =>
        intro q hq
        obtain ⟨x, hx⟩ := (bij l).2 (revLex.degree q)
        have hx' : x.1.1 + l • x.2 = revLex.degree q := hx
        obtain ⟨hu, hdeg⟩ := hLed x
        rw [hx'] at hu hdeg
        have hmem : (q.coeff (revLex.degree q) * ↑hu.unit⁻¹) • F x ∈ Submodule.span R (Set.range F) :=
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
        have hrest : q - (q.coeff (revLex.degree q) * ↑hu.unit⁻¹) • F x ∈
            Submodule.span R (Set.range F) := by
          by_cases h0 : q - (q.coeff (revLex.degree q) * ↑hu.unit⁻¹) • F x = 0
          · rw [h0]
            exact Submodule.zero_mem _
          · refine ih _ ?_ _ rfl
            rw [← hq]
            have hle : revLex.toSyn (revLex.degree (q - (q.coeff (revLex.degree q) * ↑hu.unit⁻¹) • F x))
                ≤ revLex.toSyn (revLex.degree q) :=
              le_trans MonomialOrder.degree_sub_le
                (sup_le le_rfl (le_trans MonomialOrder.degree_smul_le hdeg))
            refine lt_of_le_of_ne hle (fun e => ?_)
            have e' := revLex.toSyn.injective e
            have hz : (q - (q.coeff (revLex.degree q) * ↑hu.unit⁻¹) • F x).coeff (revLex.degree q) = 0 := by
              rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc,
                hu.val_inv_mul, mul_one, sub_self]
            exact (MonomialOrder.coeff_degree_ne_zero_iff.2 h0) (by rw [e']; exact hz)
        have h := Submodule.add_mem _ hrest hmem
        rwa [sub_add_cancel] at h
    intro q
    exact key _ q rfl

end GlobalTheory.TriBasis
