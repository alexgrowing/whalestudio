import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.NotAdmissibleHalfLatticeFamily
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinsumQuotientOfLe
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctions
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianHeisenbergOperatorLaws
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.WeilLevel

noncomputable section

theorem sq_le_of_finsum_eq {A : Type} [AddCommGroup A] {s t u : AddSubgroup A} (h : s ≤ t)
    (hn : s.relIndex t ≠ 0) (hu : t.relIndex u ≠ 0) (f g : A → ℂ)
    (hf : ∀ x, ∀ y ∈ t, f (x + y) = f x) (hg : ∀ x, ∀ y ∈ t, g (x + y) = g x)
    (hf' : ∀ x, f x ≠ 0 → x ∈ u) (hg' : ∀ x, g x ≠ 0 → x ∈ u)
    (he : ∑ᶠ q : A ⧸ s, f q.out * conj (f q.out) = ∑ᶠ q : A ⧸ s, g q.out * conj (g q.out))
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) (x : A) : ‖g x‖ ^ 2 ≤ (t.relIndex u : ℝ) * B ^ 2 := by
  classical
  have hc : t.relIndex u = Nat.card (u.map (QuotientAddGroup.mk' t)) := by
    rw [← AddSubgroup.relIndex_ker, QuotientAddGroup.ker_mk']
  haveI : Finite (u.map (QuotientAddGroup.mk' t)) := Nat.finite_of_card_ne_zero (hc ▸ hu)
  have hS : ((u.map (QuotientAddGroup.mk' t) : AddSubgroup (A ⧸ t)) : Set (A ⧸ t)).Finite :=
    Set.toFinite _
  have hcard : hS.toFinset.card = t.relIndex u := by
    rw [hc, ← Set.ncard_eq_toFinset_card _ hS]; rfl
  have key : ∀ k : A → ℂ, (∀ x, k x ≠ 0 → x ∈ u) →
      (Function.support fun q : A ⧸ t => k q.out * conj (k q.out)) ⊆ hS.toFinset := by
    intro k hk q hq
    rw [Set.Finite.coe_toFinset]
    exact ⟨q.out, hk _ (left_ne_zero_of_mul hq), QuotientAddGroup.out_eq' q⟩
  rw [HaarLevel.finsum_quotient_of_le h hn (fun x => f x * conj (f x))
      (fun x y hy => by simp only [hf x y hy]) ((Finset.finite_toSet _).subset (key f hf')),
    HaarLevel.finsum_quotient_of_le h hn (fun x => g x * conj (g x))
      (fun x y hy => by simp only [hg x y hy]) ((Finset.finite_toSet _).subset (key g hg')),
    finsum_eq_sum_of_support_subset _ (key f hf'),
    finsum_eq_sum_of_support_subset _ (key g hg')] at he
  have he2 := mul_left_cancel₀ (by exact_mod_cast hn) he
  simp only [Complex.mul_conj'] at he2
  have he3 : ∑ q ∈ hS.toFinset, ‖f q.out‖ ^ 2 = ∑ q ∈ hS.toFinset, ‖g q.out‖ ^ 2 := by
    exact_mod_cast he2
  by_cases hx : g x = 0
  · rw [hx, norm_zero, zero_pow two_ne_zero]; positivity
  have h1 : g (x : A ⧸ t).out = g x := by
    have := hg x _ (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (x : A ⧸ t)).symm)
    rw [← this]; congr 1; abel
  calc ‖g x‖ ^ 2 = ‖g (x : A ⧸ t).out‖ ^ 2 := by rw [h1]
    _ ≤ ∑ q ∈ hS.toFinset, ‖g q.out‖ ^ 2 :=
        Finset.single_le_sum (f := fun q : A ⧸ t => ‖g q.out‖ ^ 2) (fun _ _ => sq_nonneg _)
          (by rw [Set.Finite.mem_toFinset]; exact ⟨x, hg' x hx, rfl⟩)
    _ ≤ hS.toFinset.card • B ^ 2 := by
        rw [← he3]
        exact Finset.sum_le_card_nsmul _ _ _ fun q _ => by
          have := hB q.out
          gcongr
    _ = _ := by rw [hcard, nsmul_eq_mul]

theorem relIndex_nsmul {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
    (L : AddSubgroup (Matrix κ ι K)) {j : ℕ} (hj : 0 < j) (hL : ∀ x ∈ L, IntM ((j : K) • x))
    {m : ℕ} (hm : 0 < m) :
    (L.map (nsmulAddMonoidHom m)).relIndex L ≠ 0 ∧ (L.map (nsmulAddMonoidHom m)).relIndex L ≤
      m ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) := by
  let f : L →+ Matrix κ ι (𝓞 K) :=
    { toFun := fun x => Matrix.of fun k i => ⟨((j : K) • x.1) k i, hL x.1 x.2 k i⟩
      map_zero' := by
        ext k i
        change ((j : K) • (0 : Matrix κ ι K)) k i = 0
        simp
      map_add' := fun x y => by
        ext k i
        change ((j : K) • (x.1 + y.1)) k i = ((j : K) • x.1) k i + ((j : K) • y.1) k i
        rw [smul_add]; rfl }
  have hj' : (j : K) ≠ 0 := by exact_mod_cast hj.ne'
  have hf : Function.Injective f.toIntLinearMap := by
    intro x y hxy
    ext k i
    have : ((j : K) • x.1) k i = ((j : K) • y.1) k i :=
      congrArg Subtype.val (congrFun (congrFun hxy k) i)
    exact mul_left_cancel₀ hj' this
  haveI : Module.Finite ℤ L := Module.Finite.of_injective _ hf
  haveI : Module.IsTorsionFree ℤ L := hf.moduleIsTorsionFree _ (fun _ _ => map_smul _ _ _)
  have hr := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_matrix, RingOfIntegers.rank] at hr
  have : (L.map (nsmulAddMonoidHom m)).relIndex L = m ^ Module.finrank ℤ L := by
    rw [← AddSubgroup.index_range_nsmul, AddSubgroup.relIndex]
    congr 1
    ext x
    simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, AddMonoidHom.mem_range,
      nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨y, hy, e⟩; exact ⟨⟨y, hy⟩, Subtype.ext e⟩
    · rintro ⟨y, rfl⟩; exact ⟨y.1, y.2, rfl⟩
  rw [this]
  exact ⟨by positivity, Nat.pow_le_pow_right hm (by rw [mul_comm]; exact hr)⟩

theorem discr_mul_integral {E : Type} [Field E] [NumberField E] (t : E)
    (h : ∀ γ : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (t * γ) = k) :
    IsIntegral ℤ (((NumberField.discr E).natAbs : E) * t) := by
  classical
  have hmem : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨y, rfl⟩ := Submodule.mem_one.mp ha
    obtain ⟨k, hk⟩ := h y
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, hk]
    simp
  have hb : ∀ i, IsIntegral ℤ (integralBasis E i) := fun i => by
    rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
  have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have h0 := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) hb h1 hmem
  rw [← coe_discr, Algebra.smul_def, mul_one] at h0
  have h2 : IsIntegral ℤ ((NumberField.discr E : E) * t) := by simpa using h0
  rw [Nat.cast_natAbs]
  rcases abs_choice (NumberField.discr E) with h3 | h3 <;> rw [h3]
  · exact h2
  · rw [Int.cast_neg, neg_mul]; exact h2.neg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} {Λ : Lt E n}

theorem cc_add (x y : E) : cc (x + y) = cc x + cc y := by simp [cc]
theorem cc_sub (x y : E) : cc (x - y) = cc x - cc y := by simp [cc]
theorem cc_mul (x y : E) : cc (x * y) = cc x * cc y := by simp [cc]
theorem cc_nat (m : ℕ) : cc (m : E) = m := by simp [cc]
theorem cc_zero : cc (0 : E) = 0 := by simp [cc]
theorem cc_sum {α : Type} (s : Finset α) (f : α → E) : cc (∑ a ∈ s, f a) = ∑ a ∈ s, cc (f a) := by
  simp [cc]

omit [IsCMField E] in
theorem colsIn_smul (m : ℕ) {x : Matrix (Fin n) (Fin N) E} (h : ColsIn Λ x) :
    ColsIn Λ ((m : E) • x) := fun a => Model.nat_smul_mem Λ m (h a)

omit [IsCMField E] in
theorem levelL_mul {R : ℕ} {φ : Matrix (Fin n) (Fin N) E → ℂ} (h : LevelL Λ R φ) (m : ℕ) :
    LevelL Λ (m * R) φ := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_smul]; exact colsIn_smul m (h.1 x hx)
  · rw [Nat.cast_mul, mul_comm, mul_smul]; exact h.2 x _ (colsIn_smul m hy)

omit [IsCMField E] in
theorem hasLevel_of_levelL {s R : ℕ} (h1 : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n)
    (h2 : ∀ v ∈ stdL E n, (s : E) • v ∈ Λ) {φ : Matrix (Fin n) (Fin N) E → ℂ}
    (h : LevelL Λ R φ) : HasLevel (s * R) φ := by
  refine ⟨fun x hx k a => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_smul]
    exact (Model.mem_stdL _).1 (h1 _ (h.1 x hx a)) k
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact h.2 x _ fun a => h2 _ ((Model.mem_stdL _).2 fun k => hy k a)

theorem heisH_fix (hΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) {R : ℕ}
    {φ : Matrix (Fin n) (Fin N) E → ℂ} (h : LevelL Λ R φ) {d b : Matrix (Fin n) (Fin N) E}
    (hd : ColsIn Λ d) (hb : ColsIn Λ b) :
    heisH (((2 * R : ℕ) : E) • d) (((2 * R : ℕ) : E) • b) φ = φ := by
  funext x
  have e1 : φ (x - ((2 * R : ℕ) : E) • d) = φ x := by
    rw [← h.2 x (-(((2 : ℕ) : E) • d)) fun a => Λ.neg_mem (colsIn_smul 2 hd a)]
    congr 1
    rw [smul_neg, smul_smul, sub_eq_add_neg, Nat.cast_mul, mul_comm]
  rw [heisH, e1]
  by_cases hx : φ x = 0
  · rw [hx, zero_mul]
  set y : Matrix (Fin n) (Fin N) E :=
    ((2 : ℕ) : E) • ((R : E) • x) - ((2 * R * R : ℕ) : E) • d with hy
  have hyΛ : ColsIn Λ y := fun a =>
    Λ.sub_mem (colsIn_smul 2 (h.1 x hx) a) (colsIn_smul _ hd a)
  have hw : IsIntegral ℤ (∑ a, herm 1 (bᵀ a) (yᵀ a)) :=
    IsIntegral.sum _ fun a _ => (hΛ _).1 (hb a) _ (hyΛ a)
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (Algebra.isIntegral_trace (L := ℚ) (F := E) hw)
  have e2 : ∑ k, ∑ a, (((2 * R : ℕ) : E) • b) k a *
      (2 * cc (x k a) - cc ((((2 * R : ℕ) : E) • d) k a)) =
      (2 : ℚ) • ∑ a, herm 1 (bᵀ a) (yᵀ a) := by
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Model.herm_one, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hy, Matrix.transpose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
      cc_sub, cc_mul, cc_nat, Rat.smul_def]
    push_cast
    ring
  rw [e2, map_smul, ← hk]
  have : (π : ℂ) * I * (((2 : ℚ) • algebraMap ℤ ℚ k : ℚ) : ℂ) = k * (2 * π * I) := by
    simp; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]

omit [IsCMField E] in
theorem cols_mul {d b : Matrix (Fin n) (Fin N) E} (hd : ColsIn Λ d) (hb : ColsIn Λ b)
    {g : M2 E N} (hg : IntM g) (i : Fin N ⊕ Fin N) : (Matrix.fromCols d b * g)ᵀ i ∈ Λ := by
  have : (Matrix.fromCols d b * g)ᵀ i =
      ∑ j, (⟨g j i, hg j i⟩ : 𝓞 E) • (Matrix.fromCols d b)ᵀ j := by
    ext k
    rw [Finset.sum_apply, Matrix.transpose_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [this]
  refine Λ.sum_mem fun j _ => Λ.smul_mem _ ?_
  rcases j with j | j
  · exact hd j
  · exact hb j

theorem levelL_of_fix (hΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) {S : ℕ}
    {ψ : Matrix (Fin n) (Fin N) E → ℂ}
    (h : ∀ d b, ColsIn Λ d → ColsIn Λ b → heisH ((S : E) • d) ((S : E) • b) ψ = ψ) :
    LevelL Λ ((NumberField.discr E).natAbs * S) ψ := by
  classical
  have h0 : ColsIn Λ (0 : Matrix (Fin n) (Fin N) E) := fun _ => Λ.zero_mem
  refine ⟨fun x hx a => (hΛ _).2 fun y hy => ?_, fun x y hy => ?_⟩
  · have key : ∀ γ : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E ((S * herm 1 y (xᵀ a)) * γ) = k := by
      intro γ
      set b : Matrix (Fin n) (Fin N) E := Matrix.of fun k a' => if a' = a then (γ : E) * y k else 0
        with hb
      have hbΛ : ColsIn Λ b := by
        intro a'
        by_cases ha : a' = a
        · have : bᵀ a' = γ • y := by ext k; simp [hb, ha]; rfl
          rw [this]; exact Λ.smul_mem _ hy
        · have : bᵀ a' = 0 := by ext k; simp [hb, ha]
          rw [this]; exact Λ.zero_mem
      have e := congrFun (h 0 b h0 hbΛ) x
      have e2 : ∑ k, ∑ a', ((S : E) • b) k a' *
          (2 * cc (x k a') - cc (((S : E) • (0 : Matrix (Fin n) (Fin N) E)) k a')) =
          (2 : ℚ) • ((S * herm 1 y (xᵀ a)) * γ) := by
        rw [Model.herm_one, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_eq_single a (fun a' _ ha => by simp [hb, ha]) (by simp)]
        simp only [hb, smul_zero, Matrix.zero_apply, cc_zero, Matrix.smul_apply, Matrix.of_apply,
          if_true, smul_eq_mul, Matrix.transpose_apply, Rat.smul_def, mul_zero]
        push_cast
        ring
      rw [heisH, e2, smul_zero, sub_zero, map_smul, mul_right_eq_self₀, or_iff_left hx,
        Complex.exp_eq_one_iff] at e
      obtain ⟨k, hk⟩ := e
      refine ⟨k, ?_⟩
      have hp : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
      have : ((Algebra.trace ℚ E ((S * herm 1 y (xᵀ a)) * γ) : ℚ) : ℂ) = k := by
        apply mul_right_cancel₀ hp
        rw [← hk, smul_eq_mul]; push_cast; ring
      exact_mod_cast this
    have h2 := Model.cc_integral (discr_mul_integral _ key)
    convert h2 using 1
    rw [Model.herm_one, Model.herm_one, cc_mul, cc_mul, cc_nat, cc_nat, cc_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [cc_mul, Model.cc_cc, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  · have e := congrFun (h _ 0 (colsIn_smul (NumberField.discr E).natAbs hy) h0)
      (x + (((NumberField.discr E).natAbs * S : ℕ) : E) • y)
    rw [← e, heisH, smul_smul, Nat.cast_mul, mul_comm (S : E), add_sub_cancel_right]
    simp

end

end GlobalTheory.SW.WeilLevel

namespace GlobalTheory.SW

open WeilLevel in

theorem weil_level_and_sup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ c R : ℕ, 0 < c → 0 < R → ∃ (R' : ℕ) (C : ℝ), 0 < R' ∧ ∀ (M : ℕ), ∀ Λ ∈ Vset E n M, ∀ γ ∈ UU E N, Den c γ → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, LevelL Λ R φ → IsSB φ ∧ LevelL Λ R' (weil Ψ γ φ) ∧ ∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → ∀ x, ‖weil Ψ γ φ x‖ ≤ C * B := by
  intro E _ _ _ Ψ hΨ n N hn c R hc hR
  have hD : 0 < (NumberField.discr E).natAbs := Int.natAbs_pos.2 (NumberField.discr_ne_zero E)
  set R' : ℕ := (NumberField.discr E).natAbs * (2 * R * c) with hR'
  have hR'0 : 0 < R' := by positivity
  set e := Module.finrank ℚ E * (Fintype.card (Fin n) * Fintype.card (Fin N)) with he
  refine ⟨R', (R' : ℝ) ^ e, hR'0, ?_⟩
  rintro M Λ ⟨-, hΛ, s, hs, -, h1, h2⟩ γ hγ hden φ hφ
  have hSB : IsSB φ := ⟨s * R, by positivity, hasLevel_of_levelL h1 h2 hφ⟩
  have hψ : LevelL Λ R' (weil Ψ γ φ) := by
    refine levelL_of_fix hΛ fun d b hd hb => ?_
    set X := Matrix.fromCols d b * ((c : E) • γ) with hX
    have hX1 : ColsIn Λ X.toCols₁ := fun a => cols_mul hd hb hden (Sum.inl a)
    have hX2 : ColsIn Λ X.toCols₂ := fun a => cols_mul hd hb hden (Sum.inr a)
    have h3 := (GlobalTheory.SW.heisH_laws E Ψ hΨ n N hn (((2 * R : ℕ) : E) • X.toCols₁)
      (((2 * R : ℕ) : E) • X.toCols₂) φ hSB).2.2 γ hγ
    have h4 : Matrix.fromCols (((2 * R : ℕ) : E) • X.toCols₁) (((2 * R : ℕ) : E) • X.toCols₂) =
        ((2 * R : ℕ) : E) • X := by
      ext k (j | j) <;> rfl
    rw [heisH_fix hΛ hφ hX1 hX2, h4, hX, Matrix.mul_smul, smul_smul, Matrix.smul_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).1.1, Matrix.mul_one,
      ← Nat.cast_mul] at h3
    exact h3.symm
  refine ⟨hSB, hψ, fun B hB x => ?_⟩
  have hφ' : LevelL Λ R' φ := by
    have := levelL_mul hφ ((NumberField.discr E).natAbs * (2 * c))
    rwa [show (NumberField.discr E).natAbs * (2 * c) * R = R' by rw [hR']; ring] at this
  have hip := ((GlobalTheory.SW.weil_action E Ψ hΨ n N hn γ hγ φ hSB).2.2.2.1 φ hSB).1
  have hsq : ∀ k : Matrix (Fin n) (Fin N) E → ℂ, LevelL Λ R' k →
      ip k k = haarAt (s * R') fun x => k x * conj (k x) := by
    intro k hk
    have hk' := hasLevel_of_levelL h1 h2 hk
    exact (haar_eq_haarAt E _ _ (s * R') _ (by positivity)
      ⟨fun x hx => hk'.1 x (left_ne_zero_of_mul hx), fun x y hy => by simp only [hk'.2 x y hy]⟩).1
  rw [hsq _ hψ, hsq _ hφ', haarAt, haarAt] at hip
  have hip2 := mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _
    (by exact_mod_cast (show s * R' ≠ 0 by positivity)))) hip
  let u : AddSubgroup (Matrix (Fin n) (Fin N) E) :=
    { carrier := {x | ColsIn Λ ((R' : E) • x)}
      zero_mem' := fun a => by rw [smul_zero]; exact Λ.zero_mem
      add_mem' := fun {x y} hx hy a => by rw [smul_add]; exact Λ.add_mem (hx a) (hy a)
      neg_mem' := fun {x} hx a => by rw [smul_neg]; exact Λ.neg_mem (hx a) }
  have hu : ∀ x ∈ u, IntM (((s * R' : ℕ) : E) • x) := fun x hx k a => by
    rw [Nat.cast_mul, mul_smul]
    exact (Model.mem_stdL _).1 (h1 _ (hx a)) k
  set t := u.map (nsmulAddMonoidHom (R' * R')) with ht
  have htu : t ≤ u := by
    rintro _ ⟨y, hy, rfl⟩
    exact u.nsmul_mem hy _
  have hper : ∀ k : Matrix (Fin n) (Fin N) E → ℂ, LevelL Λ R' k → ∀ x, ∀ y ∈ t,
      k (x + y) = k x := by
    rintro k hk x _ ⟨y, hy, rfl⟩
    rw [nsmulAddMonoidHom_apply, ← Nat.cast_smul_eq_nsmul E, Nat.cast_mul, mul_smul]
    exact hk.2 x _ hy
  have hR'E : (R' : E) ≠ 0 := by exact_mod_cast hR'0.ne'
  have hst : perSub E (Fin n) (Fin N) (s * R') ≤ t := by
    rw [perSub, AddSubgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(R' : E)⁻¹ • (s : E) • y, fun a => ?_, ?_⟩
    · rw [smul_inv_smul₀ hR'E]
      exact h2 _ ((Model.mem_stdL _).2 fun k => hy k a)
    · rw [nsmulAddMonoidHom_apply, ← Nat.cast_smul_eq_nsmul E, Nat.cast_mul, mul_smul,
        smul_inv_smul₀ hR'E, smul_smul, Nat.cast_mul s, mul_comm (s : E)]
  have hle : t.map (nsmulAddMonoidHom ((s * R') * (s * R'))) ≤
      perSub E (Fin n) (Fin N) (s * R') := by
    rintro _ ⟨y, hy, rfl⟩
    refine AddSubgroup.subset_closure ⟨_, hu y (htu hy), ?_⟩
    rw [nsmulAddMonoidHom_apply, ← Nat.cast_smul_eq_nsmul E, Nat.cast_mul, mul_smul]
  have hi1 := (relIndex_nsmul t (show 0 < s * R' by positivity) (fun x hx => hu x (htu hx))
    (show 0 < (s * R') * (s * R') by positivity)).1
  obtain ⟨hi2, hi3⟩ := relIndex_nsmul u (show 0 < s * R' by positivity) hu
    (show 0 < R' * R' by positivity)
  have h5 := sq_le_of_finsum_eq hst
    (ne_zero_of_dvd_ne_zero hi1 (AddSubgroup.relIndex_dvd_of_le_left _ hle)) hi2 φ (weil Ψ γ φ)
    (hper _ hφ') (hper _ hψ) hφ'.1 hψ.1 hip2.symm B hB x
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (h5.trans ?_)
  have h6 : ((t.relIndex u : ℕ) : ℝ) ≤ ((R' : ℝ) ^ e) ^ 2 := by
    rw [sq, ← mul_pow]
    exact_mod_cast hi3
  rw [mul_pow]
  gcongr

end GlobalTheory.SW
