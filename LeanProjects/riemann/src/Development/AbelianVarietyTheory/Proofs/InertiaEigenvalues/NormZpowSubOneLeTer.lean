import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateOperatorLevelComplement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowSubOneLe

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CycSeries

section Abstract

variable {C : Type} [NormedField C]

theorem mulVec_mem {r : ℕ} (X : AddSubgroup C) (B : Matrix (Fin r) (Fin r) C)
    (hB : ∀ a b, ∀ x ∈ X, B a b * x ∈ X) (v : Fin r → C) (hv : ∀ a, v a ∈ X) (a : Fin r) :
    B.mulVec v a ∈ X := by
  simp only [Matrix.mulVec, dotProduct]
  exact X.sum_mem fun b _ => hB a b _ (hv b)

theorem inj_of_small {r : ℕ} (X : AddSubgroup C) (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (g : C ≃+* C)
    (hgX : ∀ x ∈ X, g x ∈ X) (p q : C) (hp : p ≠ 0) (hq : q ≠ 0) (hq1 : ‖q‖ < 1) (hgq : g q = q)
    (S : C → C) (hS : ∀ x ∈ X, S x ∈ X ∧ S (g x - x) = p * x)
    (hlin : ∀ x ∈ X, S (p * q * x) = p * q * S x)
    (B : Matrix (Fin r) (Fin r) C) (hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X)
    (y : Fin r → C) (hy : ∀ a, y a ∈ X)
    (h : ∀ a, g (y a) - y a + p * q * B.mulVec (fun b => g (y b)) a = 0) : y = 0 := by
  have key : ∀ n : ℕ, ∀ y : Fin r → C, (∀ a, y a ∈ X) →
      (∀ a, g (y a) - y a + p * q * B.mulVec (fun b => g (y b)) a = 0) → ∀ a, ‖y a‖ ≤ ‖q‖ ^ n := by
    intro n
    induction n with
    | zero => intro y hy _ a; simpa using hX1 _ (hy a)
    | succ n ih =>
      intro y hy h a
      have hm : ∀ a, -B.mulVec (fun b => g (y b)) a ∈ X := fun a =>
        X.neg_mem (mulVec_mem X B hBX _ (fun b => hgX _ (hy b)) a)
      let z : Fin r → C := fun a => S (-B.mulVec (fun b => g (y b)) a)
      have hyz : ∀ a, y a = q * z a := fun a => by
        apply mul_left_cancel₀ hp
        rw [← (hS _ (hy a)).2, eq_neg_of_add_eq_zero_left (h a), ← mul_neg, hlin _ (hm a), mul_assoc]
      have := ih z (fun a => (hS _ (hm a)).1) (fun a => by
        apply mul_left_cancel₀ hq
        have h1 := h a
        have e : (fun b => g (y b)) = q • fun b => g (z b) := by
          funext b; rw [hyz b, map_mul, hgq]; rfl
        rw [e, Matrix.mulVec_smul, hyz a, map_mul, hgq, Pi.smul_apply, smul_eq_mul] at h1
        linear_combination h1) a
      rw [hyz a, norm_mul, pow_succ']
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  funext a
  exact norm_le_zero_iff.1 (ge_of_tendsto'
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq1) fun n => key n y hy h a)

theorem surj_of_small [CompleteSpace C] {r : ℕ} (X : AddSubgroup C) (hX : IsClosed (X : Set C))
    (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (g : C ≃+* C) (hg : Continuous g) (hgX : ∀ x ∈ X, g x ∈ X)
    (p q : C) (hq1 : ‖q‖ < 1) (hgq : g q = q) (hqX : ∀ x ∈ X, q * x ∈ X) (S : C → C)
    (hS : ∀ x ∈ X, S x ∈ X ∧ g (S x) - S x = p * x)
    (B : Matrix (Fin r) (Fin r) C)
    (hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X) (w : Fin r → C) (hw : ∀ a, w a ∈ X) :
    ∃ y : Fin r → C, (∀ a, y a ∈ X) ∧
      ∀ a, g (y a) - y a + p * q * B.mulVec (fun b => g (y b)) a = p * w a := by
  let T : (Fin r → C) → (Fin r → C) := fun v a => -B.mulVec (fun b => g (S (v b))) a
  let v : ℕ → Fin r → C := fun n => T^[n] w
  have hvs : ∀ n, v (n + 1) = T (v n) := fun n => Function.iterate_succ_apply' T n w
  have hv : ∀ n a, v n a ∈ X := by
    intro n
    induction n with
    | zero => exact hw
    | succ n ih =>
      intro a
      rw [hvs]
      exact X.neg_mem (mulVec_mem X B hBX _ (fun b => hgX _ (hS _ (ih b)).1) a)
  have hqn : ∀ n : ℕ, ∀ x ∈ X, q ^ n * x ∈ X := by
    intro n x hx
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ', mul_assoc]; exact hqX _ ih
  have hbd : ∀ n : ℕ, ∀ x ∈ X, ‖q ^ n * x‖ ≤ ‖q‖ ^ n := fun n x hx => by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (hX1 x hx)
  have hsum : ∀ a, Summable fun n => q ^ n * S (v n a) := fun a =>
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg q) hq1)
      fun n => hbd n _ (hS _ (hv n a)).1
  let y : Fin r → C := fun a => ∑' n, q ^ n * S (v n a)
  let Y : ℕ → Fin r → C := fun N a => ∑ n ∈ Finset.range N, q ^ n * S (v n a)
  have hY : ∀ a, Filter.Tendsto (fun N => Y N a) Filter.atTop (nhds (y a)) := fun a =>
    (hsum a).hasSum.tendsto_sum_nat
  refine ⟨y, fun a => hX.mem_of_tendsto (hY a) (Filter.Eventually.of_forall fun N =>
    X.sum_mem fun n _ => hqn n _ (hS _ (hv n a)).1), fun a => ?_⟩
  have hN : ∀ N, g (Y N a) - Y N a + p * q * B.mulVec (fun b => g (Y N b)) a
      = p * w a - p * (q ^ N * v N a) := by
    intro N
    induction N with
    | zero => simp [Y, v, Matrix.mulVec, dotProduct]
    | succ N ih =>
      have e : ∀ b, Y (N + 1) b = Y N b + q ^ N * S (v N b) := fun b => Finset.sum_range_succ _ _
      have e2 : (fun b => g (Y (N + 1) b))
          = (fun b => g (Y N b)) + q ^ N • fun b => g (S (v N b)) := by
        funext b; rw [e, map_add, map_mul, map_pow, hgq]; rfl
      rw [e2, e, map_add, map_mul, map_pow, hgq, Matrix.mulVec_add, Matrix.mulVec_smul, hvs]
      simp only [T, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination ih + q ^ N * (hS _ (hv N a)).2
  have t1 : Filter.Tendsto (fun N => g (Y N a) - Y N a + p * q * B.mulVec (fun b => g (Y N b)) a)
      Filter.atTop (nhds (g (y a) - y a + p * q * B.mulVec (fun b => g (y b)) a)) := by
    refine (((hg.tendsto _).comp (hY a)).sub (hY a)).add (Filter.Tendsto.const_mul _ ?_)
    simp only [Matrix.mulVec, dotProduct]
    exact tendsto_finset_sum _ fun b _ => ((hg.tendsto _).comp (hY b)).const_mul _
  have t0 : Filter.Tendsto (fun N => q ^ N * v N a) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun N => hbd N _ (hv N a))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq1)
  have t2 : Filter.Tendsto (fun N => p * w a - p * (q ^ N * v N a)) Filter.atTop
      (nhds (p * w a - p * 0)) := tendsto_const_nhds.sub (t0.const_mul p)
  rw [mul_zero, sub_zero] at t2
  simp only [hN] at t1
  exact tendsto_nhds_unique t1 t2

variable [IsUltrametricDist C]

theorem norm_zpow_sub_one_le (u : C) (hu : ‖u - 1‖ < 1) (i : ℤ) : ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
  first
  | exact @_root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le
  | exact _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le
  | (apply _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le ..)

end Abstract

variable {l : ℕ} [hl : Fact l.Prime]

theorem pow_lt_rho {j : ℕ} (hj : Lev l j) : (l : ℝ) ^ (-(j : ℤ)) < rho1 l := by
  have h2 : 2 ≤ l := hl.1.two_le
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  rw [rho1, ← Real.rpow_intCast]
  apply Real.rpow_lt_rpow_of_exponent_lt h1
  rw [lt_div_iff₀ (by linarith)]
  push_cast
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
  rcases h2.eq_or_lt with h | h
  · have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj.2 h.symm
    have : (l : ℝ) = 2 := by exact_mod_cast h.symm
    rw [this]; linarith
  · have : (3 : ℝ) ≤ l := by exact_mod_cast h
    nlinarith

theorem rho_lt_one : rho1 l < 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  rw [rho1]
  apply Real.rpow_lt_one_of_one_lt_of_neg h1
  exact div_neg_of_neg_of_pos (by norm_num) (by linarith)

theorem norm_root_sub_one {ζ : PadicComplex l} (h : IsPrimitiveRoot ζ l) : ‖ζ - 1‖ = rho1 l := by
  have := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl ζ (by rwa [pow_one])
  simpa [rho1] using this

theorem mem_inC_iff (F : IntermediateField ℚ_[l] (Om l)) (y : PadicComplex l) :
    y ∈ inC F ↔ y ∈ F.toSubfield.map (algebraMap (Om l) (PadicComplex l)) := by
  simp [inC, PadicComplex.coe_eq]

theorem root_mem_inC (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {ζ : PadicComplex l}
    (h : IsPrimitiveRoot ζ l) : ζ ∈ inC (Ks K j) := by
  haveI : NeZero l := ⟨hl.1.ne_zero⟩
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hη' := hη.map_of_injective (algebraMap (Om l) (PadicComplex l)).injective
  obtain ⟨k, -, hk⟩ := hη'.eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨η ^ k, ?_, ?_⟩
  · refine pow_mem (?_ : η ∈ Ks K j) k
    refine (le_sup_right : _ ≤ Ks K j) (IntermediateField.subset_adjoin _ _ ?_)
    exact (hη.pow_eq_one_iff_dvd _).2 (dvd_pow_self l (by omega))
  · simp only [PadicComplex.coe_eq, map_pow]
    exact hk

theorem chiC_mem_inC (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g : GQ l)
    (F : IntermediateField ℚ_[l] (Om l)) : chiC χ i g ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) _, F.algebraMap_mem _, rfl⟩

theorem norm_chiC_sub_one {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) (i : ℤ) : ‖chiC χ i g - 1‖ < rho1 l := by
  have h1 : ‖(χ g : ℚ_[l]) - 1‖ < rho1 l := hg.2 ▸ pow_lt_rho hj
  have h2 := norm_zpow_sub_one_le _ (h1.trans rho_lt_one) i
  have e : chiC χ i g - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1) := by
    simp [chiC]
  rw [e, norm_algebraMap']
  exact h2.trans_lt h1

theorem exists_quot {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) {r : ℕ} (U : Matrix (Fin r) (Fin r) (PadicComplex l))
    (hU : ∀ a b, U a b ∈ intC (Ks K j)) (hU1 : ∀ a b, ‖(U - 1) a b‖ < rho1 l) (i : ℤ)
    {ζ : PadicComplex l} (h : IsPrimitiveRoot ζ l) :
    ∃ (B : Matrix (Fin r) (Fin r) (PadicComplex l)),
      (∀ a b, ‖B a b‖ < 1) ∧ (∀ a b, B a b ∈ intC (Ks K j)) ∧
      chiC χ i g • U = 1 + (ζ - 1) • B := by
  have hz := norm_root_sub_one h
  have hz0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (h.ne_one hl.1.one_lt)
  have hzp : 0 < ‖ζ - 1‖ := norm_pos_iff.2 hz0
  have hc := norm_chiC_sub_one hj hg i
  have hc1 : ‖chiC χ i g‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (chiC χ i g - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le (hc.trans rho_lt_one).le le_rfl)
  let B : Matrix (Fin r) (Fin r) (PadicComplex l) := (ζ - 1)⁻¹ • (chiC χ i g • U - 1)
  have hB : ∀ a b, ‖B a b‖ < 1 := by
    intro a b
    have e : B a b = (ζ - 1)⁻¹ * (chiC χ i g * (U - 1) a b
        + (chiC χ i g - 1) * (1 : Matrix (Fin r) (Fin r) (PadicComplex l)) a b) := by
      simp only [B, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]; ring
    rw [e, norm_mul, norm_inv, inv_mul_lt_iff₀ hzp, mul_one, hz]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hc1).trans_lt (hU1 a b)
    · rw [norm_mul]
      refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans_lt hc
      rw [Matrix.one_apply]; split_ifs <;> simp
  refine ⟨B, hB, fun a b => ⟨?_, (hB a b).le⟩, ?_⟩
  · have m1 := (mem_inC_iff _ _).1 (root_mem_inC K hj.1 h)
    have m2 := (mem_inC_iff _ _).1 (chiC_mem_inC χ i g (Ks K j))
    have m3 := (mem_inC_iff _ _).1 (hU a b).1
    rw [mem_inC_iff]
    simp only [B, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    refine mul_mem (inv_mem (sub_mem m1 (one_mem _))) (sub_mem (mul_mem m2 m3) ?_)
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  · simp only [B, smul_smul, mul_inv_cancel₀ hz0, one_smul]; abel

theorem twAct_sub {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ} {i : ℤ}
    {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l} {p : PadicComplex l}
    {B : Matrix (Fin r) (Fin r) (PadicComplex l)} (h : chiC χ i g • U g = 1 + p • B)
    (y : Fin r → PadicComplex l) (a : Fin r) :
    (twAct act χ i U g y - y) a
      = act g (y a) - y a + p * B.mulVec (fun b => act g (y b)) a := by
  rw [twAct, ← Matrix.smul_mulVec, h, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem mul_mem_intC {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l} (hx : x ∈ intC F)
    (hy : y ∈ intC F) : x * y ∈ intC F :=
  ⟨(mem_inC_iff _ _).2 (mul_mem ((mem_inC_iff _ _).1 hx.1) ((mem_inC_iff _ _).1 hy.1)),
    by rw [norm_mul]; exact mul_le_one₀ hx.2 (norm_nonneg _) hy.2⟩

theorem exists_factor {F : IntermediateField ℚ_[l] (Om l)} {r : ℕ}
    (B : Matrix (Fin r) (Fin r) (PadicComplex l)) (h1 : ∀ a b, ‖B a b‖ < 1)
    (hB : ∀ a b, B a b ∈ intC F) :
    ∃ (q : PadicComplex l) (B' : Matrix (Fin r) (Fin r) (PadicComplex l)), q ≠ 0 ∧ ‖q‖ < 1 ∧
      q ∈ intC F ∧ (∀ a b, B' a b ∈ intC F) ∧ B = q • B' := by
  have hq : ∃ q : PadicComplex l, q ≠ 0 ∧ ‖q‖ < 1 ∧ q ∈ inC F ∧ ∀ a b, ‖B a b‖ ≤ ‖q‖ := by
    by_cases h0 : B = 0
    · refine ⟨l, Nat.cast_ne_zero.2 hl.1.ne_zero, ?_, (mem_inC_iff _ _).2 (natCast_mem _ _),
        fun a b => by simp [h0]⟩
      rw [← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), norm_algebraMap', Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.1.one_lt)
    · obtain ⟨a0, b0, hab⟩ : ∃ a b, B a b ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact h0 (Matrix.ext hc)
      obtain ⟨s, -, hs⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin r × Fin r))
        (fun s => ‖B s.1 s.2‖) ⟨(a0, b0), Finset.mem_univ _⟩
      refine ⟨B s.1 s.2, ?_, h1 _ _, (hB _ _).1, fun a b => hs (a, b) (Finset.mem_univ _)⟩
      exact norm_pos_iff.1 ((norm_pos_iff.2 hab).trans_le (hs (a0, b0) (Finset.mem_univ _)))
  obtain ⟨q, hq0, hq1, hqF, hq⟩ := hq
  refine ⟨q, q⁻¹ • B, hq0, hq1, ⟨hqF, hq1.le⟩, fun a b => ⟨?_, ?_⟩, ?_⟩
  · exact (mem_inC_iff _ _).2 (mul_mem (inv_mem ((mem_inC_iff _ _).1 hqF))
      ((mem_inC_iff _ _).1 (hB a b).1))
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv,
      inv_mul_le_iff₀ (norm_pos_iff.2 hq0), mul_one]
    exact hq a b
  · rw [smul_smul, mul_inv_cancel₀ hq0, one_smul]

theorem norm_le_one_of_Ohat (K : FinExt l) {x : PadicComplex l} (hx : x ∈ Ohat K) : ‖x‖ ≤ 1 :=
  closure_minimal (fun _ hy => hy.2) (isClosed_le continuous_norm continuous_const) hx

theorem perturbation : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ g, IsGen χ K j g → ∀ (r : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)), (∀ a b, U g a b ∈ intC (Ks K j)) → (∀ a b, ‖(U g - 1) a b‖ < rho1 l) → ∀ i : ℤ, (∀ y : Fin r → PadicComplex l, (∀ a, y a ∈ Xj K j) → twAct act χ i U g y = y → y = 0) ∧ ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ l → ∀ w : Fin r → PadicComplex l, (∀ a, w a ∈ Xj K j) → ∃ y : Fin r → PadicComplex l, (∀ a, y a ∈ Xj K j) ∧ twAct act χ i U g y - y = (ζ - 1) • w := by
  intro l hl act χ hact hχ K j hj g hg r U hU hU1 i
  obtain ⟨-, -, hXO, hmul, hstab, -⟩ := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1
  have hX1 : ∀ x ∈ Xj K j, ‖x‖ ≤ 1 := fun x hx => norm_le_one_of_Ohat K (hXO x hx)
  have hg0 : g ∈ (K0 K).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Ks K j) hg.1
  have hgX := hstab g hg0
  constructor
  · intro y hy hfix
    have : NeZero l := ⟨hl.1.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicComplex l) l
    obtain ⟨S, hS, -, hlin⟩ := GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ
    obtain ⟨B, hB, hBO, hBe⟩ := exists_quot hj hg (U g) hU hU1 i hζ
    obtain ⟨q, B', hq0, hq1, hqO, hB', rfl⟩ := exists_factor B hB hBO
    rw [smul_smul] at hBe
    refine inj_of_small (Xj K j) hX1 (act g) hgX (ζ - 1) q
      (sub_ne_zero.2 (hζ.ne_one hl.1.one_lt)) hq0 hq1 (TateS.act_fix hact K hg.1 hqO.1) S
      (fun x hx => ⟨(hS x hx).1, (hS x hx).2.2⟩)
      (hlin _ (mul_mem_intC (TateS.zeta_sub_one_mem K hj.1 hζ) hqO))
      B' (fun a b => hmul _ (hB' a b)) y hy fun a => ?_
    rw [← twAct_sub hBe, hfix, sub_self, Pi.zero_apply]
  · intro ζ hζ w hw
    obtain ⟨S, hS, -, -⟩ := GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ
    obtain ⟨B, hB, hBO, hBe⟩ := exists_quot hj hg (U g) hU hU1 i hζ
    obtain ⟨q, B', hq0, hq1, hqO, hB', rfl⟩ := exists_factor B hB hBO
    rw [smul_smul] at hBe
    obtain ⟨y, hy, he⟩ := surj_of_small (Xj K j) (AddSubgroup.isClosed_topologicalClosure _) hX1
      (act g) (AddMonoidHomClass.isometry_of_norm (act g) (hact.2 g)).continuous hgX (ζ - 1) q hq1
      (TateS.act_fix hact K hg.1 hqO.1) (hmul _ hqO) S
      (fun x hx => ⟨(hS x hx).1, (hS x hx).2.1⟩) B' (fun a b => hmul _ (hB' a b)) w hw
    refine ⟨y, hy, funext fun a => ?_⟩
    rw [twAct_sub hBe, he, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.CycSeries
