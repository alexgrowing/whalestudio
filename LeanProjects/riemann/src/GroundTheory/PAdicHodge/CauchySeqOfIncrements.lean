import Mathlib
import GroundTheory.PAdicHodge.IsUnitOfRadOfMultEqZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

def RootExists : Prop :=
  ∀ (ρ0 : Set.Ioo (0 : ℝ) 1) (x : T.RobbaExt ρ0), x ≠ 0 → ∀ r : ℝ, 0 < r → r < ρ0 →
    1 ≤ T.mult x r → ∃ (ξ : T.int) (hξ : T.IsPrimOne ξ), T.ptRad ξ = r ∧ ∃ y, x = T.ξExt ξ ρ0 * y

abbrev Pt := {ξ : T.int // T.IsPrimOne ξ}

variable {ρ0 : Set.Ioo (0 : ℝ) 1}

def ptProd (ρ0 : Set.Ioo (0 : ℝ) 1) (l : List T.Pt) : T.RobbaExt ρ0 :=
  (l.map fun P => T.ξExt P.1 ρ0).prod

theorem ptProd_nil : T.ptProd ρ0 [] = 1 := rfl

theorem ptProd_cons (P : T.Pt) (l : List T.Pt) :
    T.ptProd ρ0 (P :: l) = T.ξExt P.1 ρ0 * T.ptProd ρ0 l := by
  simp [ptProd]

theorem ptProd_ne_zero (l : List T.Pt) : T.ptProd ρ0 l ≠ 0 := by
  induction l with
  | nil => exact one_ne_zero
  | cons P l ih => rw [ptProd_cons]; exact mul_ne_zero (T.ptExt_ne_zero P.2) ih

theorem mult_sum_nonneg {x : T.RobbaExt ρ0} (hx : x ≠ 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < ρ0) : 0 ≤ T.highIdx x b - T.lowIdx x a := by
  rw [← T.sum_mult_breaksR hx ha hab hb]
  exact Finset.sum_nonneg fun σ _ => T.mult_nonneg x σ

theorem exists_factor_annulus (hRE : T.RootExists) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < ρ0) :
    ∀ {x : T.RobbaExt ρ0}, x ≠ 0 → ∃ (l : List T.Pt) (y : T.RobbaExt ρ0),
      (∀ P ∈ l, a ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ b) ∧ x = T.ptProd ρ0 l * y ∧ y ≠ 0 ∧
        ∀ σ, a ≤ σ → σ ≤ b → T.mult y σ = 0 := by
  suffices H : ∀ M : ℕ, ∀ x : T.RobbaExt ρ0, x ≠ 0 → T.highIdx x b - T.lowIdx x a = M →
      ∃ (l : List T.Pt) (y : T.RobbaExt ρ0),
        (∀ P ∈ l, a ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ b) ∧ x = T.ptProd ρ0 l * y ∧ y ≠ 0 ∧
          ∀ σ, a ≤ σ → σ ≤ b → T.mult y σ = 0 by
    intro x hx
    exact H _ x hx (Int.toNat_of_nonneg (T.mult_sum_nonneg hx ha hab hb)).symm
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro x hx hM
  by_cases hz : ∀ σ, a ≤ σ → σ ≤ b → T.mult x σ = 0
  · exact ⟨[], x, by simp, by rw [ptProd_nil, one_mul], hx, hz⟩
  push_neg at hz
  obtain ⟨σ, hσa, hσb, hσm⟩ := hz
  have hσ1 : 1 ≤ T.mult x σ := by
    have := T.mult_nonneg x σ
    omega
  obtain ⟨ξ, hξ, hr, y', hxy⟩ := hRE ρ0 x hx σ (ha.trans_le hσa) (hσb.trans_lt hb) hσ1
  have hy'0 : y' ≠ 0 := by rintro rfl; rw [mul_zero] at hxy; exact hx hxy
  have hξ0 := T.ptExt_ne_zero (ρ0 := ρ0) hξ
  have hia := T.idx_mul hξ0 hy'0 ⟨ha, hab.trans_lt hb⟩
  have hib := T.idx_mul hξ0 hy'0 ⟨ha.trans_le hab, hb⟩
  have hla := (T.idx_ptExt (ρ0 := ρ0) hξ ⟨ha, hab.trans_lt hb⟩).1
  have hhb := (T.idx_ptExt (ρ0 := ρ0) hξ ⟨ha.trans_le hab, hb⟩).2
  rw [if_pos (hr ▸ hσa)] at hla
  rw [if_neg (not_lt.2 (hr ▸ hσb))] at hhb
  rw [← hxy] at hia hib
  have hM' : T.highIdx y' b - T.lowIdx y' a = (M - 1 : ℕ) := by
    have hnn := T.mult_sum_nonneg hy'0 ha hab hb
    have : T.highIdx y' b - T.lowIdx y' a + 1 = M := by
      rw [← hM, hib.2, hia.1, hla, hhb]; ring
    omega
  have hMpos : 0 < M := by
    have hnn := T.mult_sum_nonneg hy'0 ha hab hb
    have : T.highIdx y' b - T.lowIdx y' a + 1 = M := by
      rw [← hM, hib.2, hia.1, hla, hhb]; ring
    omega
  obtain ⟨l, y, hl, hy'e, hy0, hym⟩ := ih (M - 1) (by omega) y' hy'0 hM'
  refine ⟨⟨ξ, hξ⟩ :: l, y, ?_, ?_, hy0, hym⟩
  · intro P hP
    rcases List.mem_cons.1 hP with rfl | hP
    · exact ⟨hr ▸ hσa, hr ▸ hσb⟩
    · exact hl P hP
  · rw [ptProd_cons, hxy, hy'e, mul_assoc]

theorem cauchySeq_of_increments {z : ℕ → T.RobbaExt ρ0}
    (h : ∀ ρ, Tendsto (fun n => T.extNorm ρ0 ρ (z (n + 1) - z n)) atTop (𝓝 0)) :
    CauchySeq z := by
  refine T.cauchySeq_of_extNorm fun ρ ε hε => ?_
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.1 (h ρ)) ε hε
  have hinc : ∀ n ≥ J, T.extNorm ρ0 ρ (z (n + 1) - z n) < ε := fun n hn => by
    have := hJ n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (T.extNorm_nonneg _ _)] at this
  have key : ∀ k ≥ J, ∀ j, T.extNorm ρ0 ρ (z (k + j) - z k) < ε := by
    intro k hk j
    induction j with
    | zero => rw [add_zero, sub_self, extNorm_zero]; exact hε
    | succ j ih =>
      have := T.extNorm_add_le ρ (z (k + j + 1) - z (k + j)) (z (k + j) - z k)
      rw [sub_add_sub_cancel] at this
      exact this.trans_lt (max_lt (hinc _ (by omega)) ih)
  refine ⟨J, fun j hj k hk => ?_⟩
  rcases le_total k j with hkj | hjk
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hkj
    exact key k hk i
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjk
    rw [extNorm_sub_comm]
    exact key j hj i

structure InfProd (ρ0 : Set.Ioo (0 : ℝ) 1) where

  g : ℕ → T.RobbaExt ρ0
  one_le_norm : ∀ n ρ, 1 ≤ T.extNorm ρ0 ρ (g n)
  tendsto_sub_one : ∀ ρ, Tendsto (fun n => T.extNorm ρ0 ρ (g n - 1)) atTop (𝓝 0)

namespace InfProd

variable {T} (F : T.InfProd ρ0)

def part (n : ℕ) : T.RobbaExt ρ0 := ∏ i ∈ Finset.range n, F.g i

theorem part_zero : F.part 0 = 1 := by simp [part]

theorem part_succ (n : ℕ) : F.part (n + 1) = F.part n * F.g n := by
  simp [part, Finset.prod_range_succ]

theorem one_le_norm_part (n : ℕ) (ρ : Set.Ioc (0 : ℝ) ρ0) : 1 ≤ T.extNorm ρ0 ρ (F.part n) := by
  induction n with
  | zero => rw [part_zero, extNorm_one]
  | succ n ih =>
    rw [part_succ, extNorm_mul]
    exact one_le_mul_of_one_le_of_one_le ih (F.one_le_norm n ρ)

theorem part_ne_zero (n : ℕ) : F.part n ≠ 0 := by
  intro h
  have := F.one_le_norm_part n (topRad ρ0)
  rw [h, extNorm_zero] at this
  linarith

theorem eventually_norm_eq_one (ρ : Set.Ioc (0 : ℝ) ρ0) :
    ∀ᶠ n in atTop, T.extNorm ρ0 ρ (F.g n) = 1 := by
  filter_upwards [(F.tendsto_sub_one ρ).eventually (gt_mem_nhds one_pos)] with n hn
  refine le_antisymm ?_ (F.one_le_norm n ρ)
  have := T.extNorm_add_le ρ (F.g n - 1) 1
  rw [sub_add_cancel, extNorm_one] at this
  exact this.trans (max_le hn.le le_rfl)

theorem exists_bound (ρ : Set.Ioc (0 : ℝ) ρ0) : ∃ B, ∀ n, T.extNorm ρ0 ρ (F.part n) ≤ B := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (F.eventually_norm_eq_one ρ)
  refine ⟨T.extNorm ρ0 ρ (F.part N), fun n => ?_⟩
  have mono : ∀ k, T.extNorm ρ0 ρ (F.part k) ≤ T.extNorm ρ0 ρ (F.part (k + 1)) := fun k => by
    rw [part_succ, extNorm_mul]
    exact le_mul_of_one_le_right (T.extNorm_nonneg _ _) (F.one_le_norm k ρ)
  have stab : ∀ j, T.extNorm ρ0 ρ (F.part (N + j)) = T.extNorm ρ0 ρ (F.part N) := fun j => by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← add_assoc, part_succ, extNorm_mul, hN (N + j) (by omega), mul_one, ih]
  have monoLe : ∀ a b, a ≤ b → T.extNorm ρ0 ρ (F.part a) ≤ T.extNorm ρ0 ρ (F.part b) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b _ ih => exact ih.trans (mono b)
  rcases le_total n N with h | h
  · exact monoLe n N h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [stab]

theorem cauchySeq_part : CauchySeq F.part := by
  refine T.cauchySeq_of_increments fun ρ => ?_
  obtain ⟨B, hB⟩ := F.exists_bound ρ
  have hB0 : 0 ≤ B := (T.extNorm_nonneg _ _).trans (hB 0)
  have hmul := (F.tendsto_sub_one ρ).const_mul B
  rw [mul_zero] at hmul
  refine squeeze_zero (fun n => T.extNorm_nonneg _ _) (fun n => ?_) hmul
  rw [part_succ, show F.part n * F.g n - F.part n = F.part n * (F.g n - 1) by ring, extNorm_mul]
  exact mul_le_mul_of_nonneg_right (hB n) (T.extNorm_nonneg _ _)

def prod : T.RobbaExt ρ0 := Classical.choose (cauchySeq_tendsto_of_complete F.cauchySeq_part)

theorem tendsto_part : Tendsto F.part atTop (𝓝 F.prod) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete F.cauchySeq_part)

theorem one_le_norm_prod (ρ : Set.Ioc (0 : ℝ) ρ0) : 1 ≤ T.extNorm ρ0 ρ F.prod :=
  ge_of_tendsto (((T.continuous_extNorm ρ).tendsto _).comp F.tendsto_part)
    (Eventually.of_forall fun n => F.one_le_norm_part n ρ)

theorem prod_ne_zero : F.prod ≠ 0 := by
  intro h
  have := F.one_le_norm_prod (topRad ρ0)
  rw [h, extNorm_zero] at this
  linarith

theorem dvd_of_forall {x : T.RobbaExt ρ0} (h : ∀ n, F.part n ∣ x) : F.prod ∣ x := by
  choose y hy using h
  have hstep : ∀ n, y n = F.g n * y (n + 1) := fun n => by
    have e : F.part n * y n = F.part n * (F.g n * y (n + 1)) := by
      rw [← hy n, hy (n + 1), part_succ, mul_assoc]
    exact mul_left_cancel₀ (F.part_ne_zero n) e
  have hyb : ∀ n (ρ : Set.Ioc (0 : ℝ) ρ0), T.extNorm ρ0 ρ (y n) ≤ T.extNorm ρ0 ρ x := fun n ρ => by
    have e := congrArg (T.extNorm ρ0 ρ) (hy n)
    rw [extNorm_mul] at e
    rw [e]
    exact le_mul_of_one_le_left (T.extNorm_nonneg _ _) (F.one_le_norm_part n ρ)
  have hc : CauchySeq y := by
    refine T.cauchySeq_of_increments fun ρ => ?_
    have hmul := (F.tendsto_sub_one ρ).const_mul (T.extNorm ρ0 ρ x)
    rw [mul_zero] at hmul
    refine squeeze_zero (fun n => T.extNorm_nonneg _ _) (fun n => ?_) hmul
    rw [hstep n, show y (n + 1) - F.g n * y (n + 1) = -((F.g n - 1) * y (n + 1)) by ring,
      extNorm_neg, extNorm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hyb _ ρ) (T.extNorm_nonneg _ _)
  obtain ⟨yl, hyl⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨yl, ?_⟩
  have hlim : Tendsto (fun n => F.part n * y n) atTop (𝓝 (F.prod * yl)) :=
    F.tendsto_part.mul hyl
  have hconst : (fun n => F.part n * y n) = fun _ => x := funext fun n => (hy n).symm
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

def shift (k : ℕ) : T.InfProd ρ0 where
  g n := F.g (k + n)
  one_le_norm n ρ := F.one_le_norm (k + n) ρ
  tendsto_sub_one ρ := (F.tendsto_sub_one ρ).comp (tendsto_atTop_atTop_of_monotone
    (fun _ _ h => by omega) fun n => ⟨n, by omega⟩)

theorem part_add (k n : ℕ) : F.part (k + n) = F.part k * (F.shift k).part n := by
  simp only [part, shift]
  rw [Finset.prod_range_add]

theorem prod_eq_part_mul_shift (k : ℕ) : F.prod = F.part k * (F.shift k).prod := by
  have h1 : Tendsto (fun n => F.part (k + n)) atTop (𝓝 F.prod) :=
    F.tendsto_part.comp (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega)
      fun n => ⟨n, by omega⟩)
  have h2 : Tendsto (fun n => F.part k * (F.shift k).part n) atTop
      (𝓝 (F.part k * (F.shift k).prod)) := tendsto_const_nhds.mul (F.shift k).tendsto_part
  have e : (fun n => F.part (k + n)) = fun n => F.part k * (F.shift k).part n :=
    funext fun n => F.part_add k n
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

theorem part_dvd_prod (k : ℕ) : F.part k ∣ F.prod := ⟨_, F.prod_eq_part_mul_shift k⟩

end InfProd

def normProd (ρ0 : Set.Ioo (0 : ℝ) 1) (l : List T.Pt) : T.RobbaExt ρ0 :=
  (l.map fun P => T.normPtExt P.2 ρ0).prod

theorem normProd_nil : T.normProd ρ0 [] = 1 := rfl

theorem normProd_cons (P : T.Pt) (l : List T.Pt) :
    T.normProd ρ0 (P :: l) = T.normPtExt P.2 ρ0 * T.normProd ρ0 l := by
  simp [normProd]

theorem normProd_append (l l' : List T.Pt) :
    T.normProd ρ0 (l ++ l') = T.normProd ρ0 l * T.normProd ρ0 l' := by
  simp [normProd]

theorem ptProd_append (l l' : List T.Pt) :
    T.ptProd ρ0 (l ++ l') = T.ptProd ρ0 l * T.ptProd ρ0 l' := by
  simp [ptProd]

theorem one_le_norm_normPtExt (P : T.Pt) (ρ : Set.Ioc (0 : ℝ) ρ0) :
    1 ≤ T.extNorm ρ0 ρ (T.normPtExt P.2 ρ0) := by
  rw [T.extNorm_normPtExt P.2]; exact le_max_left _ _

theorem one_le_norm_normProd (l : List T.Pt) (ρ : Set.Ioc (0 : ℝ) ρ0) :
    1 ≤ T.extNorm ρ0 ρ (T.normProd ρ0 l) := by
  induction l with
  | nil => rw [normProd_nil, extNorm_one]
  | cons P l ih =>
    rw [normProd_cons, extNorm_mul]
    exact one_le_mul_of_one_le_of_one_le (T.one_le_norm_normPtExt P ρ) ih

theorem norm_normProd_of_le {l : List T.Pt} {s : ℝ} (hs : 0 ≤ s) (hl : ∀ P ∈ l, T.ptRad P.1 ≤ s)
    (ρ : Set.Ioc (0 : ℝ) ρ0) (hsρ : s ≤ ρ) :
    T.extNorm ρ0 ρ (T.normProd ρ0 l) = 1 ∧ T.extNorm ρ0 ρ (T.normProd ρ0 l - 1) ≤ s / ρ := by
  have hρ := rad_pos ρ0 ρ
  induction l with
  | nil =>
    rw [normProd_nil, extNorm_one, sub_self, extNorm_zero]
    exact ⟨rfl, div_nonneg hs hρ.le⟩
  | cons P l ih =>
    obtain ⟨h1, h2⟩ := ih fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ)
    have hP := hl P List.mem_cons_self
    have hPr : T.ptRad P.1 / ρ ≤ 1 := by rw [div_le_one hρ]; linarith
    have hfP : T.extNorm ρ0 ρ (T.normPtExt P.2 ρ0) = 1 := by
      rw [T.extNorm_normPtExt P.2, max_eq_left hPr]
    refine ⟨by rw [normProd_cons, extNorm_mul, hfP, h1, one_mul], ?_⟩
    rw [normProd_cons, show T.normPtExt P.2 ρ0 * T.normProd ρ0 l - 1 =
      (T.normPtExt P.2 ρ0 - 1) * T.normProd ρ0 l + (T.normProd ρ0 l - 1) by ring]
    refine (T.extNorm_add_le ρ _ _).trans (max_le ?_ h2)
    rw [extNorm_mul, h1, mul_one, T.extNorm_normPtExt_sub_one P.2]
    exact div_le_div_of_nonneg_right hP hρ.le

def unitProd (ρ0 : Set.Ioo (0 : ℝ) 1) (l : List T.Pt) : T.RobbaExt ρ0 :=
  (l.map fun P => T.normUnit P.2 ρ0).prod

def unitProdInv (ρ0 : Set.Ioo (0 : ℝ) 1) (l : List T.Pt) : T.RobbaExt ρ0 :=
  (l.map fun P => T.normUnitInv (ξ := P.1) ρ0).prod

theorem unitProd_mul_inv (l : List T.Pt) : T.unitProd ρ0 l * T.unitProdInv ρ0 l = 1 := by
  induction l with
  | nil => simp [unitProd, unitProdInv]
  | cons P l ih =>
    simp only [unitProd, unitProdInv, List.map_cons, List.prod_cons] at ih ⊢
    rw [show T.normUnit P.2 ρ0 * (l.map fun P => T.normUnit P.2 ρ0).prod *
      (T.normUnitInv (ξ := P.1) ρ0 * (l.map fun P => T.normUnitInv (ξ := P.1) ρ0).prod) =
      (T.normUnit P.2 ρ0 * T.normUnitInv (ξ := P.1) ρ0) *
      ((l.map fun P => T.normUnit P.2 ρ0).prod * (l.map fun P => T.normUnitInv (ξ := P.1) ρ0).prod)
      by ring, T.normUnit_mul_inv, ih, one_mul]

theorem normProd_eq (l : List T.Pt) : T.normProd ρ0 l = T.ptProd ρ0 l * T.unitProd ρ0 l := by
  induction l with
  | nil => simp [normProd, ptProd, unitProd]
  | cons P l ih =>
    rw [normProd_cons, ih, T.normPtExt_eq P.2, ptProd_cons]
    simp only [unitProd, List.map_cons, List.prod_cons]
    ring

theorem ptProd_eq (l : List T.Pt) : T.ptProd ρ0 l = T.normProd ρ0 l * T.unitProdInv ρ0 l := by
  rw [normProd_eq, mul_assoc, unitProd_mul_inv, mul_one]

theorem normProd_dvd_iff (l : List T.Pt) (x : T.RobbaExt ρ0) :
    T.normProd ρ0 l ∣ x ↔ T.ptProd ρ0 l ∣ x := by
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨T.unitProd ρ0 l * y, by rw [normProd_eq, mul_assoc]⟩
  · rintro ⟨y, rfl⟩; exact ⟨T.unitProdInv ρ0 l * y, by rw [ptProd_eq, mul_assoc]⟩

def InfProd.ofLists (ρ0 : Set.Ioo (0 : ℝ) 1) (ls : ℕ → List T.Pt) (s : ℕ → ℝ)
    (hs0 : ∀ n, 0 ≤ s n) (hs : Tendsto s atTop (𝓝 0)) (hl : ∀ n, ∀ P ∈ ls n, T.ptRad P.1 ≤ s n) :
    T.InfProd ρ0 where
  g n := T.normProd ρ0 (ls n)
  one_le_norm n ρ := T.one_le_norm_normProd _ ρ
  tendsto_sub_one ρ := by
    have hρ := rad_pos ρ0 ρ
    have hlim : Tendsto (fun n => s n / ρ) atTop (𝓝 0) := by
      simpa using hs.div_const (ρ : ℝ)
    refine squeeze_zero' (Eventually.of_forall fun n => T.extNorm_nonneg _ _) ?_ hlim
    filter_upwards [hs.eventually (ge_mem_nhds hρ)] with n hn
    exact (T.norm_normProd_of_le (hs0 n) (hl n) ρ hn).2

theorem InfProd.ofLists_part (ls : ℕ → List T.Pt) (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n)
    (hs : Tendsto s atTop (𝓝 0)) (hl : ∀ n, ∀ P ∈ ls n, T.ptRad P.1 ≤ s n) (n : ℕ) :
    (InfProd.ofLists T ρ0 ls s hs0 hs hl).part n =
      T.normProd ρ0 ((List.range n).flatMap ls) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [InfProd.part_succ, ih, List.range_succ, List.flatMap_append, normProd_append]
    simp [InfProd.ofLists]

end TeichLift

end GroundTheory.PAdicHodge
