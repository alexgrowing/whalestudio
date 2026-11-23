import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace GlobalTheory.UnitTransl

variable {D : D7} {ρ : ℕ}

theorem t2AE (D : D7) : T2Space (AE D) := by
  obtain ⟨-, -, -, i4, -⟩ := lattice_Mx D 1 1
  exact @T2Space.of_injective_continuous (AE D) (Matrix (Fin 1) (Fin 1) (AE D)) _ _ i4
    (fun x : AE D => Matrix.of fun _ _ => x)
    (fun a b h => congrFun (congrFun h 0) 0) (continuous_pi fun _ => continuous_pi fun _ => continuous_id)

theorem tagMx (D : D7) (ρ : ℕ) : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
theorem lcMx (D : D7) (ρ : ℕ) : LocallyCompactSpace (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.1
theorem scMx (D : D7) (ρ : ℕ) : SecondCountableTopology (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.1
theorem t2Mx (D : D7) (ρ : ℕ) : T2Space (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.2.1
theorem borelMx (D : D7) (ρ : ℕ) : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
theorem borelUX (D : D7) (ρ : ℕ) : BorelSpace (UX D ρ) := ⟨rfl⟩

attribute [local instance] t2AE tagMx lcMx scMx t2Mx borelMx borelUX

def supMx (D : D7) (ρ : ℕ) : AddSubgroup (Mx D ρ ρ) where
  carrier := {s | ∀ i j, ¬ i < j → s i j = 0}
  add_mem' {x y} hx hy i j h := by
    change x i j + y i j = 0
    rw [hx i j h, hy i j h, add_zero]
  zero_mem' _ _ _ := rfl
  neg_mem' {x} hx i j h := by
    change -x i j = 0
    rw [hx i j h, neg_zero]

theorem isClosed_supMx : IsClosed (supMx D ρ : Set (Mx D ρ ρ)) := by
  have : (supMx D ρ : Set (Mx D ρ ρ)) = ⋂ i, ⋂ j, {s : Mx D ρ ρ | ¬ i < j → s i j = 0} := by
    ext s
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases h : i < j
  · simp only [h, not_true_eq_false, false_implies, Set.setOf_true, isClosed_univ]
  · simp only [h, not_false_eq_true, true_implies]
    exact isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const

theorem lcSup (D : D7) (ρ : ℕ) : LocallyCompactSpace (supMx D ρ) :=
  (isClosed_supMx (D := D) (ρ := ρ)).isClosedEmbedding_subtypeVal.locallyCompactSpace

attribute [local instance] lcSup

def triGrp (D : D7) (ρ : ℕ) : Subgroup (GL (Fin ρ) (AE D)) where
  carrier := {g | BlockTriangular (g : Matrix (Fin ρ) (Fin ρ) (AE D)) id}
  one_mem' := blockTriangular_one
  mul_mem' {a b} ha hb := by
    change BlockTriangular ((a : Matrix (Fin ρ) (Fin ρ) (AE D)) * (b : Matrix (Fin ρ) (Fin ρ) (AE D))) id
    exact ha.mul hb
  inv_mem' {x} hx := by
    letI : Invertible (x : Matrix (Fin ρ) (Fin ρ) (AE D)) := x.invertible
    change BlockTriangular ((x⁻¹ : GL (Fin ρ) (AE D)) : Matrix (Fin ρ) (Fin ρ) (AE D)) id
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hx

theorem mul_mem_supMx {g : Matrix (Fin ρ) (Fin ρ) (AE D)} (hg : BlockTriangular g id) {s : Mx D ρ ρ}
    (hs : s ∈ supMx D ρ) : g * s ∈ supMx D ρ := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l < i
  · rw [hg hl, zero_mul]
  · rw [hs l j (fun h => hij (lt_of_le_of_lt (not_lt.1 hl) h)), mul_zero]

instance actSup : DistribMulAction (triGrp D ρ) (supMx D ρ) where
  smul g s := ⟨(g : GL (Fin ρ) (AE D)).1 * s.1, mul_mem_supMx g.2 s.2⟩
  one_smul s := Subtype.ext (Matrix.one_mul s.1)
  mul_smul a b s := Subtype.ext (Matrix.mul_assoc _ _ _)
  smul_zero g := Subtype.ext (Matrix.mul_zero _)
  smul_add g s t := Subtype.ext (Matrix.mul_add _ _ _)

theorem ccs (D : D7) (ρ : ℕ) : ContinuousConstSMul (triGrp D ρ) (supMx D ρ) :=
  ⟨fun g => Continuous.subtype_mk (continuous_const.matrix_mul continuous_subtype_val) _⟩

attribute [local instance] ccs

abbrev modChar (D : D7) (ρ : ℕ) : triGrp D ρ →* ℝ≥0 := distribHaarChar (supMx D ρ)

theorem modChar_eq_one_of_sq {a d : triGrp D ρ} (h : d * a * d⁻¹ = a * a) : modChar D ρ a = 1 := by
  have h1 := congrArg (modChar D ρ) h
  rw [map_mul, map_mul, map_mul] at h1
  have h2 : modChar D ρ d * modChar D ρ d⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h3 : modChar D ρ a * modChar D ρ a = modChar D ρ a * 1 := by
    rw [← h1, ← h2]; ring
  exact mul_left_cancel₀ (distribHaarChar_pos (A := supMx D ρ)).ne' h3

theorem one_add_mul_one_sub {x : Mx D ρ ρ} (hx : x * x = 0) : (1 + x) * (1 - x) = 1 := by
  rw [add_mul, one_mul, mul_sub, mul_one, hx, sub_zero, sub_add_cancel]

theorem one_sub_mul_one_add {x : Mx D ρ ρ} (hx : x * x = 0) : (1 - x) * (1 + x) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, hx, add_zero, add_sub_cancel_right]

def colU (x : Mx D ρ ρ) (hx : x * x = 0) : GL (Fin ρ) (AE D) :=
  ⟨1 + x, 1 - x, one_add_mul_one_sub hx, one_sub_mul_one_add hx⟩

theorem upper_one_add {x : Mx D ρ ρ} (hx : x ∈ supMx D ρ) : BlockTriangular (1 + x) id := by
  intro i j h
  have h' : j < i := h
  rw [Matrix.add_apply, one_apply_ne (ne_of_lt h').symm, hx i j (not_lt.2 (le_of_lt h')), add_zero]

theorem sq_col {x : Mx D ρ ρ} (hx : x ∈ supMx D ρ) {j : Fin ρ} (hcol : ∀ i k, k ≠ j → x i k = 0) :
    x * x = 0 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = j
  · subst hl
    by_cases hk : k = l
    · subst hk; rw [hx k k (lt_irrefl k), mul_zero]
    · rw [hcol l k hk, mul_zero]
  · rw [hcol i l hl, zero_mul]

def twoInv (D : D7) : AE D := algebraMap D.host.F (AE D) 2⁻¹

theorem two_mul_twoInv : (2 : AE D) * twoInv D = 1 := by
  rw [twoInv, ← map_ofNat (algebraMap D.host.F (AE D)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

def diagU (D : D7) {ρ : ℕ} (j : Fin ρ) : GL (Fin ρ) (AE D) :=
  ⟨diagonal fun i => if i = j then 1 else 2, diagonal fun i => if i = j then 1 else twoInv D,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext i
      split_ifs
      · exact mul_one 1
      · exact two_mul_twoInv,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext i
      split_ifs
      · exact mul_one 1
      · rw [mul_comm]; exact two_mul_twoInv⟩

theorem modChar_col {x : Mx D ρ ρ} (hx : x ∈ supMx D ρ) {j : Fin ρ} (hcol : ∀ i k, k ≠ j → x i k = 0) :
    modChar D ρ ⟨colU x (sq_col hx hcol), upper_one_add hx⟩ = 1 := by
  have hsq := sq_col hx hcol
  let d : triGrp D ρ := ⟨diagU D j, blockTriangular_diagonal _⟩
  refine modChar_eq_one_of_sq (d := d) (Subtype.ext (Units.ext ?_))
  change diagonal (fun i => if i = j then (1 : AE D) else 2) * (1 + x) * diagonal (fun i => if i = j then 1 else twoInv D) =
    (1 + x) * (1 + x)
  have e : (1 + x) * (1 + x) = 1 + (x + x) := by
    rw [add_mul, one_mul, mul_add, mul_one, hsq, add_zero, add_assoc]
  rw [e]
  ext i k
  rw [mul_diagonal, diagonal_mul, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply]
  by_cases hik : i = k
  · subst hik
    rw [hx i i (lt_irrefl i), one_apply_eq]
    split_ifs
    · simp
    · simp [two_mul_twoInv]
  · rw [one_apply_ne hik, zero_add, zero_add]
    by_cases hk : k = j
    · subst hk
      rw [if_pos rfl, if_neg hik, mul_one, two_mul]
    · rw [hcol i k hk]
      simp

def trunc (u : Mx D ρ ρ) (k : ℕ) : Mx D ρ ρ :=
  Matrix.of fun i j => if j.1 < k then u i j else (1 : Mx D ρ ρ) i j

def colPart (u : Mx D ρ ρ) (k : ℕ) : Mx D ρ ρ :=
  Matrix.of fun i j => if j.1 = k ∧ i < j then u i j else 0

theorem trunc_zero (u : Mx D ρ ρ) : trunc u 0 = 1 := by
  ext i j; simp [trunc]

theorem trunc_top (u : Mx D ρ ρ) : trunc u ρ = u := by
  ext i j; simp [trunc, j.2]

theorem colPart_mem (u : Mx D ρ ρ) (k : ℕ) : colPart u k ∈ supMx D ρ := by
  intro i j h
  change (if j.1 = k ∧ i < j then u i j else 0) = 0
  rw [if_neg (fun h' => h h'.2)]

theorem colPart_col (u : Mx D ρ ρ) {k : ℕ} (hk : k < ρ) : ∀ i l, l ≠ ⟨k, hk⟩ → colPart u k i l = 0 := by
  intro i l hl
  change (if l.1 = k ∧ i < l then u i l else 0) = 0
  rw [if_neg (fun h => hl (Fin.ext h.1))]

theorem trunc_succ {u : Mx D ρ ρ} (hu : u ∈ GlobalTheory.UnitU.uniSet D ρ) (k : ℕ) :
    trunc u (k + 1) = trunc u k + colPart u k := by
  ext i j
  simp only [trunc, colPart, of_apply, Matrix.add_apply]
  rcases lt_trichotomy j.1 k with h | h | h
  · simp [h, Nat.lt_succ_of_lt h, h.ne]
  · have h1 : j.1 < k + 1 := by omega
    have h2 : ¬ j.1 < k := by omega
    simp only [h1, if_true, h2, if_false, h, true_and]
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [hij, one_apply_ne hij.ne]
    · simp [(hu i i).2]
    · simp [(hu i j).1 hij, one_apply_ne hij.ne', not_lt.2 hij.le]
  · have h1 : ¬ j.1 < k + 1 := by omega
    have h2 : ¬ j.1 < k := by omega
    simp [h1, h2, h.ne']

theorem colPart_mul_trunc {u : Mx D ρ ρ} (hu : u ∈ GlobalTheory.UnitU.uniSet D ρ) {k : ℕ} (hk : k < ρ) :
    colPart u k * trunc u k = colPart u k := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨k, hk⟩ : Fin ρ)]
  · simp only [colPart, trunc, of_apply]
    by_cases hj : j.1 < k
    · have h0 : u ⟨k, hk⟩ j = 0 := (hu _ _).1 (Fin.lt_def.2 hj)
      simp [hj, h0, hj.ne]
    · by_cases hjk : j = ⟨k, hk⟩
      · subst hjk; simp
      · have : j.1 ≠ k := fun h => hjk (Fin.ext h)
        simp [hj, one_apply_ne (Ne.symm hjk), this]
  · intro l _ hl
    rw [colPart_col u hk i l hl, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem modChar_of_trunc {u : Mx D ρ ρ} (hu : u ∈ GlobalTheory.UnitU.uniSet D ρ) :
    ∀ k ≤ ρ, ∀ g : triGrp D ρ, (g : GL (Fin ρ) (AE D)).1 = trunc u k → modChar D ρ g = 1 := by
  intro k
  induction k with
  | zero =>
    intro _ g hg
    rw [trunc_zero] at hg
    have : g = 1 := Subtype.ext (Units.ext hg)
    rw [this, map_one]
  | succ k ih =>
    intro hk g hg
    have hk' : k < ρ := hk
    have hc := colPart_mem u k
    have hsq : colPart u k * colPart u k = 0 := sq_col hc (colPart_col u hk')
    let a : triGrp D ρ := ⟨colU (colPart u k) hsq, upper_one_add hc⟩
    have ha : modChar D ρ a = 1 := modChar_col hc (colPart_col u hk')
    have h2 : ((a⁻¹ * g : triGrp D ρ) : GL (Fin ρ) (AE D)).1 = trunc u k := by
      change (1 - colPart u k) * (g : GL (Fin ρ) (AE D)).1 = trunc u k
      rw [hg, trunc_succ hu]
      have e : trunc u k + colPart u k = (1 + colPart u k) * trunc u k := by
        rw [add_mul, one_mul, colPart_mul_trunc hu hk']
      rw [e, ← Matrix.mul_assoc, one_sub_mul_one_add hsq, Matrix.one_mul]
    have h3 := ih (Nat.le_of_succ_le hk) _ h2
    calc modChar D ρ g = modChar D ρ (a * (a⁻¹ * g)) := by rw [mul_inv_cancel_left]
      _ = 1 := by rw [map_mul, ha, h3, one_mul]

def ofUX (u : UX D ρ) : triGrp D ρ := ⟨u.1, fun i j h => (u.2 i j).1 h⟩

theorem modChar_ofUX (u : UX D ρ) : modChar D ρ (ofUX u) = 1 :=
  modChar_of_trunc u.2 ρ le_rfl _ (trunc_top _).symm

theorem map_smul_addHaar (u : UX D ρ) :
    (Measure.addHaar : Measure (supMx D ρ)).map (fun s => ofUX u • s) = Measure.addHaar := by
  ext S hS
  rw [Measure.map_apply (continuous_const_smul _).measurable hS, Set.preimage_smul,
    ← distribHaarChar_mul, map_inv, modChar_ofUX, inv_one, ENNReal.coe_one, one_mul]

theorem sub_one_mem (u : UX D ρ) : (u : GL (Fin ρ) (AE D)).1 - 1 ∈ supMx D ρ := by
  intro i j h
  change (u : GL (Fin ρ) (AE D)).1 i j - (1 : Mx D ρ ρ) i j = 0
  rcases lt_or_eq_of_le (not_lt.1 h) with h' | rfl
  · rw [(u.2 i j).1 h', one_apply_ne h'.ne', sub_zero]
  · rw [(u.2 j j).2, one_apply_eq, sub_self]

theorem one_add_mem {s : Mx D ρ ρ} (hs : s ∈ supMx D ρ) : 1 + s ∈ GlobalTheory.UnitU.uniSet D ρ := fun i j =>
  ⟨fun h => by
    change (1 : Mx D ρ ρ) i j + s i j = 0
    rw [one_apply_ne h.ne', hs i j (not_lt.2 h.le), add_zero],
   by
    change (1 : Mx D ρ ρ) i i + s i i = 1
    rw [hs i i (lt_irrefl i), one_apply_eq, add_zero]⟩

def coordU (D : D7) (ρ : ℕ) : UX D ρ ≃ₜ supMx D ρ where
  toFun u := ⟨(u : GL (Fin ρ) (AE D)).1 - 1, sub_one_mem u⟩
  invFun s := ⟨GlobalTheory.UnitU.toUnit (1 + s.1) (one_add_mem s.2), one_add_mem s.2⟩
  left_inv u := Subtype.ext (Units.ext (by
    change 1 + ((u : GL (Fin ρ) (AE D)).1 - 1) = (u : GL (Fin ρ) (AE D)).1
    abel))
  right_inv s := Subtype.ext (by
    change 1 + s.1 - 1 = s.1
    abel)
  continuous_toFun :=
    Continuous.subtype_mk ((GlobalTheory.UnitU.isClosedEmbedding_val D ρ).continuous.sub continuous_const) _
  continuous_invFun :=
    (GlobalTheory.UnitU.isClosedEmbedding_val D ρ).isInducing.continuous_iff.2
      (continuous_const.add continuous_subtype_val)

theorem coordU_mul (g u : UX D ρ) : coordU D ρ (g * u) = ofUX g • coordU D ρ u + coordU D ρ g := by
  apply Subtype.ext
  change (g : GL (Fin ρ) (AE D)).1 * (u : GL (Fin ρ) (AE D)).1 - 1 =
    (g : GL (Fin ρ) (AE D)).1 * ((u : GL (Fin ρ) (AE D)).1 - 1) + ((g : GL (Fin ρ) (AE D)).1 - 1)
  rw [Matrix.mul_sub, Matrix.mul_one]
  abel

theorem haar_val_add_invariant : ∀ (D : D7) (ρ : ℕ) (ν : Measure (UX D ρ)), ν.IsHaarMeasure →
    Measurable (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) ∧
    IsFiniteMeasureOnCompacts (Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) ν) ∧
    ∀ t : Mx D ρ ρ, (∀ i j, ¬ i < j → t i j = 0) →
      Measure.map (fun x => x + t) (Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) ν) =
        Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) ν := by
  intro D ρ ν hν
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.UnitU.topology D ρ
  have hemb := GlobalTheory.UnitU.isClosedEmbedding_val D ρ
  have hΦ : Measurable (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) := hemb.continuous.measurable
  refine ⟨hΦ, ⟨fun K hK => ?_⟩, fun t ht => ?_⟩
  · rw [Measure.map_apply hΦ hK.isClosed.measurableSet]
    exact (hemb.isCompact_preimage hK).measure_lt_top
  · let lam : Measure (supMx D ρ) := Measure.addHaar
    let Ψ := coordU D ρ
    let ν' : Measure (UX D ρ) := lam.map Ψ.symm
    have hΨs : Measurable Ψ.symm := Ψ.symm.continuous.measurable
    haveI : IsFiniteMeasureOnCompacts ν' := Measure.IsFiniteMeasureOnCompacts.map _ _
    haveI : ν'.IsOpenPosMeasure := Ψ.symm.continuous.isOpenPosMeasure_map Ψ.symm.surjective
    haveI : ν'.IsMulLeftInvariant := by
      refine ⟨fun g => ?_⟩
      have hsm : Measurable (fun s : supMx D ρ => ofUX g • s) := (continuous_const_smul _).measurable
      have e : (g * ·) ∘ Ψ.symm = Ψ.symm ∘ ((Ψ g + ·) ∘ (fun s : supMx D ρ => ofUX g • s)) := by
        funext s
        apply Ψ.injective
        simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
        change coordU D ρ (g * Ψ.symm s) = _
        rw [coordU_mul]
        change ofUX g • Ψ (Ψ.symm s) + Ψ g = _
        rw [Homeomorph.apply_symm_apply, add_comm]
      change Measure.map (g * ·) (Measure.map Ψ.symm lam) = Measure.map Ψ.symm lam
      rw [Measure.map_map (measurable_const_mul g) hΨs, e,
        ← Measure.map_map hΨs ((measurable_const_add _).comp hsm),
        ← Measure.map_map (measurable_const_add _) hsm, map_smul_addHaar, map_add_left_eq_self]
    haveI : ν'.IsHaarMeasure := {}
    have e1 := Measure.isMulLeftInvariant_eq_smul ν ν'
    have hf : Measurable (fun s : supMx D ρ => 1 + s.1) :=
      (continuous_const.add continuous_subtype_val).measurable
    have e2 : (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) ∘ Ψ.symm = fun s => 1 + s.1 := rfl
    rw [e1, Measure.map_smul, Measure.map_smul]
    congr 1
    change Measure.map (· + t) (Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) (Measure.map Ψ.symm lam)) =
      Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) (Measure.map Ψ.symm lam)
    rw [Measure.map_map hΦ hΨs, e2, Measure.map_map (measurable_add_const t) hf]
    have e3 : (· + t) ∘ (fun s : supMx D ρ => 1 + s.1) =
        (fun s : supMx D ρ => 1 + s.1) ∘ ((⟨t, ht⟩ : supMx D ρ) + ·) := by
      funext s
      simp only [Function.comp_apply, AddSubgroup.coe_add]
      abel
    rw [e3, ← Measure.map_map hf (measurable_const_add _), map_add_left_eq_self]

end GlobalTheory.UnitTransl
