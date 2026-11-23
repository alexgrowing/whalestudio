import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftBirationalAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedNonzeroSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace LiftBirationalAmple

set_option linter.unusedSectionVars false

section Sections

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  (y : (Σ k, ι k) → Ω)

theorem mem_chartLat_one {a : K → ℤ} {s : Ω} :
    s ∈ chartLat y a 1 ↔
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → s * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartRingZ y c := by
  show (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ chartRingZ y c) ↔ _
  simp only [Nat.cast_one, one_mul]

variable {y}

theorem chartLat_mul {a b : K → ℤ} {s u : Ω} (hs : s ∈ chartLat y a 1) (hu : u ∈ chartLat y b 1) :
    s * u ∈ chartLat y (a + b) 1 := by
  rw [mem_chartLat_one] at hs hu ⊢
  intro c hc
  have e : s * u * ∏ k, y ⟨k, c k⟩ ^ (-(a + b) k) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-a k)) * (u * ∏ k, y ⟨k, c k⟩ ^ (-b k)) := by
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact mul_mem (hs c hc) (hu c hc)

theorem chartLat_one_mem : (1 : Ω) ∈ chartLat y 0 1 := by
  rw [mem_chartLat_one]
  intro c _
  simp

theorem chartLat_pow {a : K → ℤ} {s : Ω} (hs : s ∈ chartLat y a 1) (n : ℕ) : s ^ n ∈ chartLat y (n • a) 1 := by
  induction n with
  | zero => simpa using (chartLat_one_mem (y := y))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact chartLat_mul ih hs

theorem chartLat_prod {β : Type} (t : Finset β) (f : β → Ω) (a : β → K → ℤ)
    (h : ∀ b ∈ t, f b ∈ chartLat y (a b) 1) : ∏ b ∈ t, f b ∈ chartLat y (∑ b ∈ t, a b) 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (chartLat_one_mem (y := y))
  | insert b t hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact chartLat_mul (h b (Finset.mem_insert_self b t)) (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

theorem chartLat_var [DecidableEq K] (p : Σ k, ι k) : y p ∈ chartLat y (Pi.single p.1 1) 1 := by
  rw [mem_chartLat_one]
  intro c hc
  have e : ∏ k, y ⟨k, c k⟩ ^ (-(Pi.single p.1 (1 : ℤ) : K → ℤ) k) = (y ⟨p.1, c p.1⟩)⁻¹ := by
    rw [Finset.prod_eq_single p.1 (fun k _ hk => by simp [hk]) (by simp)]
    simp
  rw [e, ← div_eq_mul_inv]
  exact Algebra.subset_adjoin ⟨p, rfl⟩

open Classical in

theorem chartLat_form {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval y g ∈ chartLat y (fun k => (d k : ℤ)) 1 := by
  rw [g.as_sum, map_sum]
  refine AddSubgroup.sum_mem _ fun m hm => ?_
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), algebraMap_int_eq, eq_intCast,
    ← zsmul_eq_mul]
  refine AddSubgroup.zsmul_mem _ ?_ _
  have hdeg : (fun k => (d k : ℤ)) = ∑ p : Σ k, ι k, (m p) • (Pi.single p.1 1 : K → ℤ) := by
    funext k
    rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one]
      rw [← hg m hm k]
      push_cast
      rfl
    · intro k' _ hk'
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [Ne.symm hk']
    · simp
  rw [hdeg]
  exact chartLat_prod _ _ _ fun p _ => chartLat_pow (chartLat_var p) _

end Sections

section Ratios

variable {Ω : Type} [Field Ω] {J : Type} [Fintype J] (z : (Σ _ : Unit, J) → Ω)

def IsRatio (w : Ω) : Prop :=
  ∃ (d : Unit → ℕ) (g h : MRing (fun _ : Unit => J)), IsMultiHomog g d ∧ IsMultiHomog h d ∧
    aeval z h ≠ 0 ∧ aeval z g = w * aeval z h

theorem homog_X_unit (j : J) : IsMultiHomog (X ⟨(), j⟩ : MRing (fun _ : Unit => J)) (fun _ => 1) := by
  have h := GenOnFibres.homog_X (R := ℤ) (ι := fun _ : Unit => J) () j
  intro m hm k
  rw [h m hm k]
  cases k
  simp

variable {z}

theorem IsRatio.intCast (r : ℤ) : IsRatio z (r : Ω) :=
  ⟨0, C r, 1, GenOnFibres.homog_C r, GenOnFibres.homog_one, by simp, by simp⟩

theorem IsRatio.add {w w' : Ω} (hw : IsRatio z w) (hw' : IsRatio z w') : IsRatio z (w + w') := by
  obtain ⟨d, g, h, hg, hh, h0, e⟩ := hw
  obtain ⟨d', g', h', hg', hh', h0', e'⟩ := hw'
  refine ⟨d + d', g * h' + h * g', h * h', GenOnFibres.homog_add (GenOnFibres.homog_mul hg hh')
    (GenOnFibres.homog_mul hh hg'), GenOnFibres.homog_mul hh hh', by simp [h0, h0'], ?_⟩
  simp only [map_add, map_mul, e, e']
  ring

theorem IsRatio.mul {w w' : Ω} (hw : IsRatio z w) (hw' : IsRatio z w') : IsRatio z (w * w') := by
  obtain ⟨d, g, h, hg, hh, h0, e⟩ := hw
  obtain ⟨d', g', h', hg', hh', h0', e'⟩ := hw'
  refine ⟨d + d', g * g', h * h', GenOnFibres.homog_mul hg hg', GenOnFibres.homog_mul hh hh',
    by simp [h0, h0'], ?_⟩
  simp only [map_mul, e, e']
  ring

theorem IsRatio.inv {w : Ω} (hw : IsRatio z w) : IsRatio z w⁻¹ := by
  by_cases hw0 : w = 0
  · rw [hw0, inv_zero]
    simpa using IsRatio.intCast (z := z) 0
  obtain ⟨d, g, h, hg, hh, h0, e⟩ := hw
  refine ⟨d, h, g, hh, hg, by rw [e]; exact mul_ne_zero hw0 h0, ?_⟩
  rw [e, ← mul_assoc, inv_mul_cancel₀ hw0, one_mul]

end Ratios

end LiftBirationalAmple

open LiftBirationalAmple in

theorem LiftBirationalAmple.proof (h : GeneratedNonzeroSection.Statement) : LiftBirationalAmple.Statement := by
  classical
  intro K _ _ ι _ _ Ω _ _ y D N c hvar hbir hc hample
  obtain ⟨q', hq', hgen, -⟩ := hample
  obtain ⟨s, hs, hs0⟩ := h K ι Ω y _ hgen

  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hvar.2.1.2.2 k
    refine ⟨i, fun hy => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker]
    simp [mConeMap, aeval_X, hy]
  choose c0 hc0 using hrel
  refine ⟨q' * c, 1, Nat.mul_le_mul hq' hc, fun t ht => ?_⟩
  have hm : 1 ≤ t * q' := Nat.mul_le_mul ht hq'

  let E : (Σ k, ι k) → K → ℕ := fun p k => if k = p.1 then t * q' - 1 else t * q'
  let xx : (Σ k, ι k) → Ω := fun p => s ^ t * (y p * ∏ k, y ⟨k, c0 k⟩ ^ E p k)
  have hxx : ∀ p, xx p ∈ chartLat y ((t * (q' * c)) • N) 1 := by
    intro p
    have hy1 : ∀ k, y ⟨k, c0 k⟩ ^ E p k ∈ chartLat y (E p k • (Pi.single k (1 : ℤ) : K → ℤ)) 1 :=
      fun k => chartLat_pow (chartLat_var (y := y) ⟨k, c0 k⟩) _
    have hyp : y p ∈ chartLat y (Pi.single p.1 (1 : ℤ) : K → ℤ) 1 := chartLat_var (y := y) p
    have hpr := chartLat_prod Finset.univ (fun k => y ⟨k, c0 k⟩ ^ E p k)
      (fun k => E p k • (Pi.single k (1 : ℤ) : K → ℤ)) fun k _ => hy1 k
    have h1 := chartLat_mul (chartLat_pow hs t) (chartLat_mul hyp hpr)
    have hdeg : (t * (q' * c)) • N = t • (q' • (c • N - fun _ => (1 : ℤ))) +
        ((Pi.single p.1 (1 : ℤ) : K → ℤ) + ∑ k, E p k • (Pi.single k (1 : ℤ) : K → ℤ)) := by
      funext k
      have hs1 : (∑ b, E p b • (Pi.single b (1 : ℤ) : K → ℤ)) k = (E p k : ℤ) := by
        rw [Finset.sum_apply, Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb])
          (by simp)]
        simp
      by_cases hk : k = p.1
      · rw [hk] at hs1 ⊢
        rw [Pi.add_apply, Pi.add_apply, hs1]
        simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, E, if_true]
        simp only [nsmul_eq_mul]
        push_cast [Nat.cast_sub hm]
        ring
      · rw [Pi.add_apply, Pi.add_apply, hs1]
        simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_of_ne hk, E, if_neg hk]
        simp only [nsmul_eq_mul]
        push_cast
        ring
    rw [hdeg]
    exact h1
  have hxx0 : ∀ k, xx ⟨k, c0 k⟩ ≠ 0 := by
    intro k
    refine mul_ne_zero (pow_ne_zero _ hs0) (mul_ne_zero (hc0 k) ?_)
    exact Finset.prod_ne_zero_iff.mpr fun k' _ => pow_ne_zero _ (hc0 k')
  have hratio : ∀ p : Σ k, ι k, xx p = y p / y ⟨p.1, c0 p.1⟩ * xx ⟨p.1, c0 p.1⟩ := by
    intro p
    show s ^ t * (y p * ∏ k, y ⟨k, c0 k⟩ ^ E p k) =
      y p / y ⟨p.1, c0 p.1⟩ * (s ^ t * (y ⟨p.1, c0 p.1⟩ * ∏ k, y ⟨k, c0 k⟩ ^ E p k))
    rw [div_mul_eq_mul_div, eq_div_iff (hc0 p.1)]
    ring

  let e := Fintype.equivFin (Σ k, ι k)
  refine ⟨Fintype.card (Σ k, ι k), fun j => xx (e.symm j), fun j => hxx _, ?_⟩
  set z : (Σ _ : Unit, Fin (Fintype.card (Σ k, ι k))) → Ω := fun p => xx (e.symm p.2) with hz
  have hzX : ∀ p : Σ k, ι k, aeval z (X ⟨(), e p⟩ : MRing (fun _ : Unit => Fin (Fintype.card (Σ k, ι k)))) = xx p := by
    intro p
    simp [hz]

  have hgen' : ∀ p : Σ k, ι k, IsRatio z (y p / y ⟨p.1, c0 p.1⟩) := by
    intro p
    refine ⟨fun _ => 1, X ⟨(), e p⟩, X ⟨(), e ⟨p.1, c0 p.1⟩⟩, homog_X_unit _, homog_X_unit _, ?_, ?_⟩
    · rw [hzX]; exact hxx0 p.1
    · rw [hzX, hzX]; exact hratio p
  have hring : ∀ w ∈ chartRingZ y c0, IsRatio z w := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact hgen' p
    | algebraMap r => simpa using IsRatio.intCast (z := z) r
    | add x x' _ _ hx hx' => exact hx.add hx'
    | mul x x' _ _ hx hx' => exact hx.mul hx'

  intro w
  obtain ⟨d, g, hh, hg, hhh, hh0, hgh⟩ := hbir w
  have hA := (mem_chartLat_one y).mp (chartLat_form (y := y) hg) c0 hc0
  have hB := (mem_chartLat_one y).mp (chartLat_form (y := y) hhh) c0 hc0
  have hP : ∏ k, y ⟨k, c0 k⟩ ^ (-(d k : ℤ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc0 k)
  have hw : w = (aeval y g * ∏ k, y ⟨k, c0 k⟩ ^ (-(d k : ℤ))) *
      (aeval y hh * ∏ k, y ⟨k, c0 k⟩ ^ (-(d k : ℤ)))⁻¹ := by
    rw [hgh, mul_assoc w, mul_inv_cancel_right₀ (mul_ne_zero hh0 hP)]
  rw [hw]
  exact (hring _ hA).mul (hring _ hB).inv

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
