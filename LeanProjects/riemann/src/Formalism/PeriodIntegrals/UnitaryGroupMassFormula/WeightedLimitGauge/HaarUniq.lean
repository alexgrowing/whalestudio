import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W.HU

open PI.RhsWLim

variable {k r : ℕ}

def tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_row (i m : Fin (2 * r + k + 1)) :
    Hpk k r i m = if m = tau k r i then sgn k r i else 0 := by
  unfold Hpk tau sgn
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mul_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * A) i j = sgn k r i * A (tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm
    rw [hpk_row, if_neg hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tau_tau (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  unfold tau
  apply Fin.ext
  simp only
  split_ifs <;> omega

theorem sgn_tau (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  unfold sgn tau
  simp only
  split_ifs <;> first | rfl | (exfalso; omega)

theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm, sgn_mul_self]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

theorem isUnit_of_uh {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * gᴴ * Hpk k r)
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

theorem uh_one : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UH (Hpk k r) := by
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem uh_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) : g * h ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem uh_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hu := isUnit_of_uh hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem uwb_one : (1 : Mat k r) ∈ UWb k r :=
  ⟨uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩⟩

theorem uwb_mul {g h : Mat k r} (hg : g ∈ UWb k r) (hh : h ∈ UWb k r) : g * h ∈ UWb k r := by
  refine ⟨uh_mul hg.1 hh.1, fun c => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mulVec_mulVec, (hh.2 c).1, (hg.2 c).1]
  · rw [← Matrix.mulVec_mulVec, (hh.2 c).2, (hg.2 c).2]

theorem uwb_unit {g : Mat k r} (hg : g ∈ UWb k r) : IsUnit g.det := isUnit_of_uh hg.1

theorem uwb_inv {g : Mat k r} (hg : g ∈ UWb k r) : g⁻¹ ∈ UWb k r := by
  have hu := uwb_unit hg
  have fix : ∀ v, g *ᵥ v = v → g⁻¹ *ᵥ v = v := by
    intro v hv
    calc g⁻¹ *ᵥ v = g⁻¹ *ᵥ (g *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨uh_inv hg.1, fun c => ⟨fix _ (hg.2 c).1, fix _ (hg.2 c).2⟩⟩

def amb (k r : ℕ) : Set (Mt k r) := {x | Matrix.of x ∈ UWb k r}

theorem amb_closed : IsClosed (amb k r) := by
  show IsClosed {x : Mt k r | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r ∧
    ∀ a : Fin r, (Matrix.of x *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      Matrix.of x *ᵥ bvec (esI k r a) = bvec (esI k r a))}
  have hid : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  rw [Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter (isClosed_eq ((hid.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hid)
    continuous_const) (isClosed_iInter fun a => ?_)
  rw [Set.ofPred_and]
  exact (isClosed_eq (hid.matrix_mulVec continuous_const) continuous_const).inter
    (isClosed_eq (hid.matrix_mulVec continuous_const) continuous_const)

def invM (x : Mt k r) : Mt k r := ((Matrix.of x : Mat k r)⁻¹ : Mat k r)

def adjF (x : Mt k r) : Mt k r := (Matrix.of x : Mat k r).adjugate
def detF (x : Mt k r) : ℂ := (Matrix.of x : Mat k r).det

theorem detF_cont : Continuous (detF (k := k) (r := r)) := Continuous.matrix_det (continuous_id (X := Mat k r))
theorem adjF_cont : Continuous (adjF (k := k) (r := r)) := Continuous.matrix_adjugate (continuous_id (X := Mat k r))

theorem invM_smul : (invM : Mt k r → Mt k r) = fun x => (detF x)⁻¹ • adjF x := by
  funext x
  unfold invM detF adjF
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rfl

theorem invM_contOn : ContinuousOn (invM : Mt k r → Mt k r) {x | detF x ≠ 0} := by
  rw [invM_smul]
  exact (detF_cont.continuousOn.inv₀ (fun x hx => hx)).smul adjF_cont.continuousOn

theorem lmulM_cont (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  unfold lmulM
  exact (continuous_const (y := a)).matrix_mul (continuous_id (X := Mat k r))

def Gp (k r : ℕ) : Type := {x : Mt k r // x ∈ amb k r}

instance : TopologicalSpace (Gp k r) := inferInstanceAs (TopologicalSpace {x : Mt k r // x ∈ amb k r})
instance : MeasurableSpace (Gp k r) := inferInstanceAs (MeasurableSpace {x : Mt k r // x ∈ amb k r})
instance : BorelSpace (Gp k r) := inferInstanceAs (BorelSpace {x : Mt k r // x ∈ amb k r})
instance : SecondCountableTopology (Gp k r) :=
  inferInstanceAs (SecondCountableTopology {x : Mt k r // x ∈ amb k r})

def inc (x : Gp k r) : Mt k r := x.1

theorem inc_cont : Continuous (inc : Gp k r → Mt k r) := continuous_subtype_val

theorem inc_mem (x : Gp k r) : Matrix.of (inc x) ∈ UWb k r := x.2

theorem inc_memb : MeasurableEmbedding (inc : Gp k r → Mt k r) :=
  MeasurableEmbedding.subtype_coe amb_closed.measurableSet

theorem range_inc : Set.range (inc : Gp k r → Mt k r) = amb k r := Subtype.range_coe

theorem lmulM_mem {x y : Mt k r} (hx : x ∈ amb k r) (hy : y ∈ amb k r) :
    lmulM (Matrix.of x) y ∈ amb k r := by
  show (Matrix.of x : Mat k r) * Matrix.of y ∈ UWb k r
  exact uwb_mul hx hy

theorem invM_mem {x : Mt k r} (hx : x ∈ amb k r) : invM x ∈ amb k r := by
  show (Matrix.of x : Mat k r)⁻¹ ∈ UWb k r
  exact uwb_inv hx

theorem one_mem_amb : (fun i j => (1 : Mat k r) i j : Mt k r) ∈ amb k r := by
  show (1 : Mat k r) ∈ UWb k r
  exact uwb_one

instance : Group (Gp k r) where
  mul a b := ⟨lmulM (Matrix.of a.1) b.1, lmulM_mem a.2 b.2⟩
  one := ⟨fun i j => (1 : Mat k r) i j, one_mem_amb⟩
  inv a := ⟨invM a.1, invM_mem a.2⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc (Matrix.of a.1 : Mat k r) (Matrix.of b.1) (Matrix.of c.1))
  one_mul a := Subtype.ext (Matrix.one_mul (Matrix.of a.1 : Mat k r))
  mul_one a := Subtype.ext (Matrix.mul_one (Matrix.of a.1 : Mat k r))
  inv_mul_cancel a := Subtype.ext (Matrix.nonsing_inv_mul (Matrix.of a.1 : Mat k r) (uwb_unit a.2))

theorem inc_mul (a b : Gp k r) : inc (a * b) = lmulM (Matrix.of (inc a)) (inc b) := rfl

instance : IsTopologicalGroup (Gp k r) where
  continuous_mul := by
    refine Continuous.subtype_mk ?_ _
    exact Continuous.matrix_mul (A := fun p : Gp k r × Gp k r => (Matrix.of (inc p.1) : Mat k r))
      (B := fun p : Gp k r × Gp k r => (Matrix.of (inc p.2) : Mat k r))
      (inc_cont.comp continuous_fst) (inc_cont.comp continuous_snd)
  continuous_inv := by
    refine Continuous.subtype_mk ?_ _
    exact invM_contOn.comp_continuous inc_cont (fun x => (uwb_unit (inc_mem x)).ne_zero)

def pull (μ : Measure (Mt k r)) : Measure (Gp k r) := μ.comap inc

theorem map_pull (μ : Measure (Mt k r)) (h : μ {x | Matrix.of x ∉ UWb k r} = 0) : (pull μ).map inc = μ := by
  rw [pull, inc_memb.map_comap, range_inc]
  exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h)

theorem pull_apply (μ : Measure (Mt k r)) (h : μ {x | Matrix.of x ∉ UWb k r} = 0) (s : Set (Mt k r)) :
    pull μ (inc ⁻¹' s) = μ s := by
  rw [pull, inc_memb.comap_apply, Set.image_preimage_eq_inter_range, range_inc]
  exact measure_inter_conull h

theorem pull_sigmaFinite (μ : Measure (Mt k r)) [SigmaFinite μ] : SigmaFinite (pull μ) := by
  refine (Measure.FiniteSpanningSetsIn.sigmaFinite (C := Set.univ)
    ⟨fun n => (inc : Gp k r → Mt k r) ⁻¹' spanningSets μ n, fun _ => trivial, fun n => ?_, ?_⟩)
  · rw [pull, inc_memb.comap_apply]
    exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top μ n)
  · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]

theorem pull_left (μ : Measure (Mt k r)) (h : ∀ a ∈ UWb k r, μ.map (lmulM a) = μ) :
    (pull μ).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext s hs
  rw [Measure.map_apply (continuous_const_mul g).measurable hs, pull, inc_memb.comap_apply, inc_memb.comap_apply]
  have e1 : (μ.map (lmulM (Matrix.of (inc g)))) (inc '' s) = μ (inc '' s) :=
    congrArg (fun m : Measure (Mt k r) => m (inc '' s)) (h (Matrix.of (inc g)) (inc_mem g))
  have e2 := Measure.map_apply (μ := μ) (lmulM_cont (Matrix.of (inc g))).measurable (inc_memb.measurableSet_image.2 hs)
  rw [← e1, e2]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g * y, hy, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨g⁻¹ * z, ?_, ?_⟩
    · show g * (g⁻¹ * z) ∈ s
      rw [mul_inv_cancel_left]; exact hz
    · rw [inc_mul, hzx]
      exact Matrix.nonsing_inv_mul_cancel_left (Matrix.of (inc g) : Mat k r) (Matrix.of x : Mat k r)
        (uwb_unit (inc_mem g))

end PI.RhsWLim.W.HU

namespace PI.RhsWLim.W

open PI.RhsWLim HU

theorem haarUniq : HaarUniq := by
  intro k r ν₁ ν₂ hk h1 h2 hB
  obtain ⟨ε, hε, hB⟩ := hB
  obtain ⟨hσ1, h01, hc1, hl1⟩ := h1
  obtain ⟨hσ2, h02, hc2, hl2⟩ := h2
  have i1 : SigmaFinite (pull ν₁) := pull_sigmaFinite ν₁
  have i2 : SigmaFinite (pull ν₂) := pull_sigmaFinite ν₂
  have i3 : (pull ν₁).IsMulLeftInvariant := pull_left ν₁ hl1
  have i4 : (pull ν₂).IsMulLeftInvariant := pull_left ν₂ hl2
  obtain ⟨hb1, hb2, hb3⟩ := hB (ε / 2) (half_pos hε) (half_lt_self hε)
  have key := measure_eq_div_smul (pull ν₁) (pull ν₂) (s := inc ⁻¹' bBall k r (ε / 2))
    (by rw [pull_apply ν₂ hc2]; exact hb2.ne') (by rw [pull_apply ν₂ hc2]; exact hb3.ne)
  refine ⟨pull ν₁ (inc ⁻¹' bBall k r (ε / 2)) / pull ν₂ (inc ⁻¹' bBall k r (ε / 2)), ?_, ?_⟩
  · rw [pull_apply ν₁ hc1, pull_apply ν₂ hc2]
    exact (ENNReal.div_lt_top hb1.ne hb2.ne').ne
  · calc ν₁ = (pull ν₁).map inc := (map_pull ν₁ hc1).symm
      _ = ((pull ν₁ (inc ⁻¹' bBall k r (ε / 2)) / pull ν₂ (inc ⁻¹' bBall k r (ε / 2))) • pull ν₂).map inc := by
          rw [← key]
      _ = _ := by rw [Measure.map_smul, map_pull ν₂ hc2]

end PI.RhsWLim.W
