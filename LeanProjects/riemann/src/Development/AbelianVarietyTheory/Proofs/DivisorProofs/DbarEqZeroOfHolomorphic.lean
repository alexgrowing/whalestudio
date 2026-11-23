import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv

set_option autoImplicit false
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm

namespace GlobalTheory.TorsionForm.FlatAcyc

theorem sgn_erase_of_lt {m : ℕ} {i j : Fin m} {S : Finset (Fin m)} (hi : i ∈ S) (hij : i < j) :
    sgn j (S.erase i) = -sgn j S := by
  unfold sgn
  have e : (S.erase i).filter (· < j) = (S.filter (· < j)).erase i := by
    ext x; simp [Finset.mem_filter, Finset.mem_erase]; tauto
  have hm : i ∈ S.filter (· < j) := Finset.mem_filter.2 ⟨hi, hij⟩
  have hc := Finset.card_erase_add_one hm
  rw [e, ← hc, pow_succ]; ring

theorem sgn_erase_of_not_lt {m : ℕ} {i j : Fin m} {S : Finset (Fin m)} (hij : ¬ i < j) :
    sgn j (S.erase i) = sgn j S := by
  unfold sgn
  have e : (S.erase i).filter (· < j) = S.filter (· < j) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨fun e => hij (e ▸ h'), h⟩, h'⟩
  rw [e]

theorem sgn_mul_erase {m : ℕ} {i j : Fin m} {S : Finset (Fin m)} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j) : sgn i S * sgn j (S.erase i) = -(sgn j S * sgn i (S.erase j)) := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [sgn_erase_of_lt hi h, sgn_erase_of_not_lt (not_lt.2 h.le)]; ring
  · rw [sgn_erase_of_lt hj h, sgn_erase_of_not_lt (not_lt.2 h.le)]; ring

theorem sgn_insert_eq {m : ℕ} {i j : Fin m} {S : Finset (Fin m)} (hi : i ∉ S) :
    sgn j (insert i S) = if i < j then -sgn j S else sgn j S := by
  have e : (insert i S).erase i = S := Finset.erase_insert hi
  split_ifs with h
  · have := sgn_erase_of_lt (Finset.mem_insert_self i S) h (j := j)
    rw [e] at this; rw [this]; ring
  · have := sgn_erase_of_not_lt (S := insert i S) h
    rw [e] at this; rw [this]

theorem wedge_wedge {m : ℕ} (i j : Fin m) (w : Ext m) :
    wedge i (wedge j w) = -wedge j (wedge i w) := by
  funext S
  by_cases hij : i = j
  · subst hij; simp [wedge]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · have hj' : j ∈ S.erase i := Finset.mem_erase.2 ⟨Ne.symm hij, hj⟩
    have hi' : i ∈ S.erase j := Finset.mem_erase.2 ⟨hij, hi⟩
    simp only [wedge, hi, hj, hj', hi', if_true, Pi.neg_apply]
    rw [Finset.erase_right_comm, ← mul_assoc, ← mul_assoc, sgn_mul_erase hi hj hij]; ring
  · have : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
    simp [wedge, hi, hj, this]
  · have : i ∉ S.erase j := fun h => hi (Finset.mem_of_mem_erase h)
    simp [wedge, hi, hj, this]
  · simp [wedge, hi, hj]

theorem contr_contr {m : ℕ} (i j : Fin m) (w : Ext m) :
    contr i (contr j w) = -contr j (contr i w) := by
  funext S
  by_cases hij : i = j
  · subst hij; simp [contr]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp [contr, hi, hj]
  · simp [contr, hi, hj]
  · simp [contr, hi, hj]
  · have hj' : j ∉ insert i S := by simp [Ne.symm hij, hj]
    have hi' : i ∉ insert j S := by simp [hij, hi]
    simp only [contr, hi, hj, hj', hi', if_false, Pi.neg_apply]
    rw [Finset.insert_comm j i S, sgn_insert_eq hi, sgn_insert_eq hj]
    rcases lt_or_gt_of_ne hij with h | h
    · simp [h, not_lt.2 h.le]; ring
    · simp [h, not_lt.2 h.le]; ring

theorem wedge_contr_of_ne {m : ℕ} {i j : Fin m} (hij : i ≠ j) (w : Ext m) :
    wedge i (contr j w) = -contr j (wedge i w) := by
  funext S
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · have : j ∈ S.erase i := Finset.mem_erase.2 ⟨Ne.symm hij, hj⟩
    simp [wedge, contr, hi, hj, this]
  · have hj' : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
    have hi' : i ∈ insert j S := Finset.mem_insert_of_mem hi
    simp only [wedge, contr, hi, hj, hj', hi', if_true, if_false, Pi.neg_apply]
    rw [Finset.erase_insert_of_ne (Ne.symm hij), sgn_insert_eq hj]
    rcases lt_or_gt_of_ne hij with h | h
    · rw [sgn_erase_of_lt hi h]; simp [not_lt.2 h.le]; ring
    · rw [sgn_erase_of_not_lt (not_lt.2 h.le)]; simp [h]; ring
  · simp [wedge, contr, hi, hj]
  · have : i ∉ insert j S := by simp [hij, hi]
    simp [wedge, contr, hi, hj, this]

theorem wedge_add {m : ℕ} (i : Fin m) (v w : Ext m) : wedge i (v + w) = wedge i v + wedge i w := by
  funext S; simp only [wedge, Pi.add_apply]; split_ifs <;> ring

theorem wedge_smul {m : ℕ} (i : Fin m) (c : ℂ) (w : Ext m) : wedge i (c • w) = c • wedge i w := by
  funext S; simp only [wedge, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

theorem contr_add {m : ℕ} (i : Fin m) (v w : Ext m) : contr i (v + w) = contr i v + contr i w := by
  funext S; simp only [contr, Pi.add_apply]; split_ifs <;> ring

theorem contr_smul {m : ℕ} (i : Fin m) (c : ℂ) (w : Ext m) : contr i (c • w) = c • contr i w := by
  funext S; simp only [contr, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

def wedgeR {m : ℕ} (i : Fin m) : Ext m →L[ℝ] Ext m :=
  LinearMap.toContinuousLinearMap
    { toFun := wedge i, map_add' := wedge_add i,
      map_smul' := fun r w => by
        have := wedge_smul i (r : ℂ) w
        simpa [Complex.coe_smul] using this }

def contrR {m : ℕ} (i : Fin m) : Ext m →L[ℝ] Ext m :=
  LinearMap.toContinuousLinearMap
    { toFun := contr i, map_add' := contr_add i,
      map_smul' := fun r w => by
        have := contr_smul i (r : ℂ) w
        simpa [Complex.coe_smul] using this }

@[simp] theorem wedgeR_apply {m : ℕ} (i : Fin m) (w : Ext m) : wedgeR i w = wedge i w := rfl
@[simp] theorem contrR_apply {m : ℕ} (i : Fin m) (w : Ext m) : contrR i w = contr i w := rfl

section Deriv
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [SMul ℂ V]

theorem dbar_add_vector {m : ℕ} {F G : V → Ext m} {P : V} (hF : DifferentiableAt ℝ F P)
    (hG : DifferentiableAt ℝ G P) (v : V) :
    d01 (fun Q => F Q + G Q) P v = d01 F P v + d01 G P v := by
  simp only [d01, fderiv_fun_add hF hG, ContinuousLinearMap.add_apply]
  module

theorem dz_add_vector {m : ℕ} {F G : V → Ext m} {P : V} (hF : DifferentiableAt ℝ F P)
    (hG : DifferentiableAt ℝ G P) (v : V) :
    d10 (fun Q => F Q + G Q) P v = d10 F P v + d10 G P v := by
  simp only [d10, fderiv_fun_add hF hG, ContinuousLinearMap.add_apply]
  module

theorem d01_sum {m : ℕ} {ι : Type} (s : Finset ι) {F : ι → V → Ext m} {P : V}
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) P) (v : V) :
    d01 (fun Q => ∑ i ∈ s, F i Q) P v = ∑ i ∈ s, d01 (F i) P v := by
  simp only [d01, fderiv_fun_sum hF, ContinuousLinearMap.sum_apply, Finset.smul_sum,
    ← Finset.sum_add_distrib]

theorem d10_finset_sum' {m : ℕ} {ι : Type} (s : Finset ι) {F : ι → V → Ext m} {P : V}
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) P) (v : V) :
    d10 (fun Q => ∑ i ∈ s, F i Q) P v = ∑ i ∈ s, d10 (F i) P v := by
  simp only [d10, fderiv_fun_sum hF, ContinuousLinearMap.sum_apply, Finset.smul_sum,
    ← Finset.sum_sub_distrib]

theorem dbar_clinear_map_comm {m m' : ℕ} (L : Ext m →L[ℝ] Ext m') (hL : ∀ (c : ℂ) w, L (c • w) = c • L w)
    {F : V → Ext m} {P : V} (hF : DifferentiableAt ℝ F P) (v : V) :
    d01 (fun Q => L (F Q)) P v = L (d01 F P v) := by
  have : fderiv ℝ (fun Q => L (F Q)) P = L.comp (fderiv ℝ F P) :=
    (L.hasFDerivAt.comp P hF.hasFDerivAt).fderiv
  simp only [d01, this, ContinuousLinearMap.comp_apply, hL, map_add]

theorem dz_clinear_map_comm {m m' : ℕ} (L : Ext m →L[ℝ] Ext m') (hL : ∀ (c : ℂ) w, L (c • w) = c • L w)
    {F : V → Ext m} {P : V} (hF : DifferentiableAt ℝ F P) (v : V) :
    d10 (fun Q => L (F Q)) P v = L (d10 F P v) := by
  have : fderiv ℝ (fun Q => L (F Q)) P = L.comp (fderiv ℝ F P) :=
    (L.hasFDerivAt.comp P hF.hasFDerivAt).fderiv
  simp only [d10, this, ContinuousLinearMap.comp_apply, hL, map_sub]

theorem dbar_wedge_comm {m : ℕ} (i : Fin m) {F : V → Ext m} {P : V} (hF : DifferentiableAt ℝ F P) (v : V) :
    d01 (fun Q => wedge i (F Q)) P v = wedge i (d01 F P v) :=
  dbar_clinear_map_comm (wedgeR i) (wedge_smul i) hF v

theorem dz_wedge_comm {m : ℕ} (i : Fin m) {F : V → Ext m} {P : V} (hF : DifferentiableAt ℝ F P) (v : V) :
    d10 (fun Q => wedge i (F Q)) P v = wedge i (d10 F P v) :=
  dz_clinear_map_comm (wedgeR i) (wedge_smul i) hF v

theorem dbar_contraction_comm {m : ℕ} (i : Fin m) {F : V → Ext m} {P : V} (hF : DifferentiableAt ℝ F P) (v : V) :
    d01 (fun Q => contr i (F Q)) P v = contr i (d01 F P v) :=
  dbar_clinear_map_comm (contrR i) (contr_smul i) hF v

theorem d01_smul {m : ℕ} {φ : V → ℂ} {F : V → Ext m} {P : V} (hφ : DifferentiableAt ℝ φ P)
    (hF : DifferentiableAt ℝ F P) (v : V) :
    d01 (fun Q => φ Q • F Q) P v = d01 φ P v • F P + φ P • d01 F P v := by
  simp only [d01, fderiv_fun_smul hφ hF, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  module

theorem d10_smul {m : ℕ} {φ : V → ℂ} {F : V → Ext m} {P : V} (hφ : DifferentiableAt ℝ φ P)
    (hF : DifferentiableAt ℝ F P) (v : V) :
    d10 (fun Q => φ Q • F Q) P v = d10 φ P v • F P + φ P • d10 F P v := by
  simp only [d10, fderiv_fun_smul hφ hF, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  module

theorem dbar_mul_leibniz {φ ψ : V → ℂ} {P : V} (hφ : DifferentiableAt ℝ φ P)
    (hψ : DifferentiableAt ℝ ψ P) (v : V) :
    d01 (fun Q => φ Q * ψ Q) P v = d01 φ P v * ψ P + φ P * d01 ψ P v := by
  simp only [d01, fderiv_fun_mul hφ hψ, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dz_mul_leibniz {φ ψ : V → ℂ} {P : V} (hφ : DifferentiableAt ℝ φ P)
    (hψ : DifferentiableAt ℝ ψ P) (v : V) :
    d10 (fun Q => φ Q * ψ Q) P v = d10 φ P v * ψ P + φ P * d10 ψ P v := by
  simp only [d10, fderiv_fun_mul hφ hψ, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dbar_apply_component {m : ℕ} {F : V → Ext m} {P : V} (hF : DifferentiableAt ℝ F P) (S : Finset (Fin m))
    (v : V) : d01 (fun Q => F Q S) P v = d01 F P v S := by
  have : fderiv ℝ (fun Q => F Q S) P = (ContinuousLinearMap.proj S).comp (fderiv ℝ F P) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Finset (Fin m) => ℂ) S).hasFDerivAt.comp P
      hF.hasFDerivAt).fderiv
  simp [d01, this]

theorem dz_apply_component {m : ℕ} {F : V → Ext m} {P : V} (hF : DifferentiableAt ℝ F P) (S : Finset (Fin m))
    (v : V) : d10 (fun Q => F Q S) P v = d10 F P v S := by
  have : fderiv ℝ (fun Q => F Q S) P = (ContinuousLinearMap.proj S).comp (fderiv ℝ F P) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Finset (Fin m) => ℂ) S).hasFDerivAt.comp P
      hF.hasFDerivAt).fderiv
  simp [d10, this]

theorem dz_conj_eq_conj_dbar {φ : V → ℂ} {P : V} (hφ : DifferentiableAt ℝ φ P) (v : V) :
    d10 (fun Q => (starRingEnd ℂ) (φ Q)) P v = (starRingEnd ℂ) (d01 φ P v) := by
  have : fderiv ℝ (fun Q => (starRingEnd ℂ) (φ Q)) P =
      (Complex.conjCLE.toContinuousLinearMap).comp (fderiv ℝ φ P) :=
    (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp P hφ.hasFDerivAt).fderiv
  simp only [d10, d01, this, ContinuousLinearMap.comp_apply, smul_eq_mul]
  simp [map_add, map_mul, map_ofNat]
  ring

end Deriv

def ev {g : ℕ} (a : Fin g) : Fin g → ℂ := Pi.single a 1

def dbarF {g : ℕ} (f : (Fin g → ℂ) → Ext (0 + 0 + g)) (z : Fin g → ℂ) : Ext (0 + 0 + g) :=
  ∑ a, wedge (dzb 0 a) (d01 f z (ev a))

def dbarAdjF {g : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (ψ : (Fin g → ℂ) → ℂ)
    (f : (Fin g → ℂ) → Ext (0 + 0 + g)) (z : Fin g → ℂ) : Ext (0 + 0 + g) :=
  -∑ a, ∑ c, G a c • contr (dzb 0 c) (d10 f z (ev a) + d10 ψ z (ev a) • f z)

def fibreOp {g : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (ψ : (Fin g → ℂ) → ℂ)
    (f : (Fin g → ℂ) → Ext (0 + 0 + g)) (z : Fin g → ℂ) : Ext (0 + 0 + g) :=
  dbarF f z + dbarAdjF G ψ f z

theorem dbar_eq_zero_of_holomorphic {g : ℕ} {φ : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (hφ : DifferentiableAt ℂ φ z) (v : Fin g → ℂ) : d01 φ z v = 0 := by
  simp only [d01, hφ.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars',
    map_smul, smul_eq_mul]
  ring_nf; simp [Complex.I_sq]

theorem dbar_comp_translate {g : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [SMul ℂ W]
    (F : (Fin g → ℂ) → W) (z w v : Fin g → ℂ) :
    d01 (fun z' => F (z' + w)) z v = d01 F (z + w) v := by
  simp only [d01, fderiv_comp_add_right]

end GlobalTheory.TorsionForm.FlatAcyc
