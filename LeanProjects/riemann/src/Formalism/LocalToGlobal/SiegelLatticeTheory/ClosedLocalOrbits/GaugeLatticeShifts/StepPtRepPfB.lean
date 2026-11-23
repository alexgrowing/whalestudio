import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfA

noncomputable section

open Matrix Formalism.MainNotions.S
open scoped ComplexOrder

namespace Formalism.L2.SG.RealObj.InfCut.PtRepPf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

section Frame

variable {n : ℕ} (ε : Fin n → Bool)

structure Fr (r k : ℕ) where
  e : Fin r → Fin n → ℂ
  fd : Fin r → Fin n → ℂ
  z : Fin n → ℂ
  wb : Fin k → Fin n → ℂ
  T : ℝ
  T_pos : 0 < T
  card : n = r + r + (1 + k)
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ff : ∀ a b, hJ ε (fd a) (fd b) = 0
  ef : ∀ a b, hJ ε (e a) (fd b) = if a = b then 1 else 0
  ez : ∀ a, hJ ε (e a) z = 0
  fz : ∀ a, hJ ε (fd a) z = 0
  zz : hJ ε z z = -(T : ℂ)
  ww : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0
  ew : ∀ a i, hJ ε (e a) (wb i) = 0
  fw : ∀ a i, hJ ε (fd a) (wb i) = 0
  zw : ∀ i, hJ ε z (wb i) = 0

variable {ε}

theorem swapJ {x y : Fin n → ℂ} {c : ℂ} (h : hJ ε x y = c) : hJ ε y x = star c := by
  rw [← h]
  simp only [hJ, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, star_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [star_mul'] <;> ring

theorem fam_cs {r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (a : Fin r) :
    fam e z (Fin.castSucc a) = e a := by
  simp [fam]

theorem fam_last {r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : fam e z (Fin.last r) = z := by
  simp [fam]

namespace Fr

variable {r k : ℕ} (F : Fr ε r k)

theorem fe (a b : Fin r) : hJ ε (F.fd a) (F.e b) = if a = b then 1 else 0 := by
  rw [swapJ (F.ef b a)]
  by_cases h : a = b
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem ze (a : Fin r) : hJ ε F.z (F.e a) = 0 := by
  rw [swapJ (F.ez a), star_zero]
theorem zf (a : Fin r) : hJ ε F.z (F.fd a) = 0 := by
  rw [swapJ (F.fz a), star_zero]
theorem we (i : Fin k) (a : Fin r) : hJ ε (F.wb i) (F.e a) = 0 := by
  rw [swapJ (F.ew a i), star_zero]
theorem wf (i : Fin k) (a : Fin r) : hJ ε (F.wb i) (F.fd a) = 0 := by
  rw [swapJ (F.fw a i), star_zero]
theorem wz (i : Fin k) : hJ ε (F.wb i) F.z = 0 := by
  rw [swapJ (F.zw i), star_zero]

theorem T_ne : (F.T : ℂ) ≠ 0 := by
  exact_mod_cast F.T_pos.ne'

theorem star_cz : star (-(F.T : ℂ)⁻¹) = -(F.T : ℂ)⁻¹ := by
  simp [Complex.star_def]

def zd : Fin n → ℂ := (-(F.T : ℂ)⁻¹) • F.z

private lemma hJ_smul_left_eq_star_mul (c : ℂ) (x y : Fin n → ℂ) : hJ ε (c • x) y = star c * hJ ε x y := by
  simp only [hJ, star_smul, smul_dotProduct, smul_eq_mul]

private lemma hJ_smul_right_gauge_lattice_shifts (c : ℂ) (x y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem frame_dual_z_pairing_one : hJ ε F.zd F.z = 1 := by
  rw [zd, hJ_smul_left_eq_star_mul, F.star_cz, F.zz]
  field_simp [F.T_ne]

theorem z_zd : hJ ε F.z F.zd = 1 := by
  rw [zd, hJ_smul_right_gauge_lattice_shifts, F.zz]
  field_simp [F.T_ne]

theorem zd_zd : hJ ε F.zd F.zd = -(F.T : ℂ)⁻¹ := by
  rw [zd, hJ_smul_left_eq_star_mul, hJ_smul_right_gauge_lattice_shifts, F.star_cz, F.zz]
  field_simp [F.T_ne]

theorem zd_left (y : Fin n → ℂ) : hJ ε F.zd y = -(F.T : ℂ)⁻¹ * hJ ε F.z y := by
  rw [zd, hJ_smul_left_eq_star_mul, F.star_cz]

theorem zd_right (y : Fin n → ℂ) : hJ ε y F.zd = -(F.T : ℂ)⁻¹ * hJ ε y F.z := by
  rw [zd, hJ_smul_right_gauge_lattice_shifts]

theorem zd_e (a : Fin r) : hJ ε F.zd (F.e a) = 0 := by
  rw [F.zd_left, F.ze, mul_zero]
theorem zd_f (a : Fin r) : hJ ε F.zd (F.fd a) = 0 := by
  rw [F.zd_left, F.zf, mul_zero]
theorem zd_w (i : Fin k) : hJ ε F.zd (F.wb i) = 0 := by
  rw [F.zd_left, F.zw, mul_zero]
theorem e_zd (a : Fin r) : hJ ε (F.e a) F.zd = 0 := by
  rw [F.zd_right, F.ez, mul_zero]
theorem f_zd (a : Fin r) : hJ ε (F.fd a) F.zd = 0 := by
  rw [F.zd_right, F.fz, mul_zero]
theorem w_zd (i : Fin k) : hJ ε (F.wb i) F.zd = 0 := by
  rw [F.zd_right, F.wz, mul_zero]

abbrev Ix (r k : ℕ) := (Fin r ⊕ Fin r) ⊕ (Unit ⊕ Fin k)

def bv : Ix r k → Fin n → ℂ := Sum.elim (Sum.elim F.e F.fd) (Sum.elim (fun _ => F.z) F.wb)

def dv : Ix r k → Fin n → ℂ :=
  Sum.elim (Sum.elim F.fd F.e) (Sum.elim (fun _ => F.zd) F.wb)

theorem card_ix (G : Fr ε r k) : Fintype.card (Ix r k) = n := by
  simp only [Ix, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  exact G.card.symm

theorem dual (j i : Ix r k) : hJ ε (F.dv j) (F.bv i) = if j = i then 1 else 0 := by
  rcases j with (a | a) | (⟨⟩ | a) <;> rcases i with (b | b) | (⟨⟩ | b) <;>
    simp [dv, bv, F.fe, F.ff, F.fz, F.fw, F.ee, F.ef, F.ez, F.ew, F.zd_e, F.zd_f, F.frame_dual_z_pairing_one, F.zd_w,
      F.we, F.wf, F.wz, F.ww]

private lemma hJ_finset_sum_left' {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ a ∈ s, f a) y = ∑ a ∈ s, hJ ε (f a) y := by
  simp only [hJ, star_sum, sum_dotProduct]

private lemma hJ_finset_sum_right_eq_sum {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (f : ι → Fin n → ℂ) :
    hJ ε x (∑ a ∈ s, f a) = ∑ a ∈ s, hJ ε x (f a) := by
  simp only [hJ, Matrix.mulVec_sum, dotProduct_sum]

theorem pair (w y : Fin n → ℂ) (hw : ∀ a, hJ ε (F.e a) w = 0) (hy : ∀ a, hJ ε (F.e a) y = 0) :
    hJ ε w y = -(F.T : ℂ)⁻¹ * hJ ε F.z y * star (hJ ε F.z w) +
      ∑ i, hJ ε (F.wb i) y * star (hJ ε (F.wb i) w) := by
  have hcoef : ∀ (g : Ix r k → ℂ) (j : Ix r k), hJ ε (F.dv j) (∑ i, g i • F.bv i) = g j := by
    intro g j
    rw [hJ_finset_sum_right_eq_sum]
    simp only [hJ_smul_right_gauge_lattice_shifts, F.dual, mul_ite, mul_one, mul_zero]
    simp [Finset.sum_ite_eq]
  have hli : LinearIndependent ℂ F.bv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := hcoef g j
    rw [hg] at h1
    rw [← h1]
    simp [hJ]
  have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [F.card_ix, Module.finrank_fin_fun])
  have hwm : w ∈ Submodule.span ℂ (Set.range F.bv) := by
    rw [hspan]
    trivial
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hwm
  have hgj : ∀ j, g j = hJ ε (F.dv j) w := fun j => by rw [← hg, hcoef]
  conv_lhs => rw [← hg, hJ_finset_sum_left']
  simp only [hJ_smul_left_eq_star_mul, hgj]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [bv, dv, Sum.elim_inl, Sum.elim_inr, hy, hw, mul_zero, star_zero, zero_mul,
    Finset.sum_const_zero, zero_add, Fintype.univ_unit, Finset.sum_singleton]
  rw [F.zd_left, star_mul', F.star_cz]
  clear hcoef hli hspan hwm hg hgj hw hy
  rw [Finset.sum_congr rfl (fun i _ => mul_comm (star (hJ ε (F.wb i) w)) (hJ ε (F.wb i) y))]
  ring

theorem gf (a b : Fin (r + 1)) :
    hJ ε (fam F.e F.z a) (fam F.e F.z b) = if a = Fin.last r ∧ b = Fin.last r then -(F.T : ℂ) else 0 := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl <;>
    simp [fam_cs, fam_last, F.ee, F.ez, F.ze, F.zz, Fin.castSucc_ne_last]

theorem w_fam (i : Fin k) (a : Fin (r + 1)) : hJ ε (F.wb i) (fam F.e F.z a) = 0 := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;> simp [fam_cs, fam_last, F.we, F.wz]

theorem fam_w (a : Fin (r + 1)) (i : Fin k) : hJ ε (fam F.e F.z a) (F.wb i) = 0 := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;> simp [fam_cs, fam_last, F.ew, F.zw]

def Fv : Fin (r + 1) → Fin n → ℂ := fam F.fd F.zd

def E0 : Fin (r + 1) → Fin n → ℂ := fam F.e 0

theorem Fv_fam (a b : Fin (r + 1)) : hJ ε (F.Fv a) (fam F.e F.z b) = if a = b then 1 else 0 := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl <;>
    simp [Fv, fam_cs, fam_last, F.fe, F.fz, F.zd_e, F.frame_dual_z_pairing_one, Fin.castSucc_ne_last,
      (Fin.castSucc_ne_last _).symm]

theorem Fv_w (a : Fin (r + 1)) (i : Fin k) : hJ ε (F.Fv a) (F.wb i) = 0 := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;> simp [Fv, fam_cs, fam_last, F.fw, F.zd_w]

theorem w_Fv (i : Fin k) (a : Fin (r + 1)) : hJ ε (F.wb i) (F.Fv a) = 0 := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;> simp [Fv, fam_cs, fam_last, F.wf, F.w_zd]

theorem frame_w_e_zero_orthogonal (i : Fin k) (a : Fin (r + 1)) : hJ ε (F.wb i) (F.E0 a) = 0 := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl
  · simp [E0, fam_cs, F.we]
  · simp [E0, fam_last, hJ]

def yv (i0 : Fin k) (Z Aα : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (t : Fin (r + 1) → ℂ) (b : Fin (r + 1)) :
    Fin n → ℂ :=
  ∑ a, Z a b • F.Fv a + ∑ a, Aα a b • F.E0 a + t b • F.wb i0

variable (i0 : Fin k) (Z Aα : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (t : Fin (r + 1) → ℂ)

private lemma hJ_add_right_gauge_lattice_shifts (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp only [hJ, Matrix.mulVec_add, dotProduct_add]

private lemma hJ_finset_sum_right' {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (f : ι → Fin n → ℂ) :
    hJ ε x (∑ a ∈ s, f a) = ∑ a ∈ s, hJ ε x (f a) := by
  simp only [hJ, Matrix.mulVec_sum, dotProduct_sum]

theorem pair_yv (x : Fin n → ℂ) (b : Fin (r + 1)) :
    hJ ε x (F.yv i0 Z Aα t b) =
      ∑ a, Z a b * hJ ε x (F.Fv a) + ∑ a, Aα a b * hJ ε x (F.E0 a) + t b * hJ ε x (F.wb i0) := by
  unfold yv
  rw [hJ_add_right_gauge_lattice_shifts, hJ_add_right_gauge_lattice_shifts, hJ_finset_sum_right', hJ_finset_sum_right', hJ_smul_right_gauge_lattice_shifts]
  simp only [hJ_smul_right_gauge_lattice_shifts]

theorem p1 (a b : Fin (r + 1)) : hJ ε (fam F.e F.z a) (F.yv i0 Z Aα t b) = Z a b := by
  rw [F.pair_yv]
  have h1 : ∀ c, hJ ε (fam F.e F.z a) (F.Fv c) = if c = a then 1 else 0 := fun c => by
    rw [swapJ (F.Fv_fam c a)]
    split_ifs <;> simp
  have h2 : ∀ c, hJ ε (fam F.e F.z a) (F.E0 c) = 0 := fun c => by
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last c with ⟨c, rfl⟩ | rfl <;>
      first
      | (simp [E0, fam_cs, fam_last, F.ee, F.ze]; done)
      | (simp [E0, fam_cs, fam_last, hJ]; done)
  simp only [h1, h2, F.fam_w, mul_zero, Finset.sum_const_zero, add_zero, mul_ite, mul_one]
  simp [Finset.sum_ite_eq']

theorem p2 (hA : ∀ j, Aα (Fin.last r) j = 0) (a c : Fin (r + 1)) :
    hJ ε (F.Fv a) (F.yv i0 Z Aα t c) =
      (if a = Fin.last r then -(F.T : ℂ)⁻¹ * Z (Fin.last r) c else 0) + Aα a c := by
  rw [F.pair_yv]
  have h1 : ∀ d, hJ ε (F.Fv a) (F.Fv d) =
      if a = Fin.last r ∧ d = Fin.last r then -(F.T : ℂ)⁻¹ else 0 := fun d => by
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last d with ⟨d, rfl⟩ | rfl <;>
      simp [Fv, fam_cs, fam_last, F.ff, F.f_zd, F.zd_f, F.zd_zd, Fin.castSucc_ne_last]
  have h2 : ∀ d, hJ ε (F.Fv a) (F.E0 d) = if d = a ∧ a ≠ Fin.last r then 1 else 0 := fun d => by
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last d with ⟨d, rfl⟩ | rfl
    · simp [Fv, E0, fam_cs, F.fe, Fin.castSucc_ne_last, eq_comm]
    · simp [Fv, E0, fam_cs, fam_last, hJ, (Fin.castSucc_ne_last _).symm]
    · simp [Fv, E0, fam_cs, fam_last, F.zd_e]
    · simp [Fv, E0, fam_last, hJ]
  simp only [h1, h2, F.Fv_w, mul_zero, add_zero]
  by_cases ha : a = Fin.last r
  · subst ha
    simp [hA, mul_comm]
  · simp [ha, mul_ite, Finset.sum_ite_eq']

theorem p3 (a c : Fin (r + 1)) :
    hJ ε (F.E0 a) (F.yv i0 Z Aα t c) = if a = Fin.last r then 0 else Z a c := by
  rw [F.pair_yv]
  have h1 : ∀ d, hJ ε (F.E0 a) (F.Fv d) = if a = Fin.last r then 0 else (if d = a then 1 else 0) := fun d => by
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last d with ⟨d, rfl⟩ | rfl <;>
      first
      | (simp [E0, Fv, fam_cs, fam_last, F.ef, F.e_zd, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, eq_comm]; done)
      | (simp [E0, Fv, fam_cs, fam_last, hJ]; done)
  have h2 : ∀ d, hJ ε (F.E0 a) (F.E0 d) = 0 := fun d => by
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last d with ⟨d, rfl⟩ | rfl <;>
      first
      | (simp [E0, fam_cs, fam_last, F.ee]; done)
      | (simp [E0, fam_cs, fam_last, hJ]; done)
  have h3 : hJ ε (F.E0 a) (F.wb i0) = 0 := by
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl
    · simp [E0, fam_cs, F.ew]
    · simp [E0, fam_last, hJ]
  simp only [h1, h2, h3, mul_zero, Finset.sum_const_zero, add_zero]
  split_ifs with ha
  · simp
  · simp [mul_ite, Finset.sum_ite_eq']

theorem p4 (i : Fin k) (c : Fin (r + 1)) :
    hJ ε (F.wb i) (F.yv i0 Z Aα t c) = if i = i0 then t c else 0 := by
  rw [F.pair_yv]
  simp only [F.w_Fv, F.frame_w_e_zero_orthogonal, mul_zero, Finset.sum_const_zero, zero_add, F.ww]
  split_ifs with h
  · subst h
    simp
  · simp [Ne.symm h]

private lemma hJ_yv_left_eq_sum (y : Fin n → ℂ) (b : Fin (r + 1)) :
    hJ ε (F.yv i0 Z Aα t b) y = ∑ a, star (Z a b) * hJ ε (F.Fv a) y +
      ∑ a, star (Aα a b) * hJ ε (F.E0 a) y + star (t b) * hJ ε (F.wb i0) y := by
  have hs : ∀ x, star (hJ ε y x) = hJ ε x y := fun x => (swapJ rfl).symm
  rw [swapJ (rfl : hJ ε y (F.yv i0 Z Aα t b) = _), F.pair_yv]
  simp only [star_add, star_sum, star_mul', hs]

theorem gram (hA : ∀ j, Aα (Fin.last r) j = 0) (b c : Fin (r + 1)) :
    hJ ε (F.yv i0 Z Aα t b) (F.yv i0 Z Aα t c) =
      -(F.T : ℂ)⁻¹ * (star (Z (Fin.last r) b) * Z (Fin.last r) c) + (Zᴴ * Aα) b c + (Aαᴴ * Z) b c +
        star (t b) * t c := by
  rw [hJ_yv_left_eq_sum, F.p4 i0 Z Aα t i0 c, if_pos rfl]
  simp only [F.p2 i0 Z Aα t hA, F.p3 i0 Z Aα t]
  have hAZ : ∑ a, star (Aα a b) * (if a = Fin.last r then 0 else Z a c) = ∑ a, star (Aα a b) * Z a c := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a = Fin.last r
    · subst ha
      simp [hA]
    · simp [ha]
  rw [hAZ, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end Fr

end Frame

section Mat

variable {m : ℕ}

theorem dot_vmv (x a b y : Fin m → ℂ) : star x ⬝ᵥ (vecMulVec a b *ᵥ y) = (star x ⬝ᵥ a) * (b ⬝ᵥ y) := by
  simp only [dotProduct, mulVec, vecMulVec, Matrix.of_apply]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem solveHerm (Z Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hZ : IsUnit Z.det) (hQ : Qᴴ = Q)
    (hc : star (Z⁻¹ *ᵥ Pi.single (Fin.last m) 1) ⬝ᵥ (Q *ᵥ (Z⁻¹ *ᵥ Pi.single (Fin.last m) 1)) = 0) :
    ∃ A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, (∀ j, A (Fin.last m) j = 0) ∧ Zᴴ * A + Aᴴ * Z = Q := by
  set e : Fin (m + 1) → ℂ := Pi.single (Fin.last m) 1 with he
  set c : Fin (m + 1) → ℂ := Z⁻¹ *ᵥ e with hcdef
  have hZc : Z *ᵥ c = e := by
    rw [hcdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hZ, Matrix.one_mulVec]
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hZc
    have h1 := congrFun hZc (Fin.last m)
    simp [he] at h1
  have hs : star c ⬝ᵥ c ≠ 0 := fun h0 => hc0 (dotProduct_star_self_eq_zero.1 h0)
  set q := Q *ᵥ c with hq
  set c' := (star c ⬝ᵥ c)⁻¹ • c with hc'
  set W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    (1 / 2 : ℂ) • Q + (1 / 2 : ℂ) • (vecMulVec q (star c') - vecMulVec c' (star q)) with hW
  have hZH : IsUnit (Zᴴ).det := by
    rw [det_conjTranspose]
    exact hZ.star
  refine ⟨(Zᴴ)⁻¹ * W, ?_, ?_⟩
  · intro j
    have hrow : ∀ k, (Zᴴ)⁻¹ (Fin.last m) k = star (c k) := by
      intro k
      rw [← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_apply, hcdef]
      simp [Matrix.mulVec, dotProduct, he, Pi.single_apply]
    have hvv : ∀ (x a b : Fin (m + 1) → ℂ), x ᵥ* vecMulVec a b = (x ⬝ᵥ a) • b := by
      intro x a b
      ext l
      simp [Matrix.vecMul, dotProduct, vecMulVec, Finset.sum_mul, mul_assoc]
    have hcq : star c ⬝ᵥ q = 0 := hc
    have hcc : star c ⬝ᵥ c' = 1 := by
      rw [hc', dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hs]
    have hsq : star c ᵥ* Q = star q := by
      rw [hq, Matrix.star_mulVec Q c, hQ]
    have hv : star c ᵥ* W = 0 := by
      rw [hW, Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_smul, Matrix.vecMul_sub, hvv, hvv,
        hcq, hcc, hsq]
      ext l
      simp
    have h2 := congrFun hv j
    rw [Matrix.mul_apply]
    simp only [hrow]
    simpa [Matrix.vecMul, dotProduct] using h2
  · have h1 : Zᴴ * ((Zᴴ)⁻¹ * W) = W := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hZH, Matrix.one_mul]
    have h2 : ((Zᴴ)⁻¹ * W)ᴴ * Z = Wᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZ, Matrix.mul_one]
    rw [h1, h2]
    ext a b
    simp only [hW, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
      vecMulVec, Matrix.of_apply, smul_eq_mul, star_add, star_mul', star_sub, Pi.star_apply, star_star]
    have hQab : star (Q b a) = Q a b := by
      have := congrFun (congrFun hQ a) b
      rwa [Matrix.conjTranspose_apply] at this
    rw [hQab]
    simp
    ring

theorem dl_top {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Dl Z (r + 1) = Z.det := by
  unfold Dl
  rw [dif_pos le_rfl]
  congr 1

theorem dl_r {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Dl Z r = adjugate Z (Fin.last r) (Fin.last r) := by
  unfold Dl
  rw [dif_pos (Nat.le_succ r), Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  have h1 : (Fin.castLE (Nat.le_succ r) : Fin r → Fin (r + 1)) = Fin.castSucc := by
    funext i
    exact Fin.ext rfl
  rw [h1, Even.neg_one_pow ⟨_, rfl⟩, one_mul]

theorem inv_last {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Z⁻¹ (Fin.last r) (Fin.last r) = (Z.det)⁻¹ * Dl Z r := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', dl_r]

theorem gv_facts {r : ℕ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hG : 0 < Gv T T' Z) : IsUnit Z.det ∧ T * T' * ‖Z⁻¹ (Fin.last r) (Fin.last r)‖ ^ 2 < 1 := by
  unfold Gv at hG
  rw [dl_top] at hG
  have hdet : Z.det ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hG
    nlinarith [sq_nonneg ‖Dl Z r‖, mul_pos hT hT']
  refine ⟨isUnit_iff_ne_zero.2 hdet, ?_⟩
  rw [inv_last, norm_mul, norm_inv, mul_pow, inv_pow]
  have hd : 0 < ‖Z.det‖ ^ 2 := by positivity
  rw [show T * T' * ((‖Z.det‖ ^ 2)⁻¹ * ‖Dl Z r‖ ^ 2) = (T * T' * ‖Dl Z r‖ ^ 2) / ‖Z.det‖ ^ 2 by ring]
  rw [div_lt_one hd]
  linarith

end Mat

end Formalism.L2.SG.RealObj.InfCut.PtRepPf
