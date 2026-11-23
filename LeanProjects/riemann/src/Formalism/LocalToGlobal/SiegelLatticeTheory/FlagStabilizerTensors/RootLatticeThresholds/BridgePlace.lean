import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierBase

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting
open Formalism.L2.SG.RealObj.InfCut

section Frame

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} (F : PtRepPf.Fr ε r k)

def wc (y : Fin n → ℂ) : Fin k → ℂ := fun i => hJ ε (F.wb i) y

def mW (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin k) (Fin k) ℂ := fun a b => hJ ε (F.wb a) (H *ᵥ F.wb b)

private lemma hJ_sum_left' {ι : Type*} (s : Finset ι) (v : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ i ∈ s, v i) y = ∑ i ∈ s, hJ ε (v i) y := by
  simp only [PtRepPf.hJ_apply, Finset.sum_apply, star_sum, Finset.sum_mul]
  exact Finset.sum_comm

private lemma hJ_sum_right_root_lattice_thresholds {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (v : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, v i) = ∑ i ∈ s, hJ ε x (v i) := by
  simp only [PtRepPf.hJ_apply, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

private lemma hJ_sub_left_root_lattice_thresholds (x x' y : Fin n → ℂ) : hJ ε (x - x') y = hJ ε x y - hJ ε x' y := by
  simp only [PtRepPf.hJ_apply, Pi.sub_apply, star_sub, sub_mul, Finset.sum_sub_distrib]

private lemma eq_zero_of_hJ_frame_eq_zero (G : PtRepPf.Fr ε r k) (d : Fin n → ℂ) (he : ∀ a, hJ ε (G.e a) d = 0)
    (hf : ∀ a, hJ ε (G.fd a) d = 0) (hz : hJ ε G.z d = 0) (hw : ∀ i, hJ ε (G.wb i) d = 0) : d = 0 := by
  apply PtRepPf.eq_zero_of_hJ (ε := ε)
  intro x
  have hx'e : ∀ b, hJ ε (G.e b) (x - ∑ a, hJ ε (G.fd a) x • G.e a - ∑ a, hJ ε (G.e a) x • G.fd a) = 0 := by
    intro b
    rw [PtRepPf.hJ_sub_right, PtRepPf.hJ_sub_right, hJ_sum_right_root_lattice_thresholds, hJ_sum_right_root_lattice_thresholds]
    simp only [PtRepPf.hJ_smul_right, G.ee, G.ef, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
  have h1 := G.pair _ d hx'e he
  simp only [hz, hw, mul_zero, zero_mul, Finset.sum_const_zero, add_zero] at h1
  have h2 : hJ ε x d = hJ ε (x - ∑ a, hJ ε (G.fd a) x • G.e a - ∑ a, hJ ε (G.e a) x • G.fd a) d := by
    rw [hJ_sub_left_root_lattice_thresholds, hJ_sub_left_root_lattice_thresholds, hJ_sum_left', hJ_sum_left']
    simp only [PtRepPf.hJ_smul_left, he, hf, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [h2, h1]

theorem isom {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε) (x y : Fin n → ℂ) :
    hJ ε (H *ᵥ x) (H *ᵥ y) = hJ ε x y := by
  simp only [hJ, Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [← Matrix.mul_assoc, hH]

theorem fixed_left {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε) {x : Fin n → ℂ}
    (hx : H *ᵥ x = x) (w : Fin n → ℂ) : hJ ε x (H *ᵥ w) = hJ ε x w := by
  calc hJ ε x (H *ᵥ w) = hJ ε (H *ᵥ x) (H *ᵥ w) := by rw [hx]
    _ = hJ ε x w := isom hH x w

theorem fix_zd {H : Matrix (Fin n) (Fin n) ℂ} (hz : H *ᵥ F.z = F.z) : H *ᵥ F.zd = F.zd := by
  show H *ᵥ ((-(F.T : ℂ)⁻¹) • F.z) = (-(F.T : ℂ)⁻¹) • F.z
  rw [Matrix.mulVec_smul, hz]

theorem H_wb {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε)
    (he : ∀ a, H *ᵥ F.e a = F.e a) (hf : ∀ a, H *ᵥ F.fd a = F.fd a) (hz : H *ᵥ F.z = F.z) (i : Fin k) :
    H *ᵥ F.wb i = ∑ j, mW F H j i • F.wb j := by
  have key : ∀ x, hJ ε x (H *ᵥ F.wb i - ∑ j, mW F H j i • F.wb j) =
      hJ ε x (H *ᵥ F.wb i) - ∑ j, mW F H j i * hJ ε x (F.wb j) := by
    intro x
    rw [PtRepPf.hJ_sub_right, hJ_sum_right_root_lattice_thresholds]
    simp only [PtRepPf.hJ_smul_right]
  rw [← sub_eq_zero]
  apply eq_zero_of_hJ_frame_eq_zero F
  · intro a
    rw [key, fixed_left hH (he a)]
    simp [F.ew]
  · intro a
    rw [key, fixed_left hH (hf a)]
    simp [F.fw]
  · rw [key, fixed_left hH hz]
    simp [F.zw]
  · intro l
    rw [key]
    simp [F.ww, mW]

theorem wc_inv {H Hi : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε)
    (hHi : H * Hi = 1)
    (he : ∀ a, H *ᵥ F.e a = F.e a) (hf : ∀ a, H *ᵥ F.fd a = F.fd a) (hz : H *ᵥ F.z = F.z) (w : Fin n → ℂ) :
    wc F (Hi *ᵥ w) = (mW F H)ᴴ *ᵥ wc F w := by
  funext i
  show hJ ε (F.wb i) (Hi *ᵥ w) = ((mW F H)ᴴ *ᵥ wc F w) i
  rw [← isom hH (F.wb i) (Hi *ᵥ w), Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec, H_wb F hH he hf hz i,
    hJ_sum_left']
  simp only [PtRepPf.hJ_smul_left, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  rfl

theorem wc_fwd {H Hi : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε)
    (hHi : H * Hi = 1) (hiH : Hi * H = 1)
    (he : ∀ a, H *ᵥ F.e a = F.e a) (hf : ∀ a, H *ᵥ F.fd a = F.fd a) (hz : H *ᵥ F.z = F.z)
    (hM : mW F H ∈ Matrix.unitaryGroup (Fin k) ℂ) (y : Fin n → ℂ) :
    wc F (H *ᵥ y) = mW F H *ᵥ wc F y := by
  have h1 := wc_inv F hH hHi he hf hz (H *ᵥ y)
  rw [Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec] at h1
  have hU : mW F H * (mW F H)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hM
  rw [h1, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

end Frame

section Model

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} (F : PtRepPf.Fr ε r k)
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ}

def trunc (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  fun i => if r ≤ i.val ∧ i.val ≤ r + k then v i else 0

theorem trunc_add (v w : Fin (2 * r + k + 1) → ℂ) : trunc (v + w) = trunc v + trunc w := by
  funext i
  simp only [trunc, Pi.add_apply]
  split_ifs <;> simp

theorem trunc_smul (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) : trunc (c • v) = c • trunc v := by
  funext i
  simp only [trunc, Pi.smul_apply]
  split_ifs <;> simp

theorem trunc_sum {ι : Type*} (s : Finset ι) (v : ι → Fin (2 * r + k + 1) → ℂ) :
    trunc (∑ i ∈ s, v i) = ∑ i ∈ s, trunc (v i) := by
  funext j
  simp only [trunc, Finset.sum_apply]
  split_ifs <;> simp

theorem trunc_inWb {v : Fin (2 * r + k + 1) → ℂ} (h : Formalism.QuantumDeterminants.inWb k r v) : trunc v = v := by
  funext i
  simp only [trunc]
  split_ifs with hi
  · rfl
  · exact (h i (by omega)).symm

theorem trunc_eI (a : Fin r) : trunc (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) = 0 := by
  funext i
  simp only [trunc, Formalism.QuantumDeterminants.bvec, Pi.zero_apply]
  split_ifs with hi
  · rw [Pi.single_apply, if_neg]
    intro h
    have h2 : i.val = a.val := congrArg Fin.val h
    have := a.isLt
    omega
  · rfl

theorem trunc_esI (a : Fin r) : trunc (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)) = 0 := by
  funext i
  simp only [trunc, Formalism.QuantumDeterminants.bvec, Pi.zero_apply]
  split_ifs with hi
  · rw [Pi.single_apply, if_neg]
    intro h
    have h2 : i.val = 2 * r + k - a.val := congrArg Fin.val h
    have := a.isLt
    omega
  · rfl

structure TrHyp (Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ) (Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ)
    (c : Fin r → ℂ) : Prop where
  h1 : Qim * Qm = 1
  h2 : Qm * Qim = 1
  hH : Qmᴴ * Formalism.REAL.Jm ε * Qm = Formalism.QuantumDeterminants.Hpk k r
  he : ∀ a, Qm *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = c a • F.e a
  hf : ∀ a, Qm *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a) = (star (c a))⁻¹ • F.fd a

variable {F} {c : Fin r → ℂ}

theorem herm_Q (hT : TrHyp F Qm Qim c) (p q : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) p q = hJ ε (Qm *ᵥ q) (Qm *ᵥ p) := by
  rw [← hT.hH]
  simp only [Formalism.QuantumDeterminants.herm, hJ, Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem c_ne (hT : TrHyp F Qm Qim c) (a : Fin r) : c a ≠ 0 := by
  intro h0
  have h := hT.he a
  rw [h0, zero_smul] at h
  have h3 : Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = 0 := by
    have h4 := congrArg (Qim *ᵥ ·) h
    simpa [Matrix.mulVec_mulVec, hT.h1] using h4
  have h5 := congrFun h3 (Formalism.QuantumDeterminants.eI k r a)
  simp [Formalism.QuantumDeterminants.bvec] at h5

theorem Qi_e (hT : TrHyp F Qm Qim c) (a : Fin r) : Qim *ᵥ F.e a = (c a)⁻¹ • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) := by
  have hc := c_ne hT a
  have h1 : F.e a = (c a)⁻¹ • (Qm *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) := by
    rw [hT.he a, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hT.h1, Matrix.one_mulVec]

theorem Qi_f (hT : TrHyp F Qm Qim c) (a : Fin r) : Qim *ᵥ F.fd a = star (c a) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a) := by
  have hc : star (c a) ≠ 0 := star_ne_zero.mpr (c_ne hT a)
  have h1 : F.fd a = star (c a) • (Qm *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)) := by
    rw [hT.hf a, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hT.h1, Matrix.one_mulVec]

private lemma herm_Hpk_bvec_eq_apply_of_antidiagonal (v : Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hpq : p.val + q.val = 2 * r + k) (hpr : p.val < r ∨ q.val < r) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v (Formalism.QuantumDeterminants.bvec p) = v q := by
  simp only [Formalism.QuantumDeterminants.herm, Formalism.QuantumDeterminants.bvec]
  have hs : star (Pi.single p (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = Pi.single p 1 := by
    funext m
    simp [Pi.single_apply]
  have hd : Pi.single p (1 : ℂ) ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) = (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) p := by
    simp [dotProduct, Pi.single_apply]
  rw [hs, hd]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single q]
  · have hq : Formalism.QuantumDeterminants.Hpk k r p q = 1 := by
      simp only [Formalism.QuantumDeterminants.Hpk]
      split_ifs <;> first | rfl | (exfalso; (try simp only [Fin.ext_iff] at *); omega)
    rw [hq, one_mul]
  · intro m _ hmq
    have hmq' : m.val ≠ q.val := fun h => hmq (Fin.ext h)
    have hm : Formalism.QuantumDeterminants.Hpk k r p m = 0 := by
      simp only [Formalism.QuantumDeterminants.Hpk]
      split_ifs <;> first | rfl | (exfalso; (try simp only [Fin.ext_iff] at *); omega)
    rw [hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ q) h

theorem inWb_Qi' (hT : TrHyp F Qm Qim c) (w : Fin n → ℂ) (hwe : ∀ a, hJ ε (F.e a) w = 0)
    (hwf : ∀ a, hJ ε (F.fd a) w = 0) : Formalism.QuantumDeterminants.inWb k r (Qim *ᵥ w) := by
  intro i hi
  have hil := i.isLt
  rcases hi with hi | hi
  · have h1 := herm_Hpk_bvec_eq_apply_of_antidiagonal (Qim *ᵥ w) (Formalism.QuantumDeterminants.esI k r ⟨i.val, hi⟩) i
      (by show (2 * r + k - i.val) + i.val = 2 * r + k; omega) (Or.inr hi)
    rw [herm_Q hT, hT.hf, Matrix.mulVec_mulVec, hT.h2, Matrix.one_mulVec, PtRepPf.hJ_smul_left, hwf,
      mul_zero] at h1
    exact h1.symm
  · have h1 := herm_Hpk_bvec_eq_apply_of_antidiagonal (Qim *ᵥ w) (Formalism.QuantumDeterminants.eI k r ⟨2 * r + k - i.val, by omega⟩) i
      (by show (2 * r + k - i.val) + i.val = 2 * r + k; omega)
      (Or.inl (by show 2 * r + k - i.val < r; omega))
    rw [herm_Q hT, hT.he, Matrix.mulVec_mulVec, hT.h2, Matrix.one_mulVec, PtRepPf.hJ_smul_left, hwe,
      mul_zero] at h1
    exact h1.symm

private lemma eq_frame_expansion_hJ (G : PtRepPf.Fr ε r k) (v : Fin n → ℂ) :
    v = ∑ a, hJ ε (G.fd a) v • G.e a + ∑ a, hJ ε (G.e a) v • G.fd a + (-(G.T : ℂ)⁻¹ * hJ ε G.z v) • G.z +
      ∑ i, hJ ε (G.wb i) v • G.wb i := by
  have hT0 : (G.T : ℂ) ≠ 0 := by exact_mod_cast G.T_pos.ne'
  have fe : ∀ a b, hJ ε (G.fd b) (G.e a) = if a = b then 1 else 0 := by
    intro a b
    rw [← PtRepPf.hJ_conj, G.ef]
    split_ifs <;> simp
  have ze : ∀ a, hJ ε G.z (G.e a) = 0 := by
    intro a
    rw [← PtRepPf.hJ_conj, G.ez, star_zero]
  have zf : ∀ a, hJ ε G.z (G.fd a) = 0 := by
    intro a
    rw [← PtRepPf.hJ_conj, G.fz, star_zero]
  have we : ∀ i a, hJ ε (G.wb i) (G.e a) = 0 := by
    intro i a
    rw [← PtRepPf.hJ_conj, G.ew, star_zero]
  have wf : ∀ i a, hJ ε (G.wb i) (G.fd a) = 0 := by
    intro i a
    rw [← PtRepPf.hJ_conj, G.fw, star_zero]
  have wz : ∀ i, hJ ε (G.wb i) G.z = 0 := by
    intro i
    rw [← PtRepPf.hJ_conj, G.zw, star_zero]
  rw [← sub_eq_zero]
  apply eq_zero_of_hJ_frame_eq_zero G
  · intro b
    simp only [PtRepPf.hJ_sub_right, PtRepPf.hJ_add_right, hJ_sum_right_root_lattice_thresholds, PtRepPf.hJ_smul_right, G.ee, G.ef,
      G.ez, G.ew, mul_zero, Finset.sum_const_zero, zero_add, add_zero, mul_ite, mul_one, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, sub_self]
  · intro b
    simp only [PtRepPf.hJ_sub_right, PtRepPf.hJ_add_right, hJ_sum_right_root_lattice_thresholds, PtRepPf.hJ_smul_right, fe, G.ff,
      G.fz, G.fw, mul_zero, Finset.sum_const_zero, zero_add, add_zero, mul_ite, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, sub_self]
  · simp only [PtRepPf.hJ_sub_right, PtRepPf.hJ_add_right, hJ_sum_right_root_lattice_thresholds, PtRepPf.hJ_smul_right, ze, zf,
      G.zz, G.zw, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
    linear_combination (-(hJ ε G.z v)) * inv_mul_cancel₀ hT0
  · intro l
    simp only [PtRepPf.hJ_sub_right, PtRepPf.hJ_add_right, hJ_sum_right_root_lattice_thresholds, PtRepPf.hJ_smul_right, we, wf,
      wz, G.ww, mul_zero, Finset.sum_const_zero, zero_add, add_zero, mul_ite, mul_one, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, sub_self]

theorem prW_Qi (hT : TrHyp F Qm Qim c) (w : Fin n → ℂ) :
    Formalism.FourierDecayAlt.D.prW k r (Qim *ᵥ F.z) (Qim *ᵥ w) = Qim *ᵥ ∑ i, wc F w i • F.wb i := by
  have hz0 : trunc (Qim *ᵥ F.z) = Qim *ᵥ F.z := trunc_inWb (inWb_Qi' hT _ F.ez F.fz)
  have hwi : ∀ i, trunc (Qim *ᵥ F.wb i) = Qim *ᵥ F.wb i :=
    fun i => trunc_inWb (inWb_Qi' hT _ (fun a => F.ew a i) (fun a => F.fw a i))
  have hvb : trunc (Qim *ᵥ w) = (-(F.T : ℂ)⁻¹ * hJ ε F.z w) • (Qim *ᵥ F.z) + Qim *ᵥ ∑ i, wc F w i • F.wb i := by
    conv_lhs => rw [eq_frame_expansion_hJ F w]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, trunc_add, trunc_sum, trunc_smul,
      Qi_e hT, Qi_f hT, trunc_eI, trunc_esI, smul_zero, Finset.sum_const_zero, zero_add, hz0, hwi, wc]
  show trunc (Qim *ᵥ w) - (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (trunc (Qim *ᵥ w)) (Qim *ᵥ F.z) /
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Qim *ᵥ F.z) (Qim *ᵥ F.z)) • (Qim *ᵥ F.z) = _
  rw [hvb, herm_Q hT, herm_Q hT]
  have hQQ : Qm *ᵥ (Qim *ᵥ F.z) = F.z := by rw [Matrix.mulVec_mulVec, hT.h2, Matrix.one_mulVec]
  have hQW : Qm *ᵥ (Qim *ᵥ ∑ i, wc F w i • F.wb i) = ∑ i, wc F w i • F.wb i := by
    rw [Matrix.mulVec_mulVec, hT.h2, Matrix.one_mulVec]
  have hzW : hJ ε F.z (∑ i, wc F w i • F.wb i) = 0 := by
    rw [hJ_sum_right_root_lattice_thresholds]
    simp [PtRepPf.hJ_smul_right, F.zw]
  have hT0 : (F.T : ℂ) ≠ 0 := by exact_mod_cast F.T_pos.ne'
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hQQ, hQW, PtRepPf.hJ_add_right, PtRepPf.hJ_smul_right, hzW, F.zz,
    add_zero, mul_div_assoc, div_self (neg_ne_zero.mpr hT0), mul_one, add_sub_cancel_left]

end Model

section Cof

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F F' : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

def lam (c : Fin r → ℂ) (sc : ℝ) : Fin (r + 1) → ℂ := fun a =>
  if h : a.val < r then c ⟨a.val, h⟩ * (sc : ℂ) ^ (r - a.val) else 1

theorem lam_last (c : Fin r → ℂ) (sc : ℝ) : lam c sc (Fin.last r) = 1 := by
  simp [lam]

theorem lam_ne (hT : TrHyp F Qm Qim c) {sc : ℝ} (hsc : sc ≠ 0) (a : Fin (r + 1)) : lam c sc a ≠ 0 := by
  unfold lam
  split_ifs with h
  · exact mul_ne_zero (c_ne hT _) (pow_ne_zero _ (by exact_mod_cast hsc))
  · exact one_ne_zero

theorem Q_fvec (hT : TrHyp F Qm Qim c) {sc : ℝ} (hsc : sc ≠ 0) (a : Fin (r + 1)) :
    Qm *ᵥ Formalism.QuantumDeterminants.fvec k r (Qim *ᵥ F.z) a = lam c sc a • famSc sc F.e F.z a := by
  induction a using Fin.lastCases with
  | last =>
    have h1 : Formalism.QuantumDeterminants.fvec k r (Qim *ᵥ F.z) (Fin.last r) = Qim *ᵥ F.z := by
      simp [Formalism.QuantumDeterminants.fvec]
    rw [h1, Matrix.mulVec_mulVec, hT.h2, Matrix.one_mulVec, lam_last, one_smul]
    simp [famSc, fam]
  | cast i =>
    have h1 : Formalism.QuantumDeterminants.fvec k r (Qim *ᵥ F.z) (Fin.castSucc i) = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r i) := by
      simp [Formalism.QuantumDeterminants.fvec]
    have h2 : lam c sc (Fin.castSucc i) = c i * (sc : ℂ) ^ (r - i.val) := by
      simp [lam]
    rw [h1, hT.he, h2]
    simp only [famSc, fam, Fin.snoc_castSucc, Fin.coe_castSucc, smul_smul]
    congr 1
    have : (sc : ℂ) ^ (r - i.val) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hsc)
    field_simp

theorem Q_delta (hT : TrHyp F Qm Qim c) (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    Qm *ᵥ ((Qim * A * Qm) *ᵥ x) = A *ᵥ (Qm *ᵥ x) := by
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hT.h2, Matrix.one_mul]

theorem zhat_cs (hT : TrHyp F Qm Qim c) (hT' : TrHyp F' Qm Qim c) {sc : ℝ} (hsc : sc ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.QuantumDeterminants.Zhat k r (Qim *ᵥ F.z) (Qim *ᵥ F'.z) (Qim * A * Qm) =
      Matrix.diagonal (fun a => star (lam c sc a)) *
        Formalism.L2.SG.RealObj.Zhat ε (famSc sc F.e F.z) (famSc sc F'.e F'.z) A * Matrix.diagonal (lam c sc) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  show Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) ((Qim * A * Qm) *ᵥ Formalism.QuantumDeterminants.fvec k r (Qim *ᵥ F'.z) b)
    (Formalism.QuantumDeterminants.fvec k r (Qim *ᵥ F.z) a) = _
  rw [herm_Q hT, Q_delta hT, Q_fvec hT hsc, Q_fvec hT' hsc, Matrix.mulVec_smul, PtRepPf.hJ_smul_left,
    PtRepPf.hJ_smul_right]
  simp only [Formalism.L2.SG.RealObj.Zhat]
  ring

theorem adj_diag {m : ℕ} (d : Fin m → ℂ) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d).adjugate = Matrix.diagonal (fun i => (∏ j, d j) / d i) := by
  have hdet : (Matrix.diagonal d).det = ∏ j, d j := Matrix.det_diagonal
  have hP : (∏ j, d j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hd j)
  have hU : IsUnit (Matrix.diagonal d).det := by rw [hdet]; exact hP.isUnit
  have h1 : Matrix.diagonal d * Matrix.diagonal (fun i => (∏ j, d j) / d i) =
      (Matrix.diagonal d).det • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    rw [Matrix.diagonal_mul_diagonal, hdet, Matrix.smul_one_eq_diagonal]
    congr 1
    funext i
    field_simp [hd i]
  have h2 := Matrix.mul_adjugate (Matrix.diagonal d)
  calc (Matrix.diagonal d).adjugate
      = (Matrix.diagonal d)⁻¹ * (Matrix.diagonal d * (Matrix.diagonal d).adjugate) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
    _ = (Matrix.diagonal d)⁻¹ * (Matrix.diagonal d * Matrix.diagonal (fun i => (∏ j, d j) / d i)) := by
        rw [h2, h1]
    _ = Matrix.diagonal (fun i => (∏ j, d j) / d i) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]

theorem adj_M {m : ℕ} (s l : Fin m → ℂ) (hs : ∀ i, s i ≠ 0) (hl : ∀ i, l i ≠ 0) (Z : Matrix (Fin m) (Fin m) ℂ) :
    (Matrix.diagonal s * Z * Matrix.diagonal l).adjugate =
      Matrix.diagonal (fun i => (∏ j, l j) / l i) * Z.adjugate * Matrix.diagonal (fun i => (∏ j, s j) / s i) := by
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, adj_diag s hs, adj_diag l hl, Matrix.mul_assoc]

end Cof

section Place

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F F' : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem fix_famSc {H : Matrix (Fin n) (Fin n) ℂ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (he : ∀ a, H *ᵥ e a = e a) (hz : H *ᵥ z = z) (sc : ℝ) (a : Fin (r + 1)) :
    H *ᵥ famSc sc e z a = famSc sc e z a := by
  simp only [famSc, Matrix.mulVec_smul]
  congr 1
  induction a using Fin.lastCases with
  | last => simp only [fam, Fin.snoc_last, hz]
  | cast i => simp only [fam, Fin.snoc_castSucc, he]

theorem dl_top' (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Formalism.L2.SG.RealObj.Dl Z (r + 1) = Z.det := by
  simp [Formalism.L2.SG.RealObj.Dl, Fin.castLE_rfl]

theorem eN_ne_zero_and_eq_smul_of_unitary_column {k : ℕ} {M : Matrix (Fin k) (Fin k) ℂ} (hM : M ∈ Matrix.unitaryGroup (Fin k) ℂ) {i0 : Fin k}
    {nn : Fin k → ℂ} (h : M *ᵥ Pi.single i0 1 = ((eN nn)⁻¹ : ℂ) • nn) :
    eN nn ≠ 0 ∧ nn = (eN nn : ℂ) • (M *ᵥ Pi.single i0 1) := by
  have hne : eN nn ≠ 0 := by
    intro h0
    simp only [h0, Complex.ofReal_zero, _root_.inv_zero, zero_smul] at h
    have h1 : (star M * M) *ᵥ Pi.single i0 (1 : ℂ) = 0 := by
      rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
    rw [Matrix.mem_unitaryGroup_iff'.mp hM, Matrix.one_mulVec] at h1
    have h2 := congrFun h1 i0
    simp at h2
  refine ⟨hne, ?_⟩
  have hc : (eN nn : ℂ) ≠ 0 := by exact_mod_cast hne
  rw [h, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem sum_single_smul {k : ℕ} (i0 : Fin k) (d : ℂ) (w : Fin k → Fin n → ℂ) :
    ∑ i, (d • (Pi.single i0 (1 : ℂ) : Fin k → ℂ)) i • w i = d • w i0 := by
  simp [Pi.single_apply, ite_smul]

end Place

section Main

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F F' : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem transport_matrix_maps_basis (hT : TrHyp F Qm Qim c) {m₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hm : ∀ i, (Qm * m₀ * Qim) *ᵥ F'.wb i = F.wb i) (i : Fin k) :
    m₀ *ᵥ (Qim *ᵥ F'.wb i) = Qim *ᵥ F.wb i := by
  rw [← hm i]
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hT.h1, Matrix.one_mul]

theorem Qi_Q (hT : TrHyp F Qm Qim c) (x : Fin (2 * r + k + 1) → ℂ) : Qim *ᵥ (Qm *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, hT.h1, Matrix.one_mulVec]

theorem wc_smul (G : PtRepPf.Fr ε r k) (d : ℂ) (w : Fin n → ℂ) : wc G (d • w) = d • wc G w := by
  funext i
  simp only [wc, PtRepPf.hJ_smul_right, Pi.smul_apply, smul_eq_mul]

theorem sum_Qi (G : PtRepPf.Fr ε r k) (d : Fin k → ℂ) :
    Qim *ᵥ ∑ i, d i • G.wb i = ∑ i, d i • (Qim *ᵥ G.wb i) := by
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]

theorem bridge_place (hT : TrHyp F Qm Qim c) (hT' : TrHyp F' Qm Qim c) {sc : ℝ} (hsc : sc ≠ 0)
    {g gi H Hi H' H'i : Matrix (Fin n) (Fin n) ℂ} (hgi : g * gi = 1)
    (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε) (hHi : H * Hi = 1) (hiH : Hi * H = 1)
    (hHe : ∀ a, H *ᵥ F.e a = F.e a) (hHf : ∀ a, H *ᵥ F.fd a = F.fd a) (hHz : H *ᵥ F.z = F.z)
    (hH' : H'ᴴ * Formalism.REAL.Jm ε * H' = Formalism.REAL.Jm ε) (hH'i : H' * H'i = 1) (hiH' : H'i * H' = 1)
    (hH'e : ∀ a, H' *ᵥ F'.e a = F'.e a) (hH'f : ∀ a, H' *ᵥ F'.fd a = F'.fd a) (hH'z : H' *ᵥ F'.z = F'.z)
    {i0 : Fin k}
    (hD : Formalism.L2.SG.RealObj.IsDFrame ε (famSc sc F.e F.z) (famSc sc F'.e F'.z) g gi F.wb F'.wb i0 i0
      (mW F H) (mW F' H'))
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (Bs : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (hz : Bs.z = Qim *ᵥ F.z) (hz' : Bs.z' = Qim *ᵥ F'.z)
    (m₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hm : ∀ i, (Qm * m₀ * Qim) *ᵥ F'.wb i = F.wb i) :
    Formalism.FourierDecayAlt.D.IsDFrame Bs (Qim *ᵥ F'.wb i0) m₀ (Qim * (Hi * g * H') * Qm) := by
  obtain ⟨hMu, hM'u, h1, h2, h3⟩ := hD
  set f := famSc sc F.e F.z with hf
  set f' := famSc sc F'.e F'.z with hf'
  set Z := Formalism.L2.SG.RealObj.Zhat ε f f' g with hZdef
  set M := mW F H with hMdef
  set M' := mW F' H' with hM'def
  set L := lam c sc with hLdef
  have hL0 : ∀ a, L a ≠ 0 := lam_ne hT hsc
  have hs0 : ∀ a, star (L a) ≠ 0 := fun a => star_ne_zero.mpr (hL0 a)
  have hLl : L (Fin.last r) = 1 := lam_last c sc
  have hHf_ : ∀ a, H *ᵥ f a = f a := fix_famSc F.e F.z hHe hHz sc
  have hH'f_ : ∀ b, H' *ᵥ f' b = f' b := fix_famSc F'.e F'.z hH'e hH'z sc
  have hAf' : ∀ b, (Hi * g * H') *ᵥ f' b = Hi *ᵥ (g *ᵥ f' b) := fun b => by
    rw [← Matrix.mulVec_mulVec, hH'f_ b, Matrix.mulVec_mulVec]
  have hZA : Formalism.L2.SG.RealObj.Zhat ε f f' (Hi * g * H') = Z := by
    ext a b
    show hJ ε (f a) ((Hi * g * H') *ᵥ f' b) = hJ ε (f a) (g *ᵥ f' b)
    rw [hAf', ← fixed_left hH (hHf_ a) (Hi *ᵥ (g *ᵥ f' b)), Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec]
  have hZC : Formalism.QuantumDeterminants.Zhat k r Bs.z Bs.z' (Qim * (Hi * g * H') * Qm) =
      Matrix.diagonal (fun a => star (L a)) * Z * Matrix.diagonal L := by
    rw [hz, hz', zhat_cs hT hT' hsc, hZA]
  have hadj := adj_M (fun a => star (L a)) L hs0 hL0 Z
  set pL : ℂ := ∏ j, L j with hpL
  set pS : ℂ := ∏ j, star (L j) with hpS
  have hpLs : star pL = pS := by rw [hpL, hpS, star_prod]
  have hpSs : star pS = pL := by rw [hpL, hpS, star_prod]; simp
  have hdet : (Formalism.QuantumDeterminants.Zhat k r Bs.z Bs.z' (Qim * (Hi * g * H') * Qm)).det = pL * pS * Z.det := by
    rw [hZC, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
    ring
  have hDl : Formalism.L2.SG.RealObj.Dl Z (r + 1) = Z.det := dl_top' Z
  have hMM : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.mp hMu
  have hMM' : star M' * M' = 1 := Matrix.mem_unitaryGroup_iff'.mp hM'u
  refine ⟨?_, ?_, ?_⟩
  ·
    set x' := Formalism.L2.SG.RealObj.xPr Z g f' with hx'
    have hcof : Qm *ᵥ Formalism.FourierDecayAlt.D.cofR Bs (Qim * (Hi * g * H') * Qm) = (pL * pS) • (Hi *ᵥ x') := by
      unfold Formalism.FourierDecayAlt.D.cofR
      rw [hZC, hadj, hz', Matrix.mulVec_sum, hx']
      unfold Formalism.L2.SG.RealObj.xPr
      rw [Matrix.mulVec_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.mulVec_smul, Q_delta hT, Q_fvec hT' hsc, Matrix.mulVec_smul, hAf', Matrix.mulVec_smul, smul_smul,
        smul_smul]
      congr 1
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, hLl, star_one, div_one]
      field_simp [hL0 b]
      ring
    obtain ⟨hne, hnn⟩ := eN_ne_zero_and_eq_smul_of_unitary_column hMu h1
    set nn := (Formalism.L2.SG.RealObj.Dl Z (r + 1))⁻¹ • wCoord ε F.wb x' with hnndef
    have hD0 : Z.det ≠ 0 := by
      intro h0
      apply hne
      rw [hnndef, hDl, h0, _root_.inv_zero, zero_smul]
      simp [eN]
    have hwc : wc F x' = Z.det • nn := by
      rw [hnndef, hDl, smul_smul, mul_inv_cancel₀ hD0, one_smul]
      rfl
    have hMnn : star M *ᵥ nn = (eN nn : ℂ) • (Pi.single i0 1 : Fin k → ℂ) := by
      conv_lhs => rw [hnn]
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
    have hcoord : wc F (Hi *ᵥ x') = (Z.det * (eN nn : ℂ)) • (Pi.single i0 1 : Fin k → ℂ) := by
      rw [wc_inv F hH hHi hHe hHf hHz, hwc, Matrix.mulVec_smul, ← Matrix.star_eq_conjTranspose, hMnn, smul_smul]
    refine ⟨eN nn, lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hne), ?_⟩
    rw [hdet, ← Qi_Q hT (Formalism.FourierDecayAlt.D.cofR Bs _), hcof, hz, prW_Qi hT, wc_smul, hcoord, smul_smul, sum_single_smul,
      transport_matrix_maps_basis hT hm, Matrix.mulVec_smul]
    congr 1
    ring
  ·
    set xu := Formalism.L2.SG.RealObj.xUn Z f with hxu
    have hAAi : (Hi * g * H') * (H'i * gi * H) = 1 := by
      calc (Hi * g * H') * (H'i * gi * H) = Hi * (g * ((H' * H'i) * (gi * H))) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hH'i, Matrix.one_mul, ← Matrix.mul_assoc g gi H, hgi, Matrix.one_mul, hiH]
    have hinv : (Qim * (Hi * g * H') * Qm)⁻¹ = Qim * (H'i * gi * H) * Qm := by
      apply Matrix.inv_eq_right_inv
      calc Qim * (Hi * g * H') * Qm * (Qim * (H'i * gi * H) * Qm)
          = Qim * ((Hi * g * H') * ((Qm * Qim) * ((H'i * gi * H) * Qm))) := by simp only [Matrix.mul_assoc]
        _ = 1 := by
          rw [hT.h2, Matrix.one_mul, ← Matrix.mul_assoc (Hi * g * H') (H'i * gi * H) Qm, hAAi, Matrix.one_mul, hT.h1]
    have hcofL : Qm *ᵥ Formalism.FourierDecayAlt.D.cofL Bs (Qim * (Hi * g * H') * Qm) = (pL * pS) • xu := by
      unfold Formalism.FourierDecayAlt.D.cofL
      rw [hZC, hadj, hz, Matrix.mulVec_sum, hxu]
      unfold Formalism.L2.SG.RealObj.xUn
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Matrix.mulVec_smul, Q_fvec hT hsc, smul_smul, smul_smul]
      congr 1
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, hLl, div_one, map_mul, map_div₀, starRingEnd_apply,
        star_star, hpLs, hpSs]
      field_simp [hL0 a]
      ring
    have hHxu : H *ᵥ xu = xu := by
      rw [hxu]
      unfold Formalism.L2.SG.RealObj.xUn
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, hHf_]
    have hQdi : Qm *ᵥ ((Qim * (H'i * gi * H) * Qm) *ᵥ Formalism.FourierDecayAlt.D.cofL Bs (Qim * (Hi * g * H') * Qm)) =
        (pL * pS) • (H'i *ᵥ (gi *ᵥ xu)) := by
      rw [Q_delta hT, hcofL, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hHxu]
    obtain ⟨hne', hnn'⟩ := eN_ne_zero_and_eq_smul_of_unitary_column hM'u h2
    set nn' := (star (Formalism.L2.SG.RealObj.Dl Z (r + 1)))⁻¹ • wCoord ε F'.wb (gi *ᵥ xu) with hnndef'
    have hD0 : Z.det ≠ 0 := by
      intro h0
      apply hne'
      rw [hnndef', hDl, h0, star_zero, _root_.inv_zero, zero_smul]
      simp [eN]
    have hsD0 : star Z.det ≠ 0 := star_ne_zero.mpr hD0
    have hwc' : wc F' (gi *ᵥ xu) = star Z.det • nn' := by
      rw [hnndef', hDl, smul_smul, mul_inv_cancel₀ hsD0, one_smul]
      rfl
    have hMnn' : star M' *ᵥ nn' = (eN nn' : ℂ) • (Pi.single i0 1 : Fin k → ℂ) := by
      conv_lhs => rw [hnn']
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]
    have hcoord' : wc F' (H'i *ᵥ (gi *ᵥ xu)) = (star Z.det * (eN nn' : ℂ)) • (Pi.single i0 1 : Fin k → ℂ) := by
      rw [wc_inv F' hH' hH'i hH'e hH'f hH'z, hwc', Matrix.mulVec_smul, ← Matrix.star_eq_conjTranspose, hMnn', smul_smul]
    refine ⟨eN nn', lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hne'), ?_⟩
    rw [hdet, hinv, ← Qi_Q hT ((Qim * (H'i * gi * H) * Qm) *ᵥ Formalism.FourierDecayAlt.D.cofL Bs (Qim * (Hi * g * H') * Qm)), hQdi,
      hz', prW_Qi hT', wc_smul, hcoord', smul_smul, sum_single_smul, Matrix.mulVec_smul]
    congr 1
    simp only [map_mul, starRingEnd_apply, hpLs, hpSs]
    ring
  ·
    intro u hu
    set y := Qm *ᵥ u with hy
    have hu' : u = Qim *ᵥ y := (Qi_Q hT u).symm
    have hfy : ∀ a, hJ ε (f a) y = 0 := fun a => by
      have := (hu a).1
      rw [herm_Q hT, hz, Q_fvec hT hsc, PtRepPf.hJ_smul_left] at this
      exact (mul_eq_zero.mp this).resolve_left (hs0 a)
    have hgy : ∀ b, hJ ε (g *ᵥ f' b) (H *ᵥ y) = 0 := fun b => by
      have := (hu b).2
      rw [herm_Q hT, hz', Q_delta hT, Q_fvec hT' hsc, Matrix.mulVec_smul, PtRepPf.hJ_smul_left, hAf'] at this
      have h0 := (mul_eq_zero.mp this).resolve_left (hs0 b)
      rw [← isom hH, Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec] at h0
      exact h0
    have hfHy : ∀ a, hJ ε (f a) (H *ᵥ y) = 0 := fun a => by rw [fixed_left hH (hHf_ a), hfy a]
    have hR := h3 (H *ᵥ y) hfHy hgy
    have hWy : wc F (H *ᵥ y) = M *ᵥ wc F y := wc_fwd F hH hHi hiH hHe hHf hHz hMu y
    have e1 : M *ᵥ (star M' *ᵥ wc F' (gi *ᵥ (H *ᵥ y))) = M *ᵥ wc F y := by rw [← hWy]; exact hR
    have e2 : (star M * M) *ᵥ (star M' *ᵥ wc F' (gi *ᵥ (H *ᵥ y))) = (star M * M) *ᵥ wc F y := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1]
    rw [hMM, Matrix.one_mulVec, Matrix.one_mulVec] at e2
    have hAi : (Qim * (Hi * g * H') * Qm)⁻¹ = Qim * (H'i * gi * H) * Qm := by
      apply Matrix.inv_eq_right_inv
      have hAAi : (Hi * g * H') * (H'i * gi * H) = 1 := by
        calc (Hi * g * H') * (H'i * gi * H) = Hi * (g * ((H' * H'i) * (gi * H))) := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hH'i, Matrix.one_mul, ← Matrix.mul_assoc g gi H, hgi, Matrix.one_mul, hiH]
      calc Qim * (Hi * g * H') * Qm * (Qim * (H'i * gi * H) * Qm)
          = Qim * ((Hi * g * H') * ((Qm * Qim) * ((H'i * gi * H) * Qm))) := by simp only [Matrix.mul_assoc]
        _ = 1 := by
          rw [hT.h2, Matrix.one_mul, ← Matrix.mul_assoc (Hi * g * H') (H'i * gi * H) Qm, hAAi, Matrix.one_mul, hT.h1]
    have hδy : (Qim * (H'i * gi * H) * Qm) *ᵥ (Qim *ᵥ y) = Qim *ᵥ (H'i *ᵥ (gi *ᵥ (H *ᵥ y))) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (Qim * (H'i * gi * H)) Qm Qim, hT.h2, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hAi, hu', hδy, hz, hz', prW_Qi hT, prW_Qi hT', wc_inv F' hH' hH'i hH'e hH'f hH'z,
      ← Matrix.star_eq_conjTranspose, e2, sum_Qi F', Matrix.mulVec_sum, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, transport_matrix_maps_basis hT hm]

end Main

end Formalism.L2.SG.Pf.Bridge
