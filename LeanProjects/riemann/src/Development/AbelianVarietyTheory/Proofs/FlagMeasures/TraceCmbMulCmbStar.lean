import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwConst.Adapted

variable {n a b c e : ℕ}

theorem trace_cmb_mul_cmb {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {F : Fin b → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i k, (E i * F k).trace = 0) (x : Fin a → ℝ) (y : Fin b → ℝ) : (cmb E x * cmb F y).trace = 0 := by
  simp [cmb, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, h]

theorem trace_cmb_mul_cmb_star {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {F : Fin b → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i k, (E i * (F k)ᴴ).trace = 0) (x : Fin a → ℝ) (y : Fin b → ℝ) : (cmb E x * (cmb F y)ᴴ).trace = 0 := by
  simp [cmb, Matrix.conjTranspose_sum, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, h]

theorem trace_star_star (X Y : Matrix (Fin n) (Fin n) ℂ) (h : (X * Y).trace = 0) : (Xᴴ * Yᴴ).trace = 0 := by
  rw [← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose, Matrix.trace_mul_comm, h, star_zero]

theorem hs_neg_star (X : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs (-Xᴴ) = Formalism.REAL.hs X := by
  rw [← nrm_sq, ← nrm_sq, nrm_neg, nrm_conjTranspose]

theorem hs_three {EN : Fin a → Matrix (Fin n) (Fin n) ℂ} {EM : Fin b → Matrix (Fin n) (Fin n) ℂ}
    (hN : IsON EN) (hM : IsON EM) (h1 : ∀ i k, (EN i * (EM k)ᴴ).trace = 0) (h2 : ∀ i k, (EN i * EM k).trace = 0)
    (h3 : ∀ i k, (EN i * EN k).trace = 0) (x u : Fin a → ℝ) (y : Fin b → ℝ) :
    Formalism.REAL.hs (cmb EN x + cmb EM y + -(cmb EN u)ᴴ) = ∑ i, x i ^ 2 + ∑ i, y i ^ 2 + ∑ i, u i ^ 2 := by
  have e2 : (cmb EM y * cmb EN u).trace = 0 := by
    rw [Matrix.trace_mul_comm]; exact trace_cmb_mul_cmb h2 u y
  rw [hs_add, hs_add, hs_neg_star, hs_cmb hN, hs_cmb hM, hs_cmb hN, trace_cmb_mul_cmb_star h1]
  simp [Matrix.add_mul, trace_cmb_mul_cmb h3, e2]

def cmbL (E : Fin a → Matrix (Fin n) (Fin n) ℂ) : (Fin a → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := cmb E
  map_add' := cmb_add E
  map_smul' := cmb_smul E

def crdL (E : Fin a → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin a → ℝ) where
  toFun := crd E
  map_add' := crd_add E
  map_smul' := crd_smul E

def adp (EN : Fin a → Matrix (Fin n) (Fin n) ℂ) (EL : Fin e → Matrix (Fin n) (Fin n) ℂ) :
    ((Fin a → ℝ) × (Fin e → ℝ)) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun v := cmb EN ((Real.sqrt 2)⁻¹ • v.1) - (cmb EN ((Real.sqrt 2)⁻¹ • v.1))ᴴ + cmb EL v.2
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, smul_add, cmb_add, Matrix.conjTranspose_add]; abel
  map_smul' r v := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_comm (Real.sqrt 2)⁻¹ r, cmb_smul EN r, cmb_smul EL r,
      Matrix.conjTranspose_smul, star_trivial, RingHom.id_apply, smul_add, smul_sub]

theorem cmb_mem_of {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (h : ∀ i, E i ∈ S) (x : Fin a → ℝ) : cmb E x ∈ S :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h i)

theorem cmb_sub_star_mem {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (h : ∀ i, E i - (E i)ᴴ ∈ S) (x : Fin a → ℝ) : cmb E x - (cmb E x)ᴴ ∈ S := by
  have : cmb E x - (cmb E x)ᴴ = cmb (fun i => E i - (E i)ᴴ) x := by
    simp [cmb, Matrix.conjTranspose_sum, smul_sub, Finset.sum_sub_distrib]
  rw [this]; exact cmb_mem_of h x

theorem sum_sq_half (w : Fin a → ℝ) : ∑ i, ((Real.sqrt 2)⁻¹ • w) i ^ 2 = ∑ i, w i ^ 2 / 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt (by norm_num)]
  ring

theorem exists_adapted (n : ℕ) (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ)
    (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ)
    (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ) (hN : IsON EN) (hM : IsON EM) (hK : IsON EK) (hL : IsON EL)
    (hR : LieRel EN EM EK EL) (hd : dK = dN + dL) :
    ∃ (Q : (Fin dK → ℝ) →ₗ[ℝ] (Fin dN → ℝ) × (Fin dL → ℝ)) (ι : (Fin dL → ℝ) →ₗ[ℝ] (Fin dM → ℝ)),
      (∀ z, ∑ i, (Q z).1 i ^ 2 + ∑ i, (Q z).2 i ^ 2 = ∑ i, z i ^ 2) ∧
      ∀ x y z, Formalism.REAL.hs (cmb EN x + cmb EM y + cmb EK z) =
        ∑ i, (x i + (Q z).1 i / Real.sqrt 2) ^ 2 + ∑ i, (y i + ι (Q z).2 i) ^ 2 + ∑ i, (Q z).1 i ^ 2 / 2 ∧
        crd EL (cmb EK z) = (Q z).2 := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := hR
  have hι : ∀ t, cmb EM (crd EM (cmb EL t)) = cmb EL t := fun t => cmb_crd hM (cmb_mem_of h4 t)
  have hmem : ∀ v, adp EN EL v ∈ Submodule.span ℝ (Set.range EK) := fun v =>
    Submodule.add_mem _ (cmb_sub_star_mem h7 _) (cmb_mem_of h5 _)
  have hsum : ∀ x y v, Formalism.REAL.hs (cmb EN x + cmb EM y + adp EN EL v) =
      ∑ i, (x i + v.1 i / Real.sqrt 2) ^ 2 + ∑ i, (y i + crd EM (cmb EL v.2) i) ^ 2 + ∑ i, v.1 i ^ 2 / 2 := by
    intro x y v
    have e : cmb EN x + cmb EM y + adp EN EL v = cmb EN (x + (Real.sqrt 2)⁻¹ • v.1) +
        cmb EM (y + crd EM (cmb EL v.2)) + -(cmb EN ((Real.sqrt 2)⁻¹ • v.1))ᴴ := by
      rw [cmb_add, cmb_add, hι]
      simp only [adp, LinearMap.coe_mk, AddHom.coe_mk]
      abel
    rw [e, hs_three hN hM h1 h2 h3, sum_sq_half]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have hhs : ∀ v, Formalism.REAL.hs (adp EN EL v) = ∑ i, v.1 i ^ 2 + ∑ i, v.2 i ^ 2 := by
    intro v
    have e : adp EN EL v = cmb EN ((Real.sqrt 2)⁻¹ • v.1) +
        cmb EM (crd EM (cmb EL v.2)) + -(cmb EN ((Real.sqrt 2)⁻¹ • v.1))ᴴ := by
      rw [hι]
      simp only [adp, LinearMap.coe_mk, AddHom.coe_mk]
      abel
    rw [e, hs_three hN hM h1 h2 h3, sum_sq_half, ← hs_cmb hM, hι, hs_cmb hL, ← Finset.sum_div]
    ring
  let T : ((Fin dN → ℝ) × (Fin dL → ℝ)) →ₗ[ℝ] (Fin dK → ℝ) := (crdL EK).comp (adp EN EL)
  have hT : ∀ v, cmb EK (T v) = adp EN EL v := fun v => cmb_crd hK (hmem v)
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h := hhs v
    rw [← hT, hv, hs_cmb hK] at h
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h
    have p1 : 0 ≤ ∑ i, v.1 i ^ 2 := by positivity
    have p2 : 0 ≤ ∑ i, v.2 i ^ 2 := by positivity
    have q1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v.1 i)).1
      (show ∑ i, v.1 i ^ 2 = 0 by linarith)
    have q2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v.2 i)).1
      (show ∑ i, v.2 i ^ 2 = 0 by linarith)
    ext i
    · exact pow_eq_zero_iff two_ne_zero |>.1 (q1 i (Finset.mem_univ i))
    · exact pow_eq_zero_iff two_ne_zero |>.1 (q2 i (Finset.mem_univ i))
  have hdim : Module.finrank ℝ ((Fin dN → ℝ) × (Fin dL → ℝ)) = Module.finrank ℝ (Fin dK → ℝ) := by
    simp [hd]
  let U := LinearMap.linearEquivOfInjective T hinj hdim
  have hU : ∀ z, cmb EK z = adp EN EL (U.symm z) := by
    intro z
    rw [← hT]
    congr 1
    exact (U.apply_symm_apply z).symm
  refine ⟨U.symm.toLinearMap, (crdL EM).comp (cmbL EL), fun z => ?_, fun x y z => ⟨?_, ?_⟩⟩
  · rw [← hs_cmb hK z, hU, hhs]; rfl
  · rw [hU, hsum]; rfl
  · rw [hU]
    change crd EL (_ - _ + _) = (U.symm z).2
    rw [crd_add, crd_cmb hL, add_eq_right]
    funext i
    simp only [crd, Pi.zero_apply]
    rw [← cmb_crd hM (h4 i), Matrix.sub_mul, Matrix.trace_sub, trace_cmb_mul_cmb_star h1,
      trace_star_star _ _ (trace_cmb_mul_cmb h2 _ _)]
    simp

end GlobalTheory.IwConst.Adapted
