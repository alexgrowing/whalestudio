import Mathlib
import Formalism.LocalToGlobal.Columns.BrpStarLatLattice

open MvPolynomial NumberField
open scoped Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

section Scale

variable {K σ : Type} [Field K] [Fintype σ]

theorem brp_aeval_scale_monomial (m : σ →₀ ℕ) (c t : K) :
    aeval (fun v => C t * X v) (monomial m c) = t ^ (m.sum fun _ e => e) • monomial m c := by
  rw [aeval_monomial, monomial_eq, smul_eq_C_mul, algebraMap_eq]
  simp only [mul_pow, Finsupp.prod_mul]
  have h : (m.prod fun _ e => (C t : MvPolynomial σ K) ^ e) = C (t ^ (m.sum fun _ e => e)) := by
    simp only [Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum, map_pow]
  rw [h, map_pow]
  ring

theorem brp_aeval_scale_whom {r n : ℕ} (ν : Fin n → ℕ) (Q : MvPolynomial (Fin r × Fin n) K)
    (hQ : Q ∈ weightedHomogeneousSubmodule K (Formalism.GradedWeylDivisibility.colW r n) ν) (t : K) :
    aeval (fun v => C t * X v) Q = t ^ (∑ s, ν s) • Q := by
  have hQ' : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) Q ν := by
    simpa [mem_weightedHomogeneousSubmodule] using hQ
  have hdeg : ∀ m ∈ Q.support, (m.sum fun _ e => e) = ∑ s, ν s := by
    intro m hm
    rw [← hQ' (mem_support_iff.mp hm)]
    simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [Pi.single_apply]
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [brp_aeval_scale_monomial, hdeg m hm]

end Scale

section Scalar

variable (K : Type) [Field K] {n : ℕ}

def brpSc (t : Kˣ) : GL (Fin n) K := Units.map (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom t

theorem brpSc_coe (t : Kˣ) : ((brpSc K t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (t : K) • 1 := by
  show algebraMap K (Matrix (Fin n) (Fin n) K) (t : K) = _
  exact Algebra.algebraMap_eq_smul_one _

theorem brp_natW_cast (lam : DomWeight n) (i : Fin n) : ((lam.natW i : ℕ) : ℤ) = lam.w i - lam.detShift := by
  have hn : 0 < n := Fin.pos i
  have h : lam.detShift ≤ lam.w i := by
    rw [DomWeight.detShift, dif_pos hn]
    exact lam.anti (show i ≤ ⟨n - 1, by omega⟩ from Fin.le_iff_val_le_val.mpr (by simp; omega))
  simp only [DomWeight.natW]
  exact Int.toNat_of_nonneg (by omega)

theorem brp_wsum (lam : DomWeight n) :
    (∑ i, lam.w i) = ((∑ i, lam.natW i : ℕ) : ℤ) + n * lam.detShift := by
  push_cast
  simp only [brp_natW_cast, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem brp_blockAct_scalar (t : K) :
    Formalism.GradedWeylDivisibility.blockAct K (S := Unit) (k := n) (n := n) (fun _ => ((t • 1 : Matrix (Fin n) (Fin n) K))ᵀ) =
      aeval fun v => C t * X v := by
  unfold Formalism.GradedWeylDivisibility.blockAct
  congr 1
  funext v
  rw [Finset.sum_eq_single v.2.1]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply_ne hb]
  · simp

theorem brp_aeval_scale_rename {σ τ : Type} (f : σ → τ) (t : K) (Q : MvPolynomial σ K) :
    aeval (fun v => C t * X v) (rename f Q) = rename f (aeval (fun v => C t * X v) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, rename_X, aeval_X, rename_C, hp]

theorem brp_trAct_scalar (lam : DomWeight n) (t : Kˣ) (F : Pol K Unit n) (hF : F ∈ VV K (oneW lam)) :
    trAct (fun _ : Unit => brpSc K t) F = (t : K) ^ (∑ i, lam.natW i) • F := by
  unfold trAct
  simp only [brpSc_coe]
  rw [brp_blockAct_scalar]
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨G, hG, rfl⟩ := hP
    rw [Fintype.prod_unique]
    unfold Formalism.GradedWeylDivisibility.blockEmb
    have hW : G default ∈ weightedHomogeneousSubmodule K (Formalism.GradedWeylDivisibility.colW n n) lam.natW :=
      (Submodule.mem_inf.1 (hG default)).1
    rw [brp_aeval_scale_rename, brp_aeval_scale_whom _ _ hW, map_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

end Scalar

section Chi

variable (K : Type) [Field K] {n : ℕ}

def brpConst : GL (Fin n) K →* (Unit → GL (Fin n) K) := MonoidHom.pi fun _ => MonoidHom.id _

def chiW (lam : DomWeight n) : GL (Fin n) K →* K :=
  (LinearMap.det : Module.End K (VV K (oneW lam)) →* K).comp ((rhoK (oneW lam)).comp (brpConst K))

theorem chiW_apply (lam : DomWeight n) (g : GL (Fin n) K) :
    chiW K lam g = LinearMap.det (rhoK (oneW lam) (fun _ => g)) := rfl

theorem chiW_ne_zero (lam : DomWeight n) (g : GL (Fin n) K) : chiW K lam g ≠ 0 := ((Group.isUnit g).map (chiW K lam)).ne_zero

def wsum (lam : DomWeight n) : ℤ := ∑ i, lam.w i

theorem brp_detTwK_scalar (lam : DomWeight n) (t : Kˣ) :
    detTwK (oneW lam) (fun _ : Unit => brpSc K t) = (t : K) ^ ((n : ℤ) * lam.detShift) := by
  have hdet : Matrix.GeneralLinearGroup.det (brpSc K t : GL (Fin n) K) = t ^ n := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, brpSc_coe, Matrix.det_smul]
  simp only [detTwK, detPow, Finset.univ_unique, Finset.prod_singleton, hdet]
  rw [← zpow_natCast, ← zpow_mul, Units.val_zpow_eq_zpow_val]

theorem rhoK_scalar (lam : DomWeight n) (t : Kˣ) :
    rhoK (oneW lam) (fun _ => brpSc K t) = ((t : K) ^ wsum lam) • (1 : Module.End K (VV K (oneW lam))) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  show actP (oneW lam) (fun _ => brpSc K t) F.1 = _
  rw [LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul, actP, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply, brp_trAct_scalar K lam t F.1 F.2, brp_detTwK_scalar, smul_smul]
  congr 1
  rw [wsum, brp_wsum, zpow_add₀ (Units.ne_zero t), zpow_natCast]
  ring

theorem chiW_scalar (lam : DomWeight n) (t : Kˣ) :
    chiW K lam (brpSc K t) = (t : K) ^ (wsum lam * (Module.finrank K (VV K (oneW lam)) : ℤ)) := by
  rw [chiW_apply, rhoK_scalar, LinearMap.det_smul, map_one, mul_one, zpow_mul, zpow_natCast]

end Chi

section ChiPow

variable (K : Type) [Field K] [CharZero K] {n : ℕ}

def brpGL (M : Matrix (Fin n) (Fin n) K) (h : IsUnit M.det) : GL (Fin n) K := Matrix.nonsingInvUnit M h

theorem brpGL_coe (M : Matrix (Fin n) (Fin n) K) (h : IsUnit M.det) : ((brpGL K M h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = M := rfl

theorem brp_isUnit_transvection (i j : Fin n) (hij : i ≠ j) (c : K) : IsUnit (Matrix.transvection i j c).det := by
  rw [Matrix.det_transvection_of_ne _ _ hij]
  exact isUnit_one

theorem brp_diag_transvection (i j : Fin n) (hij : i ≠ j) (c : K) :
    Matrix.diagonal (Function.update (1 : Fin n → K) i 2) * Matrix.transvection i j c =
      Matrix.transvection i j (2 * c) * Matrix.diagonal (Function.update (1 : Fin n → K) i 2) := by
  have h1 : Matrix.diagonal (Function.update (1 : Fin n → K) i 2) * Matrix.single i j c =
      Matrix.single i j (2 * c) := by
    ext a b
    rw [Matrix.diagonal_mul]
    by_cases ha : a = i
    · subst ha
      by_cases hb : j = b <;> simp [Matrix.single_apply, hb]
    · simp [Matrix.single_apply, ha, Ne.symm ha]
  have h2 : Matrix.single i j (2 * c) * Matrix.diagonal (Function.update (1 : Fin n → K) i 2) =
      Matrix.single i j (2 * c) := by
    ext a b
    rw [Matrix.mul_diagonal]
    by_cases hb : b = j
    · subst hb
      simp [Function.update_apply, Ne.symm hij]
    · simp [Matrix.single_apply, Ne.symm hb]
  rw [Matrix.transvection, Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, h1, h2]

theorem chiW_transvection (lam : DomWeight n) (i j : Fin n) (hij : i ≠ j) (c : K) :
    chiW K lam (brpGL K (Matrix.transvection i j c) (brp_isUnit_transvection K i j hij c)) = 1 := by
  have hD : IsUnit (Matrix.diagonal (Function.update (1 : Fin n → K) i 2)).det := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  set T : K → GL (Fin n) K := fun c => brpGL K (Matrix.transvection i j c) (brp_isUnit_transvection K i j hij c)
    with hT
  have hconj : brpGL K _ hD * T c = T (2 * c) * brpGL K _ hD := by
    apply Units.ext
    simp only [Units.val_mul, hT, brpGL_coe]
    exact brp_diag_transvection K i j hij c
  have hsq : T c * T c = T (2 * c) := by
    apply Units.ext
    simp only [Units.val_mul, hT, brpGL_coe]
    simp [Matrix.transvection_mul_transvection_same, hij, two_mul]
  have e1 : chiW K lam (T c) = chiW K lam (T (2 * c)) := by
    have h := congrArg (chiW K lam) hconj
    rw [map_mul, map_mul, mul_comm (chiW K lam (T (2 * c)))] at h
    exact mul_left_cancel₀ (chiW_ne_zero K lam _) h
  have e2 : chiW K lam (T c) * chiW K lam (T c) = chiW K lam (T c) := by
    rw [← map_mul, hsq, ← e1]
  exact mul_left_cancel₀ (chiW_ne_zero K lam (T c)) (by rw [e2, mul_one])

def brpDiag : (Fin n → Kˣ) →* GL (Fin n) K :=
  (Units.map (Matrix.diagonalRingHom (Fin n) K).toMonoidHom).comp (MulEquiv.piUnits.symm.toMonoidHom)

theorem brpDiag_coe (d : Fin n → Kˣ) :
    ((brpDiag K d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun a => (d a : K) := by rfl

end ChiPow

section ChiPow2

variable (K : Type) [Field K] [CharZero K] {n : ℕ}

theorem brp_isUnit_perm (σ : Equiv.Perm (Fin n)) : IsUnit (Equiv.Perm.permMatrix K σ).det := by
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem brp_perm_diag (σ : Equiv.Perm (Fin n)) (f : Fin n → K) :
    Equiv.Perm.permMatrix K σ * Matrix.diagonal f = Matrix.diagonal (f ∘ σ) * Equiv.Perm.permMatrix K σ := by
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply]
  by_cases h : σ a = b
  · subst h
    exact mul_comm _ _
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]

theorem chiW_single_eq (lam : DomWeight n) (a b : Fin n) (t : Kˣ) :
    chiW K lam (brpDiag K (Pi.mulSingle a t)) = chiW K lam (brpDiag K (Pi.mulSingle b t)) := by
  set P := brpGL K (Equiv.Perm.permMatrix K (Equiv.swap a b)) (brp_isUnit_perm K _) with hP
  have hc : P * brpDiag K (Pi.mulSingle a t) = brpDiag K (Pi.mulSingle b t) * P := by
    apply Units.ext
    simp only [Units.val_mul, hP, brpGL_coe, brpDiag_coe]
    rw [brp_perm_diag]
    congr 2
    funext x
    simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  have h := congrArg (chiW K lam) hc
  rw [map_mul, map_mul, mul_comm (chiW K lam (brpDiag K (Pi.mulSingle b t)))] at h
  exact mul_left_cancel₀ (chiW_ne_zero K lam P) h

end ChiPow2

section ChiPow3

variable (K : Type) [Field K] [CharZero K] {n : ℕ}

theorem brpDiag_const (t : Kˣ) : brpDiag K (n := n) (fun _ => t) = brpSc K t := by
  apply Units.ext
  rw [brpDiag_coe, brpSc_coe, Matrix.smul_one_eq_diagonal]

abbrev dimW (lam : DomWeight n) : ℕ := Module.finrank K (VV K (oneW lam))

theorem chiW_diag_pow (lam : DomWeight n) (d : Fin n → Kˣ) :
    chiW K lam (brpDiag K d) ^ n = (∏ a, (d a : K)) ^ (wsum lam * (dimW K lam : ℤ)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · let g : Kˣ →* K :=
      ((chiW K lam).comp (brpDiag K)).comp (MonoidHom.mulSingle (fun _ : Fin n => Kˣ) ⟨0, hn⟩)
    have hg : ∀ a (u : Kˣ), chiW K lam (brpDiag K (Pi.mulSingle a u)) = g u := fun a u =>
      chiW_single_eq K lam a ⟨0, hn⟩ u
    have hprod : ∀ e : Fin n → Kˣ, chiW K lam (brpDiag K e) = ∏ a, g (e a) := by
      intro e
      conv_lhs => rw [← Finset.univ_prod_mulSingle e]
      rw [← MonoidHom.comp_apply (chiW K lam) (brpDiag K), map_prod]
      simp only [MonoidHom.comp_apply, hg]
    have hpow : ∀ u : Kˣ, g u ^ n = (u : K) ^ (wsum lam * (dimW K lam : ℤ)) := by
      intro u
      have h := hprod (fun _ => u)
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, brpDiag_const, chiW_scalar] at h
      exact h.symm
    rw [hprod, ← map_prod g d, hpow, Units.coe_prod]

theorem chiW_list_transvec (lam : DomWeight n) (L : List (Matrix.TransvectionStruct (Fin n) K)) :
    chiW K lam (L.map fun t => brpGL K t.toMatrix (by rw [t.det]; exact isUnit_one)).prod = 1 := by
  induction L with
  | nil => simp
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih, mul_one]
    exact chiW_transvection K lam t.i t.j t.hij t.c

theorem brp_coe_list_transvec (L : List (Matrix.TransvectionStruct (Fin n) K)) :
    (((L.map fun t => brpGL K t.toMatrix (by rw [t.det]; exact isUnit_one)).prod : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (L.map Matrix.TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => simp
  | cons t L ih => rw [List.map_cons, List.prod_cons, Units.val_mul, ih, brpGL_coe, List.map_cons, List.prod_cons]

theorem brp_det_list_transvec (L : List (Matrix.TransvectionStruct (Fin n) K)) :
    (L.map Matrix.TransvectionStruct.toMatrix).prod.det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih => rw [List.map_cons, List.prod_cons, Matrix.det_mul, ih, t.det, one_mul]

theorem chiW_pow (lam : DomWeight n) (g : GL (Fin n) K) :
    chiW K lam g ^ n = ((g : Matrix (Fin n) (Fin n) K).det) ^ (wsum lam * (dimW K lam : ℤ)) := by
  obtain ⟨L, L', D, hM⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (g : Matrix (Fin n) (Fin n) K)
  have hdetD : (Matrix.diagonal D).det = (g : Matrix (Fin n) (Fin n) K).det := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, brp_det_list_transvec, brp_det_list_transvec, one_mul, mul_one]
  have hunit : ∀ a, IsUnit (D a) := by
    intro a
    have hg : IsUnit (g : Matrix (Fin n) (Fin n) K).det := Matrix.isUnits_det_units g
    rw [← hdetD, Matrix.det_diagonal] at hg
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem D (Finset.mem_univ a)) hg
  let d : Fin n → Kˣ := fun a => (hunit a).unit
  have hDd : Matrix.diagonal D = Matrix.diagonal fun a => (d a : K) := by
    simp [d]
  have hg : g = (L.map fun t => brpGL K t.toMatrix (by rw [t.det]; exact isUnit_one)).prod * brpDiag K d *
      (L'.map fun t => brpGL K t.toMatrix (by rw [t.det]; exact isUnit_one)).prod := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, brp_coe_list_transvec, brp_coe_list_transvec, brpDiag_coe, ← hDd, hM]
  rw [← hdetD, hDd, Matrix.det_diagonal, hg, map_mul, map_mul, chiW_list_transvec, chiW_list_transvec, one_mul,
    mul_one, chiW_diag_pow]

end ChiPow3

end Formalism.L2.Col
