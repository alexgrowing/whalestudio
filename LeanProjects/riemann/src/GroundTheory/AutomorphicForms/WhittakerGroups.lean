import Mathlib
import GroundTheory.AutomorphicForms.FiniteBruhat
import GroundTheory.AutomorphicForms.Iwasawa
import GroundTheory.AutomorphicForms.GLnLocal
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.MeasuresModulus
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.NormZpow

namespace GroundTheory.Automorphic

namespace Whittaker

open Matrix DoubleCoset

section Algebra

variable {F : Type*} [Field F] {n : ℕ}

def superdiagSum (M : Matrix (Fin n) (Fin n) F) : F :=
  ∑ i : Fin n, ∑ j : Fin n, if j.val = i.val + 1 then M i j else 0

theorem mul_apply_of_val_eq_succ {u v : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n)
    (hv : v ∈ Iwasawa.unipotent F n) {i j : Fin n} (hij : j.val = i.val + 1) :
    ((u * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (u : Matrix (Fin n) (Fin n) F) i j + (v : Matrix (Fin n) (Fin n) F) i j := by
  rw [Units.val_mul, Matrix.mul_apply]
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have key : ∀ k : Fin n, (u : Matrix (Fin n) (Fin n) F) i k * (v : Matrix (Fin n) (Fin n) F) k j =
      (if k = i then (v : Matrix (Fin n) (Fin n) F) i j else 0) +
        (if k = j then (u : Matrix (Fin n) (Fin n) F) i j else 0) := by
    intro k
    by_cases hki : k = i
    · subst hki
      rw [if_pos rfl, if_neg hne, hu.2 k, one_mul, add_zero]
    by_cases hkj : k = j
    · subst hkj
      rw [if_neg hki, if_pos rfl, hv.2 k, mul_one, zero_add]
    rw [if_neg hki, if_neg hkj, add_zero]
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · rw [hu.1 hlt, zero_mul]
    · have : j < k := by
        have h1 : i.val < k.val := hgt
        have h2 : k.val ≠ j.val := fun h => hkj (Fin.ext h)
        show j.val < k.val
        omega
      rw [hv.1 this, mul_zero]
  rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), add_comm]

theorem superdiagSum_mul {u v : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n)
    (hv : v ∈ Iwasawa.unipotent F n) :
    superdiagSum ((u * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      superdiagSum (u : Matrix (Fin n) (Fin n) F) + superdiagSum (v : Matrix (Fin n) (Fin n) F) := by
  unfold superdiagSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · exact mul_apply_of_val_eq_succ hu hv h
  · rw [add_zero]

theorem superdiagSum_one : superdiagSum (1 : Matrix (Fin n) (Fin n) F) = 0 := by
  unfold superdiagSum
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · exact Matrix.one_apply_ne (fun e => by rw [e] at h; omega)
  · rfl

def psiN (ψ₀ : AddChar F ℂ) (g : GL (Fin n) F) : ℂ :=
  ψ₀ (superdiagSum (g : Matrix (Fin n) (Fin n) F))

variable (ψ₀ : AddChar F ℂ)

theorem psiN_mul {u v : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n)
    (hv : v ∈ Iwasawa.unipotent F n) : psiN ψ₀ (u * v) = psiN ψ₀ u * psiN ψ₀ v := by
  rw [psiN, superdiagSum_mul hu hv, AddChar.map_add_eq_mul]
  rfl

@[simp]
theorem psiN_one : psiN ψ₀ (1 : GL (Fin n) F) = 1 := by
  rw [psiN, Units.val_one, superdiagSum_one, AddChar.map_zero_eq_one]

theorem psiN_inv {u : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n) :
    psiN ψ₀ u⁻¹ = (psiN ψ₀ u)⁻¹ := by
  have h : psiN ψ₀ u⁻¹ * psiN ψ₀ u = 1 := by
    rw [← psiN_mul ψ₀ ((Iwasawa.unipotent F n).inv_mem hu) hu, inv_mul_cancel, psiN_one]
  exact eq_inv_of_mul_eq_one_left h

theorem psiN_ne_zero (g : GL (Fin n) F) : psiN ψ₀ g ≠ 0 := by
  intro h
  have := AddChar.map_add_eq_mul ψ₀ (superdiagSum (g : Matrix (Fin n) (Fin n) F))
    (-superdiagSum (g : Matrix (Fin n) (Fin n) F))
  rw [add_neg_cancel, AddChar.map_zero_eq_one] at this
  rw [psiN] at h
  rw [h, zero_mul] at this
  exact one_ne_zero this

def psiNHom : Iwasawa.unipotent F n →* ℂ where
  toFun u := psiN ψ₀ (u : GL (Fin n) F)
  map_one' := psiN_one ψ₀
  map_mul' u v := psiN_mul ψ₀ u.2 v.2

@[simp]
theorem psiNHom_apply (u : Iwasawa.unipotent F n) : psiNHom ψ₀ u = psiN ψ₀ (u : GL (Fin n) F) :=
  rfl

def sigmaMat (M : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  fun i j => M (Fin.rev j) (Fin.rev i)

omit [Field F] in
theorem sigmaMat_apply (M : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    sigmaMat M i j = M (Fin.rev j) (Fin.rev i) := rfl

theorem sigmaMat_mul (M M' : Matrix (Fin n) (Fin n) F) :
    sigmaMat (M * M') = sigmaMat M' * sigmaMat M := by
  ext i j
  simp only [sigmaMat_apply, Matrix.mul_apply]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fin.revPerm_apply]
  ring

theorem sigmaMat_one : sigmaMat (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  ext i j
  simp only [sigmaMat_apply, Matrix.one_apply, Fin.rev_inj]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h]

omit [Field F] in
theorem sigmaMat_sigmaMat (M : Matrix (Fin n) (Fin n) F) : sigmaMat (sigmaMat M) = M := by
  ext i j
  simp [sigmaMat_apply]

theorem sigmaMat_eq (M : Matrix (Fin n) (Fin n) F) :
    sigmaMat M = ((permGL F (Fin.revPerm (n := n)) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Mᵀ *
      ((permGL F (Fin.revPerm (n := n)) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  ext i j
  rw [mul_permGL_apply, permGL_mul_apply, Matrix.transpose_apply, sigmaMat_apply]
  congr 1

theorem superdiagSum_sigmaMat (M : Matrix (Fin n) (Fin n) F) :
    superdiagSum (sigmaMat M) = superdiagSum M := by
  unfold superdiagSum
  rw [Finset.sum_comm, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Fin.revPerm_apply, sigmaMat_apply, Fin.rev_rev]
  have hiff : (Fin.rev a).val = (Fin.rev b).val + 1 ↔ b.val = a.val + 1 := by
    simp only [Fin.val_rev]
    have := a.isLt
    have := b.isLt
    omega
  by_cases h : b.val = a.val + 1
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

def sigma (g : GL (Fin n) F) : GL (Fin n) F :=
  ⟨sigmaMat (g : Matrix (Fin n) (Fin n) F), sigmaMat ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F),
    by rw [← sigmaMat_mul, Units.inv_mul, sigmaMat_one],
    by rw [← sigmaMat_mul, Units.mul_inv, sigmaMat_one]⟩

theorem coe_sigma (g : GL (Fin n) F) :
    ((sigma g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = sigmaMat (g : Matrix (Fin n) (Fin n) F) :=
  rfl

theorem sigma_apply (g : GL (Fin n) F) (i j : Fin n) :
    ((sigma g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (g : Matrix (Fin n) (Fin n) F) (Fin.rev j) (Fin.rev i) := rfl

theorem sigma_mul (g h : GL (Fin n) F) : sigma (g * h) = sigma h * sigma g :=
  Units.ext (by rw [Units.val_mul, coe_sigma, coe_sigma, coe_sigma, Units.val_mul, sigmaMat_mul])

@[simp]
theorem sigma_one : sigma (1 : GL (Fin n) F) = 1 :=
  Units.ext (by rw [coe_sigma, Units.val_one, sigmaMat_one])

@[simp]
theorem sigma_sigma (g : GL (Fin n) F) : sigma (sigma g) = g :=
  Units.ext (by rw [coe_sigma, coe_sigma, sigmaMat_sigmaMat])

theorem sigma_inv (g : GL (Fin n) F) : sigma g⁻¹ = (sigma g)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← sigma_mul, mul_inv_cancel, sigma_one]

theorem sigma_involutive : Function.Involutive (sigma : GL (Fin n) F → GL (Fin n) F) :=
  sigma_sigma

theorem sigma_mem_unipotent {u : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n) :
    sigma u ∈ Iwasawa.unipotent F n := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [sigma_apply]
    exact hu.1 (Fin.rev_lt_rev.2 hij)
  · rw [sigma_apply]
    exact hu.2 (Fin.rev i)

theorem sigma_mem_unipotent_iff {u : GL (Fin n) F} :
    sigma u ∈ Iwasawa.unipotent F n ↔ u ∈ Iwasawa.unipotent F n :=
  ⟨fun h => sigma_sigma u ▸ sigma_mem_unipotent h, sigma_mem_unipotent⟩

theorem sigma_mem_borel {b : GL (Fin n) F} (hb : b ∈ borel n F) : sigma b ∈ borel n F := by
  rw [mem_borel_iff] at hb ⊢
  intro i j hij
  rw [sigma_apply]
  exact hb _ _ (Fin.rev_lt_rev.2 hij)

theorem psiN_sigma (ψ₀ : AddChar F ℂ) (g : GL (Fin n) F) : psiN ψ₀ (sigma g) = psiN ψ₀ g := by
  rw [psiN, psiN, coe_sigma, superdiagSum_sigmaMat]

def theta (g : GL (Fin n) F) : GL (Fin n) F := (sigma g)⁻¹

theorem theta_eq (g : GL (Fin n) F) : theta g = sigma g⁻¹ := (sigma_inv g).symm

theorem theta_mul (g h : GL (Fin n) F) : theta (g * h) = theta g * theta h := by
  rw [theta, theta, theta, sigma_mul, _root_.mul_inv_rev]

@[simp]
theorem theta_theta (g : GL (Fin n) F) : theta (theta g) = g := by
  rw [theta, theta, ← sigma_inv g, sigma_sigma, inv_inv]

theorem sigma_theta (g : GL (Fin n) F) : sigma (theta g) = g⁻¹ := by
  rw [theta, ← sigma_inv g, sigma_sigma]

theorem sigma_mul_mul_inv (a g b : GL (Fin n) F) :
    sigma (a * g * b⁻¹) = theta b * sigma g * (theta a)⁻¹ := by
  rw [sigma_mul, sigma_mul, theta_eq, theta, inv_inv, mul_assoc]

theorem theta_mem_unipotent {u : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n) :
    theta u ∈ Iwasawa.unipotent F n :=
  (Iwasawa.unipotent F n).inv_mem (sigma_mem_unipotent hu)

theorem psiN_theta (ψ₀ : AddChar F ℂ) {u : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n) :
    psiN ψ₀ (theta u) = (psiN ψ₀ u)⁻¹ := by
  rw [theta, psiN_inv ψ₀ (sigma_mem_unipotent hu), psiN_sigma]

def thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n where
  toFun u := ⟨theta (u : GL (Fin n) F), theta_mem_unipotent u.2⟩
  invFun u := ⟨theta (u : GL (Fin n) F), theta_mem_unipotent u.2⟩
  left_inv _ := Subtype.ext (theta_theta _)
  right_inv _ := Subtype.ext (theta_theta _)
  map_mul' _ _ := Subtype.ext (theta_mul _ _)

@[simp]
theorem coe_thetaN (u : Iwasawa.unipotent F n) :
    ((thetaN u : Iwasawa.unipotent F n) : GL (Fin n) F) = theta (u : GL (Fin n) F) := rfl

theorem thetaN_symm : (thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n).symm = thetaN :=
  rfl

theorem diag_mul_permGL_apply (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) (r c : Fin n) :
    ((Iwasawa.diagGL F n t * permGL F w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r c =
      if r = w c then (t r : F) else 0 := by
  rw [Units.val_mul, Iwasawa.coe_diagGL, Matrix.diagonal_mul, permGL_apply]
  split_ifs <;> simp

theorem sigma_permGL (w : Equiv.Perm (Fin n)) :
    sigma (permGL F w) = permGL F (Fin.revPerm * w⁻¹ * Fin.revPerm) := by
  refine Units.ext ?_
  ext i j
  rw [sigma_apply, permGL_apply, permGL_apply]
  simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply]
  have hiff : Fin.rev j = w (Fin.rev i) ↔ i = Fin.rev (w⁻¹ (Fin.rev j)) := by
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [h]
      simp
  by_cases h : Fin.rev j = w (Fin.rev i)
  · rw [if_pos h, if_pos (hiff.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

theorem sigma_mem_doubleCoset_permGL {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)}
    (hg : g ∈ doubleCoset (permGL F w) (borel n F : Set (GL (Fin n) F)) (borel n F)) :
    sigma g ∈ doubleCoset (permGL F (Fin.revPerm * w⁻¹ * Fin.revPerm))
      (borel n F : Set (GL (Fin n) F)) (borel n F) := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_doubleCoset.1 hg
  refine mem_doubleCoset.2 ⟨sigma b₂, sigma_mem_borel hb₂, sigma b₁, sigma_mem_borel hb₁, ?_⟩
  rw [sigma_mul, sigma_mul, sigma_permGL, ← mul_assoc]

theorem sigma_diagGL (t : Fin n → Fˣ) :
    sigma (Iwasawa.diagGL F n t) = Iwasawa.diagGL F n (t ∘ Fin.rev) := by
  refine Units.ext ?_
  ext i j
  simp only [sigma_apply, Iwasawa.coe_diagGL, Matrix.diagonal_apply, Fin.rev_inj,
    Function.comp_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]

theorem sigma_diag_mul_permGL_eq (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n))
    (hw : ∀ b, w (Fin.rev (w b)) = Fin.rev b) (ht : ∀ b, t (w b) = t (Fin.rev b)) :
    sigma (Iwasawa.diagGL F n t * permGL F w) = Iwasawa.diagGL F n t * permGL F w := by
  refine Units.ext ?_
  ext i j
  rw [sigma_apply, diag_mul_permGL_apply, diag_mul_permGL_apply]
  have hiff : Fin.rev j = w (Fin.rev i) ↔ i = w j := by
    constructor
    · intro h
      have := hw (Fin.rev i)
      rw [← h, Fin.rev_rev, Fin.rev_rev] at this
      exact this.symm
    · intro h
      rw [h, hw j]
  by_cases h : i = w j
  · rw [if_pos (hiff.2 h), if_pos h, h, ht j]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

theorem single_mul_single_self_of_ne {i j : Fin n} (h : i ≠ j) (a b : F) :
    Matrix.single i j a * Matrix.single i j b = 0 :=
  Matrix.single_mul_single_of_ne a i j i (Ne.symm h) b

def rootElt (i j : Fin n) (a : F) : GL (Fin n) F :=
  if h : i = j then 1 else
    ⟨1 + Matrix.single i j a, 1 - Matrix.single i j a,
      by rw [add_mul, one_mul, mul_sub, mul_one, single_mul_single_self_of_ne h, sub_zero,
        sub_add_cancel],
      by rw [sub_mul, one_mul, mul_add, mul_one, single_mul_single_self_of_ne h, add_zero,
        add_sub_cancel_right]⟩

theorem coe_rootElt {i j : Fin n} (h : i ≠ j) (a : F) :
    ((rootElt i j a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + Matrix.single i j a := by
  rw [rootElt, dif_neg h]

theorem rootElt_self (i : Fin n) (a : F) : rootElt i i a = 1 := by
  rw [rootElt, dif_pos rfl]

theorem rootElt_apply {i j : Fin n} (h : i ≠ j) (a : F) (r c : Fin n) :
    ((rootElt i j a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r c =
      (1 : Matrix (Fin n) (Fin n) F) r c + if i = r ∧ j = c then a else 0 := by
  rw [coe_rootElt h, Matrix.add_apply, Matrix.single_apply]

@[simp]
theorem rootElt_zero (i j : Fin n) : rootElt i j (0 : F) = 1 := by
  by_cases h : i = j
  · rw [h, rootElt_self]
  · exact Units.ext (by rw [coe_rootElt h, Matrix.single_zero, add_zero, Units.val_one])

theorem rootElt_add (i j : Fin n) (a b : F) :
    rootElt i j (a + b) = rootElt i j a * rootElt i j b := by
  by_cases h : i = j
  · rw [h, rootElt_self, rootElt_self, rootElt_self, mul_one]
  · refine Units.ext ?_
    rw [Units.val_mul, coe_rootElt h, coe_rootElt h, coe_rootElt h, add_mul, one_mul, mul_add,
      mul_one, single_mul_single_self_of_ne h, add_zero, Matrix.single_add]
    abel

def rootEltHom (i j : Fin n) : Multiplicative F →* GL (Fin n) F where
  toFun a := rootElt i j a.toAdd
  map_one' := rootElt_zero i j
  map_mul' a b := rootElt_add i j a.toAdd b.toAdd

theorem rootElt_neg (i j : Fin n) (a : F) : rootElt i j (-a) = (rootElt i j a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← rootElt_add, neg_add_cancel, rootElt_zero])

@[simp]
theorem rootEltHom_apply (i j : Fin n) (a : Multiplicative F) :
    rootEltHom i j a = rootElt i j a.toAdd := rfl

theorem rootElt_mem_unipotent {i j : Fin n} (h : i < j) (a : F) :
    rootElt i j a ∈ Iwasawa.unipotent F n := by
  have hne : i ≠ j := ne_of_lt h
  refine ⟨fun r c hrc => ?_, fun r => ?_⟩
  · rw [rootElt_apply hne, Matrix.one_apply_ne (ne_of_gt (show c < r from hrc)), zero_add]
    refine if_neg fun e => ?_
    rw [← e.1, ← e.2] at hrc
    exact lt_asymm h hrc
  · rw [rootElt_apply hne, Matrix.one_apply_eq, if_neg fun e => hne (e.1.trans e.2.symm), add_zero]

theorem superdiagSum_add (M M' : Matrix (Fin n) (Fin n) F) :
    superdiagSum (M + M') = superdiagSum M + superdiagSum M' := by
  unfold superdiagSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem superdiagSum_single (i j : Fin n) (a : F) :
    superdiagSum (Matrix.single i j a) = if j.val = i.val + 1 then a else 0 := by
  unfold superdiagSum
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · rw [Matrix.single_apply_same]
  · intro c _ hc
    rw [Matrix.single_apply_of_col_ne i i hc.symm, ite_self]
  · intro h
    exact absurd (Finset.mem_univ j) h
  · intro r _ hr
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Matrix.single_apply_of_row_ne hr.symm, ite_self]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem psiN_rootElt (ψ₀ : AddChar F ℂ) {i j : Fin n} (h : i ≠ j) (a : F) :
    psiN ψ₀ (rootElt i j a) = if j.val = i.val + 1 then ψ₀ a else 1 := by
  rw [psiN, coe_rootElt h, superdiagSum_add, superdiagSum_one, zero_add, superdiagSum_single]
  split_ifs
  · rfl
  · exact AddChar.map_zero_eq_one ψ₀

theorem diag_mul_permGL_mul_single (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) (i j : Fin n)
    (a : F) :
    ((Iwasawa.diagGL F n t * permGL F w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        Matrix.single i j a = Matrix.single (w i) j ((t (w i) : F) * a) := by
  ext r c
  by_cases hc : c = j
  · subst hc
    rw [Matrix.mul_single_apply_same, diag_mul_permGL_apply, Matrix.single_apply]
    by_cases hr : r = w i
    · subst hr
      simp
    · rw [if_neg hr, if_neg (fun e => hr (e.1.symm)), zero_mul]
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc, Matrix.single_apply_of_col_ne _ _ (Ne.symm hc)]

theorem single_mul_diag_mul_permGL (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) (k j : Fin n)
    (b : F) :
    Matrix.single k (w j) b *
        ((Iwasawa.diagGL F n t * permGL F w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.single k j (b * (t (w j) : F)) := by
  ext r c
  by_cases hr : r = k
  · subst hr
    rw [Matrix.single_mul_apply_same, diag_mul_permGL_apply, Matrix.single_apply]
    by_cases hc : c = j
    · subst hc
      simp
    · rw [if_neg (fun e => hc (w.injective e).symm), if_neg (fun e => hc e.2.symm), mul_zero]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hr, Matrix.single_apply_of_row_ne (Ne.symm hr)]

theorem conj_rootElt (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) (i j : Fin n) (a : F) :
    (Iwasawa.diagGL F n t * permGL F w) * rootElt i j a * (Iwasawa.diagGL F n t * permGL F w)⁻¹ =
      rootElt (w i) (w j) ((t (w i) : F) / (t (w j) : F) * a) := by
  by_cases h : i = j
  · subst h
    rw [rootElt_self, rootElt_self, mul_one, mul_inv_cancel]
  have h' : w i ≠ w j := fun e => h (w.injective e)
  rw [mul_inv_eq_iff_eq_mul]
  refine Units.ext ?_
  rw [Units.val_mul (Iwasawa.diagGL F n t * permGL F w) (rootElt i j a),
    Units.val_mul (rootElt (w i) (w j) _) (Iwasawa.diagGL F n t * permGL F w),
    coe_rootElt h, coe_rootElt h', mul_add, add_mul, mul_one, one_mul,
    diag_mul_permGL_mul_single, single_mul_diag_mul_permGL]
  congr 2
  have : (t (w j) : F) ≠ 0 := Units.ne_zero _
  field_simp

end Algebra

section Topology

variable {F : Type*} [Field F] [TopologicalSpace F] {n : ℕ}

theorem continuous_sigmaMat_val :
    Continuous fun g : GL (Fin n) F => sigmaMat (g : Matrix (Fin n) (Fin n) F) :=
  continuous_matrix fun i j => Units.continuous_val.matrix_elem (Fin.rev j) (Fin.rev i)

theorem continuous_sigma : Continuous (sigma : GL (Fin n) F → GL (Fin n) F) := by
  refine Units.continuous_iff.2 ⟨continuous_sigmaMat_val, ?_⟩
  have : (fun g : GL (Fin n) F => (((sigma g)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      fun g => sigmaMat ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    funext g
    rw [← sigma_inv, coe_sigma]
  rw [this]
  exact continuous_matrix fun i j => Units.continuous_coe_inv.matrix_elem (Fin.rev j) (Fin.rev i)

def sigmaHomeo : GL (Fin n) F ≃ₜ GL (Fin n) F where
  toFun := sigma
  invFun := sigma
  left_inv := sigma_sigma
  right_inv := sigma_sigma
  continuous_toFun := continuous_sigma
  continuous_invFun := continuous_sigma

@[simp]
theorem sigmaHomeo_apply (g : GL (Fin n) F) : sigmaHomeo g = sigma g := rfl

variable [IsTopologicalRing F]

theorem continuous_theta : Continuous (theta : GL (Fin n) F → GL (Fin n) F) :=
  continuous_sigma.inv

theorem continuous_thetaN :
    Continuous (thetaN : Iwasawa.unipotent F n → Iwasawa.unipotent F n) :=
  (continuous_theta.comp continuous_subtype_val).subtype_mk _

theorem continuous_rootElt (i j : Fin n) : Continuous (rootElt i j : F → GL (Fin n) F) := by
  by_cases h : i = j
  · subst h
    have : (rootElt i i : F → GL (Fin n) F) = fun _ => 1 := funext fun a => rootElt_self i a
    rw [this]
    exact continuous_const
  have hval : Continuous fun a : F => ((rootElt i j a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    refine continuous_matrix fun r c => ?_
    simp only [rootElt_apply h]
    refine continuous_const.add ?_
    split_ifs
    · exact continuous_id
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have : (fun a : F => (((rootElt i j a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      fun a => ((rootElt i j (-a) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    funext a
    rw [rootElt_neg]
  rw [this]
  exact hval.comp continuous_neg

end Topology

theorem eq_one_of_forall_norm_zpow_sub_one_lt {z : ℂ} (h : ∀ m : ℤ, ‖z ^ m - 1‖ < 1) : z = 1 :=
  _root_.GroundTheory.Variant₂.N1.eq_one_of_forall_norm_zpow_sub_one_lt h

section LocalField

open ValuativeRel Topology

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)

theorem exists_ball_addChar_eq_one {ψ₀ : AddChar F ℂ} (hψ : Continuous ψ₀) :
    ∃ γ : (ValueGroupWithZero F)ˣ, ∀ x : F, valuation F x < γ → ψ₀ x = 1 := by
  have hball : {z : ℂ | ‖z - 1‖ < 1} ∈ 𝓝 (ψ₀ 0) := by
    rw [AddChar.map_zero_eq_one]
    have : {z : ℂ | ‖z - 1‖ < 1} = Metric.ball 1 1 := by
      ext z
      simp [dist_eq_norm]
    rw [this]
    exact Metric.ball_mem_nhds 1 one_pos
  obtain ⟨γ, -, hγ⟩ := (IsValuativeTopology.hasBasis_nhds_zero F).mem_iff.1
    (hψ.continuousAt.preimage_mem_nhds hball)
  refine ⟨γ, fun x hx => eq_one_of_forall_norm_zpow_sub_one_lt fun m => ?_⟩
  have hmx : m • x ∈ (valuation F).ltAddSubgroup γ :=
    AddSubgroup.zsmul_mem _ (Valuation.mem_ltAddSubgroup_iff.2 hx) m
  have := hγ (Valuation.mem_ltAddSubgroup_iff.1 hmx)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at this
  rwa [AddChar.map_zsmul_eq_zpow] at this

theorem isClosed_unipotent : IsClosed (Iwasawa.unipotent F n : Set (GL (Fin n) F)) := by
  have hset : (Iwasawa.unipotent F n : Set (GL (Fin n) F)) =
      (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : j < i),
        {g : GL (Fin n) F | (g : Matrix (Fin n) (Fin n) F) i j = 0}) ∩
      ⋂ i : Fin n, {g : GL (Fin n) F | (g : Matrix (Fin n) (Fin n) F) i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, Iwasawa.mem_unipotent, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨fun i j hij => h.1 hij, h.2⟩, fun h => ⟨fun i j hij => h.1 i j hij, h.2⟩⟩
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter
    fun _ => isClosed_eq (GLnLocal.continuous_entry F n i j) continuous_const)
    (isClosed_iInter fun i => isClosed_eq (GLnLocal.continuous_entry F n i i) continuous_const)

instance locallyCompactSpace_unipotent : LocallyCompactSpace (Iwasawa.unipotent F n) :=
  (isClosed_unipotent F n).locallyCompactSpace

instance totallyDisconnectedSpace_unipotent : TotallyDisconnectedSpace (Iwasawa.unipotent F n) :=
  inferInstance

instance sigmaCompactSpace_GL : SigmaCompactSpace (GL (Fin n) F) := inferInstance

instance sigmaCompactSpace_unipotent : SigmaCompactSpace (Iwasawa.unipotent F n) :=
  (isClosed_unipotent F n).sigmaCompactSpace

theorem exists_compactOpen_psiN_trivial {ψ₀ : AddChar F ℂ} (hψ : Continuous ψ₀) :
    ∃ K : Subgroup (Iwasawa.unipotent F n), IsCompact (K : Set (Iwasawa.unipotent F n)) ∧
      IsOpen (K : Set (Iwasawa.unipotent F n)) ∧ ∀ k ∈ K, psiN ψ₀ (k : GL (Fin n) F) = 1 := by
  obtain ⟨γ, hγ⟩ := exists_ball_addChar_eq_one F hψ
  set A := (valuation F).ltAddSubgroup γ
  have hAo : IsOpen (A : Set F) :=
    AddSubgroup.isOpen_of_mem_nhds A ((IsValuativeTopology.hasBasis_nhds_zero F).mem_of_mem trivial)
  let V : Set (Iwasawa.unipotent F n) :=
    ⋂ i : Fin n, ⋂ j : Fin n, {u | ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ A ∨
      j.val ≠ i.val + 1}
  have hVo : IsOpen V := by
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    by_cases hij : j.val = i.val + 1
    · have : {u : Iwasawa.unipotent F n | ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ A ∨
          j.val ≠ i.val + 1} = (fun u : Iwasawa.unipotent F n =>
            ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) ⁻¹' (A : Set F) := by
        ext u
        simp [hij]
      rw [this]
      exact hAo.preimage ((GLnLocal.continuous_entry F n i j).comp continuous_subtype_val)
    · have : {u : Iwasawa.unipotent F n | ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ A ∨
          j.val ≠ i.val + 1} = Set.univ := by
        ext u
        simp [hij]
      rw [this]
      exact isOpen_univ
  have h1V : (1 : Iwasawa.unipotent F n) ∈ V := by
    simp only [V, Set.mem_iInter, Set.mem_ofPred_eq]
    intro i j
    by_cases hij : j.val = i.val + 1
    · left
      have hne : i ≠ j := fun e => by rw [e] at hij; omega
      rw [OneMemClass.coe_one, Units.val_one, Matrix.one_apply_ne hne]
      exact A.zero_mem
    · exact Or.inr hij
  obtain ⟨K, hKc, hKV⟩ := exists_openSubgroup_isCompact_subset (hVo.mem_nhds h1V)
  refine ⟨K.toSubgroup, hKc, K.isOpen, fun k hk => ?_⟩
  have hkV : k ∈ V := hKV hk
  simp only [V, Set.mem_iInter, Set.mem_ofPred_eq] at hkV
  refine hγ _ ?_
  refine Valuation.mem_ltAddSubgroup_iff.1 (A.sum_mem fun i _ => A.sum_mem fun j _ => ?_)
  split_ifs with hij
  · exact (hkV i j).resolve_right (not_not.2 hij)
  · exact A.zero_mem

end LocalField

end Whittaker

end GroundTheory.Automorphic
