import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms

noncomputable section

open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.InvTranspose

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

def flipM (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := A.transpose.submatrix Fin.rev Fin.rev

theorem flipM_apply (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) : flipM A i j = A j.rev i.rev := rfl

theorem flipM_mul (A B : Matrix (Fin n) (Fin n) R) : flipM (A * B) = flipM B * flipM A := by
  unfold flipM
  rw [Matrix.transpose_mul]
  exact (Matrix.submatrix_mul_equiv _ _ _ (Fin.revPerm : Fin n ≃ Fin n) _).symm

theorem flipM_one : flipM (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  simp [flipM_apply, Matrix.one_apply, eq_comm]

theorem flipM_flipM (A : Matrix (Fin n) (Fin n) R) : flipM (flipM A) = A := by
  ext i j
  simp [flipM_apply]

theorem flipM_diagonal (a : Fin n → R) : flipM (Matrix.diagonal a) = Matrix.diagonal (fun i => a i.rev) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [flipM_apply]
  · have h' : j.rev ≠ i.rev := fun e => h (Fin.rev_injective e).symm
    simp [flipM_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h']

def theta : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨flipM ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R), flipM (g : Matrix (Fin n) (Fin n) R),
    by rw [← flipM_mul, Units.mul_inv, flipM_one], by rw [← flipM_mul, Units.inv_mul, flipM_one]⟩
  map_one' := by
    apply Units.ext
    simp [flipM_one]
  map_mul' g h := by
    apply Units.ext
    simp only [mul_inv_rev, Units.val_mul, flipM_mul]

theorem coe_theta (g : GL (Fin n) R) :
    (theta g : Matrix (Fin n) (Fin n) R) = flipM ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := rfl

theorem theta_theta (g : GL (Fin n) R) : theta (theta g) = g := by
  apply Units.ext
  rw [coe_theta]
  exact flipM_flipM _

end Ring

section Field

variable {L : Type} [Field L] {n : ℕ}

theorem theta_mem {O : Subring L} {g : GL (Fin n) L} (hg : g ∈ GLint (Fin n) O) : theta g ∈ GLint (Fin n) O := by
  obtain ⟨k, rfl⟩ := hg
  refine ⟨theta k, ?_⟩
  apply Units.ext
  rw [coe_theta, ← map_inv]
  rfl

theorem theta_upper {b : GL (Fin n) L} (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((theta b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  intro i j hij
  rw [coe_theta, flipM_apply]
  exact Formalism.UG.P.spherical_upper_inv b hb (Fin.rev_lt_rev.2 hij)

theorem theta_diag {b : GL (Fin n) L} (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id) (i : Fin n) :
    ((theta b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i * (b : Matrix (Fin n) (Fin n) L) i.rev i.rev = 1 := by
  rw [coe_theta, flipM_apply, ← Formalism.UG.P.spherical_diag_mul _ _ (Formalism.UG.P.spherical_upper_inv b hb) hb,
    Units.inv_mul, Matrix.one_apply_eq]

theorem getD_dualLab' (d : List ℤ) (hd : d.length = n) (i : Fin n) :
    (dualLab d).getD i.1 0 = -(d.getD i.rev.1 0) := by
  subst hd
  have h1 : i.1 < (dualLab d).length := by simp only [dualLab, List.length_reverse, List.length_map]; exact i.2
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.rev.2]
  simp only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]
  congr 2
  omega

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem hasDiv_theta {O : Subring L} {d : List ℤ} (hd : d.length = n) {g : GL (Fin n) L} (h : HasDiv O d g) :
    HasDiv O (dualLab d) (theta g) := by
  obtain ⟨ϖ, hϖ, a, ha, b, hb, e⟩ := h
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  let D : GL (Fin n) L := ⟨Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0),
    Matrix.diagonal (fun i : Fin n => ϖ ^ (-(d.getD i 0))),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i
       rw [← zpow_add₀ h0, add_neg_cancel, zpow_zero],
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i
       rw [← zpow_add₀ h0, neg_add_cancel, zpow_zero]⟩
  have hg : g = a * D * b := Units.ext e
  refine ⟨ϖ, hϖ, theta a, theta_mem ha, theta b, theta_mem hb, ?_⟩
  rw [hg, map_mul, map_mul, Units.val_mul, Units.val_mul]
  congr 2
  rw [coe_theta]
  change flipM (Matrix.diagonal (fun i : Fin n => ϖ ^ (-(d.getD i 0)))) = _
  rw [flipM_diagonal]
  congr 1
  funext i
  rw [getD_dualLab' d hd]

theorem divInd_theta (O : Subring L) {d : List ℤ} (hd : d.length = n) (g : GL (Fin n) L) :
    divInd O (dualLab d) g = divInd O d (theta g) := by
  have hdd : dualLab (dualLab d) = d := by simp [dualLab, List.map_reverse]
  have : HasDiv O (dualLab d) g ↔ HasDiv O d (theta g) := by
    constructor
    · intro h
      have := hasDiv_theta (by simpa [dualLab] using hd) h
      rwa [hdd] at this
    · intro h
      have := hasDiv_theta hd h
      rwa [theta_theta] at this
  unfold divInd
  by_cases h : HasDiv O d (theta g)
  · rw [Set.indicator_of_mem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_mem (s := {g | HasDiv O (dualLab d) g}) (this.2 h)]
    rfl
  · rw [Set.indicator_of_notMem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_notMem (s := {g | HasDiv O (dualLab d) g}) (fun h' => h (this.1 h'))]

theorem hasDiv_mul_right {O : Subring L} {d : List ℤ} {g k : GL (Fin n) L} (hk : k ∈ GLint (Fin n) O) (h : HasDiv O d g) :
    HasDiv O d (g * k) := by
  obtain ⟨ϖ, hϖ, a, ha, b, hb, e⟩ := h
  refine ⟨ϖ, hϖ, a, ha, b * k, mul_mem hb hk, ?_⟩
  rw [Units.val_mul, Units.val_mul, e]
  simp only [Matrix.mul_assoc]

theorem divInd_mul_right (O : Subring L) (d : List ℤ) (g k : GL (Fin n) L) (hk : k ∈ GLint (Fin n) O) :
    divInd O d (g * k) = divInd O d g := by
  unfold divInd
  by_cases h : HasDiv O d g
  · rw [Set.indicator_of_mem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_mem (s := {g | HasDiv O d g}) (hasDiv_mul_right hk h)]
    rfl
  · rw [Set.indicator_of_notMem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_notMem (s := {g | HasDiv O d g})]
    intro h'
    have := hasDiv_mul_right (inv_mem hk) h'
    rw [mul_inv_cancel_right] at this
    exact h this

end Field

theorem finsum_out_involution {G : Type} [Group G] (K : Subgroup G) (t : G →* G) (ht : ∀ g, t (t g) = g)
    (hK : ∀ k ∈ K, t k ∈ K) (F : G → ℂ) (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) :
    ∑ᶠ x : G ⧸ K, F (t x.out) = ∑ᶠ x : G ⧸ K, F x.out := by
  have hF' : ∀ g : G, F (QuotientGroup.mk (s := K) g).out = F g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk, hF _ _ k.2]
  let m : G ⧸ K → G ⧸ K := fun x => QuotientGroup.mk (t x.out)
  have hm : Function.Involutive m := fun x => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (t x.out)
    simp only [m]
    rw [hk, map_mul, ht, QuotientGroup.mk_mul_of_mem _ (hK _ k.2), QuotientGroup.out_eq']
  rw [← finsum_comp_equiv (hm.toPerm m) (f := fun x : G ⧸ K => F x.out)]
  exact finsum_congr fun x => (hF' _).symm

section Global

variable (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}

theorem ordV_of_mul_eq_one {x y : P.adicCompletion E} (h : x * y = 1) : ordV E P x = -ordV E P y := by
  have hx : x ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hy : y ≠ 0 := right_ne_zero_of_mul_eq_one h
  have h1 := Formalism.UG.P.spherical_ordV_mul E P x y hx hy
  have h2 := Formalism.UG.P.spherical_ordV_unit E P 1 1 (one_mem _) (one_mem _) (mul_one 1)
  rw [h, h2] at h1
  omega

theorem chiDelta_theta (α : Fin n → ℂ) {b : GL (Fin n) (P.adicCompletion E)}
    (hb : (b : Matrix (Fin n) (Fin n) (P.adicCompletion E)).BlockTriangular id) :
    chiDelta E P α (theta b) = chiDelta E P (fun i => (α i.rev)⁻¹) b := by
  unfold chiDelta
  rw [← Equiv.prod_comp (Fin.revPerm : Fin n ≃ Fin n) (fun i : Fin n => (α i.rev)⁻¹ ^ _ * _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ordV_of_mul_eq_one E P (theta_diag hb i)]
  simp only [Fin.revPerm_apply, Fin.rev_rev, inv_zpow']
  congr 2
  have : ((i.rev : ℕ) : ℂ) = (n : ℂ) - 1 - (i : ℂ) := by
    rw [Fin.val_rev, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [this]
  push_cast
  ring

end Global

theorem exists_spherical_dual : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (α : Fin n → ℂ) (φ : GL (Fin n) (P.adicCompletion E) → ℂ), (∀ i, α i ≠ 0) → IsSpherical E P α φ → ∃ φ' : GL (Fin n) (P.adicCompletion E) → ℂ, IsSpherical E P (fun i => (α i.rev)⁻¹) φ' ∧ φ' 1 = φ 1 ∧ ∀ d : List ℤ, d.length = n → hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) (dualLab d)) φ' 1 = hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) d) φ 1 := by
  intro E _ _ P n α φ _ hφ
  refine ⟨fun g => φ (theta g), ?_, by simp, ?_⟩
  · intro b g k hb hk
    have hb' := (Formalism.UG.P.spherical_upper_iff b).1 hb
    simp only [map_mul]
    rw [hφ _ _ _ ((Formalism.UG.P.spherical_upper_iff _).2 (theta_upper hb')) (theta_mem hk), chiDelta_theta E P α hb']
  · intro d hd
    have h1 : ((1 : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)).BlockTriangular id :=
      Matrix.blockTriangular_one
    have hr : ∀ g, ∀ k ∈ GLint (Fin n) (Ov E P), φ (g * k) = φ g := fun g k hk => by
      have := hφ 1 g k ((Formalism.UG.P.spherical_upper_iff _).2 h1) hk
      rwa [one_mul, Formalism.UG.P.spherical_chiDelta_int E P α 1 h1 (one_mem _), one_mul] at this
    unfold hAct
    simp only [one_mul, divInd_theta _ hd]
    exact finsum_out_involution _ theta theta_theta (fun k => theta_mem)
      (fun g => divInd (Ov E P) d g • φ g) (fun g k hk => by rw [divInd_mul_right _ _ _ _ hk, hr g k hk])

end GlobalTheory.InvTranspose

end
