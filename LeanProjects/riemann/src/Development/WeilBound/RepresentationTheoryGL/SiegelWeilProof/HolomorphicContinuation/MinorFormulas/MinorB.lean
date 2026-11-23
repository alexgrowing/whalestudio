import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorDefs

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP.Mi

theorem deriv_prod {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (D : Derivation R A A) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → A) : D (∏ i ∈ s, f i) = ∑ c ∈ s, (∏ i ∈ s.erase c, f i) * D (f c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha, smul_eq_mul,
      smul_eq_mul, Finset.mul_sum, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hca : c ≠ a := fun h => ha (h ▸ hc)
      rw [Finset.erase_insert_of_ne hca.symm, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring

theorem deriv_det {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (D : Derivation R A A) {ρ : ℕ}
    (M : Matrix (Fin ρ) (Fin ρ) A) :
    D M.det = ∑ c, (Matrix.updateCol M c (fun a => D (M a c))).det := by
  simp only [Matrix.det_apply]
  rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Derivation.map_smul_of_tower, deriv_prod, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
  simp only [Matrix.updateCol_self]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hi)]

theorem delDet : DelDet := by
  intro R _ ρ p q
  rw [deriv_det]
  have h1 : ∀ c, Matrix.updateCol (Xm R ρ) c (fun a => del p q (Xm R ρ a c)) =
      Matrix.updateCol (Xm R ρ) c (fun a => X (q, c) * X (a, p)) := by
    intro c
    congr 1
    funext a
    simp only [Xm, del, mkDerivation_X]
    ring
  simp only [h1]
  have h2 : ∀ c, (Matrix.updateCol (Xm R ρ) c (fun a => X (q, c) * X (a, p))).det =
      X (q, c) * (Matrix.updateCol (Xm R ρ) c (fun a => Xm R ρ a p)).det := by
    intro c
    have : (fun a => (X (q, c) * X (a, p) : Pm R ρ)) = (X (q, c) : Pm R ρ) • fun a => Xm R ρ a p := by
      funext a; simp [Xm]
    rw [this, Matrix.det_updateCol_smul]
  simp only [h2]
  rw [Finset.sum_eq_single p]
  · congr 1
    congr 1
    ext a d
    by_cases hd : d = p
    · subst hd; simp [Matrix.updateCol_self]
    · simp [Matrix.updateCol_ne hd]
  · intro c _ hc
    rw [Matrix.det_zero_of_column_eq (i := c) (j := p) hc, mul_zero]
    · simp [Matrix.updateCol_self, Matrix.updateCol_ne (Ne.symm hc)]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem renInt : RenInt := by
  intro R _ r s I J α p q f
  simp only [opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, map_add, map_mul]
  congr 1
  · simp [ren, rename_X]
  · induction f using MvPolynomial.induction_on with
    | C a => simp [ren]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f ad hf =>
      have e1 : ren I J (f * X ad) = ren I J f * X (J ad.1, I ad.2) := by simp [ren, rename_X]
      rw [e1, Derivation.leibniz, Derivation.leibniz, map_add, hf, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
        map_mul, map_mul]
      simp only [del, mkDerivation_X, ren, map_mul, rename_X]

theorem del_CX_mul {R : Type} [CommRing R] {ρ : ℕ} (p q : Fin ρ) (α : R) (a b : Fin ρ) (g : Pm R ρ) :
    del p q (C α * X (a, b) * g) = C α * (X (a, p) * X (q, b)) * g + C α * X (a, b) * del p q g := by
  rw [Derivation.leibniz, Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    MvPolynomial.derivation_C, del, mkDerivation_X]
  ring

theorem del_comm {R : Type} [CommRing R] {ρ : ℕ} (p q p' q' : Fin ρ) (g : Pm R ρ) :
    del p q (del p' q' g) = del p' q' (del p q g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [del]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f ad hf =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, hf]
    simp only [del, mkDerivation_X, Derivation.leibniz, smul_eq_mul]
    ring

theorem mComm : MComm := by
  intro R _ ρ α p q p' q'
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, map_add]
  rw [del_CX_mul, del_CX_mul, del_comm p q p' q']
  ring

end PositivityTheory.Rg.Sw.SP.Mi
