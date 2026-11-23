import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QhDetZpowMem
import Formalism.GradedWeylDivisibility.FinalC

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} {R : Type} [CommRing R]

lemma qh_generic {B : Type} [CommRing B] [IsDomain B] [Algebra R B] (bm gm : Matrix (Fin n) (Fin n) B)
    (hb : ∀ a c, a < c → bm a c = 0) (hbd : ∀ a, bm a a ≠ 0) (hg : gm.det ≠ 0)
    (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ))) :
    aeval (fun v : Fin n × Fin n => (bm * gm) v.2 v.1) Q =
      (∏ a, bm a a ^ ν a) * aeval (fun v : Fin n × Fin n => gm v.2 v.1) Q := by
  let F := FractionRing B
  let φ : B →+* F := algebraMap B F
  have hinj : Function.Injective φ := IsFractionRing.injective B F
  have hbdet : (φ.mapMatrix bm).det ≠ 0 := by
    rw [← RingHom.map_det, Matrix.det_of_isLowerTriangular _ (fun i j hij => hb i j hij),
      map_ne_zero_iff _ hinj]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hbd a
  have hgdet : (φ.mapMatrix gm).det ≠ 0 := by
    rw [← RingHom.map_det, map_ne_zero_iff _ hinj]; exact hg
  let b' : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hbdet
  let g' : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hgdet
  have hb' : b'.val = φ.mapMatrix bm := rfl
  have hg' : g'.val = φ.mapMatrix gm := rfl
  have h := hQ F b' g' (by intro a c hac; rw [hb']; show φ (bm a c) = 0; rw [hb a c hac, map_zero])
  have hev : ∀ (M : Matrix (Fin n) (Fin n) B) (h' : GL (Fin n) F), h'.val = φ.mapMatrix M →
      evGLR h' (algebraMap _ (GLCoord R n) (rename Prod.swap Q)) =
        φ (aeval (fun v : Fin n × Fin n => M v.2 v.1) Q) := by
    intro M h' hh
    rw [qh_evGLR_alg, coe_eval₂Hom, eval₂_rename, aeval_def, eval₂_comp_left, hh]
    rw [IsScalarTower.algebraMap_eq R B F]
    rfl
  rw [hev (bm * gm) (b' * g') (by rw [Units.val_mul, hb', hg', map_mul]), hev gm g' hg'] at h
  apply hinj
  rw [map_mul, map_prod]
  simp only [map_pow]
  simpa [hb'] using h

lemma qh_det_ne [IsDomain R] {B : Type} [CommRing B] (φ : MvPolynomial (Fin n × Fin n) R →+* B)
    (hφ : Function.Injective φ) : (Matrix.of fun a c : Fin n => φ (X (c, a))).det ≠ 0 := by
  have h : (Matrix.of fun a c : Fin n => φ (X (c, a))) =
      (φ.mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) R)).transpose := by
    ext a c; simp [Matrix.mvPolynomialX]
  rw [h, Matrix.det_transpose, ← RingHom.map_det, map_ne_zero_iff _ hφ]
  exact Matrix.det_mvPolynomialX_ne_zero _ _

def qhPhi (R : Type) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) R →ₐ[R] MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  aeval fun v : Fin n × Fin n => X v.2 * C (X v)

lemma qh_phi_mono1 (d : Fin n × Fin n →₀ ℕ) :
    qhPhi R n (monomial d 1) = monomial (Finsupp.mapDomain Prod.snd d) (monomial d 1) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d1 d2 h1 h2 =>
    have e : (monomial (d1 + d2) (1 : R)) = monomial d1 1 * monomial d2 1 := by
      rw [monomial_mul, one_mul]
    rw [e, map_mul, h1, h2, monomial_mul, Finsupp.mapDomain_add]
  | single v e =>
    rw [← X_pow_eq_monomial, map_pow, qhPhi, aeval_X, mul_pow, Finsupp.mapDomain_single, ← map_pow,
      X_pow_eq_monomial, mul_comm, C_mul_monomial, mul_one]

lemma qh_phi_mono (d : Fin n × Fin n →₀ ℕ) (r : R) :
    qhPhi R n (monomial d r) = monomial (Finsupp.mapDomain Prod.snd d) (monomial d r) := by
  have e : monomial d r = r • monomial d (1 : R) := by rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, qh_phi_mono1, smul_monomial]

lemma qh_phi_coeff (Q : MvPolynomial (Fin n × Fin n) R) (d0 : Fin n × Fin n →₀ ℕ) :
    coeff d0 (coeff (Finsupp.mapDomain Prod.snd d0) (qhPhi R n Q)) = coeff d0 Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [qh_phi_mono]
    by_cases h : d = d0
    · subst h; simp
    · rw [coeff_monomial, coeff_monomial, if_neg h]
      split_ifs
      · rw [coeff_monomial, if_neg h]
      · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, coeff_add, hp, hq]

lemma qh_weight (d : Fin n × Fin n →₀ ℕ) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) d = ⇑(Finsupp.mapDomain Prod.snd d) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d1 d2 h1 h2 => rw [map_add, h1, h2, Finsupp.mapDomain_add, Finsupp.coe_add]
  | single v e =>
    rw [Finsupp.weight_single, Finsupp.mapDomain_single]
    funext a
    simp [Formalism.GradedWeylDivisibility.colW, Finsupp.single_apply, Pi.single_apply, eq_comm]

lemma qh_homog [IsDomain R] (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ))) :
    IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) Q ν := by
  have h := qh_generic (B := MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))
    (Matrix.diagonal fun a => X a) (Matrix.of fun a c : Fin n => C (X (c, a)))
    (fun a c hac => Matrix.diagonal_apply_ne _ hac.ne) (fun a => by simp)
    (qh_det_ne (C : _ →+* MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R)) (C_injective _ _)) Q ν hQ
  have e1 : aeval (fun v : Fin n × Fin n => ((Matrix.diagonal fun a => X a) *
      (Matrix.of fun a c : Fin n => (C (X (c, a)) : MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) :
        Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) v.2 v.1) Q
      = qhPhi R n Q := by
    rw [qhPhi]; congr 2; funext v; simp [Matrix.diagonal_mul]
  have e2 : aeval (fun v : Fin n × Fin n =>
      (Matrix.of fun a c : Fin n => (C (X (c, a)) : MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) v.2 v.1) Q
      = C Q := by
    have := MvPolynomial.comp_aeval_apply (R := R) (fun v : Fin n × Fin n => (X v : MvPolynomial (Fin n × Fin n) R))
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin n × Fin n) R) (MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) Q
    rw [aeval_X_left_apply] at this
    exact this.symm
  have e3 : (∏ a, (Matrix.diagonal fun a => (X a : MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) a a ^ ν a) =
      monomial (Finsupp.equivFunOnFinite.symm ν) 1 := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    simp
  rw [e1, e2, e3, mul_comm, C_mul_monomial, mul_one] at h
  intro d hd
  rw [qh_weight]
  by_contra hne
  apply hd
  rw [← qh_phi_coeff, h, coeff_monomial, if_neg, coeff_zero]
  intro heq
  apply hne
  rw [← heq]; rfl

lemma qh_invariant [IsDomain R] (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ)))
    (l j : Fin n) (hlj : l < j) :
    Formalism.GradedWeylDivisibility.colAddGen R l j Q = rename some Q := by
  have h := qh_generic (B := MvPolynomial (Option (Fin n × Fin n)) R)
    (Matrix.transvection j l (X none)) (Matrix.of fun a c : Fin n => X (some (c, a)))
    (fun a c hac => by
      have : ¬ (j = a ∧ l = c) := by rintro ⟨rfl, rfl⟩; exact absurd hlj (not_lt.2 hac.le)
      simp [Matrix.transvection, hac.ne, this])
    (fun a => by
      have : ¬ (j = a ∧ l = a) := by rintro ⟨rfl, h⟩; exact hlj.ne h
      simp [Matrix.transvection, this])
    (qh_det_ne (rename some : MvPolynomial (Fin n × Fin n) R →ₐ[R] _).toRingHom
      (rename_injective _ (Option.some_injective _)) |> fun h => by simpa using h) Q ν hQ
  have e3 : (∏ a, (Matrix.transvection j l (X none : MvPolynomial (Option (Fin n × Fin n)) R)) a a ^ ν a) = 1 := by
    apply Finset.prod_eq_one
    intro a _
    have : ¬ (j = a ∧ l = a) := by rintro ⟨rfl, h⟩; exact hlj.ne h
    simp [Matrix.transvection, this]
  rw [e3, one_mul] at h
  have e1 : Formalism.GradedWeylDivisibility.colAddGen R l j Q = aeval (fun v : Fin n × Fin n => ((Matrix.transvection j l (X none)) *
      (Matrix.of fun a c : Fin n => (X (some (c, a)) : MvPolynomial (Option (Fin n × Fin n)) R)) :
        Matrix (Fin n) (Fin n) (MvPolynomial (Option (Fin n × Fin n)) R)) v.2 v.1) Q := by
    rw [Formalism.GradedWeylDivisibility.colAddGen]; congr 2; funext v
    by_cases hv : v.2 = j
    · rw [if_pos hv, hv, Matrix.transvection_mul_apply_same]
      simp [← hv]
    · rw [if_neg hv, Matrix.transvection_mul_apply_of_ne _ _ _ _ hv]
      simp
  rw [e1, h, ← aeval_X_left_apply (rename some Q), aeval_rename]
  rfl

lemma qh_mem_dualWeyl [IsDomain R] (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ))) :
    Q ∈ Formalism.GradedWeylDivisibility.dualWeyl R n n ν := by
  rw [Formalism.GradedWeylDivisibility.dualWeyl, Submodule.mem_inf]
  refine ⟨qh_homog Q ν hQ, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  intro l j hlj
  exact qh_invariant Q ν hQ l j hlj

end Formalism.InvariantFactorPaths.ColumnFamilies
