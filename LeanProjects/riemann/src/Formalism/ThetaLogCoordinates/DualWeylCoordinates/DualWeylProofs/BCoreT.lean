import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.BCoreW

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

lemma qb_evGL_algebraMap {R : Type} [CommRing R] (g : GL (Fin n) R) (P : MvPolynomial (Fin n × Fin n) ℤ) :
    evGL g (algebraMap _ (GLCoord ℤ n) P) =
      MvPolynomial.eval₂Hom (Int.castRingHom R) (fun ab : Fin n × Fin n => g.val ab.1 ab.2) P :=
  IsLocalization.Away.lift_eq _ _ _

lemma qb_evGL_minorC {R : Type} [CommRing R] (g : GL (Fin n) R) {h : ℕ} (J I : Finset (Fin n))
    (hJ : J.card = h) (hI : I.card = h) :
    evGL g (minorC J I hJ hI) =
      Matrix.det (Matrix.of fun a b : Fin h => g.val (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)) := by
  unfold minorC
  rw [qb_evGL_algebraMap, RingHom.map_det]
  congr 1
  ext a b
  simp [genMat]

lemma qb_evGL_detU {R : Type} [CommRing R] (g : GL (Fin n) R) : evGL g (detU n : GLCoord ℤ n) = g.val.det := by
  have : ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = algebraMap _ (GLCoord ℤ n) (genMat ℤ n).det := rfl
  rw [this, qb_evGL_algebraMap, RingHom.map_det, genMat_map_eval]

lemma qb_evGL_detU_zpow {R : Type} [CommRing R] (g : GL (Fin n) R) (u : Rˣ) (hu : (u : R) = g.val.det) (z : ℤ) :
    evGL g ((detU n ^ z : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((u ^ z : Rˣ) : R) := by
  have : Units.map (evGL g : GLCoord ℤ n →* R) (detU n) = u := Units.ext (by
    rw [Units.coe_map, hu]; exact qb_evGL_detU g)
  rw [← this, ← map_zpow, Units.coe_map]
  rfl

lemma qb_minor_diagonal {R : Type} [CommRing R] (d : Fin n → R) {h : ℕ} (J I : Finset (Fin n))
    (hJ : J.card = h) (hI : I.card = h) :
    Matrix.det (Matrix.of fun a b : Fin h => Matrix.diagonal d (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)) =
      if J = I then ∏ x ∈ J, d x else 0 := by
  split_ifs with hJI
  · subst hJI
    have : (Matrix.of fun a b : Fin h => Matrix.diagonal d (J.orderEmbOfFin hJ a) (J.orderEmbOfFin hI b)) =
        Matrix.diagonal fun a => d (J.orderEmbOfFin hJ a) := by
      ext a b
      simp [Matrix.diagonal_apply]
    rw [this, Matrix.det_diagonal]
    conv_rhs => rw [← map_orderEmbOfFin_univ J hJ]
    rw [prod_map]
    rfl
  · have : ∃ x ∈ J, x ∉ I := by
      by_contra hc
      push Not at hc
      exact hJI (eq_of_subset_of_card_le hc (by rw [hJ, hI]))
    obtain ⟨x, hxJ, hxI⟩ := this
    rw [← map_orderEmbOfFin_univ J hJ, mem_map] at hxJ
    obtain ⟨a, -, rfl⟩ := hxJ
    apply Matrix.det_eq_zero_of_row_eq_zero a
    intro b
    rw [Matrix.of_apply, Matrix.diagonal_apply_ne]
    intro hab
    apply hxI
    have := orderEmbOfFin_mem I hI b
    rw [← hab] at this
    exact this

lemma qb_prod_single {κ G : Type*} [AddCommMonoid G] (s : Finset κ) (f : κ → G) :
    ∏ x ∈ s, (AddMonoidAlgebra.single (f x) (1 : ℤ)) = AddMonoidAlgebra.single (∑ x ∈ s, f x) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, AddMonoidAlgebra.single_mul_single, one_mul]

def qb_sU (w : Fin n → ℤ) : (AddMonoidAlgebra ℤ (Fin n → ℤ))ˣ :=
  Units.map (AddMonoidAlgebra.of ℤ (Fin n → ℤ)) (toUnits (Multiplicative.ofAdd w))

lemma qb_sU_val (w : Fin n → ℤ) : ((qb_sU w : (AddMonoidAlgebra ℤ (Fin n → ℤ))ˣ) : AddMonoidAlgebra ℤ (Fin n → ℤ)) =
    AddMonoidAlgebra.single w 1 := rfl

lemma qb_sU_zpow (w : Fin n → ℤ) (z : ℤ) : qb_sU w ^ z = qb_sU (z • w) := by
  unfold qb_sU
  rw [← map_zpow, ← map_zpow, ofAdd_zsmul]

variable [NeZero n]

theorem qb_evGL_torus_TMat (mu : Fin n → ℤ) (J I : TIdx mu) :
    evGL (torusPt n) (TMat mu J I) = if J = I then AddMonoidAlgebra.single (qb_wtT mu I) 1 else 0 := by
  unfold TMat
  rw [map_mul, map_prod]
  have hdet : ((qb_sU (∑ a : Fin n, Pi.single a (1 : ℤ)) : (AddMonoidAlgebra ℤ (Fin n → ℤ))ˣ) :
      AddMonoidAlgebra ℤ (Fin n → ℤ)) = (torusPt n).val.det := by
    rw [qb_sU_val]
    change _ = Matrix.det (Matrix.diagonal _)
    rw [Matrix.det_diagonal, qb_prod_single]
  rw [qb_evGL_detU_zpow (torusPt n) _ hdet, qb_sU_zpow, qb_sU_val]
  have hm : ∀ c : ↥(TCols mu), evGL (torusPt n) (minorC (J c).1 (I c).1 (J c).2 (I c).2) =
      if (J c).1 = (I c).1 then AddMonoidAlgebra.single (∑ x ∈ (J c).1, Pi.single x (1 : ℤ)) 1 else 0 := by
    intro c
    rw [qb_evGL_minorC]
    change Matrix.det (Matrix.of fun a b => Matrix.diagonal _ _ _) = _
    rw [qb_minor_diagonal, qb_prod_single]
  simp only [hm]
  split_ifs with hJI
  · subst hJI
    simp only [if_true]
    rw [qb_prod_single, AddMonoidAlgebra.single_mul_single, one_mul]
    congr 1
    funext a
    simp only [qb_wtT, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Pi.single_apply, card_filter,
      Nat.cast_sum, smul_eq_mul]
    simp
  · have : ∃ c, (J c).1 ≠ (I c).1 := by
      by_contra hc
      push Not at hc
      exact hJI (funext fun c => Subtype.ext (hc c))
    obtain ⟨c, hc⟩ := this
    rw [prod_eq_zero (mem_univ c) (if_neg hc), mul_zero]

lemma qb_equiv_apply {M : GLMod n} (CF : ColFam M) (j : CF.J) (i : M.ι) (K : TIdx (CF.mu j)) :
    ∑ k, M.A i k * (CF.ph j k K : GLCoord ℤ n) = ∑ K', (CF.ph j i K' : GLCoord ℤ n) * TMat (CF.mu j) K' K :=
  congrFun (congrFun (CF.equiv j) i) K

theorem qb_prMu_ph {M : GLMod n} (CF : ColFam M) (j : CF.J) (nu : Fin n → ℤ) (i : M.ι) (K : TIdx (CF.mu j)) :
    ∑ k, prMu M nu i k * CF.ph j k K = if qb_wtT (CF.mu j) K = nu then CF.ph j i K else 0 := by
  have h := congrArg (evGL (torusPt n)) (qb_equiv_apply CF j i K)
  simp only [map_sum, map_mul, Int.coe_castRingHom, map_intCast,
    qb_evGL_torus_TMat, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true] at h
  have h2 := congrArg (fun x => x.coeff nu) h
  simp only [← zsmul_eq_mul', ← zsmul_eq_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    smul_eq_mul] at h2
  have hp : ∀ i k, prMu M nu i k = (evGL (torusPt n) (M.A i k)).coeff nu := fun _ _ => rfl
  simp only [hp]
  rw [mul_ite, mul_one, mul_zero] at h2
  rw [← h2]
  exact sum_congr rfl fun k _ => mul_comm _ _

end Formalism.InvariantFactorPaths.ColumnFamilies
