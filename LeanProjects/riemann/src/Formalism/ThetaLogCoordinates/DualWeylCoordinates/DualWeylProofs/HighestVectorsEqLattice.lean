import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.HighestVectorsRationalSpan

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

lemma qd_high_zero (M : GLMod n) (R : Type) [CommRing R] (mu : Fin n → ℤ) : IsHighest M R mu 0 :=
  ⟨Matrix.mulVec_zero _, fun R' _ _ u _ _ => by
    have e : (fun i => algebraMap R R' ((0 : M.ι → R) i)) = 0 := by funext i; simp
    rw [e, Matrix.mulVec_zero]⟩

lemma qd_high_add (M : GLMod n) (R : Type) [CommRing R] (mu : Fin n → ℤ) {x y : M.ι → R}
    (hx : IsHighest M R mu x) (hy : IsHighest M R mu y) : IsHighest M R mu (x + y) :=
  ⟨by rw [Matrix.mulVec_add, hx.1, hy.1], fun R' _ _ u h1 h2 => by
    have e : (fun i => algebraMap R R' ((x + y) i)) =
        (fun i => algebraMap R R' (x i)) + fun i => algebraMap R R' (y i) := by funext i; simp
    rw [e, Matrix.mulVec_add, hx.2 R' u h1 h2, hy.2 R' u h1 h2]⟩

lemma qd_high_smul (M : GLMod n) (R : Type) [CommRing R] (mu : Fin n → ℤ) (c : R) {x : M.ι → R}
    (hx : IsHighest M R mu x) : IsHighest M R mu (c • x) :=
  ⟨by rw [Matrix.mulVec_smul, hx.1], fun R' _ _ u h1 h2 => by
    have e : (fun i => algebraMap R R' ((c • x) i)) = algebraMap R R' c • fun i => algebraMap R R' (x i) := by
      funext i; simp
    rw [e, Matrix.mulVec_smul, hx.2 R' u h1 h2]⟩

lemma qd_det_unitri {R : Type} [CommRing R] (u : GL (Fin n) R) (h1 : ∀ a, u.val a a = 1)
    (h2 : ∀ a b, b < a → u.val a b = 0) : Matrix.GeneralLinearGroup.det u = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular (fun a b hab => h2 a b hab)]
  simp [h1]

variable [NeZero n]

lemma qd_minor_unitri {R : Type} [CommRing R] (u : GL (Fin n) R) (h1 : ∀ a, u.val a a = 1)
    (h2 : ∀ a b, b < a → u.val a b = 0) (mu : Fin n → ℤ) (c : ↥(TCols mu))
    (J : {J : Finset (Fin n) // J.card = colH mu c}) :
    evGL u (minorC J.1 (canT mu c).1 J.2 (canT mu c).2) = if J = canT mu c then 1 else 0 := by
  rw [qb_evGL_minorC]
  split_ifs with hJ
  · subst hJ
    rw [Matrix.det_of_isUpperTriangular]
    · simp [h1]
    · intro a b hab
      exact h2 _ _ ((OrderEmbedding.lt_iff_lt _).2 hab)
  · obtain ⟨j, hjJ, hj⟩ : ∃ j ∈ J.1, colH mu c ≤ j.val := by
      by_contra hcon
      push Not at hcon
      apply hJ
      apply Subtype.ext
      apply Finset.eq_of_subset_of_card_le
      · intro j hj
        exact (qb_mem_canT mu c j).2 (hcon j hj)
      · rw [J.2, (canT mu c).2]
    have hr : j ∈ Set.range (J.1.orderEmbOfFin J.2) := by
      rw [Finset.range_orderEmbOfFin]; exact hjJ
    obtain ⟨a, ha⟩ := hr
    apply Matrix.det_eq_zero_of_row_eq_zero a
    intro b
    rw [Matrix.of_apply, ha, qd_can_emb]
    apply h2
    exact Fin.lt_def.2 (lt_of_lt_of_le (show (Fin.castLE (colH_le mu c) b).val < colH mu c from b.2) hj)

lemma unipotent_eval_canonical {R : Type} [CommRing R] (u : GL (Fin n) R) (h1 : ∀ a, u.val a a = 1)
    (h2 : ∀ a b, b < a → u.val a b = 0) (mu : Fin n → ℤ) (K : TIdx mu) :
    evGL u (TMat mu K (canT mu)) = if K = canT mu then 1 else 0 := by
  unfold TMat
  rw [map_mul, map_prod, qd_evGL_detU, qd_det_unitri u h1 h2, one_zpow, Units.val_one, one_mul]
  simp only [qd_minor_unitri u h1 h2]
  split_ifs with hK
  · subst hK
    simp
  · obtain ⟨c, hc⟩ : ∃ c, K c ≠ canT mu c := by
      by_contra hcon
      push Not at hcon
      exact hK (funext hcon)
    exact Finset.prod_eq_zero (Finset.mem_univ c) (if_neg hc)

lemma qd_vec_can_high {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] (j : CF.J) :
    IsHighest M R (CF.mu j) (fun i => (CF.vec j (canT (CF.mu j)) i : R)) := by
  constructor
  · funext i
    have := congrArg (Int.cast : ℤ → R) (qb_prMu_ph CF j (CF.mu j) i (canT (CF.mu j)))
    rw [if_pos (qb_wtT_can (CF.dom j))] at this
    push_cast at this
    simpa [Matrix.mulVec, dotProduct, ColFam.vec] using this
  · intro R' _ _ u h1 h2
    funext i
    have h := congrArg (evGL u) (qb_equiv_apply CF j i (canT (CF.mu j)))
    simp only [map_sum, map_mul, map_intCast, unipotent_eval_canonical u h1 h2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    simpa [Matrix.mulVec, dotProduct, ColFam.vec] using h

lemma qd_high_cast (M : GLMod n) (mu : Fin n → ℤ) (x : M.ι → ℤ) (hx : IsHighest M ℤ mu x) :
    IsHighest M ℚ mu (fun i => (x i : ℚ)) := by
  constructor
  · funext i
    have := congrArg (Int.cast : ℤ → ℚ) (congrFun hx.1 i)
    simpa [Matrix.mulVec, dotProduct] using this
  · intro R' _ _ u h1 h2
    have := hx.2 R' u h1 h2
    simpa using this

theorem highest_vectors_eq_lattice_of : LemmaA → HighestVectorsEqLattice := by
  intro hA n _ M CF mu hmu
  classical
  ext x
  constructor
  · intro hx
    refine Submodule.span_induction (p := fun x _ => IsHighest M ℤ mu x) ?_ (qd_high_zero M ℤ mu)
      (fun x y _ _ hx hy => qd_high_add M ℤ mu hx hy) (fun c x _ hx => qd_high_smul M ℤ mu c hx) hx
    rintro _ ⟨j, rfl, rfl⟩
    have := qd_vec_can_high CF ℤ j
    simpa using this
  · intro hx
    have hQ := highest_vectors_rational_span_of hA n M CF mu hmu _ (qd_high_cast M mu x hx)
    obtain ⟨b, hb⟩ : ∃ b : qb_Idx CF → ℤ, ∑ y, b y • qb_vecF CF ℤ y = x := by
      have : x ∈ Submodule.span ℤ (Set.range (qb_vecF CF ℤ)) := by rw [(qb_basisR hA CF ℤ).2]; trivial
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
    let S : Set (qb_Idx CF) := {y | CF.mu y.1 = mu ∧ y.2.1 = canT (CF.mu y.1)}
    have hcast : (fun i => (x i : ℚ)) = ∑ y, (b y : ℚ) • qb_basis hA CF ℚ y := by
      funext i
      rw [← hb]
      simp [qb_basis_apply, qb_vecF, Finset.sum_apply]
    have hS : (fun i => (x i : ℚ)) ∈ Submodule.span ℚ (qb_basis hA CF ℚ '' S) := by
      refine Submodule.span_mono ?_ hQ
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨⟨j, ⟨canT (CF.mu j), qd_canT_std _⟩⟩, ⟨hj, rfl⟩, by rw [qb_basis_apply]; rfl⟩
    rw [Module.Basis.mem_span_image, hcast] at hS
    have hsupp : ∀ y, b y ≠ 0 → y ∈ S := by
      intro y hy
      apply hS
      rw [Finset.mem_coe, Finsupp.mem_support_iff, Module.Basis.repr_sum_self]
      exact_mod_cast hy
    rw [← hb]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hy : b y = 0
    · rw [hy, zero_smul]; exact zero_mem _
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      obtain ⟨e1, e2⟩ := hsupp y hy
      refine ⟨y.1, e1, ?_⟩
      funext i
      simp only [qb_vecF, Int.cast_id]
      rw [e2]

end Formalism.InvariantFactorPaths.ColumnFamilies
