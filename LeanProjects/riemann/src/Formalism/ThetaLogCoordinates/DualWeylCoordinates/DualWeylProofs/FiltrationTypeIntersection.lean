import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.HighestVectorsEqLattice

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

lemma qd_typeSum_mono (M : GLMod n) {pi pi' : Set (Fin n → ℤ)} (h : pi ⊆ pi') : typeSum M pi ≤ typeSum M pi' :=
  Submodule.span_mono (by
    rintro _ ⟨mu, hmu, v, hv, g, rfl⟩
    exact ⟨mu, h hmu, v, hv, g, rfl⟩)

def qd_low (mu : Fin n → ℤ) : Set (Fin n → ℤ) := {la | Dominant la ∧ DomLE la mu}

variable [NeZero n]

def qd_phQ {M : GLMod n} (CF : ColFam M) (j : CF.J) : (TIdx (CF.mu j) → ℚ) →ₗ[ℚ] (M.ι → ℚ) :=
  Matrix.mulVecLin ((CF.ph j).map (Int.castRingHom ℚ))

lemma qd_phQ_eq {M : GLMod n} (CF : ColFam M) (j : CF.J) (w : TIdx (CF.mu j) → ℚ) :
    qd_phQ CF j w = ∑ I, w I • (fun i => (CF.vec j I i : ℚ)) := by
  funext i
  simp [qd_phQ, Matrix.mulVec, dotProduct, ColFam.vec, Finset.sum_apply, mul_comm]

lemma qd_phQ_single {M : GLMod n} (CF : ColFam M) (j : CF.J) (I : TIdx (CF.mu j)) :
    qd_phQ CF j (Pi.single I 1) = fun i => (CF.vec j I i : ℚ) := by
  classical
  rw [qd_phQ_eq]
  simp [Pi.single_apply, ite_smul]

lemma qd_A_can {M : GLMod n} (CF : ColFam M) (j : CF.J) (g : GL (Fin n) ℚ) :
    Matrix.mulVec (M.A.map (evGL g)) (fun i => (CF.vec j (canT (CF.mu j)) i : ℚ)) =
      qd_phQ CF j (qd_gcan (CF.mu j) g) := by
  funext i
  have h := congrArg (evGL g) (qb_equiv_apply CF j i (canT (CF.mu j)))
  simp only [map_sum, map_mul, map_intCast] at h
  simpa [Matrix.mulVec, dotProduct, ColFam.vec, qd_phQ, qd_gcan] using h

lemma qd_ev_phQ {M : GLMod n} (CF : ColFam M) (j : CF.J) (nu : Fin n → ℤ) (w : TIdx (CF.mu j) → ℚ) (i : M.ι) :
    qb_ev M ℚ nu (qd_phQ CF j w) i = ∑ I, w I • qb_ev M ℚ nu (fun i => (CF.vec j I i : ℚ)) i := by
  rw [qd_phQ_eq, ← qb_evL_apply, map_sum, Finset.sum_apply]
  simp only [map_smul, qb_evL_apply, Pi.smul_apply]

lemma qd_ev_phQ_zero {M : GLMod n} (CF : ColFam M) (j : CF.J) (nu : Fin n → ℤ) (h : ¬ DomLE nu (CF.mu j))
    (w : TIdx (CF.mu j) → ℚ) : qb_ev M ℚ nu (qd_phQ CF j w) = 0 := by
  funext i
  rw [qd_ev_phQ]
  simp only [qb_key_zero CF ℚ j _ nu h, Pi.zero_apply, smul_zero, Finset.sum_const_zero]

lemma qd_ev_phQ_top {M : GLMod n} (CF : ColFam M) (j : CF.J) (w : TIdx (CF.mu j) → ℚ)
    (hw : qd_Lam (CF.mu j) w = 0) : qb_ev M ℚ (CF.mu j) (qd_phQ CF j w) = 0 := by
  funext i
  rw [qd_ev_phQ]
  simp only [qb_key_eq, ← mul_smul_comm]
  rw [← Finset.mul_sum, ← qd_Lam_apply, hw, mul_zero, Pi.zero_apply]

omit [NeZero n] in
lemma qd_low_minus (mu : Fin n → ℤ) : DomLowerSet (qd_low mu \ {mu}) := by
  refine ⟨fun la hla => hla.1.1, fun la hla nu hnu hle => ⟨⟨hnu, qb_domLE_trans hle hla.1.2⟩, ?_⟩⟩
  intro h
  rw [Set.mem_singleton_iff] at h
  subst h
  exact hla.2 (qb_domLE_antisymm hla.1.2 hle)

theorem qd_ph_type (hA : LemmaA) {M : GLMod n} (CF : ColFam M) : ∀ (N : ℕ) (j : CF.J),
    (by classical exact (univ.filter fun j' => DomLE (CF.mu j') (CF.mu j)).card) ≤ N →
    ∀ w, qd_phQ CF j w ∈ typeSum M (qd_low (CF.mu j)) := by
  classical
  intro N
  induction N with
  | zero =>
    intro j hj
    exfalso
    have : j ∈ univ.filter fun j' => DomLE (CF.mu j') (CF.mu j) := by simp [qb_domLE_refl]
    have := Finset.card_pos.2 ⟨j, this⟩
    omega
  | succ N ih =>
    intro j hj w
    obtain ⟨w', hw', he⟩ := qd_gen (CF.mu j) w
    have hsplit : qd_phQ CF j w = qd_phQ CF j w' + qd_phQ CF j (w - w') := by
      rw [← map_add, add_sub_cancel]
    rw [hsplit]
    apply Submodule.add_mem
    · have : Submodule.span ℚ (Set.range (qd_gcan (CF.mu j))) ≤
          (typeSum M (qd_low (CF.mu j))).comap (qd_phQ CF j) := by
        rw [Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, ← qd_A_can]
        exact Submodule.subset_span ⟨CF.mu j, ⟨CF.dom j, qb_domLE_refl _⟩, _, qd_vec_can_high CF ℚ j, g, rfl⟩
      exact this hw'
    · have hv : qd_Lam (CF.mu j) (w - w') = 0 := by rw [map_sub, he, sub_self]
      obtain ⟨a, ha⟩ : ∃ a : qb_Idx CF → ℚ, ∑ y, a y • qb_vecF CF ℚ y = qd_phQ CF j (w - w') := by
        have : qd_phQ CF j (w - w') ∈ Submodule.span ℚ (Set.range (qb_vecF CF ℚ)) := by
          rw [(qb_basisR hA CF ℚ).2]; trivial
        exact (Submodule.mem_span_range_iff_exists_fun ℚ).1 this
      have hs := qb_supp_in hA CF ℚ a _ (qd_low_minus (CF.mu j)) (by
        intro nu hnu hnot
        rw [ha]
        by_cases h : nu = CF.mu j
        · rw [h]; exact qd_ev_phQ_top CF j _ hv
        · exact qd_ev_phQ_zero CF j nu (fun hd => hnot ⟨⟨hnu, hd⟩, h⟩) _)
      rw [← ha]
      refine Submodule.sum_mem _ fun y _ => ?_
      by_cases hy : a y = 0
      · rw [hy, zero_smul]; exact zero_mem _
      · apply Submodule.smul_mem
        have hy' := hs y hy
        have hcard : (univ.filter fun j' => DomLE (CF.mu j') (CF.mu y.1)).card ≤ N := by
          have hlt : (univ.filter fun j' => DomLE (CF.mu j') (CF.mu y.1)) ⊂
              (univ.filter fun j' => DomLE (CF.mu j') (CF.mu j)) := by
            refine (Finset.ssubset_iff_of_subset ?_).2 ⟨j, by simp [qb_domLE_refl], ?_⟩
            · intro j' hj'
              simp only [mem_filter, mem_univ, true_and] at hj' ⊢
              exact qb_domLE_trans hj' hy'.1.2
            · simp only [mem_filter, mem_univ, true_and]
              intro hd
              exact hy'.2 (qb_domLE_antisymm hy'.1.2 hd)
          have := Finset.card_lt_card hlt
          omega
        have h1 := ih y.1 hcard (Pi.single y.2.1 1)
        rw [qd_phQ_single] at h1
        exact qd_typeSum_mono M (show qd_low (CF.mu y.1) ⊆ qd_low (CF.mu j) from
          fun la hla => ⟨hla.1, qb_domLE_trans hla.2 hy'.1.2⟩) h1

theorem filtration_type_intersection_ofA : LemmaA → FiltrationTypeIntersection := by
  intro hA n _ M CF pi hpi x
  classical
  constructor
  · intro hx
    refine Submodule.span_induction (p := fun x _ => (fun i => (x i : ℚ)) ∈ typeSum M pi) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, hj, I, rfl⟩
      have h1 := qd_ph_type hA CF _ j le_rfl (Pi.single I 1)
      rw [qd_phQ_single] at h1
      exact qd_typeSum_mono M (show qd_low (CF.mu j) ⊆ pi from fun la hla => hpi.2 _ hj la hla.1 hla.2) h1
    · have : (fun i => (((0 : M.ι → ℤ) i : ℤ) : ℚ)) = 0 := by funext i; simp
      rw [this]; exact zero_mem _
    · intro x y _ _ hx hy
      have : (fun i => (((x + y) i : ℤ) : ℚ)) = (fun i => (x i : ℚ)) + fun i => (y i : ℚ) := by funext i; simp
      rw [this]; exact add_mem hx hy
    · intro c x _ hx
      have : (fun i => (((c • x) i : ℤ) : ℚ)) = (c : ℚ) • fun i => (x i : ℚ) := by funext i; simp
      rw [this]; exact Submodule.smul_mem _ _ hx
  · intro hx
    have hK : ∀ nu, Dominant nu → nu ∉ pi → typeSum M pi ≤ LinearMap.ker (qb_evL M ℚ nu) := by
      intro nu hnu hnot
      unfold typeSum
      rw [Submodule.span_le]
      rintro _ ⟨mu, hmu, v, hv, g, rfl⟩
      have hvs := highest_vectors_rational_span_of hA n M CF mu (hpi.1 mu hmu) v hv
      have : Submodule.span ℚ {y | ∃ j, CF.mu j = mu ∧ y = fun i => (CF.vec j (canT (CF.mu j)) i : ℚ)} ≤
          (LinearMap.ker (qb_evL M ℚ nu)).comap (Matrix.mulVecLin (M.A.map (evGL g))) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, hj, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mem_ker, Matrix.mulVecLin_apply, qd_A_can, qb_evL_apply]
        exact qd_ev_phQ_zero CF j nu (fun hd => hnot (hpi.2 _ (by rw [hj]; exact hmu) nu hnu hd)) _
      exact this hvs
    obtain ⟨b, hb⟩ : ∃ b : qb_Idx CF → ℤ, ∑ y, b y • qb_vecF CF ℤ y = x := by
      have : x ∈ Submodule.span ℤ (Set.range (qb_vecF CF ℤ)) := by rw [(qb_basisR hA CF ℤ).2]; trivial
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
    have hcast : (fun i => (x i : ℚ)) = ∑ y, (b y : ℚ) • qb_vecF CF ℚ y := by
      funext i
      rw [← hb]
      simp [qb_vecF, Finset.sum_apply]
    have hs := qb_supp_in hA CF ℚ (fun y => (b y : ℚ)) pi hpi (fun nu hnu hnot => by
      rw [← hcast]; exact hK nu hnu hnot hx)
    rw [← hb]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hy : b y = 0
    · rw [hy, zero_smul]; exact zero_mem _
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨y.1, hs y (by exact_mod_cast hy), y.2.1, ?_⟩
      funext i
      simp only [qb_vecF, Int.cast_id]

theorem filtration_type_intersection_of : LemmaA → SBasis → FiltrationTypeIntersection := fun hA _ => filtration_type_intersection_ofA hA

end Formalism.InvariantFactorPaths.ColumnFamilies
