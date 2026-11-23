import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLengthEqAndCardEqPowOfIsFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSublatticeIndexRpowLeSolomonStatement

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.LatticePairSum

section Index

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

theorem index_range_eq_pow {r : ℕ} (A : Matrix (Fin r) (Fin r) O) (hA : A.det ≠ 0) :
    ∃ n : ℕ, IsDiscreteValuationRing.addVal O A.det = n ∧
      (LinearMap.range A.mulVecLin).toAddSubgroup.index =
        Nat.card (IsLocalRing.ResidueField O) ^ n := by
  have hl := GlobalTheory.length_quotient_range_mulVecLin_eq_addVal_det A
  have hne : Module.length O ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ≠ ⊤ := by
    rw [hl, ne_eq, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact hA
  have hfl := Module.length_ne_top_iff.mp hne
  obtain ⟨n, hn, hc⟩ := GlobalTheory.exists_length_eq_and_card_eq_pow_of_isFiniteLength O _ hfl
  exact ⟨n, by rw [← hl, hn], hc⟩

theorem index_range_ne_zero {r : ℕ} (A : Matrix (Fin r) (Fin r) O) (hA : A.det ≠ 0) :
    (LinearMap.range A.mulVecLin).toAddSubgroup.index ≠ 0 := by
  obtain ⟨n, -, hc⟩ := index_range_eq_pow A hA
  rw [hc]
  exact pow_ne_zero _ Nat.card_pos.ne'

theorem index_range_transpose {r : ℕ} (A : Matrix (Fin r) (Fin r) O) (hA : A.det ≠ 0) :
    (LinearMap.range A.transpose.mulVecLin).toAddSubgroup.index =
      (LinearMap.range A.mulVecLin).toAddSubgroup.index := by
  obtain ⟨n, hn, hc⟩ := index_range_eq_pow A hA
  obtain ⟨m, hm, hd⟩ := index_range_eq_pow A.transpose (by rwa [Matrix.det_transpose])
  rw [Matrix.det_transpose, hn] at hm
  have : n = m := by exact_mod_cast hm
  rw [hc, hd, this]

theorem exists_matrix_of_index_ne_zero {r : ℕ} (M : Submodule O (Fin r → O))
    (hM : M.toAddSubgroup.index ≠ 0) :
    ∃ B : Matrix (Fin r) (Fin r) O, B.det ≠ 0 ∧ LinearMap.range B.mulVecLin = M := by
  classical
  have hfin : Finite ((Fin r → O) ⧸ M) := Nat.finite_of_card_ne_zero hM
  have hinf : Infinite O := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    exact IsDiscreteValuationRing.not_isField O (Finite.isField_of_domain O)
  have htors : Module.finrank O ((Fin r → O) ⧸ M) = 0 := by
    apply Module.finrank_eq_zero_of_rank_eq_zero
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun c : O => c • x)
    exact ⟨a - b, sub_ne_zero.mpr hab, by rw [sub_smul, he, sub_self]⟩
  have hrank : Module.finrank O M = r := by
    have := Submodule.finrank_quotient_add_finrank M
    simpa [htors] using this
  let b := Module.finBasisOfFinrankEq O M hrank
  let B : Matrix (Fin r) (Fin r) O := Matrix.of fun i j => (b j : Fin r → O) i
  have hB : LinearMap.range B.mulVecLin = M := by
    rw [Matrix.range_mulVecLin]
    have h1 : Set.range B.col = Subtype.val '' (Set.range b) := by
      ext v
      simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
      rfl
    have h2 : Submodule.span O (Subtype.val '' (Set.range b)) =
        (Submodule.span O (Set.range b)).map M.subtype := (Submodule.map_span M.subtype _).symm
    rw [h1, h2, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  refine ⟨B, ?_, hB⟩
  intro h0
  have hl := GlobalTheory.length_quotient_range_mulVecLin_eq_addVal_det B
  rw [h0, IsDiscreteValuationRing.addVal_zero, hB] at hl
  obtain ⟨n, hn, -⟩ := GlobalTheory.exists_length_eq_and_card_eq_pow O ((Fin r → O) ⧸ M)
  rw [hn] at hl
  exact ENat.coe_ne_top n hl

end Index

section Lat

variable (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  {r : ℕ}

noncomputable def incl (r : ℕ) : (Fin r → O) →ₗ[O] (Fin r → K) :=
  LinearMap.compLeft (Algebra.linearMap O K) (Fin r)

abbrev stdLat (r : ℕ) : Submodule O (Fin r → K) :=
  Submodule.span O (Set.range (Pi.basisFun K (Fin r)))

abbrev lat (X : Matrix (Fin r) (Fin r) K) : Submodule O (Fin r → K) :=
  (stdLat O K r).map ((X.mulVecLin).restrictScalars O)

variable {O K}

theorem incl_apply (x : Fin r → O) (i : Fin r) : incl O K r x i = algebraMap O K (x i) := rfl

theorem incl_injective : Function.Injective (incl O K r) := by
  intro x y h
  funext i
  exact IsFractionRing.injective O K (congrFun h i)

theorem stdLat_eq_range : stdLat O K r = LinearMap.range (incl O K r) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    funext j
    rw [incl_apply, Pi.basisFun_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · rintro _ ⟨x, rfl⟩
    have : incl O K r x = ∑ i, x i • (Pi.basisFun K (Fin r)) i := by
      funext j
      simp [incl_apply, Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_lat {X : Matrix (Fin r) (Fin r) K} {v : Fin r → K} :
    v ∈ lat O K X ↔ ∃ x : Fin r → O, X.mulVec (incl O K r x) = v := by
  rw [lat, stdLat_eq_range]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, rfl⟩

theorem map_mulVec_incl (A : Matrix (Fin r) (Fin r) O) (x : Fin r → O) :
    (A.map (algebraMap O K)).mulVec (incl O K r x) = incl O K r (A.mulVec x) := by
  funext i
  rw [incl_apply]
  exact (RingHom.map_mulVec (algebraMap O K) A x i).symm

theorem exists_int_matrix (X : Matrix (Fin r) (Fin r) K) (h : lat O K X ≤ stdLat O K r) :
    ∃ X₀ : Matrix (Fin r) (Fin r) O, X₀.map (algebraMap O K) = X := by
  classical
  have hc : ∀ j, ∃ y : Fin r → O, incl O K r y = X.mulVec (Pi.single j 1) := by
    intro j
    have h1 : X.mulVec (Pi.single j 1) ∈ lat O K X := by
      rw [mem_lat]
      refine ⟨Pi.single j 1, ?_⟩
      congr 1
      funext i
      rw [incl_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_eq_of_ne hij]
    have h2 := h h1
    rw [stdLat_eq_range] at h2
    exact h2
  choose y hy using hc
  refine ⟨Matrix.of fun i j => y j i, ?_⟩
  ext i j
  have := congrFun (hy j) i
  rw [incl_apply] at this
  simpa using this

end Lat

section Main

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K] {r : ℕ}

omit [IsDiscreteValuationRing O] in
theorem relIndex_stdLat (H : AddSubgroup (Fin r → K)) :
    H.relIndex (stdLat O K r).toAddSubgroup =
      (H.comap (incl O K r).toAddMonoidHom).index := by
  have h : (stdLat O K r).toAddSubgroup =
      (⊤ : AddSubgroup (Fin r → O)).map (incl O K r).toAddMonoidHom := by
    ext v
    rw [Submodule.mem_toAddSubgroup, stdLat_eq_range]
    simp
  rw [h, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right]

omit [IsDiscreteValuationRing O] in
theorem det_map_ne_zero (B : Matrix (Fin r) (Fin r) O) (hB : B.det ≠ 0) :
    (B.map (algebraMap O K)).det ≠ 0 := by
  have h1 : (B.map (algebraMap O K)).det = algebraMap O K B.det :=
    (RingHom.map_det (algebraMap O K) B).symm
  rw [h1]
  exact fun h => hB (IsFractionRing.injective O K (by simpa using h))

omit [IsDiscreteValuationRing O] in
theorem exists_dual (B : Matrix (Fin r) (Fin r) O) (hB : B.det ≠ 0) (g : GL (Fin r) K)
    (h : (lat O K (g : Matrix (Fin r) (Fin r) K)).comap (incl O K r) =
      LinearMap.range B.mulVecLin) :
    ∃ A : Matrix (Fin r) (Fin r) O,
      A.map (algebraMap O K) =
        ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * B.map (algebraMap O K) ∧
      A.det ≠ 0 ∧
      (stdLat O K r).toAddSubgroup.relIndex
          (lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup =
        (LinearMap.range A.mulVecLin).toAddSubgroup.index := by
  have hGi : ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * (g : Matrix (Fin r) (Fin r) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGG : (g : Matrix (Fin r) (Fin r) K) * ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  generalize hG : (g : Matrix (Fin r) (Fin r) K) = G at *
  generalize hGinv : ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = Gi at *
  have hle : lat O K (Gi * B.map (algebraMap O K)) ≤ stdLat O K r := by
    intro v hv
    obtain ⟨x, rfl⟩ := mem_lat.1 hv
    have h1 : B.mulVec x ∈ (lat O K G).comap (incl O K r) := by
      rw [h]; exact ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := mem_lat.1 (Submodule.mem_comap.1 h1)
    rw [stdLat_eq_range]
    refine ⟨y, ?_⟩
    rw [← Matrix.mulVec_mulVec, map_mulVec_incl, ← hy, Matrix.mulVec_mulVec, hGi,
      Matrix.one_mulVec]
  obtain ⟨A, hA⟩ := exists_int_matrix _ hle
  have hdet : A.det ≠ 0 := by
    intro h0
    have h1 : (A.map (algebraMap O K)).det = algebraMap O K A.det :=
      (RingHom.map_det (algebraMap O K) A).symm
    rw [h0, map_zero, hA, Matrix.det_mul] at h1
    have h2 : Gi.det ≠ 0 := by
      intro h3
      have := congrArg Matrix.det hGi
      rw [Matrix.det_mul, h3, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    exact (mul_ne_zero h2 (det_map_ne_zero B hB)) h1
  refine ⟨A, hA, hdet, ?_⟩
  have hmap : (lat O K G).toAddSubgroup =
      (stdLat O K r).toAddSubgroup.map G.mulVecLin.toAddMonoidHom := by
    ext v
    simp
  rw [hmap, ← AddSubgroup.relIndex_comap, relIndex_stdLat]
  congr 1
  ext x
  simp only [AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe, Submodule.mem_toAddSubgroup,
    LinearMap.mem_range, Matrix.mulVecLin_apply]
  constructor
  · intro hx
    rw [stdLat_eq_range] at hx
    obtain ⟨y, hy⟩ := hx
    have h1 : y ∈ (lat O K G).comap (incl O K r) := by
      refine Submodule.mem_comap.2 (mem_lat.2 ⟨x, hy.symm⟩)
    rw [h] at h1
    obtain ⟨z, rfl⟩ := h1
    refine ⟨z, incl_injective (K := K) ?_⟩
    rw [← map_mulVec_incl, hA, ← Matrix.mulVec_mulVec]
    rw [Matrix.mulVecLin_apply, ← map_mulVec_incl (K := K)] at hy
    rw [hy, Matrix.mulVec_mulVec, hGi, Matrix.one_mulVec]
  · rintro ⟨z, rfl⟩
    rw [stdLat_eq_range]
    refine ⟨B.mulVec z, ?_⟩
    rw [← map_mulVec_incl, ← map_mulVec_incl, hA, Matrix.mulVec_mulVec, ← mul_assoc, hGG,
      one_mul]

end Main

section Final

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K] {r : ℕ}

omit [IsDiscreteValuationRing O] in

theorem lat_le_of_range_transpose_le (B : Matrix (Fin r) (Fin r) O) (hB : B.det ≠ 0)
    (g₀ g₁ : GL (Fin r) K) (A₀ A₁ : Matrix (Fin r) (Fin r) O)
    (h₀ : A₀.map (algebraMap O K) =
      ((g₀⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * B.map (algebraMap O K))
    (h₁ : A₁.map (algebraMap O K) =
      ((g₁⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * B.map (algebraMap O K))
    (hr : LinearMap.range A₁.transpose.mulVecLin ≤ LinearMap.range A₀.transpose.mulVecLin) :
    lat O K (g₀ : Matrix (Fin r) (Fin r) K) ≤ lat O K (g₁ : Matrix (Fin r) (Fin r) K) := by
  classical
  have hcol : ∀ j, ∃ u : Fin r → O,
      A₀.transpose.mulVec u = A₁.transpose.mulVec (Pi.single j 1) := fun j => by
    obtain ⟨u, hu⟩ := hr (LinearMap.mem_range_self A₁.transpose.mulVecLin (Pi.single j 1))
    exact ⟨u, hu⟩
  choose u hu using hcol
  let U : Matrix (Fin r) (Fin r) O := Matrix.of fun i j => u j i
  have hU : A₁.transpose = A₀.transpose * U := by
    ext i j
    have := congrFun (hu j) i
    rw [Matrix.mulVec_single_one] at this
    rw [Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct, U] using this.symm
  have hU' : A₁ = U.transpose * A₀ := by
    rw [← Matrix.transpose_transpose A₁, hU, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hdetB : IsUnit (B.map (algebraMap O K)).det := (det_map_ne_zero B hB).isUnit
  have hmap : ((g₁⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
      U.transpose.map (algebraMap O K) * ((g₀⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) := by
    have h2 : ((g₁⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * B.map (algebraMap O K) =
        U.transpose.map (algebraMap O K) *
          ((g₀⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * B.map (algebraMap O K) := by
      rw [← h₁, hU', Matrix.map_mul, h₀, mul_assoc]
    have h3 := congrArg (· * (B.map (algebraMap O K))⁻¹) h2
    simpa only [mul_assoc, Matrix.mul_nonsing_inv _ hdetB, mul_one] using h3
  have hg : (g₀ : Matrix (Fin r) (Fin r) K) =
      (g₁ : Matrix (Fin r) (Fin r) K) * U.transpose.map (algebraMap O K) := by
    have e₁ : (g₁ : Matrix (Fin r) (Fin r) K) * ((g₁⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e₀ : ((g₀⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * (g₀ : Matrix (Fin r) (Fin r) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g₀ : Matrix (Fin r) (Fin r) K)
        = (g₁ : Matrix (Fin r) (Fin r) K) * ((g₁⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
            (g₀ : Matrix (Fin r) (Fin r) K) := by rw [e₁, one_mul]
      _ = (g₁ : Matrix (Fin r) (Fin r) K) * U.transpose.map (algebraMap O K) := by
          rw [hmap, mul_assoc, mul_assoc, e₀, mul_one]
  intro v hv
  obtain ⟨x, rfl⟩ := mem_lat.1 hv
  refine mem_lat.2 ⟨U.transpose.mulVec x, ?_⟩
  rw [hg, ← Matrix.mulVec_mulVec, map_mulVec_incl]

variable [Finite (IsLocalRing.ResidueField O)]

theorem sum_over_fiber_le (σ : ℝ) (hσ : (r : ℝ) - 1 < σ) (B : Matrix (Fin r) (Fin r) O)
    (hB : B.det ≠ 0) (S : Finset (GL (Fin r) K))
    (hinj : ∀ g ∈ S, ∀ g' ∈ S, lat O K (g : Matrix (Fin r) (Fin r) K) =
      lat O K (g' : Matrix (Fin r) (Fin r) K) → g = g')
    (hS : ∀ g ∈ S, (lat O K (g : Matrix (Fin r) (Fin r) K)).comap (incl O K r) =
      LinearMap.range B.mulVecLin) :
    ∑ g ∈ S, (((stdLat O K r).toAddSubgroup.relIndex
        (lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup : ℕ) : ℝ) ^ (-σ) ≤
      ∏ i ∈ Finset.range r,
        (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹ := by
  classical
  choose! A hA₁ hA₂ hA₃ using fun g (hg : g ∈ S) => exists_dual B hB g (hS g hg)
  let f : GL (Fin r) K → Submodule O (Fin r → O) :=
    fun g => LinearMap.range (A g).transpose.mulVecLin
  have hf : Set.InjOn f S := fun g hg g' hg' he => by
    have hg₀ : g ∈ S := hg
    have hg₁ : g' ∈ S := hg'
    refine hinj g hg₀ g' hg₁ (le_antisymm ?_ ?_)
    · exact lat_le_of_range_transpose_le B hB g g' _ _ (hA₁ g hg₀) (hA₁ g' hg₁) he.ge
    · exact lat_le_of_range_transpose_le B hB g' g _ _ (hA₁ g' hg₁) (hA₁ g hg₀) he.le
  calc ∑ g ∈ S, (((stdLat O K r).toAddSubgroup.relIndex
        (lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup : ℕ) : ℝ) ^ (-σ)
      = ∑ g ∈ S, (((f g).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) := by
        refine Finset.sum_congr rfl fun g hg => ?_
        rw [hA₃ g hg]
        simp only [f]
        rw [index_range_transpose _ (hA₂ g hg)]
    _ = ∑ N ∈ S.image f, ((N.toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) :=
        (Finset.sum_image (f := fun N : Submodule O (Fin r → O) => ((N.toAddSubgroup.index : ℕ) : ℝ) ^ (-σ)) hf).symm
    _ ≤ _ := GlobalTheory.T.sum_sublattice_index_rpow_le_solomon O r σ hσ _ (by
        intro N hN
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hN
        exact index_range_ne_zero _ (by rw [Matrix.det_transpose]; exact hA₂ g hg))

end Final

theorem sum_index_pairs_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (σ : ℝ), (r : ℝ) - 1 < σ → ∀ C : Finset (GL (Fin r) K), (∀ g ∈ C, ∀ g' ∈ C, (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) → g = g') → ∑ g ∈ C, (((((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup : ℕ) : ℝ) * (((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup.relIndex ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup : ℕ) : ℝ)) ^ (-σ) ≤ (∏ i ∈ Finset.range r, (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹) ^ 2 := by
  intro O K _ _ _ _ _ _ _ r σ hσ C hC
  classical
  change ∑ g ∈ C, ((((lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup.relIndex
      (stdLat O K r).toAddSubgroup : ℕ) : ℝ) *
    (((stdLat O K r).toAddSubgroup.relIndex
      (lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup : ℕ) : ℝ)) ^ (-σ) ≤ _
  generalize hZ : (∏ i ∈ Finset.range r,
    (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹) = Z
  have hZ0 : 0 ≤ Z := by
    have := GlobalTheory.T.sum_sublattice_index_rpow_le_solomon O r σ hσ ∅ (by simp)
    simpa [hZ] using this
  let Mg : GL (Fin r) K → Submodule O (Fin r → O) :=
    fun g => (lat O K (g : Matrix (Fin r) (Fin r) K)).comap (incl O K r)
  have hI : ∀ g : GL (Fin r) K, (lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup.relIndex
      (stdLat O K r).toAddSubgroup = (Mg g).toAddSubgroup.index := fun g => by
    rw [relIndex_stdLat]
    rfl
  let I2 : GL (Fin r) K → ℝ := fun g => (((stdLat O K r).toAddSubgroup.relIndex
      (lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup : ℕ) : ℝ) ^ (-σ)
  have hterm : ∀ g : GL (Fin r) K, ((((lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup.relIndex
      (stdLat O K r).toAddSubgroup : ℕ) : ℝ) *
    (((stdLat O K r).toAddSubgroup.relIndex
      (lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup : ℕ) : ℝ)) ^ (-σ) =
      (((Mg g).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * I2 g := fun g => by
    rw [hI, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  have hzero : ∀ g : GL (Fin r) K, (Mg g).toAddSubgroup.index = 0 →
      (((Mg g).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * I2 g = 0 := by
    intro g hg
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have : Subsingleton (Fin 0 → O) := inferInstance
      rw [AddSubgroup.index_eq_zero_iff_infinite] at hg
      exact absurd hg (by simp [not_infinite_iff_finite]; infer_instance)
    · have hσ0 : 0 < σ := by
        have : (1 : ℝ) ≤ r := by exact_mod_cast hr
        linarith
      rw [hg, Nat.cast_zero, Real.zero_rpow (by linarith), zero_mul]
  simp only [hterm]
  let C' := C.filter fun g => (Mg g).toAddSubgroup.index ≠ 0
  have h1 : ∑ g ∈ C, (((Mg g).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * I2 g =
      ∑ g ∈ C', (((Mg g).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * I2 g := by
    exact (Finset.sum_filter_of_ne (p := fun g => (Mg g).toAddSubgroup.index ≠ 0)
      fun g _ hne hg => hne (hzero g hg)).symm
  rw [h1, ← Finset.sum_fiberwise_of_maps_to (s := C') (t := C'.image Mg) (g := Mg)
    (fun g hg => Finset.mem_image_of_mem _ hg)]
  have hfib : ∀ M ∈ C'.image Mg, ∑ g ∈ C' with Mg g = M,
      (((Mg g).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * I2 g ≤
      ((M.toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * Z := by
    intro M hM
    obtain ⟨g₀, hg₀, rfl⟩ := Finset.mem_image.1 hM
    have hne : (Mg g₀).toAddSubgroup.index ≠ 0 := (Finset.mem_filter.1 hg₀).2
    obtain ⟨B, hB, hBM⟩ := exists_matrix_of_index_ne_zero _ hne
    have h2 : ∑ g ∈ C' with Mg g = Mg g₀,
        (((Mg g).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * I2 g =
        (((Mg g₀).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * ∑ g ∈ C' with Mg g = Mg g₀, I2 g := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [(Finset.mem_filter.1 hg).2]
    rw [h2]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    rw [← hZ]
    refine sum_over_fiber_le σ hσ B hB _ ?_ ?_
    · intro g hg g' hg' he
      exact hC g (Finset.mem_filter.1 (Finset.mem_filter.1 hg).1).1 g'
        (Finset.mem_filter.1 (Finset.mem_filter.1 hg').1).1 he
    · intro g hg
      rw [hBM]
      exact (Finset.mem_filter.1 hg).2
  calc _ ≤ ∑ M ∈ C'.image Mg, ((M.toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * Z :=
        Finset.sum_le_sum hfib
    _ = (∑ M ∈ C'.image Mg, ((M.toAddSubgroup.index : ℕ) : ℝ) ^ (-σ)) * Z :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ Z * Z := by
        refine mul_le_mul_of_nonneg_right ?_ hZ0
        rw [← hZ]
        refine GlobalTheory.T.sum_sublattice_index_rpow_le_solomon O r σ hσ _ ?_
        intro M hM
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hM
        exact (Finset.mem_filter.1 hg).2
    _ = Z ^ 2 := (sq Z).symm

end GlobalTheory.LatticePairSum
