import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsMore
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyLines
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.ExistsSmulMemFamilyOfSpanEqTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights TensorProduct
open scoped nonZeroDivisors ComplexOrder

noncomputable section

theorem S6.MatrixSubDegree.genIndex_trans {G : Type*} [AddCommGroup G] {A B C : AddSubgroup G}
    (hCA : C ≤ A) (hCB : C ≤ B) (hBC : C.relIndex B ≠ 0) :
    genIndex A C = genIndex A B * genIndex B C := by
  unfold genIndex
  rw [AddSubgroup.relIndex_eq_one.mpr hCA, AddSubgroup.relIndex_eq_one.mpr hCB]
  have h1 := AddSubgroup.relIndex_mul_relIndex C (A ⊓ B) A (le_inf hCA hCB) inf_le_left
  have h2 := AddSubgroup.relIndex_mul_relIndex C (A ⊓ B) B (le_inf hCA hCB) inf_le_right
  have h1' : (A ⊓ B).relIndex A = B.relIndex A := by
    rw [inf_comm]; exact AddSubgroup.inf_relIndex_right B A
  have h2' : (A ⊓ B).relIndex B = A.relIndex B := AddSubgroup.inf_relIndex_right A B
  rw [h1'] at h1
  rw [h2'] at h2
  have hb : (A.relIndex B : ℝ) ≠ 0 := by
    intro h0
    apply hBC
    rw [← h2, Nat.cast_eq_zero.mp h0, mul_zero]
  rw [← h1, ← h2]
  push_cast
  field_simp

theorem S6.MatrixSubDegree.genIndex_map {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    (f : G →+ G') (hf : Function.Injective f) (A B : AddSubgroup G) :
    genIndex (A.map f) (B.map f) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hf,
    AddSubgroup.relIndex_map_map_of_injective _ _ hf]

theorem S6.MatrixSubDegree.exists_smul_mem {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (𝓞 K) (Fin N → K)) (hspan : Submodule.span K (M : Set (Fin N → K)) = ⊤)
    {ι : Type*} [Fintype ι] (v : ι → Fin N → K) :
    ∃ t : 𝓞 K, t ≠ 0 ∧ ∀ i, algebraMap (𝓞 K) K t • v i ∈ M :=
  _root_.GroundTheory.Variant₂.N1.exists_smul_mem_family_of_span_eq_top M hspan v

theorem S6.MatrixSubDegree.finrank_satSub {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M] {r : ℕ} (u : Fin r → Fin N → K)
    (hu : LinearIndependent K u) (s : Fin r → satSub M u) (hs : LinearIndependent (𝓞 K) s) :
    Module.finrank (𝓞 K) (satSub M u) = r := by
  set W := Submodule.span K (Set.range u)
  let L : satSub M u →ₗ[𝓞 K] (Fin N → K) := M.subtype ∘ₗ (satSub M u).subtype
  have hLi : Function.Injective L := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  apply le_antisymm
  · apply Module.finrank_le_of_rank_le
    apply rank_le
    intro T hT
    have h0 := hT.map_injOn L hLi.injOn
    have h1 : LinearIndependent K (L ∘ fun i : T => (i : satSub M u)) :=
      (LinearIndependent.iff_fractionRing (𝓞 K) K).mp h0
    have hmem : ∀ i : T, L i ∈ W := fun i => (i : satSub M u).2
    have h2 : LinearIndependent K (fun i : T => (⟨L i, hmem i⟩ : W)) :=
      LinearIndependent.of_comp W.subtype h1
    have := h2.fintype_card_le_finrank
    rw [finrank_span_eq_card hu, Fintype.card_fin, Fintype.card_coe] at this
    exact this
  · have := hs.fintype_card_le_finrank
    simpa using this

theorem S6.MatrixSubDegree.gramAt_smul {K : Type} [Field K] {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ)
    (σ : K →+* ℂ) {ι : Type*} [Fintype ι] (u : ι → Fin N → K) (c : K) :
    gramAt h σ (fun i => c • u i) = ((‖σ c‖ ^ 2 : ℝ) : ℂ) • gramAt h σ u := by
  have he : ∀ v : Fin N → K, embVec σ (c • v) = σ c • embVec σ v := fun v => by
    funext k; simp [embVec]
  ext a b
  simp only [gramAt, he, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    Matrix.smul_apply, RCLike.star_def, ← mul_assoc]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem S6.MatrixSubDegree.log_gramDet {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M]
    (H : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hH : ∀ σ, (H σ).PosDef)
    (hconj : ∀ σ, H (conjugate σ) = (H σ).map (starRingEnd ℂ)) {r : ℕ} (u : Fin r → Fin N → K)
    (hu : LinearIndependent K u) (c : K) (hc : c ≠ 0) (v : Fin r → M)
    (hv : ∀ i, (v i : Fin N → K) = c • u i) (σ : K →+* ℂ) :
    Real.log (gramDet (matrixBundle M H hH hconj).metric σ v) =
      r * (2 * Real.log ‖σ c‖) + Real.log (gramAt (H σ) σ u).det.re := by
  have hG : (gram ℂ fun i => fibreVec (matrixBundle M H hH hconj).metric σ (v i)) =
      ((‖σ c‖ ^ 2 : ℝ) : ℂ) • gramAt (H σ) σ u := by
    have e : (fun i => c • u i) = fun i => (v i : Fin N → K) := funext fun i => (hv i).symm
    rw [← S6.MatrixSubDegree.gramAt_smul, e]
    ext i j
    rw [gram_apply]
    exact matrixMetric_inner_one_tmul M H hH hconj σ (v i) (v j)
  have hD : 0 < (gramAt (H σ) σ u).det.re := by
    have := (LinesGramPosDef.full K N (H σ) σ (Fin r) u (hH σ) hu).det_pos
    exact (RCLike.pos_iff.mp this).1
  have hσc : ‖σ c‖ ≠ 0 := by
    rw [norm_ne_zero_iff, map_ne_zero]; exact hc
  simp only [GroundTheory.Heights₂.Heights.gramDet]
  rw [hG, det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Real.log_mul (pow_ne_zero _ (pow_ne_zero _ hσc)) hD.ne', Real.log_pow, Real.log_pow]
  push_cast
  ring

theorem S6.MatrixSubDegree.genIndex_span_smul {K : Type} [Field K] [NumberField K] {N r : ℕ}
    (u : Fin r → Fin N → K) (hu : LinearIndependent K u) (c : K) (hc : c ≠ 0) :
    genIndex (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup
        (Submodule.span (𝓞 K) (Set.range fun i => c • u i)).toAddSubgroup =
      |((Algebra.norm ℚ c : ℚ) : ℝ)| ^ r := by
  let φ : (Fin r → K) →ₗ[𝓞 K] (Fin N → K) :=
    (Fintype.linearCombination K u).restrictScalars (𝓞 K)
  have hφx : ∀ x, φ x = ∑ i, x i • u i := fun x => Fintype.linearCombination_apply K u x
  have hφ : Function.Injective φ := by
    intro x y hxy
    rw [hφx, hφx] at hxy
    have h0 : ∑ i, (x - y) i • u i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hxy, sub_self]
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hu _ h0 i)
  have hstd := LinesStdIndexDet.full K r (c • (1 : Matrix (Fin r) (Fin r) K))
    (by rw [det_smul, det_one, mul_one]; exact pow_ne_zero _ hc)
  have e1 : (⇑φ ∘ fun j : Fin r => (Pi.single j 1 : Fin r → K)) = u := by
    funext j
    show Fintype.linearCombination K u (Pi.single j 1) = u j
    rw [Fintype.linearCombination_apply_single, one_smul]
  have e2 : (⇑φ ∘ fun j : Fin r => (c • (1 : Matrix (Fin r) (Fin r) K)) *ᵥ Pi.single j 1) =
      fun i => c • u i := by
    funext j
    show Fintype.linearCombination K u ((c • (1 : Matrix (Fin r) (Fin r) K)) *ᵥ Pi.single j 1) =
      c • u j
    rw [Matrix.smul_mulVec, one_mulVec, map_smul, Fintype.linearCombination_apply_single,
      one_smul]
  have hB : Submodule.span (𝓞 K) (Set.range u) = (stdLattice K r).map φ := by
    rw [stdLattice, Submodule.map_span, ← Set.range_comp, e1]
  have hC : Submodule.span (𝓞 K) (Set.range fun i => c • u i) = (Submodule.span (𝓞 K)
      (Set.range fun j => (c • (1 : Matrix (Fin r) (Fin r) K)) *ᵥ Pi.single j 1)).map φ := by
    rw [Submodule.map_span, ← Set.range_comp, e2]
  rw [hB, hC, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    S6.MatrixSubDegree.genIndex_map _ hφ, hstd, det_smul, det_one, mul_one, Fintype.card_fin,
    map_pow, Rat.cast_pow, abs_pow]

theorem S6.MatrixSubDegree.card_quotient_eq_genIndex {R E G : Type*} [Ring R] [AddCommGroup E]
    [Module R E] [AddCommGroup G] [Module R G] (F : Submodule R E) (p : Submodule R F)
    (L : F →ₗ[R] G) (hL : Function.Injective L) :
    (Nat.card (F ⧸ p) : ℝ) = genIndex ((⊤ : Submodule R F).map L).toAddSubgroup (p.map L).toAddSubgroup := by
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    S6.MatrixSubDegree.genIndex_map _ hL, genIndex, Submodule.top_toAddSubgroup,
    AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_top_left, Nat.cast_one, div_one]
  rfl

theorem S6.MatrixSubDegree.card_quotient_pos {K : Type} [Field K] [NumberField K] {E : Type*}
    [AddCommGroup E] [Module (𝓞 K) E] (F : Submodule (𝓞 K) E) [Module.Finite (𝓞 K) F] {r : ℕ}
    (s : Fin r → F) (hs : LinearIndependent (𝓞 K) s) (hr : Module.finrank (𝓞 K) F = r) :
    (0 : ℝ) < Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
  have := finite_quotient_span hs (by rw [Fintype.card_fin, hr])
  exact_mod_cast Nat.card_pos

theorem S6.MatrixSubDegree.proof : S6.MatrixSubDegree.Statement := by
  intro K _ _ N M _ H hH hconj hspan r u hu
  obtain ⟨t, ht, htM⟩ := S6.MatrixSubDegree.exists_smul_mem M hspan u
  have hτ : algebraMap (𝓞 K) K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ht
  have hfW : ∀ i, algebraMap (𝓞 K) K t • u i ∈ Submodule.span K (Set.range u) :=
    fun i => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let s : Fin r → satSub M u := fun i => ⟨⟨algebraMap (𝓞 K) K t • u i, htM i⟩, hfW i⟩
  let L : satSub M u →ₗ[𝓞 K] (Fin N → K) := M.subtype ∘ₗ (satSub M u).subtype
  have hL : Function.Injective L := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  have hLs : ⇑L ∘ s = fun i => algebraMap (𝓞 K) K t • u i := rfl
  have hs : LinearIndependent (𝓞 K) s := by
    refine LinearIndependent.of_comp L ?_
    rw [hLs]
    exact (LinearIndependent.iff_fractionRing (𝓞 K) K).mpr
      (hu.units_smul fun _ => Units.mk0 _ hτ)
  have hrank : (matrixBundle M H hH hconj).rank (satSub M u) = r :=
    S6.MatrixSubDegree.finrank_satSub M u hu s hs
  refine ⟨hrank, ?_⟩
  have hcard : Fintype.card (Fin r) = (matrixBundle M H hH hconj).rank (satSub M u) := by
    rw [Fintype.card_fin, hrank]
  rw [(matrixBundle M H hH hconj).degree_eq_of_linearIndependent (satSub M u) hs hcard]
  have hlog := fun σ => S6.MatrixSubDegree.log_gramDet M H hH hconj u hu _ hτ
    (fun i => (s i : M)) (fun i => rfl) σ
  simp_rw [hlog]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    LinesProductFormula.full K _ hτ]

  have hA : M ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K) =
      (⊤ : Submodule (𝓞 K) (satSub M u)).map L := by
    rw [Submodule.map_top, LinearMap.range_comp, Submodule.range_subtype, satSub,
      Submodule.map_comap_subtype]
  have hC : Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i) =
      (Submodule.span (𝓞 K) (Set.range s)).map L := by
    rw [Submodule.map_span, ← Set.range_comp, hLs]
  have hpos := S6.MatrixSubDegree.card_quotient_pos (satSub M u) s hs hrank
  rw [S6.MatrixSubDegree.card_quotient_eq_genIndex (satSub M u) _ L hL, ← hA, ← hC] at hpos
  erw [S6.MatrixSubDegree.card_quotient_eq_genIndex (satSub M u) _ L hL]
  rw [← hA]
  erw [← hC]
  have hBC := S6.MatrixSubDegree.genIndex_span_smul u hu _ hτ
  have hN : |((Algebra.norm ℚ (algebraMap (𝓞 K) K t) : ℚ) : ℝ)| ≠ 0 := by
    rw [abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]; exact hτ
  have hCA : (Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i)).toAddSubgroup ≤
      (M ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).toAddSubgroup := by
    rw [Submodule.toAddSubgroup_le, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨htM i, hfW i⟩
  have hCB : (Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i)).toAddSubgroup ≤
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup := by
    rw [Submodule.toAddSubgroup_le, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show algebraMap (𝓞 K) K t • u i ∈ Submodule.span (𝓞 K) (Set.range u)
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ t (Submodule.subset_span ⟨i, rfl⟩)
  have hrel : (Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup ≠ 0 := by
    intro h0
    apply pow_ne_zero r hN
    rw [← hBC, genIndex, h0, Nat.cast_zero, zero_div]
  have htrans := S6.MatrixSubDegree.genIndex_trans hCA hCB hrel
  rw [htrans, hBC] at hpos ⊢
  have hAB := left_ne_zero_of_mul hpos.ne'
  rw [Real.log_mul hAB (pow_ne_zero _ hN), Real.log_pow, subDegree]
  ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
