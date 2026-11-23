import Formalism.HermitianCurvature.PrimeToDifferent

namespace Formalism.FourierDecayAlt.P.S6x5

open Module MeasureTheory

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem covolume_index (μ : Measure V) [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ V)
    [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂]
    (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ =
      (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) * ZLattice.covolume L₂ μ := by
  classical
  have : Module.Free ℤ L₁ := ZLattice.module_free ℝ L₁
  have : Module.Free ℤ L₂ := ZLattice.module_free ℝ L₂
  have : Module.Finite ℤ L₁ := ZLattice.module_finite ℝ L₁
  have : Module.Finite ℤ L₂ := ZLattice.module_finite ℝ L₂
  let b₂ := Free.chooseBasis ℤ L₂
  let b₁ := (Free.chooseBasis ℤ L₁).reindex (Fintype.equivOfCardEq
    (β := Free.ChooseBasisIndex ℤ L₂)
    (by rw [← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex,
      ZLattice.rank ℝ, ZLattice.rank ℝ]))
  rw [ZLattice.covolume_eq_det_mul_measureReal L₁ μ b₁ (b₂.ofZLatticeBasis ℝ),
    ZLattice.covolume_eq_det_mul_measureReal L₂ μ b₂ (b₂.ofZLatticeBasis ℝ), ← mul_assoc]
  congr 1
  have h2 : (b₂.ofZLatticeBasis ℝ).det ((↑) ∘ b₂) = 1 := by
    have : ((↑) ∘ b₂ : _ → V) = b₂.ofZLatticeBasis ℝ := by ext; simp
    rw [this, Basis.det_self]
  have hrel : L₁.toAddSubgroup.relIndex L₂.toAddSubgroup =
      (b₂.det (fun i => (⟨b₁ i, h (SetLike.coe_mem _)⟩ : L₂))).natAbs :=
    AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂
  rw [h2, abs_one, mul_one, hrel, Nat.cast_natAbs, Int.cast_abs]
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  exact (b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ j, h (SetLike.coe_mem _)⟩ i)

noncomputable abbrev scal (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ) : V →ₗ[ℤ] V :=
  (c • (LinearMap.id : V →ₗ[ℝ] V)).restrictScalars ℤ

noncomputable def scalInv (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ) (hc : c ≠ 0) :
    V ≃L[ℝ] V :=
  ContinuousLinearEquiv.equivOfInverse (c⁻¹ • ContinuousLinearMap.id ℝ V)
    (c • ContinuousLinearMap.id ℝ V) (fun x => by simp [smul_smul, hc])
    (fun x => by simp [smul_smul, hc])

theorem scalInv_apply (c : ℝ) (hc : c ≠ 0) (x : V) : scalInv V c hc x = c⁻¹ • x := rfl

theorem scalInv_symm_apply (c : ℝ) (hc : c ≠ 0) (x : V) : (scalInv V c hc).symm x = c • x := rfl

theorem map_scal_eq_comap (c : ℝ) (hc : c ≠ 0) (L : Submodule ℤ V) :
    L.map (scal V c) = ZLattice.comap ℝ L (scalInv V c hc).toLinearMap := by
  ext x
  simp only [Submodule.mem_map, ZLattice.comap, Submodule.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : (scalInv V c hc) (c • y) = y := by rw [scalInv_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
    show (scalInv V c hc) (c • y) ∈ L
    rw [this]; exact hy
  · intro hx
    refine ⟨_, hx, ?_⟩
    show c • (scalInv V c hc) x = x
    rw [scalInv_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem covolume_scal (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V)
    [DiscreteTopology L] [IsZLattice ℝ L] (c : ℝ) (hc : c ≠ 0) :
    ZLattice.covolume (ZLattice.comap ℝ L (scalInv V c hc).toLinearMap) μ =
      |c| ^ finrank ℝ V * ZLattice.covolume L μ := by
  classical
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b := Free.chooseBasis ℤ L
  rw [ZLattice.covolume_eq_det_mul_measureReal _ μ
      (b.ofZLatticeComap ℝ L (scalInv V c hc).toLinearEquiv) (b.ofZLatticeBasis ℝ),
    ZLattice.covolume_eq_det_mul_measureReal L μ b (b.ofZLatticeBasis ℝ), ← mul_assoc]
  congr 1
  have h1 : ((↑) ∘ (b.ofZLatticeComap ℝ L (scalInv V c hc).toLinearEquiv) : _ → V)
      = fun i => c • ((↑) ∘ b : _ → V) i := by
    ext i
    rw [Function.comp_apply, Basis.ofZLatticeComap_apply]
    rfl
  have h2 := (b.ofZLatticeBasis ℝ).det.toMultilinearMap.map_smul_univ (fun _ => c)
    ((↑) ∘ b : _ → V)
  rw [h1]
  erw [h2]
  simp only [Finset.prod_const, Finset.card_univ, smul_eq_mul, abs_mul, abs_pow]
  rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ]
  rfl

theorem lattice_of_index (μ : Measure V) [μ.IsAddHaarMeasure] (M₁ M₂ : Submodule ℤ V)
    [DiscreteTopology M₁] [IsZLattice ℝ M₁] (h : M₁ ≤ M₂)
    (hn : M₁.toAddSubgroup.relIndex M₂.toAddSubgroup ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    DiscreteTopology (M₂.map (scal V c)) ∧
    Submodule.span ℝ (M₂.map (scal V c) : Set V) = ⊤ ∧
    ZLattice.covolume (M₂.map (scal V c)) μ =
      |c| ^ finrank ℝ V * ZLattice.covolume M₁ μ /
        (M₁.toAddSubgroup.relIndex M₂.toAddSubgroup : ℝ) := by
  set n := M₁.toAddSubgroup.relIndex M₂.toAddSubgroup with hn'
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn

  have hsub : M₂ ≤ ZLattice.comap ℝ M₁ (scalInv V (n : ℝ)⁻¹ (inv_ne_zero hnR)).toLinearMap := by
    intro x hx
    show (scalInv V (n : ℝ)⁻¹ (inv_ne_zero hnR)) x ∈ M₁
    rw [scalInv_apply, inv_inv, Nat.cast_smul_eq_nsmul]
    have := AddSubgroup.nsmul_index_mem (M₁.toAddSubgroup.addSubgroupOf M₂.toAddSubgroup) ⟨x, hx⟩
    exact this
  have hd : DiscreteTopology M₂ := DiscreteTopology.of_subset (t := (M₂ : Set V))
    (s := (ZLattice.comap ℝ M₁ (scalInv V (n : ℝ)⁻¹ (inv_ne_zero hnR)).toLinearMap : Set V))
    (inferInstanceAs (DiscreteTopology
      (ZLattice.comap ℝ M₁ (scalInv V (n : ℝ)⁻¹ (inv_ne_zero hnR)).toLinearMap))) hsub
  have hz : IsZLattice ℝ M₂ := ⟨by
    rw [eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := M₁)]
    exact Submodule.span_mono h⟩
  rw [map_scal_eq_comap c hc]
  refine ⟨inferInstance, IsZLattice.span_top, ?_⟩
  rw [covolume_scal μ M₂ c hc, covolume_index μ M₁ M₂ h, ← hn']
  field_simp

end General
end Formalism.FourierDecayAlt.P.S6x5

namespace Formalism.FourierDecayAlt.P.S6x5

open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors

noncomputable abbrev emb (E : Type) [Field E] [NumberField E] : E →ₗ[ℤ] mixedEmbedding.mixedSpace E :=
  (mixedEmbedding E).toAddMonoidHom.toIntLinearMap

theorem map_zsub_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (B : FI E) (hB : B ≠ 0) :
    (zsub E B).map (emb E) = mixedEmbedding.idealLattice E (Units.mk0 B hB) := by
  ext x
  rw [mixedEmbedding.mem_idealLattice, Submodule.mem_map]
  rfl

theorem finrank_eq (E : Type) [Field E] [NumberField E] [IsCMField E] :
    finrank ℚ E = 2 * deg E := by
  have h2 : finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [h2] at h3
  unfold deg; omega

theorem mem_twLat (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ) (t : E) :
    t ∈ twLat E A B s ↔ t ∈ A ∧ t - (-1) ^ s * complexConj E t ∈ B := by
  unfold twLat
  rw [Submodule.mem_inf, Submodule.mem_comap]
  have : ((LinearMap.id : E →ₗ[ℤ] E) - ((-1 : ℤ) ^ s) • conjZ E) t
      = t - (-1) ^ s * complexConj E t := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, zsmul_eq_mul]
    push_cast
    rfl
  rw [this]; rfl

theorem conj_real (E : Type) [Field E] [NumberField E] [IsCMField E]
    (a : 𝓞 (maximalRealSubfield E)) :
    complexConj E (algebraMap (𝓞 (maximalRealSubfield E)) E a)
      = algebraMap (𝓞 (maximalRealSubfield E)) E a :=
  complexConj_apply_eq_self E (a : maximalRealSubfield E)

theorem smul_mem_FI (E : Type) [Field E] [NumberField E] [IsCMField E] (A : FI E)
    (a : 𝓞 (maximalRealSubfield E)) (t : E) (ht : t ∈ A) :
    algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ A := by
  have := (A : Submodule (𝓞 E) E).smul_mem (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) ht
  rw [Algebra.smul_def] at this
  exact this

theorem exists_nat_mul_mem (E : Type) [Field E] [NumberField E] (B : FI E) (hB : B ≠ 0) (t : E) :
    ∃ n : ℕ, 0 < n ∧ (n : E) * t ∈ B := by
  obtain ⟨b, hb, hb0⟩ : ∃ b ∈ B, b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hB ((FractionalIdeal.eq_zero_iff).2 hcon)
  have halg : IsAlgebraic ℤ (t / b) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (t / b))
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  have h1 : (y : E) * t ∈ B := by
    obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, algebraMap (𝓞 E) E z = y • (t / b) :=
      ⟨⟨y • (t / b), hy⟩, rfl⟩
    have := (B : Submodule (𝓞 E) E).smul_mem z hb
    rw [Algebra.smul_def, hz, zsmul_eq_mul] at this
    have h2 : (y : E) * (t / b) * b = (y : E) * t := by field_simp
    rw [h2] at this
    exact this
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact h1
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact (B : Submodule (𝓞 E) E).neg_mem h1

end Formalism.FourierDecayAlt.P.S6x5

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x5
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors

open scoped Classical in

theorem covolumeIndex : Formalism.FourierDecayAlt.S6.CovolumeIndex := by
  intro E _ _ _ B L c hB hc hBL hn
  have hinj : Function.Injective (emb E).toAddMonoidHom := (mixedEmbedding E).injective
  have hidx : ((zsub E B).map (emb E)).toAddSubgroup.relIndex (L.map (emb E)).toAddSubgroup
      = idx E (zsub E B) L := by
    unfold idx
    rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hle : (zsub E B).map (emb E) ≤ L.map (emb E) := Submodule.map_mono hBL
  rw [map_zsub_eq E B hB] at hidx hle
  have key := lattice_of_index (volume : Measure (mixedEmbedding.mixedSpace E))
    (mixedEmbedding.idealLattice E (Units.mk0 B hB)) (L.map (emb E)) hle (by rw [hidx]; exact hn)
    c hc
  refine ⟨key.1, key.2.1, ?_⟩
  have h1 : InfinitePlace.nrComplexPlaces E = deg E := by
    have h5 := IsTotallyComplex.finrank E
    have := finrank_eq E
    omega
  have h3 := key.2.2
  rw [hidx, mixedEmbedding.covolume_idealLattice, mixedEmbedding.finrank, finrank_eq E, h1] at h3
  unfold frameLat
  rw [h3]
  simp [mul_assoc]

theorem twistedIsRealOrderLattice : Formalism.FourierDecayAlt.S6.TwIsFLattice := by
  intro E _ _ _ A B s hB hBA hconj
  refine ⟨fun a t ht => ?_, fun t => ?_⟩
  · rw [mem_twLat] at ht ⊢
    refine ⟨smul_mem_FI E A a t ht.1, ?_⟩
    have := smul_mem_FI E B a _ ht.2
    rw [map_mul, conj_real]
    convert this using 1
    ring
  · obtain ⟨n, hn, hmem⟩ := exists_nat_mul_mem E B hB t
    refine ⟨n, hn, ?_⟩
    rw [mem_twLat]
    refine ⟨hBA hmem, ?_⟩
    have h1 : complexConj E ((n : E) * t) ∈ B := hconj _ hmem
    have h2 : (-1 : E) ^ s * complexConj E ((n : E) * t) ∈ B := by
      rcases neg_one_pow_eq_or E s with h | h <;> rw [h]
      · simpa using h1
      · rw [neg_one_mul]; exact B.coeToSubmodule.neg_mem h1
    exact B.coeToSubmodule.sub_mem hmem h2

end Formalism.FourierDecayAlt.P
