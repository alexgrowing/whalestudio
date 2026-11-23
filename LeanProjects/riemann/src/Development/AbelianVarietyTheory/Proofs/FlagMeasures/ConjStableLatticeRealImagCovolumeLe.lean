import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsNeZeroForallNormLeOfCovolumeLe
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.ReImLattice

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem covolume_prod (μ : Measure E) [μ.IsAddHaarMeasure] (L L' : Submodule ℤ E)
    [DiscreteTopology L] [DiscreteTopology L'] [IsZLattice ℝ L] [IsZLattice ℝ L'] :
    ZLattice.covolume (L.prod L') (μ.prod μ) = ZLattice.covolume L μ * ZLattice.covolume L' μ := by
  have hD : IsAddFundamentalDomain (L.prod L') (latticeDomain L ×ˢ latticeDomain L')
      (μ.prod μ) := by
    refine IsAddFundamentalDomain.mk' ((measurableSet_latticeDomain L).prod
      (measurableSet_latticeDomain L')).nullMeasurableSet fun x => ?_
    obtain ⟨a, ha, hu⟩ := existsUnique_add_mem_latticeDomain L x.1
    obtain ⟨a', ha', hu'⟩ := existsUnique_add_mem_latticeDomain L' x.2
    refine ⟨⟨(a, a'), a.2, a'.2⟩, ⟨?_, ?_⟩, ?_⟩
    · simpa [Submodule.vadd_def, add_comm] using ha
    · simpa [Submodule.vadd_def, add_comm] using ha'
    · rintro ⟨b, hb⟩ hb'
      have h1 := hu ⟨b.1, hb.1⟩ (by simpa [Submodule.vadd_def, add_comm] using hb'.1)
      have h2 := hu' ⟨b.2, hb.2⟩ (by simpa [Submodule.vadd_def, add_comm] using hb'.2)
      apply Subtype.ext
      simp [← h1, ← h2]
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hD, measureReal_prod_prod,
    ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_latticeDomain L μ),
    ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_latticeDomain L' μ)]

theorem reflection_stable (μ : Measure E) [μ.IsAddHaarMeasure] (M : Submodule ℤ (E × E))
    [DiscreteTopology M] [IsZLattice ℝ M] (hM : ∀ p ∈ M, (p.1, -p.2) ∈ M) (A B : Submodule ℤ E)
    (hA : ∀ y, y ∈ A ↔ (y, (0 : E)) ∈ M) (hB : ∀ y, y ∈ B ↔ ((0 : E), y) ∈ M) :
    (∃ _ : DiscreteTopology A, IsZLattice ℝ A) ∧ (∃ _ : DiscreteTopology B, IsZLattice ℝ B) ∧
      ZLattice.covolume A μ * ZLattice.covolume B μ ≤
        2 ^ Module.finrank ℝ E * ZLattice.covolume M (μ.prod μ) := by
  have h2A : ∀ p ∈ M, p.1 + p.1 ∈ A := fun p hp => by
    rw [hA]
    have := M.add_mem hp (hM p hp)
    convert this using 1
    ext <;> simp
  have h2B : ∀ p ∈ M, p.2 + p.2 ∈ B := fun p hp => by
    rw [hB]
    have := M.sub_mem hp (hM p hp)
    convert this using 1
    ext <;> simp
  haveI dA : DiscreteTopology A :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : A => (⟨(x.1, 0), (hA _).1 x.2⟩ : M))
      ((continuous_subtype_val.prodMk continuous_const).subtype_mk _)
      (fun x y h => Subtype.ext (congrArg (fun z : M => z.1.1) h))
  haveI dB : DiscreteTopology B :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : B => (⟨(0, x.1), (hB _).1 x.2⟩ : M))
      ((continuous_const.prodMk continuous_subtype_val).subtype_mk _)
      (fun x y h => Subtype.ext (congrArg (fun z : M => z.1.2) h))
  have key : ∀ (C : Submodule ℤ E) (f : E × E →ₗ[ℝ] E), Function.Surjective f →
      (∀ p ∈ M, f p + f p ∈ C) → Submodule.span ℝ (C : Set E) = ⊤ := by
    intro C f hf hC
    rw [eq_top_iff, ← LinearMap.range_eq_top.2 hf, LinearMap.range_eq_map,
      ← IsZLattice.span_top (K := ℝ) (L := M), Submodule.map_span, Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    have h := (Submodule.span ℝ (C : Set E)).smul_mem (2⁻¹ : ℝ) (Submodule.subset_span (hC p hp))
    rwa [← two_smul ℝ, inv_smul_smul₀ two_ne_zero] at h
  haveI lA : IsZLattice ℝ A := ⟨key A (LinearMap.fst ℝ E E) LinearMap.fst_surjective h2A⟩
  haveI lB : IsZLattice ℝ B := ⟨key B (LinearMap.snd ℝ E E) LinearMap.snd_surjective h2B⟩
  refine ⟨⟨dA, lA⟩, ⟨dB, lB⟩, ?_⟩
  have hle : A.prod B ≤ M := fun p hp => by
    have := M.add_mem ((hA _).1 hp.1) ((hB _).1 hp.2)
    simpa using this
  rw [← covolume_prod μ A B, covolume_eq_relIndex_mul_of_haar (μ.prod μ) _ M hle]
  refine mul_le_mul_of_nonneg_right ?_ (ZLattice.covolume_pos M (μ.prod μ)).le
  let f : M.toAddSubgroup →+ A :=
    { toFun := fun p => ⟨p.1.1 + p.1.1, h2A _ p.2⟩
      map_zero' := by ext; simp
      map_add' := fun p q => by ext; simp; abel }
  have hK : (nsmulAddMonoidHom (α := A) 2).range.index = 2 ^ Module.finrank ℝ E := by
    rw [AddSubgroup.index_range_nsmul, ZLattice.rank ℝ A]
  have hc : (A.prod B).toAddSubgroup.addSubgroupOf M.toAddSubgroup =
      (nsmulAddMonoidHom (α := A) 2).range.comap f := by
    ext p
    simp only [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, Submodule.mem_prod,
      AddSubgroup.mem_comap, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨⟨_, h1⟩, Subtype.ext (by simp [f, two_nsmul])⟩
    · rintro ⟨y, hy⟩
      have h1 : y.1 + y.1 = p.1.1 + p.1.1 := by
        have := congrArg Subtype.val hy
        simpa [f, two_nsmul] using this
      have h2 : y.1 = p.1.1 := by
        rw [← two_smul ℝ, ← two_smul ℝ] at h1
        exact smul_right_injective E two_ne_zero h1
      have h3 : p.1.1 ∈ A := h2 ▸ y.2
      refine ⟨h3, (hB _).2 ?_⟩
      have := M.sub_mem p.2 ((hA _).1 h3)
      convert this using 1
      ext <;> simp
  have hidx : (A.prod B).toAddSubgroup.relIndex M.toAddSubgroup ≤ 2 ^ Module.finrank ℝ E := by
    rw [AddSubgroup.relIndex, hc, AddSubgroup.index_comap, ← hK, ← AddSubgroup.relIndex_top_right]
    refine AddSubgroup.relIndex_le_of_le_right le_top ?_
    rw [AddSubgroup.relIndex_top_right, hK]
    positivity
  exact_mod_cast hidx

end General

noncomputable def reImEquiv (ι κ : Type) [Fintype ι] [Fintype κ] :
    ((ι → κ → ℝ) × (ι → κ → ℝ)) ≃L[ℝ] (ι → κ → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p v i => ⟨p.1 v i, p.2 v i⟩
      invFun := fun z => (fun v i => (z v i).re, fun v i => (z v i).im)
      map_add' := fun p q => by ext v i; apply Complex.ext <;> simp
      map_smul' := fun c p => by ext v i; apply Complex.ext <;> simp
      left_inv := fun p => rfl
      right_inv := fun z => rfl }

theorem reImEquiv_apply {ι κ : Type} [Fintype ι] [Fintype κ] (p : (ι → κ → ℝ) × (ι → κ → ℝ))
    (v : ι) (i : κ) : reImEquiv ι κ p v i = ⟨p.1 v i, p.2 v i⟩ := rfl

theorem measurePreserving_reImEquiv (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (reImEquiv ι κ) (Measure.prod volume volume) volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow (κ → ℝ) (κ → ℝ) ι).symm
  have h2 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ κ).symm
  have h3 := Complex.volume_preserving_equiv_real_prod.symm
  have h4 := volume_preserving_pi (ι := κ) (fun _ => h3)
  have h5 := volume_preserving_pi (ι := ι) (fun _ => h4.comp h2)
  exact h5.comp h1

theorem real_imag_covolume_le : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (L : Submodule ℤ (ι → κ → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L], (∀ z ∈ L, (fun v i => starRingEnd ℂ (z v i)) ∈ L) → ∀ A B : Submodule ℤ (ι → κ → ℝ), (∀ y, y ∈ A ↔ (fun v i => (y v i : ℂ)) ∈ L) → (∀ y, y ∈ B ↔ (fun v i => Complex.I * (y v i : ℂ)) ∈ L) → (∃ _ : DiscreteTopology A, IsZLattice ℝ A) ∧ (∃ _ : DiscreteTopology B, IsZLattice ℝ B) ∧ ZLattice.covolume A volume * ZLattice.covolume B volume ≤ 2 ^ (Fintype.card ι * Fintype.card κ) * ZLattice.covolume L volume := by
  intro ι κ _ _ L _ _ hL A B hA hB
  have hmem : ∀ p, p ∈ ZLattice.comap ℝ L (reImEquiv ι κ).toLinearMap ↔ reImEquiv ι κ p ∈ L :=
    fun p => Iff.rfl
  have h := reflection_stable volume (ZLattice.comap ℝ L (reImEquiv ι κ).toLinearMap)
    (fun p hp => by
      rw [hmem] at hp ⊢
      convert hL _ hp using 1
      ext v i; apply Complex.ext <;> simp [reImEquiv_apply]) A B
    (fun y => by
      rw [hA, hmem]
      congr! 1)
    (fun y => by
      rw [hB, hmem]
      congr! 1
      ext v i; apply Complex.ext <;> simp [reImEquiv_apply])
  haveI : (volume : Measure (κ → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (κ → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ι → κ → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : ((volume : Measure (ι → κ → ℝ)).prod (volume : Measure (ι → κ → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  rw [ZLattice.covolume_comap L volume _ (measurePreserving_reImEquiv ι κ)] at h
  have hr : Module.finrank ℝ (ι → κ → ℝ) = Fintype.card ι * Fintype.card κ := by
    rw [Module.finrank_pi_fintype]; simp
  rwa [hr] at h

end GlobalTheory.ReImLattice
