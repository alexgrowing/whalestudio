import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassEqKummerCharacterOfChosenRootFunctionFi

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

private theorem unif_lc {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {f : G → A} (hf : IsLocallyConstant f) : ∀ᶠ h in nhds (1 : G), ∀ g : G, f (g * h) = f g := by
  choose V hVo hV1 hVm using fun g : G => exists_open_nhds_one_mul_subset
    (show {y : G | f (g * y) = f g} ∈ nhds (1 : G) from
      ((hf.isOpen_fiber (f g)).preimage (continuous_const_mul g)).mem_nhds (by simp))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun g : G => (fun x => g⁻¹ * x) ⁻¹' V g)
    (fun g => (hVo g).preimage (continuous_const_mul g⁻¹))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using hV1 x⟩)
  filter_upwards [(Filter.biInter_finset_mem t).2 (fun g _ => (hVo g).mem_nhds (hV1 g))] with h hh x
  obtain ⟨g, hg, hx⟩ : ∃ g ∈ t, g⁻¹ * x ∈ V g := by
    simpa using ht (Set.mem_univ x)
  have h1 : f (g * (g⁻¹ * x * h)) = f g := hVm g (Set.mul_mem_mul hx (Set.mem_iInter₂.1 hh g hg))
  have h2 : f (g * (g⁻¹ * x * 1)) = f g := hVm g (Set.mul_mem_mul hx (hV1 g))
  simp only [mul_one, ← mul_assoc, mul_inv_cancel, one_mul] at h1 h2
  rw [h1, h2]

theorem UpperTheory.V.Z.Kato.Sym.PT.lcGeo :
    UpperTheory.V.Z.Kato.Sym.PT.LcGeo := by
  classical
  intro F K E _ _ _ _ _ _ _ _ A η hη
  have l : IsLocallyConstant (fun g : E ≃ₐ[K] E => η (AlgEquiv.restrictScalarsHom F g)) :=
    hη.comp_continuous
      (f := fun g : E ≃ₐ[K] E => (⟨AlgEquiv.restrictScalarsHom F g, TopSpec.res_mem_geo g⟩ : geo F K E))
      ((TopSpec.continuous_res (F := F) (K := K) (Ω := E)).subtype_mk _)
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff K E _).1 (unif_lc l)
  let b := Module.finBasis K L
  refine ⟨Finset.univ.image fun i => (b i : E), fun g hg g' hg' hB => ?_⟩
  obtain ⟨g, rfl⟩ := TopSpec.exists_res hg
  obtain ⟨g', rfl⟩ := TopSpec.exists_res hg'
  have hlin : g.toLinearMap.comp L.val.toLinearMap = g'.toLinearMap.comp L.val.toLinearMap :=
    b.ext fun i => hB _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hmem : g⁻¹ * g' ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    have hz' : g z = g' z := LinearMap.congr_fun hlin ⟨z, hz⟩
    rw [AlgEquiv.mul_apply, ← hz']
    exact g.symm_apply_apply z
  have h := hsub hmem g
  simp only [mul_inv_cancel_left] at h
  exact h.symm
