import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalTwists.ZeroComplOfFb
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.CoeSmEqSymm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MemArchMaxCompactIffOrthogonalAtInfinitePlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicHeightInfGLLeOpNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConstantTermEqZeroOfIsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsCuspidalOfConstantTermEqZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsKFiniteTotallyRealModelOfIsKFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ModerateGrowthTotallyRealModelOfModerateGrowth
open NumberField GlobalTheory.CuspRep UpperTheory.V

section
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

private theorem cusp_to (φ : TR.Sm F a) (h : TR.IsCuspForm φ) : φ.1 ∈ cuspForms F a := by
  have hs : IsSmooth φ.1 := ⟨UpperTheory.isArchSmooth_of_contDiff_chart F a _ φ.2, fun g => by
    filter_upwards [h.1.level.mem_nhds (show TR.finRep F a 1 φ = φ by simp)] with y hy
    rw [Fb.finEmb_eq]
    exact congrFun (congrArg Subtype.val hy) g⟩
  have hA : IsAutomorphicForm φ.1 := ⟨h.1.left, hs, UpperTheory.isKFinite_totallyRealModel_of_isKFinite F a φ h.1.level h.1.kfin,
    (Fb.zfin_iff φ).1 h.1.zfin, UpperTheory.moderateGrowth_totallyRealModel_of_moderateGrowth F a φ h.1.left h.1.level h.1.growth⟩
  exact ⟨hA, UpperTheory.constantTerm_eq_zero_of_isCuspidal F a _ hA.isLeftInvariant hA.continuous h.2⟩

private theorem cusp_of (f : GA F a → ℂ) (hf : f ∈ cuspForms F a) : ∃ h : f ∈ TR.Sm F a, TR.IsCuspForm ⟨f, h⟩ := by
  have hA := hf.1
  have h := UpperTheory.contDiff_chart_of_isArchSmooth F a f hA.isSmooth.1
  refine ⟨h, ⟨hA.isLeftInvariant, ?_, ?_, (Fb.zfin_iff _).2 hA.isZFinite, fun g => ?_⟩,
    UpperTheory.isCuspidal_of_constantTerm_eq_zero F a f hA.isLeftInvariant hA.continuous hf.2⟩
  · obtain ⟨W, -, hW⟩ := exists_openSubgroup_rightInvariant hA.isSmooth hA.isKFinite
    refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (W.isOpen.mem_nhds W.one_mem) fun k hk => ?_)
    refine Subtype.ext (funext fun g => ?_)
    have := hW g k hk
    rwa [Fb.finEmb_eq] at this
  · have := hA.isKFinite
    unfold IsKFinite at this
    refine UnitaryAdmissible.finiteDimensional_of_map_subtype_le _ (S := Submodule.span ℂ
      (Set.range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL F a)) =>
        rightTranslate (k : AdelicGLn.AdelicGL F a) f)) ?_
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    have hk : infEmb F a (Fb.grpEq F a (Unitary.toUnits k)) ∈ Reduction.maxCompact := (UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces F a _).2 k.2
    rw [Fb.infEmb_grpEq] at hk
    exact Submodule.subset_span ⟨⟨_, hk⟩, rfl⟩
  · obtain ⟨C, N, hC⟩ := hA.hasModerateGrowth
    obtain ⟨M, hM⟩ := UpperTheory.adelicHeight_infGL_le_opNorm F a
    have h0 : 0 ≤ C := by
      have := (norm_nonneg _).trans (hC 1)
      rwa [height_one, one_pow, mul_one] at this
    have h1 := (one_le_heightConst (K := F) (n := a))
    have h2 := height_pos g
    refine ⟨C * (heightConst F a * height g) ^ N, M * N, fun y => (hC _).trans ?_⟩
    rw [mul_assoc, pow_mul, ← mul_pow]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le ((height_mul_le _ _).trans ?_) N) h0
    exact mul_le_mul_of_nonneg_left (hM y) (by positivity)

end

theorem UpperTheory.V.Af.cuspSemisimpleReal :
    UpperTheory.V.Published.CuspSemisimpleReal :=
  TR.SS.cuspSemisimple_of fun _ _ _ _ _ => TR.SS.zeroCompl_of_fb cusp_to cusp_of
    (fun X φ _ => (congrArg Subtype.val (Fb.uAction_ι_smEq X φ)).symm) UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces
