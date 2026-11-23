import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalTwists.ZeroComplOfFb
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.CoeSmEqSymm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MemArchMaxCompactIffOrthogonalAtInfinitePlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicHeightInfGLLeOpNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConstantTermEqZeroOfIsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsCuspidalOfConstantTermEqZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.KFiniteVectors
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GrowthOfSiegelHeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelH
open NumberField GlobalTheory.CuspRep UpperTheory.V

section
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

private theorem aut_to (φ : TR.Sm F a) (h : TR.IsAutForm φ) : IsAutomorphicForm φ.1 := by
  refine ⟨h.left, ⟨UpperTheory.isArchSmooth_of_contDiff_chart F a _ φ.2, fun g => ?_⟩, UpperTheory.k_finite_vectors F a φ h.level h.kfin, (zfin_iff φ).1 h.zfin,
    UpperTheory.growth_of_siegel_height siegelHeight F a φ h.left h.level h.growth⟩
  filter_upwards [h.level.mem_nhds (show TR.finRep F a 1 φ = φ by rw [map_one]; rfl)] with y hy
  rw [finEmb_eq]
  exact congrFun (congrArg Subtype.val hy) g

private theorem aut_of (φ : TR.Sm F a) (h : IsAutomorphicForm φ.1) : TR.IsAutForm φ := by
  refine ⟨h.isLeftInvariant, ?_, ?_, (zfin_iff φ).2 h.isZFinite, fun g => ?_⟩
  · obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant h.isSmooth h.isKFinite
    refine isOpen_iff_mem_nhds.2 fun k hk => ?_
    have h1 : (fun x => k⁻¹ * x) ⁻¹' (U : Set _) ∈ nhds k :=
      (U.isOpen.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using U.one_mem)
    filter_upwards [h1] with x hx
    refine Subtype.ext (funext fun g => ?_)
    have h2 := hU (g * finGL F a k) _ hx
    rw [finEmb_eq, mul_assoc, ← map_mul, mul_inv_cancel_left] at h2
    exact h2.trans (congrFun (congrArg Subtype.val hk) g)
  · have hk : FiniteDimensional ℂ _ := h.isKFinite
    refine FiniteDimensional.of_injective ((TR.Sm F a).subtype.restrict (q := Submodule.span ℂ (Set.range
      fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL F a)) => rightTranslate (k : AdelicGLn.AdelicGL F a) φ.1)) ?_) ?_
    · intro x hx
      refine Submodule.mem_comap.1 (Submodule.span_le.2 ?_ hx)
      rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨⟨TR.infGL F a (Unitary.toUnits k), ?_⟩, rfl⟩
      rw [← infEmb_grpEq]
      exact (UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces F a _).2 k.2
    · intro x y hxy
      have h2 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h2)
  · obtain ⟨C, N, hC⟩ := h.hasModerateGrowth
    obtain ⟨M, hM⟩ := UpperTheory.adelicHeight_infGL_le_opNorm F a
    refine ⟨|C| * (heightConst F a * height g) ^ N, M * N, fun y => (hC _).trans ?_⟩
    have h0 : 0 ≤ heightConst F a * height g := mul_nonneg (zero_le_one.trans one_le_heightConst) (height_pos g).le
    rw [mul_assoc, pow_mul, ← mul_pow]
    exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (height_pos _).le
      ((height_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hM y) h0)) N) (pow_nonneg (height_pos _).le N) (abs_nonneg C)

end

theorem UpperTheory.V.Af.cuspSemisimpleReal_dB :
    UpperTheory.V.Published.CuspSemisimpleReal := by
  refine TR.SS.cuspSemisimple_of fun F _ _ _ a => TR.SS.zeroCompl_of_fb (fun φ h => ?_) (fun f h => ?_)
    (fun X φ _ => congrArg Subtype.val (Fb.uAction_ι_smEq X φ).symm) UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces
  · have h1 := aut_to φ h.1
    exact ⟨h1, UpperTheory.constantTerm_eq_zero_of_isCuspidal F a _ h1.isLeftInvariant h1.continuous h.2⟩
  · exact ⟨UpperTheory.contDiff_chart_of_isArchSmooth F a f h.1.isSmooth.1, aut_of _ h.1, UpperTheory.isCuspidal_of_constantTerm_eq_zero F a f h.1.isLeftInvariant h.1.continuous h.2⟩
