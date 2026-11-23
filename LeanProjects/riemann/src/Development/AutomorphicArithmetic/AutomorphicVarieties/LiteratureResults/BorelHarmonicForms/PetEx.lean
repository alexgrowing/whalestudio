import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SumCoordRe
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OpenFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SkewLieActionL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.LieOneComm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

open MeasureTheory GlobalTheory.CuspRep.CuspidalL2GL in

theorem UpperTheory.V.Lit.Bor.petEx :
    UpperTheory.V.Lit.Bor.PetEx := by
  intro E _ _ _ a ha r
  obtain ⟨χ, hχ⟩ := twEx E a ha r
  let μ : Measure (GA E a) := Measure.haar
  have hs := sqMem E a ha μ r χ hχ
  have hm : ∀ φ ∈ (sqSub E a r).map (mulChi a χ).toLinearMap,
      GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hs φ hφ).2
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (sqSub E a r).subtype (Submodule.ker_subtype _)
  obtain ⟨T, hT⟩ : ∃ T : Sm E a →ₗ[ℂ] GlobalTheory.AutomorphicL2Unitary.L2 (GlobalTheory.UnitaryBC.latticeGL E a) μ, ∀ φ ∈ sqSub E a r, ∀ (ψ : Sm E a)
      (h : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ ψ.1), ψ = mulChi a χ φ → T φ = h.toL2 := by
    refine ⟨toL2ₗ μ _ hm ∘ₗ (mulChi a χ).toLinearMap.submoduleMap (sqSub E a r) ∘ₗ p, ?_⟩
    rintro φ hφ _ h rfl
    have e : p φ = ⟨φ, hφ⟩ := LinearMap.congr_fun hp ⟨φ, hφ⟩
    simp only [LinearMap.comp_apply, e]
    rfl
  refine ⟨((innerₛₗ ℂ) ∘ₛₗ T).compl₂ T, ⟨fun x y => ?_, fun x _ => ?_, fun x hx h0 => ?_⟩, fun X φ hφ ψ hψ => ?_⟩
  · exact (inner_conj_symm (T y) (T x)).symm
  · exact inner_self_nonneg (𝕜 := ℂ) (x := T x)
  · have h1 : T x = 0 := inner_self_eq_zero.1 (show inner ℂ (T x) (T x) = 0 from h0)
    rw [hT x hx _ (hs x hx).2 rfl] at h1
    by_contra hne
    refine toL2_ne_zero (hs x hx).2 (ContAut.continuous_of_isOpen_stab E a _ (hs x hx).1) (fun e => hne ?_) h1
    exact (mulChi a χ).map_eq_zero_iff.1 (Subtype.ext e)
  · have hL := (sqLie E a r).2 X
    have hmem : ∀ f ∈ sqSub E a r, lie E a X f + ((r * ell E a X : ℝ) : ℂ) • f ∈ sqSub E a r := fun f hf =>
      add_mem (hL f hf) (Submodule.smul_mem _ _ hf)
    have hd : ∀ f ∈ sqSub E a r, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X (mulChi a χ f)).1 :=
      fun f hf => by
        rw [hχ.2]
        exact (hs _ (hmem f hf)).2
    have hk := skew_lie_action_L2 E a μ X _ _ (hs φ hφ).1 (hs ψ hψ).1 (hs φ hφ).2 (hs ψ hψ).2 (hd φ hφ) (hd ψ hψ)
    rw [← hT _ (hmem φ hφ) _ (hd φ hφ) (hχ.2 X φ), ← hT _ (hmem ψ hψ) _ (hd ψ hψ) (hχ.2 X ψ),
      ← hT φ hφ _ (hs φ hφ).2 rfl, ← hT ψ hψ _ (hs ψ hψ).2 rfl, map_add, map_add, map_smul, map_smul,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at hk
    change inner ℂ (T (lie E a X φ)) (T ψ) + inner ℂ (T φ) (T (lie E a X ψ)) = _ * inner ℂ (T φ) (T ψ)
    push_cast at hk ⊢
    linear_combination hk
