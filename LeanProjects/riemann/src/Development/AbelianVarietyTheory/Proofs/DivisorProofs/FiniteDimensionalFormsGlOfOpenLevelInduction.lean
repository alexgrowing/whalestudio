import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermFiniteDimensionalSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermFiniteDimensionalSpanParabolicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanGenEigenOfFiniteDimensionalOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlInductiveRankStatement

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.LeviSliceTwo

set_option maxHeartbeats 1000000 in

theorem secondSlice_mem_finiteDimensional : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ V₂ : Submodule ℂ (GA E (a - r) → ℂ), FiniteDimensional ℂ V₂ ∧ ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ m₁ : GA E r, (fun m₂ : GA E (a - r) => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∈ V₂ := by
  intro E _ _ _ a hind L hL W hW X hX N r hr0 hr _ _ μ 𝓕 hμ h𝓕 h1 t κ
  obtain ⟨L', W', hL', hW', hA⟩ := GlobalTheory.T.constant_term_finite_dimensional_span E a L hL W hW X hX N r hr0 hr μ 𝓕 hμ h𝓕 h1 t κ
  obtain ⟨X', D, hX', hB⟩ := GlobalTheory.T.constant_term_finite_dimensional_span_parabolic E a L hL W hW X hX N r hr0 hr μ 𝓕 hμ h𝓕 h1 t κ
  have hfin := hind (a - r) (by omega)
  haveI := hfin L' hL' W' hW' X' hX' D
  refine ⟨(Submodule.span ℂ (GlobalTheory.HCF.formsGL E (a - r) L' W' X' D)).map (Sm E (a - r)).subtype, inferInstance, ?_⟩
  intro φ hφ m₁
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨ψ, hψ, hleft, hlev, hkfin, hgr, hL'ψ, hW'ψ⟩ := hA φ hφ m₁
    obtain ⟨hU, hUD, hchar⟩ := hB φ hφ m₁ ψ hψ
    have hAψ : IsAutForm ψ := ⟨hleft, hlev, hkfin, hU, hgr⟩
    have hdec := GlobalTheory.T.mem_span_genEigen_of_finiteDimensional_orbit_alt (Sm E (a - r)) (Zalg E (a - r))
      (fun x hx y hy => (GlobalTheory.AutGrowth.KilledFin.Zalg_commute hx hy).eq) X' D ψ hU hUD hchar
    refine ⟨ψ, Submodule.span_mono ?_ hdec, hψ⟩
    rintro ψ' ⟨hψ'U, χ, hχ, hnil⟩
    obtain ⟨e1, e2, e3⟩ := GlobalTheory.T.finiteDimensional_forms_gl_inductive_rank E (a - r) hfin L' W' ψ hAψ hL'ψ hW'ψ ψ' hψ'U
    exact ⟨e1, e2, e3, χ, hχ, hnil⟩
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    funext m₂
    simp only [Submodule.coe_subtype, ZeroMemClass.coe_zero, Pi.zero_apply, integral_zero]
  | add x y hx hy ihx ihy =>
    have hint : ∀ z ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ h,
        IntegrableOn (fun x => z.1 (unip x * h)) 𝓕 μ := by
      intro z hz h
      have hP : Continuous z.1 ∧ (∀ γ h, z.1 (ratGL E a γ * h) = z.1 h) := by
        induction hz using Submodule.span_induction with
        | mem x hx => exact ⟨ContAut.continuous_of_isOpen_stab E a x hx.1.level, hx.1.left⟩
        | zero => exact ⟨continuous_const, fun _ _ => rfl⟩
        | add x y _ _ hx hy => exact ⟨hx.1.add hy.1, fun γ h => congrArg₂ (· + ·) (hx.2 γ h) (hy.2 γ h)⟩
        | smul c x _ hx => exact ⟨hx.1.const_smul c, fun γ h => congrArg (c * ·) (hx.2 γ h)⟩
      haveI := hμ
      exact CuspidalL2GL.integrableOn_unip hP.1 hP.2 μ h𝓕 h
    obtain ⟨u, hu, eu⟩ := ihx
    obtain ⟨v, hv, ev⟩ := ihy
    refine ⟨u + v, add_mem hu hv, ?_⟩
    funext m₂
    have := congrFun eu m₂
    have := congrFun ev m₂
    simp only [Submodule.coe_subtype, Submodule.coe_add, Pi.add_apply] at *
    rw [integral_add (hint x hx _) (hint y hy _)]
    simp_all
  | smul c x hx ihx =>
    obtain ⟨u, hu, eu⟩ := ihx
    refine ⟨c • u, Submodule.smul_mem _ c hu, ?_⟩
    funext m₂
    have := congrFun eu m₂
    simp only [Submodule.coe_subtype, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at *
    rw [integral_const_mul, this]

end GlobalTheory.LeviSliceTwo

end
