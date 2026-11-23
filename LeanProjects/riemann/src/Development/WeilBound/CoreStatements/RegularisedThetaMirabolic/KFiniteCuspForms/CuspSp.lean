import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfL2CuspidalMemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothKFiniteCenterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteL2SmoothRepresentative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeneralHyps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalSmoothModuleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSmoothModuleUniqueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteVectorsDenseStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace RfCs.FrobeniusSplitPrimeDatum

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
  {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem mem_of_stable {H : Submodule ℂ (L2 (latticeGL E a) μ)} (hH : H ≤ L2cusp μ)
    (hi : IsIrredSubrep (R (latticeGL E a) μ) H) (W : Submodule ℂ (Sm E a)) (hs : IsStable W) (h0 : W ≠ ⊥)
    (hW : ∀ φ ∈ W, IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
      ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) (φ : Sm E a)
    (hφ : IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
      ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) : φ ∈ W :=
  GlobalTheory.T.irreducible_smooth_module_unique E a μ H hH hi W hs h0 hW φ hφ

theorem exists_cusp_form_of_K_finite {H : Submodule ℂ (L2 (latticeGL E a) μ)} (hH : H ≤ L2cusp μ)
    (hi : IsIrredSubrep (R (latticeGL E a) μ) H) {F : L2 (latticeGL E a) μ} (hF : F ∈ H) (hk : IsKFinL2 μ F) :
    ∃ φ : Sm E a, lift (latticeGL E a) F =ᵐ[μ] φ.1 ∧ IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
      ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H := by
  obtain ⟨φ, e, hm, hl, hz, hlev, hkf, hzf⟩ := GlobalTheory.CompanionTheory.SmoothRep.smoothRep E a μ H hH hi F hF hk
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hlev
  have hFe : hm.toL2 = F := l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (hm.lift_toL2_ae_eq.trans e.symm)
  have hcusp : IsCuspidal φ.1 := GlobalTheory.T.cuspidal_of_L2_cuspidal_mem E a μ φ.1 hc hl hz hm (by rw [hFe]; exact hH hF)
  exact ⟨φ, e, ⟨⟨hl, hlev, hkf, hzf, GlobalTheory.T.smooth_K_finite_center E a μ φ hl hz hlev hkf hzf hm⟩, hcusp⟩, hz, hm,
    by rw [hFe]; exact hF⟩

end RfCs.FrobeniusSplitPrimeDatum

namespace RfCs

open RfCs.FrobeniusSplitPrimeDatum in

theorem cuspFiniteVectorsGL : GlobalTheory.Published.CuspFiniteVectorsGL := by
  intro E _ _ _ a μ _ _ H hH hi
  obtain ⟨V, hV, hs⟩ := GlobalTheory.T.irreducible_cuspidal_smooth_module E a μ H hH hi
  have hkf : ∀ F ∈ H, IsKFinL2 μ F → F ∈ classes V μ := fun F hF hk => by
    obtain ⟨φ, e, h1, h2, h3⟩ := exists_cusp_form_of_K_finite hH hi hF hk
    exact ⟨φ, (hV φ).2 ⟨h1, h2, h3⟩, e⟩
  have hcl : classes V μ ≤ H := by
    rintro F ⟨φ, hφ, e⟩
    obtain ⟨-, -, h, hH'⟩ := (hV φ).1 hφ
    have : F = h.toL2 := l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans h.lift_toL2_ae_eq.symm)
    exact this ▸ hH'
  have hdense : H ≤ (classes V μ).topologicalClosure :=
    (GlobalTheory.T.K_finite_vectors_dense E a μ H hi.1).trans (Submodule.topologicalClosure_mono
      (Submodule.span_le.2 fun F hF => hkf F hF.1 hF.2))
  have hne : V ≠ ⊥ := by
    intro hb
    refine hi.2.1 (eq_bot_iff.2 (hdense.trans (Submodule.topologicalClosure_minimal _ ?_ ?_)))
    · rintro F ⟨φ, hφ, e⟩
      rw [hb, Submodule.mem_bot] at hφ
      have h0 : φ.1 = 0 := by rw [hφ]; rfl
      rw [h0] at e
      exact (Submodule.mem_bot ℂ).2 (l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans (show lift (latticeGL E a) (0 : L2 (latticeGL E a) μ) =ᵐ[μ] 0 from
        ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)).symm))
    · rw [Submodule.bot_coe]
      exact isClosed_singleton
  have hirr : ∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V := fun W hWV hWs => by
    by_cases h0 : W = ⊥
    · exact Or.inl h0
    · exact Or.inr (le_antisymm hWV fun φ hφ =>
        mem_of_stable hH hi W hWs h0 (fun ψ hψ => (hV ψ).1 (hWV hψ)) φ ((hV φ).1 hφ))
  let π : CuspSub E a := ⟨V, fun φ hφ => ((hV φ).1 hφ).1, hs, hne, hirr⟩
  exact ⟨π, fun φ hφ => ((hV φ).1 hφ).2.1, fun φ hφ => ((hV φ).1 hφ).2.2.1,
    le_antisymm (Submodule.topologicalClosure_minimal _ hcl hi.1.1) hdense, hkf⟩

end RfCs

end

theorem RfCs.cuspidalSpectrumGL : GlobalTheory.Published.CuspidalSpectrumGL :=
  ⟨GlobalTheory.CompanionTheory.CuspRep.cuspDiscreteDecompositionGL, RfCs.cuspFiniteVectorsGL, GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL⟩
