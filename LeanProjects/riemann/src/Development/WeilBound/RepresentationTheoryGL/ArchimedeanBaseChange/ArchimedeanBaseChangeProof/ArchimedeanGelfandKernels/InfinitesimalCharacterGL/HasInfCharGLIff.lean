import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.BridgeSt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.PChart
import Development.WeilBound.CoreStatements.SatakeConjugation.CapEqQdet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementsActByGelfandValuesStatement

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC Finset

namespace PositivityTheory.RgBcC.Bridge

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem hasInfCharGL_iff (V : Submodule ℂ (Sm E a)) (τ : E →+* ℂ) (χ' : Fin a → ℂ) :
    HasInfCharGL V τ (Multiset.map χ' Finset.univ.val) ↔
      ∀ φ ∈ V, ∀ k, Formalism.REAL.etr (Eop τ) k φ = GlobalTheory.Dec.gelfVal χ' k • φ := by
  have hprod : ∀ u : ℂ, ((Multiset.map χ' univ.val).map (u + ·)).prod = Formalism.QuantumDeterminants.capP χ' u := by
    intro u; rw [Multiset.map_map, Formalism.QuantumDeterminants.capP, Finset.prod_eq_multiset_prod]; rfl
  have hcard : Multiset.card (Multiset.map χ' Finset.univ.val) = a := by simp
  unfold HasInfCharGL
  simp only [hcard, true_and, hprod, PositivityTheory.NCmp.cap_eq_qdet]
  rcases a with _ | m
  · constructor
    · intro _ φ _ k; simp [Formalism.REAL.etr, GlobalTheory.Dec.gelfVal]
    · intro _ u φ _; simp [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.QuantumDeterminants.capP]
  · constructor
    · intro h φ hφ k
      exact GlobalTheory.T.trace_elements_act_by_gelfand_values (Sm E (m + 1)) m (Eop τ) χ' φ (glRel_Eop τ) (fun Y => h Y φ hφ) k
    · intro h u φ hφ
      exact gelfToCap (Sm E (m + 1)) m (Eop τ) χ' φ (glRel_Eop τ) (h φ hφ) u

theorem one_mem_GLs : (1 : Matrix (Fin a) (Fin a) ℂ) ∈ PositivityTheory.RgBcC.GLs a := by
  simp [PositivityTheory.RgBcC.GLs]

theorem bridge : BridgeSt := by
  intro E _ _ _ a V w χ
  rw [hasInfCharGL_iff, hasInfCharGL_iff]
  constructor
  · intro h
    have key : ∀ s, ∀ φ ∈ V, ∀ k, Formalism.REAL.etr (eopW w s) k φ = GlobalTheory.Dec.gelfVal (χ s) k • φ := by
      intro s φ hφ k
      apply Subtype.ext; funext g
      have h1 := h φ hφ g s k 1 one_mem_GLs
      rw [gel_along w g s k φ one_mem_GLs, along_one, along_one] at h1
      rw [Submodule.coe_smul, Pi.smul_apply]
      exact h1
    exact ⟨by simpa [eopW] using key true, by simpa [eopW] using key false⟩
  · rintro ⟨h1, h2⟩ φ hφ g s k x hx
    have key : Formalism.REAL.etr (eopW w s) k φ = GlobalTheory.Dec.gelfVal (χ s) k • φ := by
      cases s
      · simpa [eopW] using h2 φ hφ k
      · simpa [eopW] using h1 φ hφ k
    rw [gel_along w g s k φ hx, key, Submodule.coe_smul, along_smul, Pi.smul_apply]

end PositivityTheory.RgBcC.Bridge
