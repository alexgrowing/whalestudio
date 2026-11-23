import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetTwistedConjugacy
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFiniteness

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw

namespace GlobalTheory.CompanionTheory.UnitarySide

theorem charpoly_conj_diagonal {K : Type} [Field K] {n : ℕ} (c D g : GL (Fin n) K) (d : Fin n → K)
    (hD : D.val = Matrix.diagonal d) (hg : g = c * D * c⁻¹) :
    g.val.charpoly = ∏ i, (X - C (d i)) := by
  subst hg
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, hD,
    Matrix.charpoly_diagonal]

open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hasVals_conj_diag (w : Pl E) (n : ℕ) (c : GLw n w) (u : Fin n → (w.adicCompletion E)ˣ)
    (a : Fin n → ℤ) (hu : ∀ i, ordL (u i : w.adicCompletion E) = a i) (g : GLw n w)
    (hg : g = c * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * c⁻¹) :
    HasVals g.val.charpoly a :=
  ⟨fun i => (u i : w.adicCompletion E),
    charpoly_conj_diagonal c _ g _ (GlobalTheory.SmGL.val_diagT _ _) hg,
    fun i => ⟨(u i).ne_zero, hu i⟩⟩

theorem s2 : P_contr_id → DiagonalConjDistinctValuations → Hilbert90InertPlace → P_iwU_facts → UnitaryHeckeSingleCoset := by
  intro hcontr _ _ hiw E _ _ _ hU w hw n b hb ϖ hϖ l hl γ hP
  have hyp : ∀ (y : Fin n → ℤ), StrictAnti y → ∀ δ : GLw n w, dcos n w (tdiag ϖ y) δ ≠ 0 →
      ∃ m ∈ iwGL n w, ∃ τ : GLw n w, ((∀ i j : Fin n, i ≠ j → τ.val i j = 0) ∧
        ∀ i, Valued.v (τ.val i i) = 1) ∧ m⁻¹ * δ * m = tdiag ϖ y * τ := by
    intro y hy δ hδ
    obtain ⟨m, hm, τ, hτ, e⟩ := hcontr w ϖ hϖ n y hy δ hδ
    exact ⟨m, hm, τ, hτ, e⟩
  obtain ⟨p₀, u, hu, hγ0, hsupp, hcpt⟩ :=
    GlobalTheory.CompanionTheory.SuppCent.main E hU w hw n b hb ϖ hϖ l hl hyp γ hP
  obtain ⟨-, hKc, -, -, -⟩ := hiw w hw n b hb ϖ l
  obtain ⟨-, -, hWc, -⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  have hle : cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ (iwU n w b).map (MulAut.conj p₀).toMonoidHom := by
    rw [hcpt]
    exact inf_le_right
  refine ⟨⟨p₀, fun p => ?_, hle⟩, fun x => ⟨?_, ?_⟩, ?_⟩
  · exact hsupp p
  · exact GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj _ hKc x)
  · exact GlobalTheory.LocFin.relIndex_cptPart_ne_zero _ _ _
      (GlobalTheory.LocFin.isOpen_map_conj _ (GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w b) x)
      (GlobalTheory.LocFin.isCompact_map_conj _ hWc p₀) hle
  · have hγ : γ.1 = (p₀.1 * b) * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * (p₀.1 * b)⁻¹ := by
      have e : γ.1 = p₀.1 * (p₀⁻¹ * γ * p₀).1 * p₀.1⁻¹ := by
        change γ.1 = p₀.1 * (p₀.1⁻¹ * γ.1 * p₀.1) * p₀.1⁻¹
        group
      rw [e, hγ0]
      group
    exact hasVals_conj_diag w n _ u _ hu _ hγ

end GlobalTheory.CompanionTheory.UnitarySide
