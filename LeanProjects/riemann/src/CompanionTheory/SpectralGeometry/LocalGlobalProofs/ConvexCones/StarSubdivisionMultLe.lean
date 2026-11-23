import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNoNewCellOfMaximalMultiplicityFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.OldCellMultLeAfterStarStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.NewCellMultLtAfterStarStatement

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarMultiplicity

theorem starMult : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) →
    IsPolyFan bar q φ → SimpLab bar q φ lab → IsCentreSet bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    IsPolyFan bar q ψ' → Subordinate bar q ψ' φ → IsStarOf bar q φ w ψ' → ∀ M : ℕ, maxMult bar q φ ≤ M →
    maxMult bar q ψ' ≤ M ∧
      ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar ψ' M δ →
          IsMultCell bar φ M δ ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β ≠ 1 := by
  intro O _ _ _ _ bar hCM q φ lab w ψ' hDom hφ hlab hw hc1 hψ' hsub hstar M hM
  obtain ⟨hs1, hs2, hs3⟩ := hstar
  have key : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim bar (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) →
        (∃ (_ : IsCell bar φ γ'), (cellMult bar fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) ≤ M ∧
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ' β → w.evalZ β ≠ 1) ∨
        (cellMult bar fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) < M := by
    intro X _ _ _ _ hX n γ' hγ' hli hpr
    rcases hs3 X hX n γ' hγ' with ⟨m, γ, hγ, hw0, hin⟩ |
        ⟨m, γ, β₀, m', s, h, hγ, hβ₀, hpsd, hw1, hcone, hcut, hpos, hin⟩
    · left
      exact GlobalTheory.T.old_cell_mult_le_after_star O bar hCM q φ lab w ψ' hDom hφ hlab M hM X hX n γ' hγ' hli hpr m γ hγ
        (hs1 X hX m γ hγ hw0) hw0 hin
    · right
      exact GlobalTheory.T.new_cell_mult_lt_after_star O bar hCM q φ lab w ψ' hlab hw hc1 M hM X hX n γ' hγ' hli hpr m γ β₀ m' s h
        hγ hβ₀ hpsd hw1 hcone hcut hpos (hs2 X hX m γ hγ β₀ hβ₀ hpsd hw1 hcone m' s h hcut hpos) hin
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.PolFan.maxMult
    refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun hX => iSup_le fun n => iSup_le fun γ' => iSup_le fun hγ' => iSup_le fun hli =>
      iSup_le fun hpr => ?_
    rcases key X hX n γ' hγ' hli hpr with ⟨_, hle, _⟩ | hlt
    · exact_mod_cast hle
    · exact_mod_cast hlt.le
  · intro X _ _ _ _ hX m δ hδ
    obtain ⟨hc, hli, hpr, hEq⟩ := hδ
    rcases key X hX m δ hc hli hpr with ⟨hφ', _, hno⟩ | hlt
    · exact ⟨⟨hφ', hli, hpr, hEq⟩, hno⟩
    · exact absurd hEq (ne_of_lt hlt)

end GlobalTheory.CompanionTheory.Ar.Fan.StarMultiplicity
