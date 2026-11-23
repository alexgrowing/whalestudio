import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionOldCellMultiplicityLeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNewCellMultiplicityLtStatement

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem GlobalTheory.PolFan.starMult : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → SimpLab H.bar q φ lab → IsCentreSet H.bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    IsPolyFan H.bar q ψ' → Subordinate H.bar q ψ' φ → IsStarOf H.bar q φ w ψ' → ∀ M : ℕ, maxMult H.bar q φ ≤ M →
    maxMult H.bar q ψ' ≤ M ∧
      ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell H.bar ψ' M δ →
          IsMultCell H.bar φ M δ ∧ ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β ≠ 1 := by
  intro E _ _ _ H q φ lab w ψ' hD hφ hSL hW hC hψ' hSub hStar M hM
  have cI := GlobalTheory.T.starSubdivision_oldCell_multiplicity_le E H q φ lab w ψ' hD hφ hSL M hM
  have cII := GlobalTheory.T.starSubdivision_newCell_multiplicity_lt E H q φ lab w ψ' hSL hW hC M hM
  refine ⟨?_, ?_⟩
  · refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun hX =>
      iSup_le fun n => iSup_le fun γ' => iSup_le fun hγ' => iSup_le fun hli => iSup_le fun hpr => ?_
    rcases hStar.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, hw, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, hb, hp, hw1, hin0, hcut, hpos, hin⟩
    · obtain ⟨hφγ, hle, -⟩ := cI X hX n γ' hγ' hli hpr m γ hγ (hStar.1 X hX m γ hγ hw) hw hin
      exact_mod_cast hle
    · have := cII X hX n γ' hγ' hli hpr m γ β₀ m' s h hγ hb hp hw1 hin0 hcut hpos
        (hStar.2.1 X hX m γ hγ β₀ hb hp hw1 hin0 m' s h hcut hpos) hin
      exact_mod_cast this.le
  · intro X _ _ _ _ hX n γ' ⟨hγ', hli, hpr, heq⟩
    rcases hStar.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, hw, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, hb, hp, hw1, hin0, hcut, hpos, hin⟩
    · obtain ⟨hφγ, -, hno⟩ := cI X hX n γ' hγ' hli hpr m γ hγ (hStar.1 X hX m γ hγ hw) hw hin
      exact ⟨⟨hφγ, hli, hpr, heq⟩, hno⟩
    · have := cII X hX n γ' hγ' hli hpr m γ β₀ m' s h hγ hb hp hw1 hin0 hcut hpos
        (hStar.2.1 X hX m γ hγ β₀ hb hp hw1 hin0 m' s h hcut hpos) hin
      omega
