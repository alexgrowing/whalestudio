import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCrystallineBlockDataOfReductionPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachLatticesRankOneModelsReducedFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasesBlockTriangularOfReducedEtaleFiltratStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.WachBlock

theorem wach_inputs : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → BlockPair E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (Wl : Formalism.CohomologicalDescent.FrobeniusPeriodChange.WLat (E →+* PadicAlgCl l) t n O' F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (kap : (E →+* PadicAlgCl l) → Fin t → ℤ) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), Formalism.CohomologicalDescent.FrobeniusPeriodChange.NInputs Wl σ l h u c J (fun i s => bot i + ((s : ℕ) : ℤ)) kap I ζ em jj := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl2 hdisc σ hσ n t h J bot hJ hbot hBP
  obtain ⟨O', F, L', i1, i2, i3, i4, i5, i6, I, i7, red, un, N, Npsi, u, c, ζ, em, jj, hU, hR, hN, hψ, hF⟩ :=
    GlobalTheory.T.wachLattices_rankOne_models_reducedFiltration hBS E Ω l hl2 hdisc σ hσ n t h J bot hJ hbot (GlobalTheory.T.integralCrystallineBlockData_of_reductionPair E Ω l n t J bot hBP)
  obtain ⟨g, b, pos, w, kap, hpos, hP, hG, hPd, hGd⟩ :=
    GlobalTheory.T.adaptedBases_blockTriangular_of_reducedEtaleFiltration _ σ l n t F _ _ _ _ _ (Fact.out : l.Prime).pos inferInstance hF
  exact ⟨O', F, L', i1, i2, i3, i4, i5, i6, I, i7, ⟨red, un, N, Npsi, g, b, pos, w⟩, u, c, kap, ζ, em, jj,
    ⟨hU, hJ, hbot, hpos, hP, hG, hPd, hGd⟩, hR, hN, hψ⟩

end GlobalTheory.WachBlock

end
