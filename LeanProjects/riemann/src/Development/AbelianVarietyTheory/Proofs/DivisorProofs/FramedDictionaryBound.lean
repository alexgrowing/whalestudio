import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelComponentsDoubleCosetsCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuAllData
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevGeo.MassLev

theorem mass_components_le : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → ∑ k, muF ((U σ).X k) (x0 k) (FF k) ≤ ENNReal.ofReal (massLev D.host.E D.R.r l.M) := by
  intro hMB hTB D j H Dw l Xo c U dict hL σ hσ x0 FF hF
  obtain ⟨G, Λ, g, Λk, u, hSD, hk, hdist⟩ := GlobalTheory.T.principalLevel_components_doubleCosets_congruence D j H Dw l Xo c U dict hL σ hσ
  have hX' := fun k => GlobalTheory.T.exists_flagDomainData_principalCongruenceLevel D.host.E D.R.r l.M ((U σ).X k) (Λk k) l.three_le (hk k).2.2.2.1 (hk k).2.2.2.2.1
  choose X' hX'Gm hX'Ψ hX'p0 hX'Λ hX'Γ using hX'
  have hfm : ∀ k, ∃ y, IsOrth (X' k) y ∧ ∃ FF', IsFundSet (X' k) y FF' ∧ muF (X' k) y FF' < ⊤ :=
    fun k => GlobalTheory.finMu_all_data D.host.E D.R.r (X' k)
  choose y hy FF' hFF' _ using hfm
  have hμ : ∀ k, muF ((U σ).X k) (x0 k) (FF k) = muF (X' k) (y k) (FF' k) := by
    intro k
    obtain ⟨hGm, -, -, -, -, hgram, hfw, hbw⟩ := hk k
    refine GlobalTheory.T.covolume_eq_of_realUnitary_conj D.host.E D.R.r ((U σ).X k) (X' k) (hX'Ψ k) (u k) (x0 k) (y k) (FF k) (FF' k)
      (hX'Gm k) (hX'p0 k) (by rw [hGm]; exact hgram) ?_ ?_ (hF k).1 (hy k) (hF k).2 (hFF' k)
    · intro γ hγ
      obtain ⟨γ', hγ', hc⟩ := hfw γ hγ
      exact ⟨γ', (hX'Γ k γ').2 (by rw [hGm]; exact hγ'), hc⟩
    · intro γ' hγ'
      have := (hX'Γ k γ').1 hγ'
      rw [hGm] at this
      exact hbw γ' this
  have hunf := hL.unf σ hσ
  set Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter (fun τ => τ (H.rt : D.host.E) = H.rt0) with hΨdef
  have hΨ : ∀ k, (X' k).Ψ = Ψ := by
    intro k
    rw [hX'Ψ k]
    ext τ
    rw [(hunf.2.1 k).2 τ, hΨdef, Finset.mem_filter]
    simp
  rw [Finset.sum_congr rfl (fun k _ => hμ k)]
  set e := Fintype.equivFin (U σ).Comp
  rw [← e.symm.sum_comp]
  have hr : 2 ≤ D.R.r := Formalism.L2.Geo.two_le_r D
  have hTor := hTB D.host.E D.R.r l.M G Λ (by omega) (by have := l.three_le; omega) H.unram hSD
  exact hMB D.host.E D.R.r l.M _ _ G Λ Ψ (fun i => X' (e.symm i)) (fun i => g (e.symm i)) (fun i => y (e.symm i))
    (fun i => FF' (e.symm i)) hr l.three_le H.unram hSD hTor (fun i => (hk (e.symm i)).2.1)
    (fun i i' h => e.symm.injective (hdist _ _ h))
    (fun i => ⟨(hX'Gm _).trans (hk _).1, hΨ _, by rw [hX'Λ]; exact (hk _).2.2.1, fun γ => by rw [hX'Λ, hX'Γ, (hk _).1],
      hy _, hFF' _⟩)

end GlobalTheory.LevGeo.MassLev
