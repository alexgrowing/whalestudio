import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaKernelTranslateSumEqClassicalShortSeriesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicLiftEqGeometricClassSumAllTuples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignThird
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTermsMeanZeroUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordEqOfPerConj
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntilinear
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SingleDatum.AddValue

theorem theta_transSum {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) (V W : HSp D) (l : Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E))
    (e : AE D) {f₀ : WO V W → ℂ} (hf : IsThetaFunO ψ V W f₀) (w : (Fin V.rank → LevQ Dw l) → ℂ) :
    IsThetaFunO ψ V W (transSum ψ V W l ι e f₀ w) := by
  haveI := GlobalTheory.AdTh.ShortSeries.finite_levQ Dw l
  letI : Fintype (Fin V.rank → LevQ Dw l) := Fintype.ofFinite _
  unfold transSum
  rw [finsum_eq_sum_of_fintype]
  refine GlobalTheory.WeilVacMove.isTheta_smul _ ?_
  exact Finset.sum_induction _ (IsThetaFunO ψ V W) (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add) GlobalTheory.WeilVacMove.isTheta_zero
    fun q _ => GlobalTheory.WeilVacMove.isTheta_smul _ (GlobalTheory.AnisoMean.isTheta_heisO hψ hf _)

theorem fvar_eq {D : D7} {m n : ℕ} {τ : D.host.E →+* ℂ} {i p : ℕ} {j : Fin n} {x y : FVar D m n}
    (hx : x.2.2 = j ∧ ((τ = tauE D x.1 ∧ (x.2.1 : ℕ) = i) ∨ (τ = conjEmb (tauE D x.1) ∧ (x.2.1 : ℕ) = p + i)))
    (hy : y.2.2 = j ∧ ((τ = tauE D y.1 ∧ (y.2.1 : ℕ) = i) ∨ (τ = conjEmb (tauE D y.1) ∧ (y.2.1 : ℕ) = p + i)))
    (hne : ∀ s t : D.what₂.Tau, tauE D s ≠ conjEmb (tauE D t)) : x = y := by
  have hc : ∀ s t : D.what₂.Tau, conjEmb (tauE D s) = conjEmb (tauE D t) → s = t := fun s t h => by
    apply GlobalTheory.StdRat.tauE_injective D
    ext z
    have := congrArg (starRingEnd ℂ) (RingHom.congr_fun h z)
    simpa [conjEmb] using this
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  obtain ⟨hx3, hx'⟩ := hx
  obtain ⟨hy3, hy'⟩ := hy
  dsimp only at hx3 hy3 hx' hy'
  have key : x1 = y1 ∧ (x2 : ℕ) = y2 := by
    rcases hx' with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hy' with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact ⟨GlobalTheory.StdRat.tauE_injective D (a1.symm.trans b1), by omega⟩
    · exact absurd (a1.symm.trans b1) (hne _ _)
    · exact absurd (b1.symm.trans a1) (hne _ _)
    · exact ⟨hc _ _ (a1.symm.trans b1), by omega⟩
  obtain ⟨k1, k2⟩ := key
  rw [k1, Fin.ext k2, hx3, hy3]

theorem sq_root_identity (S m z : ℂ) (hm : m ≠ 0) (hz : z = m * (S * S)) : S = S⁻¹ * (m⁻¹ * z) := by
  subst hz
  by_cases hS : S = 0
  · simp [hS]
  · field_simp

end GlobalTheory.SingleDatum.AddValue
