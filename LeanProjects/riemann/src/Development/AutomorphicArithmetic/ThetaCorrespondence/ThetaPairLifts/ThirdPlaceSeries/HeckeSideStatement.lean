import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SphericalVectorFixedLocalStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeSide
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_vector_fixed_local_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E)
    (w : PlE D.host) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
    IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → ∀ J : Subgroup (GAf D.host.E D.R.nV),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV)) → ∀ f ∈ π.S, f ≠ 0 →
    (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) → ∀ c : ℕ → ℂ,
    (∀ k, 1 ≤ k → k ≤ D.R.nV → NG.tN J s ϖ k f = c k • f) → ∀ x, GlobalTheory.AutQuot.LocAt π w x →
    ((_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x).lpTw ((1 - (D.R.nV : ℝ)) / 2)).unr ∧
    X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        Polynomial.C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      (Multiset.map (fun α => X - Polynomial.C α)
        ((_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x).lpTw ((1 - (D.R.nV : ℝ)) / 2)).frobEig).prod := by
  first | exact @_root_.GlobalTheory.HeckeFrob.locPol_eq_alt | exact _root_.GlobalTheory.HeckeFrob.locPol_eq_alt | (intros; apply _root_.GlobalTheory.HeckeFrob.locPol_eq_alt <;> assumption)
end
