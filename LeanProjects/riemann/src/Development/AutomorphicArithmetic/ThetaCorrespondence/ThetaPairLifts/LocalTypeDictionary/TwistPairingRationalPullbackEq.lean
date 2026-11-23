import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankSelfDualUnitary
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankSelfDualUnitaryStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets
noncomputable section
namespace GlobalTheory.RatMoveIop
open Formalism.L2.KerInert Formalism.L2.KerInert.PullbackComparison GlobalTheory.ThLoc.AllPlaces
section Arith
variable {F : Type} [NormedField F] {lam : Qbar →+* F}
end Arith
variable {D : D7} {N N' : ℕ}
variable (A : Matrix.unitaryGroup (Fin N) D.host.E) (A' : Matrix.unitaryGroup (Fin N') D.host.E)
variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
theorem twist_pairing_pullback_of_rational : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {δ t0 : ℂ}, Crv D D.host.ccK δ →
    GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 → ∀ {N N' : ℕ} {e0 : VC D N N' → ℂ}, oddE0 D D.host.ccK δ t0 N N' e0 → Even (N * N') →
    ∀ (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D M → SD D M' →
    ∀ (U : Matrix.unitaryGroup (Fin N) D.host.E) (U' : Matrix.unitaryGroup (Fin N') D.host.E),
    ∃ ε : ℂ, Mod1All ε ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q M (stdL D N) → EqAt D q M' (stdL D N') →
        EqAt D q (SDLat.smulLat U.1 M) (stdL D N) → EqAt D q (SDLat.smulLat U'.1 M') (stdL D N') → GlobalTheory.MovedKappaEx.UnitAt q ε) ∧
      ∀ z, Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) M M') e0
          (Formalism.L2.KerInert.tPull D (tor0 D D.host.ccK δ) U.1 U'.1 z) =
        ε * Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N')
          (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (SDLat.smulLat U.1 M) (SDLat.smulLat U'.1 M')) e0 z := by
  intro _ hI D δ t0 hC ht N N' e0 he _ M M' hM hM' A A'
  obtain ⟨ε, h1, h2⟩ := iop_move A A' D.host.ccK δ (hI D) hC ht he.2.2.2.1 hM hM'
  have hc : ∀ σ : Qbar →+* ℂ, NormOne σ ε := fun σ =>
    h1 ℂ σ fun τ => ⟨(norm_det_complex _ A').1, (norm_det_complex _ A).2⟩
  refine ⟨ε, ⟨(hc (algebraMap Qbar ℂ)).1, fun σ => (hc σ).2⟩, fun q _ a1 a2 a3 a4 lam => ?_, h2⟩
  obtain ⟨h3, h4⟩ := h1 ℂ_[q] lam fun τ => ⟨(norm_det_padic _ A' a2 a4).1, (norm_det_padic _ A a1 a3).2⟩
  rw [lamC, dif_pos h3]
  exact h4
end GlobalTheory.RatMoveIop
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_pairing_rational_pullback_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {δ t0 : ℂ}, Crv D D.host.ccK δ →
    GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 → ∀ {N N' : ℕ} {e0 : VC D N N' → ℂ}, oddE0 D D.host.ccK δ t0 N N' e0 → Even (N * N') →
    ∀ (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D M → SD D M' →
    ∀ (U : Matrix.unitaryGroup (Fin N) D.host.E) (U' : Matrix.unitaryGroup (Fin N') D.host.E),
    ∃ ε : ℂ, Mod1All ε ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q M (stdL D N) → EqAt D q M' (stdL D N') →
        EqAt D q (SDLat.smulLat U.1 M) (stdL D N) → EqAt D q (SDLat.smulLat U'.1 M') (stdL D N') → GlobalTheory.MovedKappaEx.UnitAt q ε) ∧
      ∀ z, Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) M M') e0
          (Formalism.L2.KerInert.tPull D (tor0 D D.host.ccK δ) U.1 U'.1 z) =
        ε * Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N')
          (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (SDLat.smulLat U.1 M) (SDLat.smulLat U'.1 M')) e0 z := by
  first | exact @_root_.GlobalTheory.RatMoveIop.twist_pairing_pullback_of_rational | exact _root_.GlobalTheory.RatMoveIop.twist_pairing_pullback_of_rational | (intros; apply _root_.GlobalTheory.RatMoveIop.twist_pairing_pullback_of_rational <;> assumption)
end
