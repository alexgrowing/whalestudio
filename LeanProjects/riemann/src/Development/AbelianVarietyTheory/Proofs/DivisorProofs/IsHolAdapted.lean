import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulPowLeRpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialLogGrowthBound
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo
open GlobalTheory.MatDeriv GlobalTheory.GradedNorm Matrix
open scoped ComplexOrder
open GlobalTheory.ShFam.Hor GlobalTheory.HermFrame GlobalTheory.Toroidal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdGram

variable {D : D7} (O : Setup D) {c : O.s.Comp} {σ : D.what₂.LL →+* ℂ}

def gramIn (G : EigMet O.s.T.Z (embOf O.κ.e σ)) (ch : AlgChart (O.var c).str σ (O.var c).dim)
    (g : ∀ p : GlobalTheory.CxPts (O.var c).str σ, (O.Φ.C c).FrameAt p) (τ : D.host.E →+* ℂ)
    (w : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim) : Matrix (Fin (O.S.Dw.mult τ)) (Fin (O.S.Dw.mult τ)) ℂ :=
  G.gram _ (g (ch.e.symm w)) τ

def IsHolAdapted (ch : AlgChart (O.var c).str σ (O.var c).dim) (U : Set (GlobalTheory.CxPts (O.var c).str σ))
    (g : ∀ p : GlobalTheory.CxPts (O.var c).str σ, (O.Φ.C c).FrameAt p) : Prop :=
  IsOpen U ∧ U ⊆ ch.e.source ∧ IsOpen (U ∩ offBd O.Φ c σ) ∧
    (∀ p ∈ U, ∃ t t', (O.Φ.C c).Adapted p t (g p) t') ∧
    HolFam (ch.e '' U) (fun w => (⟨(O.Φ.C c).down (ch.e.symm w), g (ch.e.symm w)⟩ : CxFr O.s.T.Z (embOf O.κ.e σ))) ∧
    ∀ (G : EigMet O.s.T.Z (embOf O.κ.e σ)) (S : Set (GlobalTheory.CxPts (genStr O.s.T.Z) (embOf O.κ.e σ))), IsOpen S →
      G.SmoothOn (manifold O.s.T.Z (embOf O.κ.e σ)) S → ∀ τ : D.host.E →+* ℂ,
        IsPosFrame (ch.e '' (U ∩ {p | (O.Φ.C c).down p ∈ S})) fun w => (gramIn O G ch g τ w)ᵀ

end GlobalTheory.BdGram
