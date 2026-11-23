import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ElemPairJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSatakeParameterOfIsSubquotientOfInjective

noncomputable section

open NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory.C GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions UpperTheory.CBC

namespace UpperTheory.ConvolutionTheory.Sph

def SatDict : Prop :=
  ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (π : CuspSub K n) (v : Pl K)
    (τ : SmIrr (Gw n v)), (Cusp.cx π).locComp v τ →
      ((∃ B, (Cusp.cx π).sat v B) → IsSpherical τ.ρ) ∧
      (IsSpherical τ.ρ → ∃ α : Fin n → ℂˣ, IsSubquotient τ.ρ (prinSeries fun i => unrChar (v.adicCompletion K) (α i))) ∧
      ∀ α : Fin n → ℂˣ, IsSpherical τ.ρ → IsSubquotient τ.ρ (prinSeries fun i => unrChar (v.adicCompletion K) (α i)) →
        (Cusp.cx π).sat v (Finset.univ.val.map fun i => α i ^ ε)

def UnlSph : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (v : Pl K) (τ : SmIrr (Gw n v)) (α : Fin n → ℂˣ),
    (∀ i j, (α i : ℂ) ≠ (Ideal.absNorm v.asIdeal : ℂ) * α j) →
    IsSubquotient τ.ρ (prinSeries fun i => unrChar (v.adicCompletion K) (α i)) → IsSpherical τ.ρ

def UnrNorm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (w : PlacesOver E v)
    (σw : w.1.adicCompletion E ≃+* w.1.adicCompletion E) (l : ℕ) (N : (w.1.adicCompletion E)ˣ →* (v.adicCompletion F)ˣ),
    UpperTheory.Gal.Join.IsNorm (completionMap v w.1) σw l N → Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal → ∀ a : ℂˣ,
      (unrChar (v.adicCompletion F) a).comp N = unrChar (w.1.adicCompletion E) a

def WeakStable : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M] [IsTotallyComplex K]
    [IsTotallyComplex M], (Module.finrank K M).Prime → ∀ n : ℕ, 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub M n),
    UpperTheory.V.Published.WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → (∀ g : M ≃ₐ[K] M, (Cusp.cx P).ConjIso g.toRingEquiv) ∧
      (∀ v, ∃ τ, (Cusp.cx π).locComp v τ) ∧ ∀ w, ∃ τ', (Cusp.cx P).locComp w τ'

end UpperTheory.ConvolutionTheory.Sph
