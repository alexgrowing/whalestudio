import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG Polynomial GlobalTheory.SphPar GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.SphGal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParUEx {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (q n : ℕ) (lab : List ℤ → Prop)
    (c : List ℤ → ℂ) (s : Multiset ℂ) : Prop :=
  ∃ α : Fin (n / 2) → ℂ, (∀ i, α i ≠ 0) ∧ bcPar n α = s ∧
    ∀ φ : GU σ n → ℂ, IsSphericalU q α φ → ∀ d, lab d →
      hAct (KU σ n) (fun g : GU σ n => divInd (intL L) d (g : GL (Fin n) L)) φ 1 = c d * φ 1

section Global

variable {E : Type} [Field E] [NumberField E]

def ParGLEx (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) : Prop :=
  ∃ α : Fin n → ℂ, (∀ i, α i ≠ 0) ∧ Finset.univ.val.map α = s ∧
    ∀ φ : GL (Fin n) (P.adicCompletion E) → ℂ, IsSpherical E P α φ → ∀ d, lab d →
      hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) d) φ 1 = c d * φ 1

def IsParEx [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) : Prop :=
  (Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal ≠ P.asIdeal → ParGLEx P n lab c s) ∧
  (Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = P.asIdeal →
    ∀ (σ : P.adicCompletion E →+* P.adicCompletion E) (ϖ : P.adicCompletion E) (q : ℕ),
      IsConjAt P σ → IsUnramInv ϖ σ q → ParUEx σ q n lab c s)

end Global

def spehInf (d : ℕ) (A : Multiset ℂ) : Multiset ℂ :=
  ∑ j : Fin d, A.map (· + (((d : ℂ) - 1) / 2 - (j : ℕ)))

def spehSat (q d : ℕ) (B : Multiset ℂˣ) : Multiset ℂ :=
  ∑ j : Fin d, B.map fun b : ℂˣ => (b : ℂ) * (q : ℂ) ^ (-(((d : ℂ) - 1) / 2 - (j : ℕ)))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (M : DSModel V S)

def IsStableSub (W : Submodule ℂ (MMap M)) : Prop :=
  W ≤ Mult θ M ∅ (fun _ => 1) ∧ ∀ k ∈ GfC V, ∀ T ∈ W, heckeOn M {k} T ∈ W

def IsCuspQuot (W' W : Submodule ℂ (MMap M)) : Prop :=
  IsStableSub θ M W' ∧ IsStableSub θ M W ∧ W' < W ∧ ∀ U, IsStableSub θ M U → W' ≤ U → U ≤ W → U = W' ∨ U = W

def SphEig (W' W : Submodule ℂ (MMap M)) (P : HeightOneSpectrum (𝓞 D.host.E)) (c : List ℤ → ℂ) : Prop :=
  ∃ T ∈ W, T ∉ W' ∧ (∀ k ∈ GlobalTheory.Hk3.hyp V P, heckeOn M {k} T - T ∈ W') ∧
    ∀ d R, GlobalTheory.Hk3.SphOp V P d R → heckeOn M R T - c d • T ∈ W'

def HasBaseChange (W' W : Submodule ℂ (MMap M)) : Prop :=
  haveI := host_isCMField D.host
  ∃ (r : ℕ) (m d : Fin r → ℕ) (π : ∀ i, CuspSub D.host.E (m i)),
    (∀ i, 1 ≤ m i ∧ 1 ≤ d i ∧ (π i).IsCsd) ∧ ∑ i, m i * d i = V.rank ∧
    (∀ τ, ∃ A A' : Fin r → Multiset ℂ,
      (∀ i, (π i).HasInfChar (tauE D τ) (A i) ∧ (π i).HasInfChar (ComplexEmbedding.conjugate (tauE D τ)) (A' i)) ∧
      ∑ i, spehInf (d i) (A i) = Finset.univ.val.map (fun a => (M.lam τ a : ℂ)) ∧
      ∑ i, spehInf (d i) (A' i) = Finset.univ.val.map (fun a => -(M.lam τ a : ℂ))) ∧
    ∀ P c, SphEig M W' W P c → ∃ B : Fin r → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL P ((π i).locRep P) (B i)) ∧
      IsParEx P V.rank (GlobalTheory.Hk3.IsLab V P) c (∑ i, spehSat (Formalism.ConjugateSelfDual.normV P) (d i) (B i))

def BaseChangeRegular : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (W' W : Submodule ℂ (MMap M)),
    IsInfFam θ → (∀ τ, Formalism.QuantumDeterminants.IsHCParam (M.lam τ)) → RegularWt M → IsCuspQuot θ M W' W → HasBaseChange M W' W

def GaloisOfPolarized : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (m : ℕ) (π : CuspSub E m) (χ : Formalism.L2.Host.HChar E) (u : ℝ),
    1 ≤ m → π.IsCsd → χ.IsAbsPow u → (CG.mk (π.twist χ)).IsRegAlg →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Formalism.ConjugateSelfDual.Qbar l ≃+* ℂ),
      ∃ ρ : Formalism.ConjugateSelfDual.G E (AlgebraicClosure E) →* GL (Fin m) (Formalism.ConjugateSelfDual.Qbar l), Continuous ρ ∧
        ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, GlobalTheory.LFun.HasSatGL w ((π.twist χ).locRep w) B →
          ∀ (A : ValuationSubring (AlgebraicClosure E)) (g : Formalism.ConjugateSelfDual.G E (AlgebraicClosure E)),
            Formalism.ConjugateSelfDual.IsPlaceOver (F := E) A w → Formalism.ConjugateSelfDual.IsFrob (F := E) A (Formalism.ConjugateSelfDual.normV w) g →
              ((ρ g⁻¹ : GL (Fin m) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin m) (Fin m) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.map
                (ι : Formalism.ConjugateSelfDual.Qbar l →+* ℂ) = frobPoly (Formalism.ConjugateSelfDual.normV w) m (B.map fun b : ℂˣ => (b : ℂ))

theorem spehInf_one (A : Multiset ℂ) : spehInf 1 A = A := by simp [spehInf]

end GlobalTheory.SphGal

end
