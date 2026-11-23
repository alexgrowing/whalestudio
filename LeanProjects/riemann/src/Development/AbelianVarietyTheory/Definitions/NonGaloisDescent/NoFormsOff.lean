import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

def EigTrue (D : D7) (cf : CharFrame D) (Rw : RowSide D) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : Prop :=
  ∀ (j : Fin D.R.m) σ, D.what₂.isot (j.1 + 1) σ ≠ ⊥ → D.nd.goodRow σ → ∀ P, IsSplitPl D.host P → P ∉ Sb →
    D.naut.unr (Rw.locR σ P) ∧ ∀ k, 1 ≤ k → k ≤ D.R.r → D.what₂.embLL (eig (j.1 + 1) σ k P : D.what₂.LL) =
      ((normV P : ℕ) : ℂ) ^ (k * (D.R.r - k) / 2) * ((D.naut.frobEig (Rw.locR σ P)).map fun a =>
        a⁻¹ * (((cf.mu0 j).val P : ℂˣ) : ℂ)⁻¹ * (((normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹).esymm k

def EigOcc (D : D7) (S : RatDat D.ntw) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → ∃ x ∈ goodL D S θ j, x ≠ 0 ∧
    ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ Sb → hL j k P x = ((eig j σ k P : ↥D.LL0) : D.what₂.LL) • x

def RowParam (D : D7) (Rw : RowSide D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → ∃ π, GlobalTheory.EigTie.IsRowPar Rw σ π

def NoFormsOff (D : D7) : Prop := ∀ i j, j ∉ Finset.Icc 1 D.R.m → ∀ b, Subsingleton (D.nexp.Fm i j b)

def MeetsAll (D : D7) : Prop := ∀ i j b (W : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)), W ≠ ⊥ →
  GStable D.nexp i j b W → (∀ x ∈ W, eG D.nexp i j b x = x) → W ⊓ Fm0 D.nexp i j b ≠ ⊥

def CommAll (D : D7) : Prop := ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ g x,
  D.nexp.hkF i j b k P (D.nexp.actG i j b g x) = D.nexp.actG i j b g (D.nexp.hkF i j b k P x)

def FullAll (D : D7) : Prop := ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
  Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i j b : Set (D.nexp.Fm i j b)) = ⊤

end GlobalTheory.TwInputs

end
