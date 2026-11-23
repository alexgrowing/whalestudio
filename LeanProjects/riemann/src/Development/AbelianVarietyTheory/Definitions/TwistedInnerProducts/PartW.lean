import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.TrCopy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

abbrev partE {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap M) :=
  partDual θ M J χ Sb c ⊓ goodPart θ M J χ e

abbrev partW {V' : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel V' S') (J' : Set (GA D V')) (χ' : GA D V' → ℂ)
    (e' : (GA D V' → ℂ) →ₗ[ℂ] (GA D V' → ℂ)) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap M') :=
  partFull θ M' J' χ' Sb c ⊓ goodPart θ M' J' χ' e'

def TRc {V V' : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (M' : DSModel V' S') (J' : Set (GA D V')) (χ' : GA D V' → ℂ)
    (e' : (GA D V' → ℂ) →ₗ[ℂ] (GA D V' → ℂ)) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
    Module.rank ℂ (partE θ M J χ e Sb c) = Module.rank ℂ (partW θ M' J' χ' e' Sb c)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def TRAt (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (i : Fin D.R.m) (P P' : LevelP R.Pg D.R.r ℂ) : Prop :=
  TRc R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0
    (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P')) (levChi _ (R.βW i) (R.datWp i P')) (R.eWf i (sg0 D A)) SF

def TRLev (F : Face D A) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ i, TRAt R SF i R.triv R.triv ∧ ∀ b, TRAt R SF i (R.levR F b) (R.levL F b (sg0 D A))

end GlobalTheory.TrCopy

end
