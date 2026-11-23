import Formalism.LocalToGlobal.IndefiniteReal.OneMapT

noncomputable section

open NumberField
open scoped TensorProduct

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))

def phiAt (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ)
    (f : T.R ((i : ℕ) + 1)) : GA D (Wc D i) → ℂ :=
  castDict hV (adel (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ)
    (muPin (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ) (T.mu ((i : ℕ) + 1) σ) c) (rdU (T.U ((i : ℕ) + 1) σ) f))

def EqAt {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (σ : T.Q.c.F →+* ℂ)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ) : Prop :=
  ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k →
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      actLev T.Q.c O.lev2 g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n ∧
      ∃ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) =
          ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ) ∧
        ∀ h, phiAt T i σ hV c (actLev T.Q.c O.lev2 g f) h = σ y * phiAt T i σ hV c f (h * k)

def EquivAll (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) : Prop :=
  ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    (∃ c', CUnit c' ∧ EqAt T R κ (O i) σ hV c') → EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)

variable (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

def CTie (i : Fin D.R.m) : Prop :=
  OneMapRow0 T R κ v₀ O i → ∃ ph', (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph'

end Formalism.IndefR.FWT
