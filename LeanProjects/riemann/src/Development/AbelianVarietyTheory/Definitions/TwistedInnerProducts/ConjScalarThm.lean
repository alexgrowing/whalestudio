import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

variable {D : D7}

def RelLab (V : HSp D) (P : Pl D.host.E) (d : List ℤ) : Prop :=
  (Formalism.DivisionValues.conjPl P ≠ P ∧ ∃ k, k ≤ V.rank ∧ d = splitLab V.rank k) ∨ (Formalism.DivisionValues.conjPl P = P ∧ GlobalTheory.Hk3.IsLab V P d)

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Eig

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def EigF {W : Type} [AddCommGroup W] [Module ℂ W] (a : Pl D.host.E → List ℤ → ℂ) (Φ : Bridge.Gf (Vc D i) → W) : Prop :=
  ∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → RelLab (Vc D i) P d → GlobalTheory.Hk3.hkF (Vc D i) P (Finsupp.single d 1) Φ = a P d • Φ

def EigK (a : Pl D.host.E → List ℤ → D.what₂.LL) (x : A.fam.amb.FL i A.μ0) : Prop :=
  EigF R i (fun P d => D.what₂.embLL (a P d)) ((R.HV i A.μ0).e (R.jV i A.μ0 x))

end Eig

def ConjScalarThm : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → IsStdChar D R.ψ (-1) → (∀ χ ∈ A.X, IsAbsIrrChar χ) →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
        (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ →
    ∀ μ' η' c c₁ H j th, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th →
    ∀ ev : Pl D.host.E → List ℤ → ℂ, ∃ l : ℝ, ∀ u : H.H, th u ∈ GlobalTheory.LiftLower.partH R i σ ev →
      th (LinearMap.adjoint th (th u)) = (l : ℂ) • th u

def ConjRatLift : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ),
    R.Char F → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R κ v₀, BarTie fw → IoExt R → R.LUnif → (∀ i, OMPins T R κ v₀ O i) →
    ∀ i : Fin D.R.m, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph →
    (∀ x, ∃! y, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x y) ∧
    (∀ gramR c0R c0L,
      Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
        (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
      ∀ σ, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjAt R i σ ph (c0L i)) ∧
    ∀ σ, ¬ GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK ((starRingEnd ℂ).comp σ) ∧
      ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ =
        starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ

end GlobalTheory.ConjScalar

end
