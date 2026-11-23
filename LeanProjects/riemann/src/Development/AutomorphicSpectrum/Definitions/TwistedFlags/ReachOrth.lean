import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.UpNonzero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars (EigSys badPl IsIP IsUp IsUpTop topStep IsLValue)
open GlobalTheory.LFun (Fam twist segFam seg val above IsCont Bounded IsSysParamD IsParamFunV UnrAt)
open GlobalTheory.CompanionTheory.OntoAll

namespace GlobalTheory.CompanionTheory.Ipf.Aut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsTp {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (Tp : PolF D W.rank V.rank →ₗ⋆[ℂ] SmT M →ₗ[ℂ] SmT M') : Prop :=
  ∀ (p : PolF D W.rank V.rank) (w : M'.Vec) (v : M.Vec),
    ellT M (fun τ => v τ) (inclT M (It p (PiTensorProduct.tprod ℂ w))) =
      starRingEnd ℂ (ellT M' (fun τ => w τ) (inclT M' (Tp p (PiTensorProduct.tprod ℂ v))))

def UpPair (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (V W : HSp D) (M : DSModel V (parB (Ptw D) k)) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → GlobalTheory.Chain.ChainPar D k →
    ∀ ω f, GlobalTheory.Chain.IsStepWeil k ψ V W ω → GlobalTheory.Chain.IsVacVec ψ θ M M' f →
    ∀ It, IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It → ∀ Tp, IsTp M M' It Tp →
    ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν →
    ∀ u ∈ MultT θ M ∅ 1, ∃ x ∈ MultT θ M' ∅ 1, ∀ (p : PolF D W.rank V.rank) (v : SmT M) (h : GA D W),
      IntegrableOn (fun g => star (thetaKO ω g h (GlobalTheory.Chain.ptOf ψ θ M M' f p)) * u v g) 𝓕 ν ∧
      ∫ g in 𝓕, star (thetaKO ω g h (GlobalTheory.Chain.ptOf ψ θ M M' f p)) * u v g ∂ν = x (Tp p v) h

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def topMap (x : (R.HX A.μ0).H) : MMap R.MX := PiTensorProduct.lift.symm (R.cX.toMap R.prX ((R.HX A.μ0).e x))

def UpIsY : Prop :=
  ∀ k, k + 1 < D.R.m → ∃ Tp, IsTp (R.MY k) (R.MY (k + 1)) (R.ItY k) Tp ∧
    ∀ u : MMap (R.MY k), PiTensorProduct.lift u ∈ R.CC A.μ0 k → (∃ x, IsUp R A.μ0 k u x) ∧
      ∀ x, IsUp R A.μ0 k u x → ∀ p v h,
        upFun R k u p v h = PiTensorProduct.lift x (Tp p (PiTensorProduct.tprod ℂ v)) h

def UpIsX : Prop :=
  ∃ (κ : ℝ) (Tp : _), 0 < κ ∧ IsTp (R.MY (D.R.m - 1)) R.MX R.ItX Tp ∧
    (∀ x y : (R.HX A.μ0).H, IsMultIP R.MX (R.νX A.μ0) (R.fdX A.μ0) (topMap R x) (topMap R y) ((κ : ℂ) * ⟪x, y⟫_ℂ)) ∧
    ∀ u : MMap (R.MY (D.R.m - 1)), PiTensorProduct.lift u ∈ R.CC A.μ0 (D.R.m - 1) → (∃ x, IsUpTop R A.μ0 u x) ∧
      ∀ x, IsUpTop R A.μ0 u x → ∀ p v h,
        (κ : ℂ) * upFunX R u p v h = PiTensorProduct.lift (topMap R x) (Tp p (PiTensorProduct.tprod ℂ v)) h

def partX (c : EigSys D) : Submodule ℂ (MMap R.MX) :=
  partDual R.θ R.MX (levS _ R.βX (R.datXt A.μ0)) (levChi _ R.βX (R.datXt A.μ0)) (badPl R A.μ0) c

def TopPar : Prop :=
  ∀ (B : Fam D.host.E) (c : EigSys D), IsSysParamD D (badPl R A.μ0) (Yc D (D.R.m - 1)).rank c (parK R B (D.R.m - 1)) →
    ∀ u ∈ partAt R (D.R.m - 1) c, ∀ x, IsUpTop R A.μ0 u x → x ≠ 0 →
      ∃ c', topMap R x ∈ partX R c' ∧ IsSysParamD D (badPl R A.μ0) D.sp.X'.rank c' (parK R B D.R.m)

def UnitSym (B : Fam D.host.E) : Prop :=
  ∀ w ∉ badE R, ∀ w', Formalism.IndefR.Lev.IsConjPl w w' → B w' = (B w).map star

def ParSym : Prop :=
  ∀ c : EigSys D, partAll R c ≠ ⊥ → ∀ B, IsSysParamD D (badPl R A.μ0) D.R.r c B → TrivBd R B ∧ UnitSym R B

def ReachPar : Prop :=
  ∀ (c : EigSys D) (B : Fam D.host.E), IsSysParamD D (badPl R A.μ0) D.R.r c B → ∀ k, k < D.R.m →
    ∀ u ∈ reachedAll R c k, u ≠ 0 →
      (∃ c', u ∈ partAt R k c' ∧ IsSysParamD D (badPl R A.μ0) (Yc D k).rank c' (parK R B k)) ∧
      ∀ v, u v ≠ 0 → IsParamFunV (Yc D k) (badPl R A.μ0) (fun g => star (u v g)) (parK R B k)

def ReachOrth : Prop :=
  ∀ (c₁ c₂ : EigSys D) (B₁ B₂ : Fam D.host.E), IsSysParamD D (badPl R A.μ0) D.R.r c₁ B₁ →
    IsSysParamD D (badPl R A.μ0) D.R.r c₂ B₂ → (∃ w ∉ badE R, B₁ w ≠ B₂ w) →
    (∀ k, k < D.R.m → ∀ u₁ ∈ reachedAll R c₁ k, ∀ u₂ ∈ reachedAll R c₂ k, IsIP R A.μ0 k u₁ u₂ 0) ∧
    ∀ u₁ ∈ reachedAll R c₁ (D.R.m - 1), ∀ u₂ ∈ reachedAll R c₂ (D.R.m - 1), ∀ x₁ x₂,
      IsUpTop R A.μ0 u₁ x₁ → IsUpTop R A.μ0 u₂ x₂ → ⟪x₁, x₂⟫_ℂ = 0

def LPos : Prop :=
  ∃ b : ℕ → ℝ, (∀ k, k < D.R.m → 0 < b k) ∧ ∀ B, TrivBd R B → UnitSym R B → ∀ k, k < D.R.m →
    ∃ (l σ : ℝ) (Λ : ℂ → ℂ), IsLValue R A.μ0 B (k + 1) l ∧ σ < (1 + (D.R.t : ℝ)) / 2 ∧
      IsCont (badE R) (stepPar R B k) σ Λ ∧ Λ ((1 + (D.R.t : ℂ)) / 2) = ((l * b k : ℝ) : ℂ)

def NSAll : Prop :=
  ∀ B, TrivBd R B → ∀ k, k < D.R.m → ∀ p : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p →
    ∀ w ∉ badE R, (p : 𝓞 D.host.E) ∈ w.asIdeal → ∀ β ∈ stepPar R B k w,
      (β : ℂ) ∉ GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.excluded (Ideal.absNorm w.asIdeal) D.R.t

end GlobalTheory.CompanionTheory.Ipf.Aut

end
