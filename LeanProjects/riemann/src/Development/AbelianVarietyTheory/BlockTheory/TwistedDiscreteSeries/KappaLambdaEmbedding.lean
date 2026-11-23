import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalRingCardinality.DataParams

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.KappaLambdaEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

variable (D) in

abbrev Eig : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

open Classical in

def badF : Finset (HeightOneSpectrum (𝓞 D.host.F)) := R.Pg.image fun PP => PP.under (𝓞 D.host.F)

def rowsAt (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ R.HE.H := (R.EEat P).comap R.HE.e

def rowPart (c : Eig D) : Submodule ℂ R.HE.H :=
  (partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) (badF R) c ⊓
    R.EEat R.triv).comap R.HE.e

def rowLabels : Set (Eig D) :=
  {c | (fun P d => c P (dualLab d)) ∈
    IxFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) (badF R) R.e0}

def liftPart (i : Fin D.R.m) (c : Eig D) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) (badF R) c ⊓
    R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e

def lamFull (i : Fin D.R.m) (t : T) (c : Eig D) : ℝ :=
  (LinearMap.trace ℂ (R.HW i (sg0 D A)).H
    (R.thG i t ∘ₗ LinearMap.adjoint (R.thG i t) ∘ₗ
      ((liftPart R F i c).starProjection : (R.HW i (sg0 D A)).H →ₗ[ℂ] (R.HW i (sg0 D A)).H))).re /
    (Module.finrank ℂ (liftPart R F i c) : ℝ)

def ScalarIdentity (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ t, ∀ c ∈ rowLabels R, (∀ i, 0 < lamFull R F i t c) ∧
    ∀ x ∈ rowPart R c, R.Th t (LinearMap.adjoint (R.Th t) x) = ((κ * ∏ i, lamFull R F i t c : ℝ) : ℂ) • x

def datXP (t : T) (P : LevelP R.Pg D.R.r ℂ) : LevDat D.host.E ℂ D.sp.X'.rank :=
  datY _ D.R.r D.R.t D.R.m r_le_X R.Pg (R.Q t) P R.chi (R.xiR t) Frm.B

def scal (t : T) : (R.HX t).H →ₗ[ℂ] (SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) := R.cX.toMap R.prX ∘ₗ (R.HX t).e

def formsAt (t : T) (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (R.HX t).H where
  carrier := {x | ∀ v, HasType D.sp.X' R.βX (datXP R t P) (scal R t x v)}
  add_mem' := by
    intro x y hx hy v κ hκ h
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, hx v κ hκ h, hy v κ hκ h, mul_add]
  zero_mem' := by
    intro v κ _ h
    simp
  smul_mem' := by
    intro a x hx v κ hκ h
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, hx v κ hκ h, smul_eq_mul]
    ring

def eX (t : T) : (GA D D.sp.X' → ℂ) →ₗ[ℂ] (GA D D.sp.X' → ℂ) :=
  gaL D.sp.X' R.βX (R.datXt t) R.eG (RealDat.eC (A := A) D.what₂.embLL)

def goodAt (t : T) (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (R.HX t).H :=
  formsAt R t P ⊓ ⨅ v : SmT R.MX,
    LinearMap.ker ((eX R t - LinearMap.id) ∘ₗ LinearMap.applyₗ v ∘ₗ scal R t)

def kerAt (t : T) (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (R.HX t).H := goodAt R t P ⊓ LinearMap.ker (R.Th t)

def quotAt (t : T) (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (R.HX t).H := goodAt R t P ⊓ (kerAt R t P)ᗮ

def iotaAt (t : T) (P : LevelP R.Pg D.R.r ℂ) : quotAt R t P →ₗ[ℂ] rowsAt R P :=
  ((rowsAt R P).orthogonalProjection : R.HE.H →ₗ[ℂ] rowsAt R P) ∘ₗ R.Th t ∘ₗ (quotAt R t P).subtype

def lamProdAt (P : LevelP R.Pg D.R.r ℂ) : ℝ :=
  ∏ᶠ c ∈ rowLabels R, (∏ i, lamFull R F i A.μ0 c) ^ Module.finrank ℂ ↥(rowPart R c ⊓ rowsAt R P)

def IsDetConst (P : LevelP R.Pg D.R.r ℂ) (κ : ℝ) : Prop :=
  0 < κ ∧ 0 < lamProdAt R F P ∧
    LinearMap.det (iotaAt R A.μ0 P ∘ₗ LinearMap.adjoint (iotaAt R A.μ0 P)) =
      ((κ ^ Module.finrank ℂ (rowsAt R P) * lamProdAt R F P : ℝ) : ℂ)

def RowTie (b : Bool) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)
    {n : ℕ} (bs : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (cOf : D.what₂.FT → Eig D) : Prop :=
  ∃ (uA : S.Amb D.what₂.mu0 →ₗ[ℂ] (R.HX A.μ0).H) (uE : EE →ₗ[ℂ] R.HE.H),
    (∀ x, ‖uA x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2) ∧ LinearMap.range uA = formsAt R A.μ0 (R.levR F b) ∧
    (S.V0 D.what₂.mu0).map uA = goodAt R A.μ0 (R.levR F b) ∧
    (∀ y, ‖uE y‖ ^ 2 = RealDat.nP F b * ‖y‖ ^ 2) ∧ LinearMap.range uE = rowsAt R (R.levR F b) ∧
    (∀ x ∈ S.V0 D.what₂.mu0, uE (S.iota D.what₂.mu0 x) = R.Th A.μ0 (uA x)) ∧
    ∀ σ, cOf (ty σ) ∈ rowLabels R ∧ uE (bs σ) ∈ rowPart R (cOf (ty σ)) ∧
      ∀ i : Fin D.R.m, D.what₂.lamP D.what₂.mu0 ((i : ℕ) + 1) (ty σ) = lamFull R F i A.μ0 (cOf (ty σ))

def OneKappa (X : DivX D) : Prop :=
  ∀ e : D.what₂.LL →+* ℂ, InfinitePlace.mk e ≠ InfinitePlace.mk D.what₂.embLL → X.kapR e = X.kapR D.what₂.embLL

def DetConstAllLevels : Prop :=
  IsDetConst R F R.triv R.kap ∧ IsDetConst R F (R.levR F false) R.kap ∧ IsDetConst R F (R.levR F true) R.kap

def RecordConst : Prop :=
  ∀ cOf : D.what₂.FT → Eig D,
    (∀ X₀ : BaseLevelRowSide D, RowTie R F false X₀.s D.what₂.onb0 D.what₂.ft0 cOf → 0 < D.what₂.D0 → X₀.kap0 = R.kap) ∧
    (RowTie R F true (RowSide.sharp D) D.what₂.onb D.what₂.ft cOf → 0 < D.what₂.Drows →
      kapSharp D = R.kap ∧ ∀ X : DivX D, DV.KapRBase X →
        (∀ e : D.what₂.LL →+* ℂ, InfinitePlace.mk e = A.v0 → X.kapR e = (R.toCx F).κ (InfinitePlace.mk e)) ∧
        (OneKappa X → ∀ e : D.what₂.LL →+* ℂ, X.kapR e = (R.toCx F).κ (InfinitePlace.mk e)))

def KappaIdentityAt : Prop :=
  R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsChain → R.IsThP → R.IsScal F →
    ScalarIdentity R F R.kap → DetConstAllLevels R F ∧ RecordConst R F

def KappaIdentity : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), KappaIdentityAt R F

example (t : T) : datXP R t R.triv = R.datXt t := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.KappaLambdaEmbedding

end
