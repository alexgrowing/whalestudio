import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StepVecThetaLem
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.BaseSt
import Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Stages

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable (R : RealDat D A Ks) (F : Face D A)

structure Pre0 : Prop where
  lev : R.toLevCh.Is A.μ0
  red_R : R.grp_red_R
  red_L : R.grp_red_L
  levels : R.grp_levels F
  record : R.grp_record
  fam : R.IsFam
  inf : R.models_inf
  vpos : models_vpos (D := D)
  cX : R.models_cX
  cV : R.models_cV
  prX : R.models_prX
  order : R.models_order
  std : IsStdChar D R.ψ (-1)

def Pre1 : Prop := R.Pre0 F ∧ R.IsModels

end RealDat

end Stages

section Generic

open Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Am : DefAmb Bs} {fc : DefSub Am → DefFace Bs}

def reScal (X : CxData Am) (κ : InfinitePlace K → ℝ) (lam : type_of% X.lam) : CxData Am := { X with κ := κ, lam := lam }

theorem zs_reScal (X : CxData Am) (κ lam) : (reScal X κ lam).zs = X.zs := rfl

def NonzeroIndexPlaceOfSide (cr : Crd Am fc) (X : CxData Am) (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ w', (w' = w ∨ w' = conjPl w) ∧ ∃ i : Bs.J,
    idx w' (X.M false i) (matLat (X.liftMat cr false i Bs.μ0) ((lv (fc X.zs) false).Tl i Bs.μ0)) ≠ 0 ∨
    idx (conjPl w') (X.M false i) (matLat (X.liftMat cr false i Bs.μ0) ((lv (fc X.zs) false).Tl i Bs.μ0)) ≠ 0 ∨
    jw ((lv (fc X.zs) false).HT i Bs.μ0) w' ((lv (fc X.zs) false).Tl i Bs.μ0) ≠ 0 ∨
    (fc X.zs).Z.F0 w' i ≠ 0 ∨ (fc X.zs).Z.F0 (conjPl w') i ≠ 0

def PartX (cr : Crd Am fc) (X : CxData Am) (b : Bool) (i : Bs.J) (p : Bs.Ix) (v : InfinitePlace K) : Prop :=
  ∃ x, X.tC cr b i Bs.μ0 (cpt Bs.v0.embedding x) ∈ X.Wp i p ∧
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc X.zs) b).XT i Bs.μ0) v x x ≠ 0

def SimX (cr : Crd Am fc) (X : CxData Am) (b : Bool) (i : Bs.J) (p : Bs.Ix) (v : InfinitePlace K) (l : ℝ) : Prop :=
  ∀ x, X.tC cr b i Bs.μ0 (cpt Bs.v0.embedding x) ∈ X.Wp i p → ∀ y,
    inner ℂ (X.wC b i v (cpt v.embedding ((X.liftMat cr b i Bs.μ0).mulVec x)))
        (X.wC b i v (cpt v.embedding ((X.liftMat cr b i Bs.μ0).mulVec y))) =
      ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc X.zs) b).XT i Bs.μ0) v x y

theorem partX_reScal (cr : Crd Am fc) (X : CxData Am) (κ lam b i p v) : PartX cr (reScal X κ lam) b i p v ↔ PartX cr X b i p v := Iff.rfl

theorem simX_reScal (cr : Crd Am fc) (X : CxData Am) (κ lam b i p v l) :
    SimX cr (reScal X κ lam) b i p v l ↔ SimX cr X b i p v l := Iff.rfl

end Generic

section Stages2

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (D) in

def CartanOK : Prop :=
  (∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), V.SigOK → ∀ τ, IsCartanInv (gramAt D V τ) (cart M τ)) ∧
    ∀ V : HSp D, V.SigOK → V.IsPosDef → ∀ τ, IsCartanInv (gramAt D V τ) 1

variable (D) in

def SelfDualOK : Prop :=
  ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ),
    IsBaseFrame V β Λ N → IsSelfDualC V Λ

namespace RealDat

variable (R : RealDat D A Ks) (F : Face D A)

def SplitAt : Prop :=
  ∀ t, (∀ k, k + 1 < D.R.m → IsHeckeChar D (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 ∧
      IsHeckeChar D (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 ∧
      ResEta D (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (Yc D k).rank ∧
      ResEta D (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (Yc D (k + 1)).rank) ∧
    (IsHeckeChar D (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1 ∧ IsHeckeChar D (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 ∧
      ResEta D (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1 (Yc D (D.R.m - 1)).rank ∧
      ResEta D (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 D.sp.X'.rank) ∧
    ∀ i : Fin D.R.m, IsHeckeChar D (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 ∧
      IsHeckeChar D (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 ∧
      ResEta D (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 (Vc D i).rank ∧
      ResEta D (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 (Wc D i).rank

open Classical in

def IdemAt : Prop := ∀ t, Disjoint R.Pg (R.Q t) ∧ ∃ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t)

def FullY : Prop :=
  (∀ t k, k + 1 < D.R.m → IsWeilFull R.ψ (Yc D k) (Yc D (k + 1)) (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.ωY t k)) ∧
    ∀ t, IsWeilFull R.ψ (Yc D (D.R.m - 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 (R.ωX t)

def FullP : Prop :=
  ∀ i t, IsWeilFull R.ψ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
    (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 (R.ωP i t)

def KerY : Prop := R.FullY ∧ R.chain_vY ∧ R.chain_vX ∧ R.chain_ptY ∧ R.chain_ptX

def KerP : Prop := R.FullP ∧ R.thP_vP ∧ R.thP_pt_theta

end RealDat

variable (D A Ks)

def SeedFacts (F : Face D A) : Prop := ∀ R : RealDat D A Ks, R.Pre0 F → R.SplitAt ∧ R.IdemAt

def VecTheta : Prop :=
  (∀ ψ θ S T sS sT ΛS ΛT βS βT LS χ Q ξ f₀ f, IsStepVecOf (D := D) ψ θ S T sS sT ΛS ΛT βS βT LS χ Q ξ f₀ f → IsThetaFunO ψ S T f) ∧
    ∀ ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f, IsThPVecOf (D := D) ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f → IsThetaFunO ψ S T f

def ItExists (F : Face D A) : Prop :=
  ∀ R : RealDat D A Ks, R.Pre1 F → R.KerY →
    (∀ k, k + 1 < D.R.m → ∃ It, ∀ t, IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY t k) (R.ptY t k) It) ∧
      ∃ It, ∀ t, IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t) (R.ptX t) It

def IoChainExists (F : Face D A) : Prop :=
  ∀ R : RealDat D A Ks, R.Pre1 F → R.KerY → R.chain_ItY → R.chain_ItX → ∀ t,
    (∀ k, k + 1 < D.R.m → Lift.IoExists (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k) (R.ItY k)
      (R.CC t (k + 1)) (R.CC t k)) ∧
    Lift.IoExists (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t) R.ItX
      (LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (R.CC t (D.R.m - 1))

def GoodLands (F : Face D A) : Prop :=
  ∀ R : RealDat D A Ks, R.Pre1 F →
    (∀ t, ∀ u ∈ R.CC t 0, postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm u) ∈ R.EEat R.triv) ∧
      ∀ i, ∀ u ∈ R.Wall i (sg0 D A), postOn _ (R.eWf i (sg0 D A)) u ∈ R.Wall i (sg0 D A)

def IoWExists (F : Face D A) : Prop :=
  ∀ R : RealDat D A Ks, R.Pre1 F → R.KerP → ∀ i, ∃ io, ∀ t,
    IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t) (R.ptP i t) (RealDat.Delta i) io

def ThetaPExists (F : Face D A) : Prop :=
  ∀ R : RealDat D A Ks, R.Pre1 F → R.KerP → R.thP_ioP → ∀ i t, ∃ th : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A)),
    (∀ x, th x ∈ R.Wall i (sg0 D A)) ∧
      ∃ thP, Lift.IsThetaP (R.νV i t) (R.fdV i t) (fun g h f => thetaKO (R.ωP i t) h g f) (R.ptP i t) (R.ioP i)
          (LinearMap.range (R.extV i t)) thP ∧
        ∀ x (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
          th x (fun ρ => v ρ) = thP ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v)

variable {D A Ks}

theorem exists_factor {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (e : Y →ₗ[ℂ] Z) (he : Function.Injective e) (f : X →ₗ[ℂ] Z) (hf : ∀ x, f x ∈ LinearMap.range e) :
    ∃ g : X →ₗ[ℂ] Y, ∀ x, e (g x) = f x := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ f.codRestrict (LinearMap.range e) hf, fun x => ?_⟩
  show e ((LinearEquiv.ofInjective e he).symm (f.codRestrict (LinearMap.range e) hf x)) = f x
  rw [← LinearEquiv.ofInjective_apply (h := he), LinearEquiv.apply_symm_apply]
  rfl

namespace RealDat

variable (R : RealDat D A Ks) {F : Face D A}

def upd3 (ωY : type_of% R.ωY) (ωX : type_of% R.ωX) (vac : type_of% R.vac) (vacX : type_of% R.vacX) (vY : type_of% R.vY) (vX : type_of% R.vX) (ItY : type_of% R.ItY) (ItX : type_of% R.ItX) (ioY : type_of% R.ioY) (ioX : type_of% R.ioX) (Th : type_of% R.Th)
    : RealDat D A Ks :=
  { R with ωY := ωY, ωX := ωX, vac := vac, vacX := vacX, vY := vY, vX := vX, ItY := ItY, ItX := ItX, ioY := ioY, ioX := ioX, Th := Th }

def upd4 (ωP : type_of% R.ωP) (vacP : type_of% R.vacP) (vP : type_of% R.vP) (ioP : type_of% R.ioP) (thF : type_of% R.thF) (thG : type_of% R.thG)
    : RealDat D A Ks :=
  { R with ωP := ωP, vacP := vacP, vP := vP, ioP := ioP, thF := thF, thG := thG }

def upd5 (nW : Fin D.R.m → ℕ)
    (FW : ∀ i, Arith.FormsL D.what₂.LL Ks (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G) (mu : type_of% R.mu) (twPl : type_of% R.twPl) (err0 : type_of% R.err0)
    : RealDat D A Ks := { R with nW := nW, FW := FW, mu := mu, twPl := twPl, err0 := err0 }

def upd6 (kap : type_of% R.kap) (lam : type_of% R.lam) : RealDat D A Ks := { R with kap := kap, lam := lam }

end RealDat

end Stages2

section StagesU

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.PeterssonHilbertSpace Formalism.IndefR.Eqv

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RealDat.upd1 (R : RealDat D A Ks) (HX : type_of% R.HX) (HV : type_of% R.HV) (HE : type_of% R.HE) (HW : type_of% R.HW)
    (gE : Representation ℂ G HE.H) (gW : ∀ i σ, Representation ℂ G (HW i σ).H)
    (jX : ∀ t, A.fam.amb.FR t →ₛₗ[D.what₂.embLL] (HX t).H) (jV : ∀ i t, A.fam.amb.FL i t →ₛₗ[D.what₂.embLL] (HV i t).H)
    (νY : type_of% R.νY) (fdY : type_of% R.fdY) (ν0 : type_of% R.ν0) (fd0 : type_of% R.fd0) (νX : type_of% R.νX) (fdX : type_of% R.fdX)
    (νV : type_of% R.νV) (fdV : type_of% R.fdV) (νW : type_of% R.νW) (fdW : type_of% R.fdW) (BV : type_of% R.BV) : RealDat D A Ks :=
  { R with
    HX := HX, HV := HV, HE := HE, HW := HW, gE := gE, gW := gW, jX := jX, jV := jV,
    νY := νY, fdY := fdY, ν0 := ν0, fd0 := fd0, νX := νX, fdX := fdX, νV := νV, fdV := fdV, νW := νW, fdW := fdW,
    BV := BV, ioX := fun _ => 0, Th := fun _ => 0, thF := fun _ _ => 0, thG := fun _ _ => 0, nW := fun _ => 0,
    FW := fun _ =>
      { WK := ⊥, Pt := fun _ => Empty, nrm := fun _ _ _ => 0, nrm_nonneg := fun _ _ _ => le_rfl,
        nrm_zero := fun _ _ => rfl, nrm_add := fun _ _ _ _ => by simp, nrm_smul := fun _ _ _ _ => by simp,
        towKs := inferInstance, ρ := 1, chi := 1, j := fun _ => 0 } }

end StagesU

section Hyps

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.PeterssonHilbertSpace Formalism.IndefR.Eqv

variable (D)

def SpOK : Prop := (Yc D (D.R.m - 1)).IsDefinite ∧ D.sp.X'.IsDefinite

def LevOK : Prop :=
  ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank),
    IsLevelA V (lev D.sp.cm V.gram β L) ∧
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ levG V β L ∧ levChi V β L k = 1

def HCAll : Prop :=
  ∀ (V : HSp D), V.SigOK → ∀ (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ),
    HCFinite θ M J χ

def SchurAll : Prop :=
  ∀ (V : HSp D), V.SigOK → ∀ (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurMult θ M J χ μ 𝓕

def PetAll : Prop :=
  ∀ (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ →
    PetPos V μ 𝓕

def SmAll : Prop := ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), SmNonzero M

def DimOK : Prop := ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), 0 < dimK _ _ (kapAt (Wc D i) σ ρ)

def ActRep : Prop :=
  ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (S : D.what₂.Tau → SPar) (θ : InfFam D)
    (M : DSModel V S), LiftsExist V β L → L.P = LevelP.triv L.Pg L.r ℂ →
    (∀ g, ∀ T ∈ Mult θ M (levS V β L) (levChi V β L), postOn M (actL V β L g) T ∈ Mult θ M (levS V β L) (levChi V β L)) ∧
    (∀ T ∈ Mult θ M (levS V β L) (levChi V β L), postOn M (actL V β L 1) T = T) ∧
    (∀ g h, ∀ T ∈ Mult θ M (levS V β L) (levChi V β L),
      postOn M (actL V β L (g * h)) T = postOn M (actL V β L g) (postOn M (actL V β L h) T)) ∧
    ∀ (G : Type) [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ), (∀ a b, c (a * b * a⁻¹) = c b) →
      ∀ g, ∀ T ∈ Mult θ M (levS V β L) (levChi V β L),
        postOn M (gaL V β L eG c) (postOn M (actL V β L g) T) = postOn M (actL V β L g) (postOn M (gaL V β L eG c) T)

end Hyps
section Inp

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull Formalism.IndefR.Fin Formalism.IndefR.Eqv

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (D A Ks) in

def LiftsAt (F : Face D A) : Prop :=
  ∀ R : RealDat D A Ks, R.Pre0 F →
    LiftsExist (Yc D 0) (R.βY 0) (R.dat0 R.triv) ∧ ∀ i, LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv)

variable (D) in

structure Inputs : Prop where
  weil : WeilExistsFull D
  vac : VacExistsO D
  stepVec : StepVecExists D
  thPVec : ThPVecExists D
  ptStable : PtStable D
  cartan : CartanOK D
  selfDual : SelfDualOK D
  vecTheta : Formalism.IndefR.Fin.VecThetaSD D
  measFD : MeasFDExists D
  measDef : MeasLevDefExists D
  fund : FundDomExists D
  sp : SpOK D
  lev : LevOK D
  hc : HCAll D
  schur : SchurAll D
  pet : PetAll D
  sm : SmAll D
  dim : DimOK D
  act : ActRep D

end Inp

end Formalism.IndefR.Links

end
