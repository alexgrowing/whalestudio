import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.DataParams
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsFinIntertwiner (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W)
    (φ : W →ₗ[ℂ] (GA D V → ℂ)) : Prop :=
  ∀ (k : GfC V) (w : W), φ (σ k w) = fun g => φ w (g * (k : GA D V))

def isoFun (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) :
    Submodule ℂ (GA D V → ℂ) :=
  ⨆ (φ : W →ₗ[ℂ] (GA D V → ℂ)) (_ : IsFinIntertwiner V σ φ), LinearMap.range φ

def IsoRep {H : Type} [Group H] {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ H W) (σ' : Representation ℂ H W') : Prop :=
  ∃ e : W ≃ₗ[ℂ] W', ∀ k w, e (σ k w) = σ' k (e w)

section Chain

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

abbrev Sys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

open Classical in

def typePl : Finset (HeightOneSpectrum (𝓞 D.host.F)) := R.Pg.image fun PP => PP.under (𝓞 D.host.F)

def rowLev : Option Bool → LevelP R.Pg D.R.r ℂ
  | none => R.triv
  | some b => R.levR F b

def heckePart (P : LevelP R.Pg D.R.r ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Sys D) :
    Submodule ℂ (MMap (R.MY 0)) :=
  partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) Sb c ⊓ R.EEat P

def Differ (P : LevelP R.Pg D.R.r ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c c' : Sys D) : Prop :=
  ∃ w d Rp, Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) Sb w d Rp ∧
    c w (dualLab d) ≠ c' w (dualLab d)

def isoPart (P : LevelP R.Pg D.R.r ℂ) {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GfC (Yc D 0)) W) : Set (MMap (R.MY 0)) :=
  {u | u ∈ R.EEat P ∧ ∀ v, u v ∈ isoFun (Yc D 0) σ}

variable (t : T)

def eY (j : ℕ) : (GA D (Yc D j) → ℂ) →ₗ[ℂ] (GA D (Yc D j) → ℂ) :=
  gaL (Yc D j) (R.βY j) (R.datYt t j R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL)

def eX : (GA D D.sp.X' → ℂ) →ₗ[ℂ] (GA D D.sp.X' → ℂ) :=
  gaL D.sp.X' R.βX (R.datXt t) R.eG (RealDat.eC (A := A) D.what₂.embLL)

def toX : (R.HX t).H →ₗ[ℂ] (SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) := R.cX.toMap R.prX ∘ₗ (R.HX t).e

def lastStep : (R.HX t).H →ₗ[ℂ] R.CC t (D.R.m - 1) := R.ioX t ∘ₗ (R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict

def InProjectedFormSpace (P : LevelP R.Pg D.R.r ℂ) (f : (R.HX t).H) : Prop :=
  (∀ v, HasType D.sp.X' R.βX (withP (R.datXt t) P) (toX R t f v)) ∧ eX R t ∘ₗ toX R t f = toX R t f

def dn (f : (R.HX t).H) : MMap (R.MY 0) := PiTensorProduct.lift.symm (R.thDn t f)

def UpStep (k : ℕ) (u : MMap (R.MY k)) (x : MMap (R.MY (k + 1))) : Prop :=
  PiTensorProduct.lift x ∈ R.CC t (k + 1) ∧ ∀ y : R.CC t (k + 1), ∃ a : ℂ,
    IsMultIP (R.MY k) (R.νY t k) (R.fdY t k) u (PiTensorProduct.lift.symm (R.ioY t k y).1) a ∧
    IsMultIP (R.MY (k + 1)) (R.νY t (k + 1)) (R.fdY t (k + 1)) x (PiTensorProduct.lift.symm y.1) a

def UpIter (u : MMap (R.MY 0)) (j : ℕ) : MMap (R.MY j) → Prop :=
  Nat.rec (motive := fun j => MMap (R.MY j) → Prop) (fun x => x = u)
    (fun j ih x => ∃ y, ih y ∧ UpStep R t j y x) j

def UpTop (u : MMap (R.MY 0)) (x : (R.HX t).H) : Prop :=
  ∃ y, UpIter R t u (D.R.m - 1) y ∧ ∀ f : (R.HX t).H,
    IsMultIP (R.MY (D.R.m - 1)) (R.νY t (D.R.m - 1)) (R.fdY t (D.R.m - 1)) y
      (PiTensorProduct.lift.symm (lastStep R t f).1) (inner ℂ x f)

def LiftsOrth (u u' : MMap (R.MY 0)) : Prop :=
  (∀ j, 1 ≤ j → j < D.R.m → ∀ x x', UpIter R t u j x → UpIter R t u' j x' →
    IsMultIP (R.MY j) (R.νY t j) (R.fdY t j) x x' 0) ∧
  ∀ x x', UpTop R t u x → UpTop R t u' x' → inner ℂ x x' = (0 : ℂ)

variable (P : LevelP R.Pg D.R.r ℂ)

def UpExists : Prop :=
  ∀ u ∈ R.EEat P, (∀ j, j < D.R.m → ∃! x, UpIter R t u j x) ∧ ∃! x, UpTop R t u x

def UpIsAdjoint : Prop := ∀ u : R.HE.H, UpTop R t (R.HE.e u) (LinearMap.adjoint (R.Th t) u)

def StepsCommute : Prop :=
  (∀ k, k + 1 < D.R.m → ∀ y : R.CC t (k + 1), ∃ y' : R.CC t (k + 1), y'.1 = eY R t (k + 1) ∘ₗ y.1 ∧
    (R.ioY t k y').1 = eY R t k ∘ₗ (R.ioY t k y).1) ∧
  ∀ f : (R.HX t).H, ∃ f' : (R.HX t).H, toX R t f' = eX R t ∘ₗ toX R t f ∧
    (lastStep R t f').1 = eY R t (D.R.m - 1) ∘ₗ (lastStep R t f).1

def UpLiftInProjectedFormSpace : Prop := ∀ u ∈ R.EEat P, ∀ x, UpTop R t u x → InProjectedFormSpace R t P x

def DnIntoEE : Prop := ∀ f, InProjectedFormSpace R t P f → dn R t f ∈ R.EEat P

def DnUpMapsEE : Prop := ∀ u ∈ R.EEat P, ∀ x, UpTop R t u x → dn R t x ∈ R.EEat P

def HeckeOrth : Prop :=
  ∀ Sb, typePl R ⊆ Sb → ∀ c c', Differ R P Sb c c' →
    ∀ u ∈ heckePart R P Sb c, ∀ u' ∈ heckePart R P Sb c', LiftsOrth R t u u'

def HeckeKept : Prop :=
  ∀ Sb, typePl R ⊆ Sb → ∀ c, ∀ u ∈ heckePart R P Sb c, ∀ x, UpTop R t u x → dn R t x ∈ heckePart R P Sb c

def IsoOrth : Prop :=
  ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GfC (Yc D 0)) W) (σ' : Representation ℂ (GfC (Yc D 0)) W'),
    σ.IsIrreducible → σ'.IsIrreducible → ¬ IsoRep σ σ' →
    ∀ u ∈ isoPart R P σ, ∀ u' ∈ isoPart R P σ', LiftsOrth R t u u'

def IsoKept : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC (Yc D 0)) W), σ.IsIrreducible →
    ∀ u ∈ isoPart R P σ, ∀ x, UpTop R t u x → dn R t x ∈ isoPart R P σ

structure Common : Prop where
  upExists : UpExists R t P
  upIsAdjoint : UpIsAdjoint R t
  stepsCommute : StepsCommute R t
  upIntoProjectedForms : UpLiftInProjectedFormSpace R t P
  dnIntoEE : DnIntoEE R t P
  dnUpMapsEE : DnUpMapsEE R t P

def GoodTypes : Prop :=
  ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k ∧
      (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∀ (v : D.nd.PlG k) (j : Fin D.R.m) (PP : Pl D.host.E), R.C.P.Div k PP →
        ∀ (a : ℕ) (u : (kP PP)ˣ), (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = L.gen 1 → (u : kP PP) = (a : kP PP) →
          L.teich (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
              ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
            ((R.chi ((j : ℕ) + 1) PP u : ℂˣ) : ℂ) ∨
          L.teich (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
              ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
            (((R.chi ((j : ℕ) + 1) PP u)⁻¹ : ℂˣ) : ℂ)

structure HidaSetting : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP
  scal : R.IsScal F
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  good : GoodTypes R

def OneFinitePart : Prop :=
  HidaSetting R F → ∀ (t : T) (b : Option Bool),
    Common R t (rowLev R F b) ∧ HeckeOrth R t (rowLev R F b) ∧ HeckeKept R t (rowLev R F b)

def OneFinitePartIsotypic : Prop :=
  HidaSetting R F → ∀ (t : T) (b : Option Bool),
    Common R t (rowLev R F b) ∧ IsoOrth R t (rowLev R F b) ∧ IsoKept R t (rowLev R F b)

example (P : LevelP R.Pg D.R.r ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Sys D) : ¬ Differ R P Sb c c :=
  fun ⟨_, _, _, _, h⟩ => h rfl

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators

end
