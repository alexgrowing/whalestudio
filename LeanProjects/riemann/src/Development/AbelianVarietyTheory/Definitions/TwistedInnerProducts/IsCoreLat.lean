import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open scoped TensorProduct nonZeroDivisors ComplexConjugate
open GlobalTheory.SepRows GlobalTheory.EvenOnto
open GlobalTheory.Chain (IsVacVec ptOf)
open GlobalTheory.PairLift (adjO)

namespace GlobalTheory.CoreOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure ReLat (V : HSp D) where

  L0 : Submodule (𝓞 D.host.E) V.V
  lat : Submodule.IsLattice D.host.E L0
  unimod : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L0

@[reducible] def ReLat.sp {V : HSp D} (r : ReLat V) : HSp D := { V with L0 := r.L0, standardTuple_isLattice := r.lat, baseLattice_isUnimodular := r.unimod }

@[reducible] def ReLat.mod {V : HSp D} (r : ReLat V) {S : D.what₂.Tau → SPar} (M : DSModel V S) : DSModel r.sp S where
  H := M.H
  σ := M.σ
  lam := M.lam
  ε := M.ε
  fr := M.fr
  enum := M.enum
  ds := M.ds
  fr_unit := M.fr_unit
  fr_gram := M.fr_gram

def scaleLat {n : ℕ} (𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  Submodule.span (𝓞 D.host.E) {y | ∃ a ∈ 𝔟, ∃ x ∈ Λ, y = a • x}

def exch (A B : HSp D) (f : WO A B → ℂ) : WO (negSp B) A → ℂ := fun x => f (adjO A B x)

def Exch {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D (negSp B) × GA D A →* Module.End ℂ (WO (negSp B) A → ℂ))
    (ω' : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ A B f → ∀ g h, ω (negGA B h, g) (exch A B f) = exch A B (ω' (g, h) f)

def ExchLaw (D : D7) : Prop := ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), IsStdChar D ψ (-1) →
  (∀ f, IsThetaFunO ψ A B f ↔ IsThetaFunO ψ (negSp B) A (exch A B f)) ∧
  (∀ x f, heisO ψ (negSp B) A x (exch A B f) = exch A B (heisO ψ A B (adjO A B x) f)) ∧
  (∀ x x' : WO (negSp B) A, symplO (negSp B) A x x' = symplO A B (adjO A B x) (adjO A B x')) ∧
  Function.Bijective (adjO A B) ∧
  (∀ m X, IsCovolOne (ratL B A) m X → ∃ m' X', IsCovolOne (ratL A (negSp B)) m' X' ∧
    ∀ f f' : WO A B → ℂ, ∫ w in X, f w * conj (f' w) ∂m = ∫ w in X', exch A B f w * conj (exch A B f' w) ∂m') ∧
  ∀ χS χT ω, IsWeilDatumO ψ (negSp B) A χS χT ω → ∃ ω', IsWeilDatumO ψ A B χT⁻¹ χS⁻¹ ω' ∧ Exch ψ ω ω'

def ReLatLaw (D : D7) : Prop :=
  (∀ (V : HSp D) Λ, IsSelfDualC V Λ → ∃ r : ReLat V, GlobalTheory.AdelicU.frameLat r.sp = Λ) ∧
  (∀ (V : HSp D) (r : ReLat V) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)),
    (MultT θ (r.mod M) J 1 : Submodule ℂ (SmT M →ₗ[ℂ] (GA D V → ℂ))) = MultT θ M J 1 ∧
    (KF (r.mod M) : Submodule ℂ (SmT M)) = KF M ∧ cart (r.mod M) = cart M ∧
    GlobalTheory.Cusp.wittIndex r.sp = GlobalTheory.Cusp.wittIndex V ∧ ∀ F : GA D V → ℂ, RapidDec r.sp F ↔ RapidDec V F) ∧
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (r : ReLat A) (r' : ReLat B),
    (∀ f : WO A B → ℂ, IsThetaFunO ψ r.sp r'.sp f ↔ IsThetaFunO ψ A B f) ∧
    ∀ χS χT (ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)),
      IsWeilDatumO ψ r.sp r'.sp χS χT ω ↔ IsWeilDatumO ψ A B χS χT ω

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

def gridCom : Com D where
  θ := W.θ
  ψ := W.ψ
  S := G.pl.S0
  n := nRk D
  t := sLen D - 1
  m := D.R.m
  χ := fun k => (G.ch.chi (D.R.m - k))⁻¹
  a := fun k τ => -(cen D sc.cGap τ (D.R.m - k) : ℚ)

variable (G) in

def IsCoreLat (i : ℕ) (r : ReLat (G.V (.core i))) : Prop :=
  GlobalTheory.AdelicU.frameLat r.sp = scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) (G.Λ (.core i))

variable (G) in

@[reducible] def gridStage (v : CoreVol G) (i : ℕ) (r : ReLat (G.V (.core i)))
    (M : DSModel (G.V (.core i)) (Node.par D sc.cGap (.core i))) : PiLocalization₂ D where
  V := r.sp
  par := Node.par D sc.cGap (.core i)
  M := r.mod M
  J := lev G (.core i)
  ν := (v i).μ
  fd := (v i).𝓕

variable (G) in

def IsOntoMod (i : ℕ) (x₀ : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core (i + 1))).rank) D.host.E) : Prop :=
  x₀ ∈ homLat (G.Λ (.core (i + 1))) (G.Λ (.core i)) ∧ ∃ y₀ ∈ homLat (G.Λ (.core i)) (G.Λ (.core (i + 1))),
    x₀ * y₀ - 1 ∈ G.modul • homLat (G.Λ (.core i)) (G.Λ (.core i))

def CosLaw (i : ℕ) (x₀ : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core (i + 1))).rank) D.host.E)
    (Φ : WO (G.pS (.core i)) (G.pT (.core i)) → ℂ) : Prop :=
  Dep W (.core i) Φ ∧ ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
    (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
    heisO W.ψ _ _ y Φ = W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) • Φ

def Below (v : CoreVol G) (k : ℕ) (F : Fn G (.core k)) : Set (Fn G (.core 0)) :=
  {F₀ | ∃ Ψ : ∀ i, Fn G (.core i), (∀ i, i ≤ k → RapidDec (G.V (.core i)) (Ψ i)) ∧
    (∀ i, i < k → ∃ f : Sch G (.coreDown i), Dep W (.core i) f ∧ Ψ i = dn W v i f (Ψ (i + 1))) ∧ Ψ 0 = F₀ ∧ Ψ k = F}

def ComOK : Prop := Gap fun {_} _ _ _ _ W _ => (gridCom W).Is

def StageOK : Prop := All fun {D} _ _ _ {G} W _ => ∀ i, i ≤ D.R.m → (∃ r, IsCoreLat G i r) ∧
  ∀ r, IsCoreLat G i r → ∀ v M, (gridStage G v i r M).Is (gridCom W) i

def ParOK : Prop := ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ i, i < D.R.m → ∀ τ,
  UpPair (sLen D - 1) (Node.par D 1 (.core i) τ) (Node.par D 1 (.core (i + 1)) τ) (-(cen D 1 τ (D.R.m - i) : ℚ))
    (-(cen D 1 τ (D.R.m - i) : ℚ))

def OntoModEx : Prop := All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∃ x₀, IsOntoMod G i x₀

def LatExch : Prop := All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' →
  ∀ (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (x : WO (G.pS (.core i)) (G.pT (.core i))),
    x ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (T := _) (.core i) : Set _) (G.latT (.core i) : Set _) P ↔
      adjO (G.V (.core i)) (G.V (.core (i + 1))) x ∈
        latO r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) P

def DatumEx : Prop := All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' →
  ∀ (S S' : D.what₂.Tau → SPar) (M : DSModel r.sp S) (M' : DSModel r'.sp S'), ∀ x₀ ∈ homLat (G.Λ (.core (i + 1))) (G.Λ (.core i)),
    ∃ f, IsVacVec W.ψ W.θ M M' f ∧
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff W.ψ r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp) (GlobalTheory.AdelicU.frameLat r'.sp) G.pl.S0 f ∧
      ∀ φ, CosLaw W i x₀ (exch (G.V (.core i)) (G.V (.core (i + 1))) (ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ M M' f φ))

def CosSupp : Prop := All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ Φ, CosLaw W i x₀ Φ →
  ∀ m X, IsCovolOne (ratL (G.pT (.core i)) (G.pS (.core i))) m X → ∀ g : GA D (G.V (.core i)),
    (∀ v ∉ G.pl.S0, GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.core i)).gram v g ∈
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (G.V (.core i)).gram (G.Λ (.core i)) v) →
    (∫ w in X, W.om (.core i) (1, g) Φ w * conj (Φ w) ∂m) ≠ 0 → Lev.finE (G.V (.core i)) g ∈ G.levCong (.core i)

def PreOK : Prop := Gap fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' → ∀ v M M',
  ∃ ω f, PreStep (gridCom W) i (gridStage G v i r M) (gridStage G v (i + 1) r' M') ω f ∧ Exch W.ψ (W.om (.core i)) ω ∧
    ∀ φ, Dep W (.core i) (exch (G.V (.core i)) (G.V (.core (i + 1))) (ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ (r.mod M) (r'.mod M') f φ))

def ChainEx : Prop := Gap fun {D} _ _ _ {G} W _ => ∀ v r₀ M₀, IsCoreLat G 0 r₀ → ∀ k, k ≤ D.R.m → ∃ r M, IsCoreLat G k r ∧
  ∃ Θ, GlobalTheory.EvenOnto.Reach (gridCom W) (gridStage G v 0 r₀ M₀) k (gridStage G v k r M) Θ ∧
    ∀ y, ∀ x ∈ (gridStage G v 0 r₀ M₀).KF, PiLocalization₂.val (Θ y) x ∈
      Submodule.span ℂ {F₀ : Fn G (.core 0) | ∃ w, F₀ ∈ Below W v k (PiLocalization₂.val y w)}

def TopCols : Prop := All fun {D} _ _ {sc} {G} W _ =>
  ∀ M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m)), ∀ y ∈ CoreForms G W.θ D.R.m M, ∀ w,
    ∃ c ∈ Cols G W.θ, ∃ ξ : Module.Dual ℂ (coefPlus G W.θ).W, y w = pairVec (coefPlus G W.θ) ξ c

example (V : HSp D) : (ReLat.sp (V := V) ⟨V.L0, V.standardTuple_isLattice, V.baseLattice_isUnimodular⟩).gram = V.gram := rfl

end GlobalTheory.CoreOnto

end
