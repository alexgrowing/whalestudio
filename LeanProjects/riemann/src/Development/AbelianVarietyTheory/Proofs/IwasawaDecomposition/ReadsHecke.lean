import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiedChoiceOfReads
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThirdLevelOfGoodTwists

noncomputable section

namespace GlobalTheory.LevCmp

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def Eig {V : Type} [AddCommGroup V] [Module ℂ V] (F : GAf L n → V) (κ : GAf L n) (c : ℂ) : Prop := ∀ g, F (g * κ) = c • F g

def FrameAut (θ : GAf L n ≃* GAf L n) : Prop :=
  (∀ κ, θ κ ∈ Umax L n ↔ κ ∈ Umax L n) ∧ ∀ v κ, TrivOutside {v} (θ κ) ↔ TrivOutside {v} κ

def cx {K : Type} [Field K] (e : K →+* ℂ) {J : Subgroup (GAf L n)} (χ : J →* Kˣ) : J →* ℂˣ := (Units.map e.toMonoidHom).comp χ

theorem cx_apply {K : Type} [Field K] (e : K →+* ℂ) {J : Subgroup (GAf L n)} (χ : J →* Kˣ) (κ : J) :
    ((cx e χ κ : ℂˣ) : ℂ) = e (χ κ : Kˣ) := rfl

def LevEq (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (J' : Subgroup (GAf L n)) (χ' : J' →* ℂˣ) : Prop :=
  J = J' ∧ ∀ κ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩

def WtMatch {K : Type} [Field K] (e : K →+* ℂ) {W W' : Type} [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation K (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W') : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W'),
    ∀ γ, LinearMap.toMatrix b' b' (ρ' γ) = (LinearMap.toMatrix b b (ρ γ)).map e

example : FrameAut (MulEquiv.refl (GAf L n)) := ⟨fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩

end Gen

variable {D : D7}

def SideRead (i : D.ntw.Tw) (b : Bool) (k : ℕ) (e : NX.Kk D i k →+* ℂ) : Prop :=
  ∀ x : ↥D.LL0, e (NX.toKk D i k (GlobalTheory.SeriesTie.sideEmb D.ntw i b x)) = embLL0 D x

def ReadsHecke {i : D.ntw.Tw} {k : ℕ} (e : NX.Kk D i k →+* ℂ) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (χ : HChar D.host.E) : Prop :=
  ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧
    GlobalTheory.GalToHecke.IsHeckeOf art ((Units.map (e.comp (NX.ofOk D i k)).toMonoidHom).comp ψ) χ

variable (D) in

def GalOf (χ : HChar D.host.E) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om)) ∧ ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧
    GlobalTheory.GalToHecke.IsHeckeOf art ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀) χ

variable (D) in

def GPlaces : Prop :=
  (∀ k v, D.naut.plGw k v ∈ placesOver D.host.E (D.host.g k) ∧ ∃ s : SplitPlace D.host.E, s.w = D.naut.plGw k v) ∧
    (∀ u ∈ gPl D, ∃ (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E), s.v = u ∧ s.w = D.naut.plGw k v) ∧
    ∃ k, Nonempty (D.nd.PlG k)

variable (D) in

def ParaShape (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ) : Prop :=
  ∀ v ∈ qPl D η, ∃ (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧
    NG.IsCompAt η s ξ ∧ NG.LevelPara J χ s D.R.r ξ

variable (D) in

def GrpShape (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)) : Prop :=
  NG.IsProdLevel J ∧
    (∀ v ∈ qPl D η, ∃ s : SplitPlace D.host.E, s.v = v ∧ ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.ParaRT s D.R.r (s.loc _ κ))) ∧
    (∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v →
      ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.UniRT s D.R.r (s.loc _ κ))) ∧
    ∀ κ, TrivOutside (gPl D ∪ qPl D η)ᶜ κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV)

abbrev cell (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ} {Q : Finset (PlE D.host)}
    {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m) :=
  X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA

abbrev eta (cf : CharFrame D) (xi : D.what₂.Tup → HChar D.host.E) (v : D.what₂.places.Pl) (j : Fin D.R.m) : HChar D.host.E :=
  cf.mu0 j * xi (D.what₂.muTw v)

abbrev mtAt (M : MtFam D) (v : D.what₂.places.Pl) (j : Fin D.R.m) : MtReal D (D.what₂.muTw v) (j.1 + 1) :=
  M (D.what₂.muTw v) (j.1 + 1) (by omega) (by omega)

def CellWt {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m)
    (e : NX.Kk D i k →+* ℂ) : Prop := WtMatch e (cell X b hA j).ρ m.wt.ρ

def Joint (η : HChar D.host.E) {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m) : Prop :=
  ∃ (θ : GAf D.host.E D.R.nV ≃* GAf D.host.E D.R.nV) (J₁ : Subgroup (GAf D.host.E D.R.nV)) (e : NX.Kk D i k →+* ℂ)
    (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ω : (cell X b hA j).W →ₛₗ[e] V),
    FrameAut θ ∧ SideRead i b k e ∧ Function.Injective ω ∧
    (∀ v ∈ qPl D η, ∃ s : SplitPlace D.host.E, s.v = v ∧ ∀ κ, TrivOutside {s.v} κ → NG.ParaRT s D.R.r (s.loc _ κ) → κ ∈ J₁) ∧
    (∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v →
      ∀ κ, TrivOutside {s.v} κ → NG.UniRT s D.R.r (s.loc _ κ) → κ ∈ J₁) ∧
    ∀ κ ∈ J₁, ∃ c c' : ℂ, (∀ x, Eig (m.real x) (θ κ) c) ∧ (∀ f, Eig (fun g => ω (((cell X b hA j).real f).1 g)) (θ κ) c') ∧
      ∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v → TrivOutside {s.v} κ →
        c ^ (D.host.g kk - 1) = c' ^ (D.host.g kk - 1)

end GlobalTheory.LevCmp

end
