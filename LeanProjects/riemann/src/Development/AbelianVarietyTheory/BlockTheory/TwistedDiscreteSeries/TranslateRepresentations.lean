import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Space

variable (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)

def LiftsTo (κ : (levEnv V β L).Q) (g₀ : G0 L.Pg L.r) : Prop :=
  rTup β L (Formalism.UG.bc (swapAE D) ((κ : Bridge.Gf V) : GL _ _)) = g₀

def IsTranslate {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (g₀ : G0 L.Pg L.r) (F F' : Bridge.Gf V → W) : Prop :=
  (∃ κ, LiftsTo V β L κ g₀) ∧
    ∀ κ, LiftsTo V β L κ g₀ → ∀ h, F' h = ((((levEnv V β L).ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * (κ : Bridge.Gf V))

def IsTransRep {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {G : Type} [Group G] (eG : G ≃* G0 L.Pg L.r)
    (M : HMod (Bridge.Gf V → W)) (ρ : Representation ℂ G M.H) : Prop :=
  ∀ g x, IsTranslate V β L (eG g) (M.e x) (M.e (ρ g x))

variable {V β L}

theorem IsTranslate.unique {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {g₀ : G0 L.Pg L.r}
    {F F₁ F₂ : Bridge.Gf V → W} (h₁ : IsTranslate V β L g₀ F F₁) (h₂ : IsTranslate V β L g₀ F F₂) : F₁ = F₂ := by
  obtain ⟨κ, hκ⟩ := h₁.1
  funext h
  rw [h₁.2 κ hκ h, h₂.2 κ hκ h]

theorem IsTransRep.unique {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {G : Type} [Group G]
    {eG : G ≃* G0 L.Pg L.r} {M : HMod (Bridge.Gf V → W)} (hM : Function.Injective M.e) {ρ₁ ρ₂ : Representation ℂ G M.H}
    (h₁ : IsTransRep V β L eG M ρ₁) (h₂ : IsTransRep V β L eG M ρ₂) : ρ₁ = ρ₂ := by
  ext g x
  exact hM ((h₁ g x).unique (h₂ g x))

theorem IsTransRep.eq_of_translate {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {G : Type} [Group G]
    {eG : G ≃* G0 L.Pg L.r} {M : HMod (Bridge.Gf V → W)} (hM : Function.Injective M.e) {ρ : Representation ℂ G M.H}
    (h : IsTransRep V β L eG M ρ) {g : G} {x x' : M.H} (hx : IsTranslate V β L (eG g) (M.e x) (M.e x')) : x' = ρ g x :=
  hM (hx.unique (h g x))

theorem IsTranslate.eq_g0Act {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {g₀ : G0 L.Pg L.r}
    {F F' : Bridge.Gf V → W} (h : IsTranslate V β L g₀ F F') (κ : (levEnv V β L).Q) (hκ : LiftsTo V β L κ g₀) :
    F' = Bridge.g0Act (levEnv V β L).ch κ F :=
  funext (h.2 κ hκ)

end Space

def Commutes {G E E' : Type} [Group G] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (ρ : Representation ℂ G E) (ρ' : Representation ℂ G E') (f : E →ₗ[ℂ] E') : Prop :=
  ∀ g x, f (ρ g x) = ρ' g (f x)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def IsActX (t : T) (ρ : Representation ℂ G (R.HX t).H) : Prop :=
  IsTransRep D.sp.X' R.βX (R.datXt t) R.eG (R.HX t) ρ

def IsActV (i : Fin D.R.m) (t : T) (ρ : Representation ℂ G (R.HV i t).H) : Prop :=
  IsTransRep (Vc D i) (R.βV i) (R.datVt i t) R.eG (R.HV i t) ρ

def GEquiv : Prop :=
  (∀ t, ∃ ρ, IsActX R t ρ ∧ Commutes ρ R.gE (R.Th t)) ∧
    ∀ i t, ∃ ρ, IsActV R i t ρ ∧ Commutes ρ (R.gW i (sg0 D A)) (R.thG i t)

def GEquivAdj : Prop :=
  (∀ t, ∃ ρ, IsActX R t ρ ∧ Commutes R.gE ρ (LinearMap.adjoint (R.Th t))) ∧
    ∀ i t, ∃ ρ, IsActV R i t ρ ∧ Commutes (R.gW i (sg0 D A)) ρ (LinearMap.adjoint (R.thG i t))

theorem GEquiv.th_of_translate (h : GEquiv R) (t : T) (hinj : Function.Injective (R.HX t).e) (g : G) (x x' : (R.HX t).H)
    (hx : IsTranslate D.sp.X' R.βX (R.datXt t) (R.eG g) ((R.HX t).e x) ((R.HX t).e x')) :
    R.Th t x' = R.gE g (R.Th t x) := by
  unfold GEquiv at h
  refine (h.1 t).elim fun ρ hh => ?_
  have hρ := hh.1
  have hc := hh.2
  unfold IsActX at hρ
  have e : x' = ρ g x := IsTransRep.eq_of_translate (V := D.sp.X') (β := R.βX) (L := R.datXt t) (eG := R.eG) hinj hρ hx
  rw [e]
  exact hc g x

variable (D) in

def GEquivAll : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → GEquiv R ∧ GEquivAdj R

end GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

end
