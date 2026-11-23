import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (freeModule)

namespace GlobalTheory.FlagZ.Univ

variable {X : Scheme.{0}} {N : ℕ}

variable (X N) in

def stalkStd (x : X) : Module.Basis (Fin N) (X.presheaf.stalk x) ((freeModule X (Fin N)).presheaf.stalk x :) :=
  (VB.isFrame_freeFrame X (Fin N)).stalkBasis x trivial

def colSpan {x : X} (g : Matrix (Fin N) (Fin N) (X.presheaf.stalk x)) (l : ℕ) :
    Submodule (X.presheaf.stalk x) ((freeModule X (Fin N)).presheaf.stalk x :) :=
  Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = ∑ i, g i j • stalkStd X N x i}

end GlobalTheory.FlagZ.Univ

namespace GlobalTheory.FlagZ.Univ

variable (ι : Type) [Fintype ι] (N : ℕ)

def stalkStep (τ : ι) (l : ℕ) (y : Fl ι N) :
    Submodule ((Fl ι N).presheaf.stalk y) ((freeModule (Fl ι N) (Fin N)).presheaf.stalk y :) :=
  ⨅ (g : ι → GL (Fin N) ((Fl ι N).presheaf.stalk y))
    (_ : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g = (Fl ι N).fromSpecStalk y), colSpan (g τ).1 l

def sub (τ : ι) (l : ℕ) : VB.Sub (freeModule (Fl ι N) (Fin N)) := VB.Sub.ofStalks (stalkStep ι N τ l)

def freeIso : (Scheme.Modules.pullback (flStr ι N)).obj (freeModule (Sp ℤ) (Fin N)) ≅ freeModule (Fl ι N) (Fin N) :=
  ((VB.isFrame_freeFrame (Sp ℤ) (Fin N)).pullback (flStr ι N)).iso (VB.isFrame_freeFrame _ (Fin N))

def F (τ : ι) (i : Fin (N + 1)) : (Fl ι N).Modules := (sub ι N τ i).toMod

def incl (τ : ι) (i : Fin (N + 1)) : F ι N τ i ⟶ (Scheme.Modules.pullback (flStr ι N)).obj (freeModule (Sp ℤ) (Fin N)) :=
  (sub ι N τ i).incl ≫ (freeIso ι N).inv

theorem stalkStep_mono (τ : ι) {l l' : ℕ} (h : l ≤ l') (y : Fl ι N) : stalkStep ι N τ l y ≤ stalkStep ι N τ l' y :=
  iInf_mono fun _ => iInf_mono fun _ => Submodule.span_mono fun _ ⟨j, hj, e⟩ => ⟨j, lt_of_lt_of_le hj h, e⟩

def step (τ : ι) (i : Fin N) : F ι N τ i.castSucc ⟶ F ι N τ i.succ :=
  (sub ι N τ i.succ).lift (sub ι N τ i.castSucc).incl fun _ s x hx => by
    exact stalkStep_mono ι N τ (by simp [Fin.val_succ]) x ((sub ι N τ i.castSucc).incl_app_mem s x hx)

theorem step_incl (τ : ι) (i : Fin N) : step ι N τ i ≫ incl ι N τ i.succ = incl ι N τ i.castSucc :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (freeIso ι N).inv) (VB.Sub.lift_incl _ _ _))

variable {ι N} in

def Lifts {T : Scheme.{0}} (g : T ⟶ Sp ℤ)
    (fl' : ι → Vert.Flag ((Scheme.Modules.pullback g).obj (freeModule (Sp ℤ) (Fin N))) N) (g' : T ⟶ Fl ι N) : Prop :=
  ∃ w : g' ≫ flStr ι N = g, ∀ a i, ∃ e : (Scheme.Modules.pullback g').obj (F ι N a i) ≅ (fl' a).F i,
    e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map (incl ι N a i) ≫
      (Scheme.Modules.pullbackComp g' (flStr ι N)).hom.app _ ≫ (Scheme.Modules.pullbackCongr w).hom.app _

end GlobalTheory.FlagZ.Univ
