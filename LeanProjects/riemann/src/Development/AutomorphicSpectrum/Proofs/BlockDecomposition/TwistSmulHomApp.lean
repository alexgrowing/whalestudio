import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE.Step

variable {X : Scheme.{0}} {P : X.Modules}

def lvl (S : ℕ → Subobject P) : ℕ → Subobject P
  | 0 => ⊤
  | e + 1 => S e

@[simp] lemma lvl_zero (S : ℕ → Subobject P) : lvl S 0 = ⊤ := rfl
@[simp] lemma lvl_succ (S : ℕ → Subobject P) (e : ℕ) : lvl S (e + 1) = S e := rfl

lemma lvl_succ_le {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    lvl S (e + 1) ≤ lvl S e := by
  cases e with
  | zero => exact le_top
  | succ e => exact hS e

def incl {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    (lvl S (e + 1) : X.Modules) ⟶ (lvl S e : X.Modules) :=
  Subobject.ofLE _ _ (lvl_succ_le hS e)

@[reassoc (attr := simp)]
lemma incl_arrow {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    incl hS e ≫ (lvl S e).arrow = (lvl S (e + 1)).arrow :=
  Subobject.ofLE_arrow _

def gr {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) : X.Modules :=
  cokernel (incl hS e)

def grπ {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    (lvl S e : X.Modules) ⟶ gr hS e :=
  cokernel.π _

@[reassoc (attr := simp)]
lemma incl_grπ {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    incl hS e ≫ grπ hS e = 0 :=
  cokernel.condition _

def MapsDown (S : ℕ → Subobject P) (r : Γ(X, ⊤)) : Prop :=
  ∀ e, (lvl S (e + 1)).Factors ((lvl S e).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P r)

def mulLvl {S : ℕ → Subobject P} {r : Γ(X, ⊤)} (hr : MapsDown S r) (e : ℕ) :
    (lvl S e : X.Modules) ⟶ (lvl S (e + 1) : X.Modules) :=
  (lvl S (e + 1)).factorThru _ (hr e)

@[reassoc (attr := simp)]
lemma mulLvl_arrow {S : ℕ → Subobject P} {r : Γ(X, ⊤)} (hr : MapsDown S r) (e : ℕ) :
    mulLvl hr e ≫ (lvl S (e + 1)).arrow = (lvl S e).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P r :=
  Subobject.factorThru_arrow _ _ _

lemma incl_mulLvl {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) {r : Γ(X, ⊤)}
    (hr : MapsDown S r) (e : ℕ) :
    incl hS e ≫ mulLvl hr e = mulLvl hr (e + 1) ≫ incl hS (e + 1) := by
  rw [← cancel_mono (lvl S (e + 1)).arrow]
  simp only [Category.assoc, mulLvl_arrow, incl_arrow, incl_arrow_assoc]

def grT {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) {r : Γ(X, ⊤)} (hr : MapsDown S r)
    (e : ℕ) : gr hS e ⟶ gr hS (e + 1) :=
  cokernel.desc _ (mulLvl hr e ≫ grπ hS (e + 1)) (by
    rw [← Category.assoc, incl_mulLvl, Category.assoc, incl_grπ, comp_zero])

@[reassoc (attr := simp)]
lemma grπ_grT {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) {r : Γ(X, ⊤)}
    (hr : MapsDown S r) (e : ℕ) :
    grπ hS e ≫ grT hS hr e = mulLvl hr e ≫ grπ hS (e + 1) :=
  cokernel.π_desc _ _ _

lemma grT_comm {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) {r s : Γ(X, ⊤)}
    (hr : MapsDown S r) (hs : MapsDown S s) (e : ℕ) :
    grT hS hr e ≫ grT hS hs (e + 1) = grT hS hs e ≫ grT hS hr (e + 1) := by
  apply coequalizer.hom_ext
  change grπ hS e ≫ _ = grπ hS e ≫ _
  simp only [grπ_grT_assoc, grπ_grT]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono (lvl S (e + 2)).arrow]
  simp only [Category.assoc, mulLvl_arrow, mulLvl_arrow_assoc]
  rw [smulHom_comp_smulHom, smulHom_comp_smulHom, mul_comm]

lemma anti {A : Type} [CommRing A] [IsNoetherianRing A] {I : Ideal A} [X.Over (Spec (.of A))]
    {S : ℕ → Subobject P} (hS : ClosedSys I P S) (e : ℕ) : S (e + 1) ≤ S e := by
  rw [hS.succ e]
  exact le_sup_left

lemma twist_smulHom_app (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (F : X.Modules) (r : Γ(X, ⊤))
    (V : X.Opens) (s : Γ(GlobalTheory.twist F L, V)) :
    (GlobalTheory.Twist.map L (GroundTheory.Arith.SchemeCoh.smulHom F r)).app V s = restrictTop V r • s := by
  ext i
  rw [GlobalTheory.Twist.coord_map_app, GlobalTheory.Twist.coord_smul, GroundTheory.Arith.SchemeCoh.smulHom_app_apply]
  congr 1
  exact (restrictTop_restrict (homOfLE inf_le_left) r).symm

def Lifts {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {S : ℕ → Subobject P} (hS : ClosedSys I P S) (n : ℤ) (e : ℕ) :
    Prop :=
  ∀ y : Γ(GlobalTheory.twistZ (gr (anti hS) e) H n, ⊤), ∃ c : Γ(GlobalTheory.twistZ (lvl S e : X.Modules) H n, ⊤),
    (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) e)).app ⊤ c = y ∧
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (lvl S e).arrow).app ⊤ c ∈ twPow I H n P e

end GlobalTheory.CompanionTheory.GE.Step
