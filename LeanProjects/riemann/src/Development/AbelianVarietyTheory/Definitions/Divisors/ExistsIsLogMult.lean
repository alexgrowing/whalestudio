import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic

namespace GlobalTheory.Discrepancy

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

abbrev fnPull (s : Y ⟶ X) [IsDominant s] : X.functionFieldˣ →* Y.functionFieldˣ :=
  Units.map (functionFieldMap s).toMonoidHom

def pullCart (s : Y ⟶ X) [IsDominant s] (D : CartierDiv X) : CartierDiv Y :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose

theorem isEqn_pullCart (s : Y ⟶ X) [IsDominant s] {D : CartierDiv X} {y : Y} {g : X.functionFieldˣ}
    (h : D.IsEqn (s y) g) : (pullCart s D).IsEqn y (fnPull s g) :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose_spec.2 y g h

theorem toPic_pullCart (s : Y ⟶ X) [IsDominant s] (D : CartierDiv X) :
    toPic (pullCart s D) = CechPic.pull s (toPic D) :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose_spec.1

theorem pullCart_add (s : Y ⟶ X) [IsDominant s] (D E : CartierDiv X) :
    pullCart s (D + E) = pullCart s D + pullCart s E :=
  CartierDiv.ext_of_isEqn fun y =>
    have ⟨g, hg⟩ := D.exists_isEqn (s y)
    have ⟨g', hg'⟩ := E.exists_isEqn (s y)
    ⟨_, isEqn_pullCart s (hg.add hg'),
      (map_mul (fnPull s) g g').symm ▸ (isEqn_pullCart s hg).add (isEqn_pullCart s hg')⟩

def pullCartHom (s : Y ⟶ X) [IsDominant s] : CartierDiv X →+ CartierDiv Y :=
  AddMonoidHom.mk' (pullCart s) (pullCart_add s)

variable {k : Type} [Field k]

def DivOver.Over {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] (E' : DivOver (s ≫ p)) (E : DivOver p) :
    Prop :=
  ∀ f, f ∈ E.ring ↔ functionFieldMap s f ∈ E'.ring

structure IsLogRes (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X)
    (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) : Prop where

  smooth : SmoothOfRelativeDimension n (s ≫ p)

  proj : IsProjOver (s ≫ p)

  bir : Function.Bijective (functionFieldMap s)

  div : IsDivOfForm K (EtaleKlt.ratPull p s n η)

  snc : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)

  supp : (pullCart s G - m • K).supp ≤ B

structure IsLogMult (p : X ⟶ Sp k) (n : ℕ) (Δ : X → ℚ) (η : RatForms p n) (m : ℕ)
    (G : CartierDiv X) : Prop where

  ne_zero : η ≠ 0

  pos : 0 < m

  eqn : ∀ x g, G.IsEqn x g → IsLogEqn p Δ η x m g

theorem IsLogCanonicalMultiple.exists_isLogMult {p : X ⟶ Sp k} {n : ℕ} {Δ : X → ℚ} {m : ℕ}
    {G : CartierDiv X} (h : IsLogCanonicalMultiple p n Δ m G) (hm : 0 < m) :
    ∃ η, IsLogMult p n Δ η m G :=
  have ⟨η, h₁, h₂⟩ := h; ⟨η, h₁, hm, h₂⟩

def InMultAt (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (x : X)
    (u : X.functionFieldˣ) : Prop :=
  ∀ g, G.IsEqn x g → ∀ E : DivOver p, E.Through x → -1 < (E.ord u : ℚ) + discrep E η m g

def IsMultIdeal (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X)
    (J : X.IdealSheafData) : Prop :=
  ∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔
    ∀ (x : X) (hx : x ∈ U.1) (u : X.functionFieldˣ),
      (u : X.functionField) = fnOf U.1 (gen_mem hx) f → InMultAt p n η m G x u

theorem IsMultIdeal.unique {p : X ⟶ Sp k} {n : ℕ} {η : RatForms p n} {m : ℕ} {G : CartierDiv X}
    {J J' : X.IdealSheafData} (h : IsMultIdeal p n η m G J) (h' : IsMultIdeal p n η m G J') :
    J = J' :=
  Scheme.IdealSheafData.ext (funext fun U => Ideal.ext fun f => (h U f).trans (h' U f).symm)

structure IsSncChart [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) (B : Closeds Y) (y : Y)
    (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y)
    (u : Fin n → Y.functionFieldˣ) : Prop where

  frame : IsFrame (dOn q z)

  val : ∀ j ∈ J, (u j : Y.functionField) = fnOf U (gen_mem hy) (z j)

  spec : ∀ j ∈ J, w j ⤳ y

  coheight : ∀ j ∈ J, Order.coheight (w j) = 1

  inj : Set.InjOn w J

  ord_self : ∀ j ∈ J, Scheme.ord (u j : Y.functionField) (w j) = 1

  ord_other : ∀ j ∈ J, ∀ v, v ⤳ y → v ≠ w j → Scheme.ord (u j : Y.functionField) v = 0

  mem : ∀ v, v ⤳ y → Order.coheight v = 1 → (v ∈ B ↔ ∃ j ∈ J, v = w j)

end GlobalTheory.Discrepancy
