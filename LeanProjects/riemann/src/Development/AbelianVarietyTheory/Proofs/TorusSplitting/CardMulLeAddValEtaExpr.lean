import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaVal.RatBound

theorem addVal_prod {K : Type} [CommRing K] (ν : AddValuation K (WithTop ℚ)) {I : Type} (s : Finset I) (f : I → K) :
    ν (∏ i ∈ s, f i) = ∑ i ∈ s, ν (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ν.map_mul, ih]

theorem addVal_intCast_nonneg {K : Type} [CommRing K] (ν : AddValuation K (WithTop ℚ)) (m : ℤ) : 0 ≤ ν (m : K) := by
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih =>
    push_cast at ih ⊢
    exact ν.map_le_add ih ν.map_one.ge
  | pred i ih =>
    push_cast at ih ⊢
    exact ν.map_le_sub ih ν.map_one.ge

theorem le_addVal_prod_sum {K : Type} [CommRing K] (ν : AddValuation K (WithTop ℚ)) {G J : Type} [Fintype G]
    [Fintype J] {n : ℕ} (cf : J → ℤ) (a : G → J → Fin n → K) (t : ℚ)
    (h : ∀ g j, (t : WithTop ℚ) ≤ ∑ b, ν (a g j b)) :
    (((Fintype.card G : ℚ) * t : ℚ) : WithTop ℚ) ≤ ν (∏ g, ∑ j, (cf j : K) * ∏ b, a g j b) := by
  rw [addVal_prod]
  have e : (((Fintype.card G : ℚ) * t : ℚ) : WithTop ℚ) = ∑ _g : G, (t : WithTop ℚ) := by
    rw [← WithTop.coe_sum]
    simp
  rw [e]
  refine Finset.sum_le_sum fun g _ => ν.map_le_sum fun j _ => ?_
  rw [ν.map_mul, addVal_prod]
  exact (h g j).trans (le_add_of_nonneg_left (addVal_intCast_nonneg ν _))

end GlobalTheory.EtaVal.RatBound

namespace GlobalTheory.EtaVal

theorem card_mul_le_addVal_etaExpr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (k : ℕ) [Finite (LevGrp Dw k)] (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw k) (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (w : LatMod Dw k → F) (q : ℚ), (∀ (g : LevGrp Dw k) j, (q : WithTop ℚ) ≤ ∑ b, v (w (g (xs j b)))) → (((Nat.card (LevGrp Dw k) : ℚ) * q : ℚ) : WithTop ℚ) ≤ v (etaExpr k cf xs w) := by
  intro E _ _ _ H Dw k _ J _ n cf xs F _ v w q h
  have := Fintype.ofFinite (LevGrp Dw k)
  have e : etaExpr k cf xs w = ∏ g : LevGrp Dw k, ∑ j, (cf j : F) * ∏ b, w (g (xs j b)) :=
    finprod_eq_prod_of_fintype _
  rw [e, Nat.card_eq_fintype_card]
  exact RatBound.le_addVal_prod_sum v cf (fun (g : LevGrp Dw k) j b => w (g (xs j b))) q h

end GlobalTheory.EtaVal
