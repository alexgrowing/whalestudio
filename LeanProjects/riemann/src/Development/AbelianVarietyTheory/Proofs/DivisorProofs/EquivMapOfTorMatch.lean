import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorMatchComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

theorem equivMap_of_torMatch : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), Function.Injective g → ∀ ρ, TorMatch U U' g β ρ → EquivMap U U' β ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hg ρ h
  intro f f' hf hf' hc m m' hm hm' y
  have hkV : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : V) := fun k hk => by
    simpa using hk.map g
  have hkR : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : R) := fun _ hk => hk
  have t := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar R hR G hG D A U f hf m hm
  have t' := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar V hV G' hG' D' A' U' f' hf' m' hm'
  have c₁ := torMatch_comp R hR G hG D A U R hR G hG D A U (RingHom.id R) f.left V hV G' hG' D' A' U' g β hg hkR m ρ t h
  have c₂ := torMatch_comp R hR G hG D A U V hV G' hG' D' A' U' g β V hV G' hG' D' A' U' (RingHom.id V) f'.left
    Function.injective_id hkV ρ m' h t'
  rw [RingHom.comp_id] at c₁
  rw [RingHom.id_comp, hc] at c₂
  have e := torMatch_unique R hR G hG D A U V hV G' hG' D' A' U' g (β ≫ f.left) hg _ _ c₁ c₂
  exact DFunLike.congr_fun e y

end GlobalTheory.Poinc.Eq8
