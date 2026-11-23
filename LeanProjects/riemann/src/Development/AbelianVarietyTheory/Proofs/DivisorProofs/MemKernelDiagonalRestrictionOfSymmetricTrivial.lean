import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AbDual

theorem memKL_diag_of_triv_ev_of_symm : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) a := by
  intro R _ _ G _ hA P hP h0l h0r hsym T a ha
  have hs : (swap P).IsLB := pull_isLB hP _
  have hadd := (isAdditive_iff hP).1 (CubeNoeth.isAdditive_of_triv_axes hA hA hP h0l h0r)
  have hadd' := (isAdditive_iff hs).1 (CubeNoeth.isAdditive_swap_of_triv_axes hA hA hP h0l h0r)
  have hadd2 : ∀ (Y : Over (Sp R)) (u v w : Y ⟶ G), evc hP u (v * w) = evc hP u v + evc hP u w := by
    intro Y u v w
    rw [← evc_swap hP hs, ← evc_swap hP hs, ← evc_swap hP hs]
    exact hadd' Y v w u
  have hc : cls P hP = cls (swap P) hs := (cls_eq_iff hP hs).2 hsym
  have hsymm : ∀ (Y : Over (Sp R)) (u v : Y ⟶ G), evc hP u v = evc hP v u := by
    intro Y u v
    rw [← evc_swap hP hs u v]
    simp only [evc, hc]
  have hL : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  have hcL : ∀ (Y : Over (Sp R)) (u : Y ⟶ G), CechPic.pull u.left (cls _ hL) = evc hP u u := by
    intro Y u
    rw [cls_ev hP, pull_evc, Category.comp_id]
  have hx0 : evc hP (fst T G ≫ a) (snd T G) = 0 := by
    have e := congrArg (CechPic.pull (lift (snd T G) (fst T G)).left) ((triv_ev_iff hP _ _).1 ha)
    rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e
  have hD : (Out.translDiff G _ a).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc'⟩ := exists_pull_eq_zero (evc hP a a) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL a hD (fst T G) (snd T G)
  rw [lift_fst_snd, Over.id_left, pull_id, hcL, hcL] at e₁
  have e₂ : cls _ hD = CechPic.pull (fst T G).left (evc hP a a) := by
    rw [e₁, pull_evc, hadd, hadd2, hadd2, hsymm _ (snd T G) (fst T G ≫ a), hx0]
    abel
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T G).left ⁻¹ᵁ V).ι ≫ (fst T G).left) (fun z ↦ z.2) hc'

end GlobalTheory.AbDual
