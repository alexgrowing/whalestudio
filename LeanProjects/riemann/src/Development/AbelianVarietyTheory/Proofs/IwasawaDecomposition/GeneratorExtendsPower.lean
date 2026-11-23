import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtAt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitGen

variable {X Y : Scheme.{0}}

theorem powPull_le (L : LB X) (m : ℕ) (χ : Y ⟶ X) (j : ((lbPow L m).pull χ).ι) :
    ((lbPow L m).pull χ).U j ≤ (L.pull χ).U (fun _ => j PUnit.unit PUnit.unit) := fun _ hy =>
  Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (Set.mem_iInter.1 hy PUnit.unit) PUnit.unit

def powPull (L : LB X) (m : ℕ) (χ : Y ⟶ X) (e : LB.Gen (L.pull χ)) : LB.Gen ((lbPow L m).pull χ) where
  s j := res (powPull_le L m χ j) (e.s (fun _ => j PUnit.unit PUnit.unit)) ^ m

theorem gm_powPull {Z : Scheme.{0}} (L : LB X) (m : ℕ) (χ : Y ⟶ X) (e : LB.Gen (L.pull χ)) (r : Z ⟶ Y) (z : Z)
    (j : ((lbPow L m).pull χ).ι) (h : r z ∈ ((lbPow L m).pull χ).U j) :
    gm r z _ ((powPull L m χ e).s j) = gm r z _ (e.s (fun _ => j PUnit.unit PUnit.unit)) ^ m :=
  (map_pow _ _ _).trans (congrArg (· ^ m) (gm_res r z _ h _))

theorem gm_powPull_g {Z : Scheme.{0}} (L : LB X) (m : ℕ) (χ : Y ⟶ X) (r : Z ⟶ Y) (z : Z)
    (j j' : ((lbPow L m).pull χ).ι) (hj : r z ∈ ((lbPow L m).pull χ).U j)
    (hj' : r z ∈ ((lbPow L m).pull χ).U j') :
    gm r z _ (((lbPow L m).pull χ).g j j') =
      trF (L := L) (fun _ : PUnit => χ) (fun _ => 1) r z (fun _ => j PUnit.unit PUnit.unit)
        (fun _ => j' PUnit.unit PUnit.unit) ^ m := by
  refine (gm_pull_g (lbPow L m) χ r z j j' hj hj').trans ?_
  refine (gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => (m : ℤ)) (r ≫ χ) z (j PUnit.unit) (j' PUnit.unit)
    (Set.mem_iInter.1 hj PUnit.unit) (Set.mem_iInter.1 hj' PUnit.unit)).trans ?_
  simp only [trF, Fintype.prod_unique, Category.comp_id, zpow_natCast, zpow_one]

theorem powPull_isGen (L : LB X) (m : ℕ) (χ : Y ⟶ X) (e : LB.Gen (L.pull χ)) (he : e.IsGen) :
    (powPull L m χ e).IsGen := by
  intro j j'
  refine unit_ext fun y hy => ?_
  have hj := powPull_le L m χ j hy.1
  have hj' := powPull_le L m χ j' hy.2
  have ht := gen_trans (L := L) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) (t := e) he (𝟙 Y) y hj hj'
  refine (gm_res _ y _ hy _).trans ?_
  refine (gm_powPull L m χ e (𝟙 Y) y j hy.1).trans ?_
  refine Eq.trans ?_ (map_mul _ _ _).symm
  rw [gm_powPull_g L m χ (𝟙 Y) y j j' hy.1 hy.2, gm_res _ y _ hy, gm_powPull L m χ e (𝟙 Y) y j' hy.2, ← mul_pow]
  exact congrArg (· ^ m) ht

theorem val_powPull {Z : Scheme.{0}} (L : LB X) (m : ℕ) (χ : Y ⟶ X) (e : LB.Gen (L.pull χ)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → (lbPow L m).ι) (hJ : Good (lbPow L m) z J) :
    val (L := lbPow L m) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) (powPull L m χ e) r z J =
      val (L := L) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e r z (fun ψ => J ψ PUnit.unit) ^ m :=
  gm_powPull L m χ e r z _ (hJ.mem (fun _ : PUnit => χ) r)

theorem extAt_lbPow (X : Scheme.{0}) (L : LB X) (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ X)
    (e : LB.Gen (L.pull x)) (m : ℕ) (he : e.IsGen) (hx : GlobalTheory.TraitGen.ExtAt L x e) :
    ∃ e' : LB.Gen ((lbPow L m).pull x), e'.IsGen ∧ GlobalTheory.TraitGen.ExtAt (lbPow L m) x e' := by
  refine ⟨powPull L m x e, powPull_isGen L m x e he, ?_⟩
  intro V _ _ _ hV ψ gam hg χ hχ
  obtain ⟨e₁, h₁, hv⟩ := hx V hV ψ gam hg χ hχ
  refine ⟨powPull L m χ e₁, powPull_isGen L m χ e₁ h₁, fun z J hJ => ?_⟩
  rw [val_powPull L m x e _ z J hJ, val_powPull L m χ e₁ _ z J hJ]
  exact congrArg (· ^ m) (hv z (fun ψ => J ψ PUnit.unit) fun ψ => Set.mem_iInter.1 (hJ ψ) PUnit.unit)

end GlobalTheory.TraitGen
