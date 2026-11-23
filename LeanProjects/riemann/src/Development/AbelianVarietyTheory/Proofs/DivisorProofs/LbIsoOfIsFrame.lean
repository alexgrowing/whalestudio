import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBObs

theorem gm_id_res' {X : Scheme.{0}} {U V : X.Opens} (hle : V ≤ U) {x : X} (hx : x ∈ V) (a : Γ(X, U)ˣ) :
    gm (𝟙 X) x V (ReciprocityTheory.ChartRestriction.G.Semi.res hle a) = gm (𝟙 X) x U a :=
  gm_res (𝟙 X) x hle hx a

theorem lbIso_of_isFrame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (L L' : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsBas V → L.IsLB → L'.IsLB → IsFrame L V hV u → IsFrame L' V hV u → LBIso L L' := by
  intro X C _ V hV _ L L' u hB _ _ hF hF'
  obtain ⟨τ, hτg, hτ⟩ := hF
  obtain ⟨τ', hτ'g, hτ'⟩ := hF'

  have e : ∀ (T T' : C) (a : T ⟶ T') (m : L.ι) (x : X) (hx : x ∈ V T' ⊓ L.U m),
      gm (𝟙 X) x _ (τ T m) = gm (𝟙 X) x _ (u T T' a) * gm (𝟙 X) x _ (τ T' m) := by
    intro T T' a m x hx
    have h := congrArg (gm (𝟙 X) x (V T' ⊓ L.U m)) (hτ T T' a m)
    rwa [map_mul, gm_id_res' _ hx, gm_id_res' _ hx] at h
  have e' : ∀ (T T' : C) (a : T ⟶ T') (m : L'.ι) (x : X) (hx : x ∈ V T' ⊓ L'.U m),
      gm (𝟙 X) x _ (τ' T m) = gm (𝟙 X) x _ (u T T' a) * gm (𝟙 X) x _ (τ' T' m) := by
    intro T T' a m x hx
    have h := congrArg (gm (𝟙 X) x (V T' ⊓ L'.U m)) (hτ' T T' a m)
    rwa [map_mul, gm_id_res' _ hx, gm_id_res' _ hx] at h

  have key : ∀ (T₁ T₂ : C) (m : L.ι) (m' : L'.ι) (x : X), x ∈ V T₁ → x ∈ V T₂ → x ∈ L.U m → x ∈ L'.U m' →
      gm (𝟙 X) x (V T₁ ⊓ L'.U m') (τ' T₁ m') / gm (𝟙 X) x (V T₁ ⊓ L.U m) (τ T₁ m) =
        gm (𝟙 X) x (V T₂ ⊓ L'.U m') (τ' T₂ m') / gm (𝟙 X) x (V T₂ ⊓ L.U m) (τ T₂ m) := by
    intro T₁ T₂ m m' x h1 h2 hm hm'
    obtain ⟨T₃, ⟨a⟩, ⟨b⟩, h3, -⟩ := hB.2 T₁ T₂ x ⊤ trivial h1 h2
    rw [e T₁ T₃ a m x ⟨h3, hm⟩, e' T₁ T₃ a m' x ⟨h3, hm'⟩, e T₂ T₃ b m x ⟨h3, hm⟩, e' T₂ T₃ b m' x ⟨h3, hm'⟩,
      mul_div_mul_left_eq_div, mul_div_mul_left_eq_div]

  have hglue : ∀ p : L'.ι × L.ι, ∃ s : Γ(X, L'.U p.1 ⊓ L.U p.2)ˣ, ∀ (T : C) (x : X),
      x ∈ V T → x ∈ L'.U p.1 ⊓ L.U p.2 →
        gm (𝟙 X) x _ s = gm (𝟙 X) x (V T ⊓ L'.U p.1) (τ' T p.1) / gm (𝟙 X) x (V T ⊓ L.U p.2) (τ T p.2) := by
    intro p
    obtain ⟨s, hs⟩ := glue_unit (L'.U p.1 ⊓ L.U p.2) (fun T => V T ⊓ (L'.U p.1 ⊓ L.U p.2)) (fun T => inf_le_right)
      (fun x hx => by
        obtain ⟨T, hT, -⟩ := hB.1 x ⊤ trivial
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨T, hT, hx⟩)
      (fun T => ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf_left (V T) inf_le_left) (τ' T p.1) /
        ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf_left (V T) inf_le_right) (τ T p.2))
      (fun T₁ T₂ x hx => by
        simp only [map_div]
        rw [gm_id_res' _ hx.1, gm_id_res' _ hx.1, gm_id_res' _ hx.2, gm_id_res' _ hx.2]
        exact key T₁ T₂ p.2 p.1 x hx.1.1 hx.2.1 hx.1.2.2 hx.1.2.1)
    refine ⟨s, fun T x hT hx => ?_⟩
    have h := congrArg (gm (𝟙 X) x (V T ⊓ (L'.U p.1 ⊓ L.U p.2))) (hs T)
    simp only [map_div] at h
    have hTx : x ∈ V T ⊓ (L'.U p.1 ⊓ L.U p.2) := ⟨hT, hx⟩
    rwa [gm_id_res' _ hTx, gm_id_res' _ hTx, gm_id_res' _ hTx] at h
  choose w hw using hglue
  refine ⟨⟨w⟩, fun p q => ?_⟩
  apply ReciprocityTheory.ChartRestriction.G.Geo.Tor.unit_ext
  intro x hx
  obtain ⟨T, hT, -⟩ := hB.1 x ⊤ trivial
  have hp : x ∈ L'.U p.1 ⊓ L.U p.2 := hx.1
  have hq : x ∈ L'.U q.1 ⊓ L.U q.2 := hx.2

  have g1 := congrArg (gm (𝟙 X) x _) (hτ'g T p.1 q.1)
  have g2 := congrArg (gm (𝟙 X) x _) (hτg T p.2 q.2)
  have hx1 : x ∈ V T ⊓ L'.U p.1 ⊓ L'.U q.1 := ⟨⟨hT, hp.1⟩, hq.1⟩
  have hx2 : x ∈ V T ⊓ L.U p.2 ⊓ L.U q.2 := ⟨⟨hT, hp.2⟩, hq.2⟩
  rw [map_mul, gm_id_res' _ hx1, gm_id_res' _ hx1, gm_id_res' _ hx1] at g1
  rw [map_mul, gm_id_res' _ hx2, gm_id_res' _ hx2, gm_id_res' _ hx2] at g2
  have hwp : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q)
      (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_left : (L'.div L).U p ⊓ (L'.div L).U q ≤ (L'.div L).U p) (w p)) =
      gm (𝟙 X) x ((L'.div L).U p) (w p) := gm_id_res' _ hx _
  have hwq : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q)
      (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_right : (L'.div L).U p ⊓ (L'.div L).U q ≤ (L'.div L).U q) (w q)) =
      gm (𝟙 X) x ((L'.div L).U q) (w q) := gm_id_res' _ hx _
  have hx' : x ∈ L'.U p.1 ⊓ L.U p.2 ⊓ (L'.U q.1 ⊓ L.U q.2) := hx
  have hg : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q) ((L'.div L).g p q) =
      gm (𝟙 X) x (L'.U p.1 ⊓ L'.U q.1) (L'.g p.1 q.1) * (gm (𝟙 X) x (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := by
    show gm (𝟙 X) x (L'.U p.1 ⊓ L.U p.2 ⊓ (L'.U q.1 ⊓ L.U q.2))
      (ReciprocityTheory.ChartRestriction.G.Semi.res _ (L'.g p.1 q.1) * (ReciprocityTheory.ChartRestriction.G.Semi.res _ (L.g p.2 q.2))⁻¹) = _
    rw [map_mul, map_inv, gm_id_res' _ hx', gm_id_res' _ hx']
  rw [map_mul, hwp, hwq, hg]
  erw [hw p T x hT hp, hw q T x hT hq]
  rw [g1, g2]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

end GlobalTheory.LBObs
