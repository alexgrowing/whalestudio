import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

open GlobalTheory.AbLaw in

theorem cech_one_cocycle_split : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (K : Type) (W : K → X.Opens), (∀ i, W i ≤ U) → U ≤ ⨆ i, W i → ∀ f : ∀ i j, Γ(X, W i ⊓ W j), (∀ i j k, (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ⊓ W k ≤ W i ⊓ W j)).op).hom (f i j) + (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W j ⊓ W k ≤ W j ⊓ W k)).op).hom (f j k) = (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W j ⊓ W k ≤ W i ⊓ W k)).op).hom (f i k)) → ∃ a : ∀ i, Γ(X, W i), ∀ i j, f i j = (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op).hom (a i) - (X.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op).hom (a j) := by
  intro X U hU K W hW hc f hf
  have hM := ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB_isLB X
  obtain ⟨ψ, hψ⟩ := GlobalTheory.AbLaw.CechOne.cechHOneVanishesOnOpen_of_isAffineOpen hM hU K W hW hc
    (fun a b => (GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top).symm (f a b)) (by
      intro a b d O ha hb hd
      apply (GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top).injective
      have h : rs X inf_le_left (f a b) + rs X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (f b d) =
        rs X (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W a ⊓ W b ⊓ W d ≤ W a ⊓ W d) (f a d) := hf a b d
      have h := congrArg (rs X (le_inf (le_inf ha hb) hd)) h
      simp only [map_add, rs_rs] at h
      rw [map_add, GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
        GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
        GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top]
      simpa only [LinearEquiv.apply_symm_apply] using h)
  refine ⟨fun a => GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top (ψ a), fun a b => ?_⟩
  have h := (LinearEquiv.symm_apply_eq _).1 (hψ a b)
  rw [h, map_sub, GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
    GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top]

end GlobalTheory.CechPer
