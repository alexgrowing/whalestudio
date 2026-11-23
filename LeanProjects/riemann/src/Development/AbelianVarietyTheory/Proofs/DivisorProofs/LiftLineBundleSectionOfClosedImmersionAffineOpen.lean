import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Matched
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.PinchLift

open TopologicalSpace

theorem sec_eq_of_germ {X : Scheme.{0}} {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ x (hx : x ∈ U), X.presheaf.germ U x hx a = X.presheaf.germ U x hx b) : a = b :=
  TopCat.Presheaf.section_ext X.sheaf U a b h

theorem germ_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (a : Γ(X, U)) :
    X.presheaf.germ V x hx (resG X h a) = X.presheaf.germ U x (h hx) a :=
  X.presheaf.germ_res_apply (homOfLE h) x hx a

theorem epi_toPushforward_of_closedImm {X' Z' : Scheme.{0}} (i' : Z' ⟶ X') [IsClosedImmersion i'] {L' : LB X'}
    (hL : L'.IsLB) : Epi (GlobalTheory.LB.toPushforward L' i') := by
  refine GlobalTheory.QCoh.epi_of_locally_app_surjective _ fun W x hx => ?_
  obtain ⟨k, hk⟩ := exists_chart hL x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hle⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ W ⊓ L'.U k from ⟨hx, hk⟩) (W ⊓ L'.U k).2
  have hVW : V ≤ W ⊓ L'.U k := hle
  have hVk : V ≤ L'.U k := hVW.trans inf_le_right
  refine ⟨V, hxV, hVW.trans inf_le_left, fun t => ?_⟩
  have h' : i' ⁻¹ᵁ V ≤ (L'.pull i').U (fun _ => k) := (i'.preimage_mono hVk).trans (GlobalTheory.LB.pull_U i' (fun _ => k)).ge
  obtain ⟨b, hb⟩ := i'.app_surjective V hV
    (GlobalTheory.LB.chartEquiv (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hL i') (fun _ => k) h' t)
  refine ⟨(GlobalTheory.LB.chartEquiv hL k hVk).symm b, ?_⟩
  apply (GlobalTheory.LB.chartEquiv (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hL i') (fun _ => k) h').injective
  rw [← hb]
  exact (GlobalTheory.LB.chartEquiv_pullSec i' hL (fun _ => k) hVk h' _).trans
    (congrArg (i'.app V).hom (LinearEquiv.apply_symm_apply _ _))

theorem lift_section_of_closedImm : ∀ (X' Z' : Scheme.{0}) (i' : Z' ⟶ X') [IsClosedImmersion i'] (L' : LB X'), L'.IsLB →
    ∀ (Y' : X'.Opens), IsAffineOpen Y' → ∀ (τ : ∀ k, Γ(Z', i' ⁻¹ᵁ (L'.U k ⊓ Y'))),
    (∀ (k l : L'.ι) (z : Z') (hk : z ∈ i' ⁻¹ᵁ (L'.U k ⊓ Y')) (hl : z ∈ i' ⁻¹ᵁ (L'.U l ⊓ Y')),
      Z'.presheaf.germ _ z hk (τ k) =
        Z'.presheaf.germ (i' ⁻¹ᵁ (L'.U k ⊓ L'.U l)) z ⟨hk.1, hl.1⟩ ((i'.app _).hom (L'.g k l).val) *
          Z'.presheaf.germ _ z hl (τ l)) →
    ∃ θ : ∀ k, Γ(X', L'.U k ⊓ Y'),
      (∀ (k l : L'.ι) (x : X') (hk : x ∈ L'.U k ⊓ Y') (hl : x ∈ L'.U l ⊓ Y'),
        X'.presheaf.germ _ x hk (θ k) =
          X'.presheaf.germ (L'.U k ⊓ L'.U l) x ⟨hk.1, hl.1⟩ (L'.g k l).val * X'.presheaf.germ _ x hl (θ l)) ∧
      ∀ k, (i'.app (L'.U k ⊓ Y')).hom (θ k) = τ k := by
  intro X' Z' i' _ L' hL Y' hY τ hτ
  have hL' := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hL i'
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL'
  haveI := epi_toPushforward_of_closedImm i' hL
  have hsurj := GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen (GlobalTheory.LB.toPushforward L' i') hY
  have le1 : ∀ m : (L'.pull i').ι, i' ⁻¹ᵁ Y' ⊓ (L'.pull i').U m ≤ i' ⁻¹ᵁ (L'.U (m PUnit.unit) ⊓ Y') :=
    fun m z hz => ⟨GlobalTheory.LB.pull_U_le i' m hz.2, hz.1⟩
  let c : ∀ m, Γ(Z', i' ⁻¹ᵁ Y' ⊓ (L'.pull i').U m) := fun m => resG Z' (le1 m) (τ (m PUnit.unit))
  have hc : c ∈ secOn (L'.pull i') (i' ⁻¹ᵁ Y') := by
    intro m n
    apply sec_eq_of_germ
    intro z hz
    have hzm : z ∈ i' ⁻¹ᵁ (L'.U (m PUnit.unit) ⊓ Y') := le1 m ⟨hz.1.1, hz.1.2⟩
    have hzn : z ∈ i' ⁻¹ᵁ (L'.U (n PUnit.unit) ⊓ Y') := le1 n ⟨hz.1.1, hz.2⟩
    simp only [c, map_mul, germ_resG]
    rw [hτ (m PUnit.unit) (n PUnit.unit) z hzm hzn]
    congr 1
    have e := GlobalTheory.LB.resG_pull_g (L := L') i' m n (le_refl _)
    rw [GlobalTheory.LB.resG_self] at e
    rw [e, ← GlobalTheory.LB.resG_app, germ_resG]
  obtain ⟨s, hs⟩ := hsurj (GlobalTheory.LB.mkSec c hc)
  have hcoord : ∀ k, (i'.appLE (Y' ⊓ L'.U k) (i' ⁻¹ᵁ Y' ⊓ (L'.pull i').U (fun _ => k))
      (GlobalTheory.LB.pull_inf_le i' Y' (fun _ => k))).hom (GlobalTheory.LB.coord s k) = c (fun _ => k) := fun k => by
    have := congrArg (fun u => GlobalTheory.LB.coord u (fun _ : PUnit => k)) hs
    exact Eq.trans (GlobalTheory.LB.coord_pullSec i' s _).symm this
  refine ⟨fun k => resG X' (le_inf inf_le_right inf_le_left : L'.U k ⊓ Y' ≤ Y' ⊓ L'.U k) (GlobalTheory.LB.coord s k),
    ?_, ?_⟩
  · intro k l x hk hl
    have hx3 : x ∈ Y' ⊓ L'.U k ⊓ L'.U l := ⟨⟨hk.2, hk.1⟩, hl.1⟩
    have e := GlobalTheory.LB.coord_mem s k l
    simp only [germ_resG]
    rw [← germ_resG (inf_le_left : Y' ⊓ L'.U k ⊓ L'.U l ≤ Y' ⊓ L'.U k) x hx3, e, map_mul, germ_resG, germ_resG]
  · intro k
    have h : L'.U k ⊓ Y' ≤ Y' ⊓ L'.U k := le_inf inf_le_right inf_le_left
    apply sec_eq_of_germ
    intro z hz
    have hzB : z ∈ i' ⁻¹ᵁ Y' ⊓ (L'.pull i').U (fun _ => k) :=
      ⟨hz.2, (GlobalTheory.LB.pull_U i' (fun _ => k)).ge hz.1⟩
    have e1 : (i'.app (L'.U k ⊓ Y')).hom (resG X' h (GlobalTheory.LB.coord s k)) =
        (i'.appLE (Y' ⊓ L'.U k) (i' ⁻¹ᵁ (L'.U k ⊓ Y')) (i'.preimage_mono h)).hom (GlobalTheory.LB.coord s k) := by
      rw [← Scheme.Hom.appLE_eq_app, GlobalTheory.LB.appLE_resG]
    show Z'.presheaf.germ _ z hz ((i'.app (L'.U k ⊓ Y')).hom (resG X' h (GlobalTheory.LB.coord s k))) = _
    rw [e1, ← GlobalTheory.LB.resG_app, germ_resG,
      ← germ_resG (GlobalTheory.LB.pull_inf_le i' Y' (fun _ => k)) z hzB, GlobalTheory.LB.resG_app, hcoord k]
    simp only [c, germ_resG]

end GlobalTheory.PinchLift
