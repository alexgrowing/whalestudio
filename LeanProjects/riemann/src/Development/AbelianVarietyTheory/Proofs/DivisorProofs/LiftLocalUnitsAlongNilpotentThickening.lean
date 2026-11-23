import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecOnPullSurjectiveOfSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem lift_localUnits_of_thickening :
    ∀ (R : Type) [CommRing R] (J : Ideal R) (X X₀ : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (γ : X₀ ⟶ X) (q : X₀ ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback γ q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → Surjective γ → ∀ (L : LB X), L.IsLB → ∀ D : X.Opens, IsAffineOpen D → ∀ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' → gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) → ∃ τ : ∀ m : L.ι, Γ(X, D ⊓ L.U m)ˣ, (∀ m, (γ.app (D ⊓ L.U m)).hom (τ m).val = (u m).val) ∧ ∀ x m m', x ∈ D ⊓ L.U m → x ∈ D ⊓ L.U m' → gm (𝟙 X) x _ (τ m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ m') := by
  intro R _ J X X₀ f γ q hpb hsurj L hL D hD u hu
  have hLp := LB.isLB_pull hL γ
  let O : L.ι → X₀.Opens := fun m => γ ⁻¹ᵁ (D ⊓ L.U m)
  have hO : ∀ m, O m ≤ γ ⁻¹ᵁ D := fun m => γ.preimage_mono inf_le_left
  have hc : γ ⁻¹ᵁ D ≤ ⨆ m, O m := by
    intro z hz
    obtain ⟨m, hm⟩ := exists_chart hL (γ z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨m, show γ z ∈ D ⊓ L.U m from ⟨hz, hm⟩⟩
  have hU : ∀ m, O m ≤ (L.pull γ).U (fun _ => m) := fun m z hz => mem_pull.2 hz.2

  have hg : ∀ z a b, γ z ∈ L.U a → γ z ∈ L.U b →
      gm (𝟙 X₀) z ((L.pull γ).U (fun _ => a) ⊓ (L.pull γ).U (fun _ => b))
        ((L.pull γ).g (fun _ => a) (fun _ => b)) = gm γ z _ (L.g a b) := by
    intro z a b ha hb
    have hp : (𝟙 X₀) z ∈ (L.pull γ).U (fun _ => a) ⊓ (L.pull γ).U (fun _ => b) :=
      ⟨mem_pull.2 ha, mem_pull.2 hb⟩
    show gm (𝟙 X₀) z _ (∏ _k : PUnit, (res _ (pullU γ _ (L.g a b))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_res (𝟙 X₀) z _ hp _).trans ((gm_pull (𝟙 X₀) γ z (L.U a ⊓ L.U b) ⟨ha, hb⟩ _).trans ?_)
    rw [Category.id_comp]
  have hcomp : ∀ a b, rs X₀ (inf_le_left : O a ⊓ O b ≤ O a) (u a).val =
      rs X₀ (inf_le_inf (hU a) (hU b)) ((L.pull γ).g (fun _ => a) (fun _ => b)).val *
        rs X₀ (inf_le_right : O a ⊓ O b ≤ O b) (u b).val := by
    intro a b
    have e : res (inf_le_left : O a ⊓ O b ≤ O a) (u a) =
        res (inf_le_inf (hU a) (hU b)) ((L.pull γ).g (fun _ => a) (fun _ => b)) *
          res (inf_le_right : O a ⊓ O b ≤ O b) (u b) := by
      apply unit_ext
      intro z hz
      have hz' : (𝟙 X₀) z ∈ O a ⊓ O b := hz
      rw [map_mul, gm_res _ z _ hz', gm_res _ z _ hz', gm_res _ z _ hz',
        hg z a b hz.1.2 hz.2.2]
      exact hu z a b hz.1 hz.2
    have e' := congrArg Units.val e
    simp only [Units.val_mul, GlobalTheory.LB.val_res] at e'
    exact e'
  obtain ⟨t, ht, -⟩ := SecOn.existsUnique_of_local hLp O hO hc (fun m _ => m) hU
    (fun m => (u m).val) hcomp
  obtain ⟨s, hs⟩ := secOn_pull_surjective_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective X X₀ f q γ hpb L hL D hD t
  have hcoord : ∀ m, (γ.app (D ⊓ L.U m)).hom (GlobalTheory.LB.coord s m) = (u m).val := by
    intro m
    have e := ht m
    rw [← hs] at e
    erw [SecOn.coord_pull γ s (fun _ => m), GlobalTheory.LB.resG_appLE] at e
    rw [Scheme.Hom.app_eq_appLE]
    exact e
  have hunit : ∀ m, IsUnit (GlobalTheory.LB.coord s m) := by
    intro m
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    obtain ⟨z, rfl⟩ := γ.surjective x
    apply isUnit_of_map_unit (γ.stalkMap z).hom
    erw [Scheme.Hom.germ_stalkMap_apply γ (D ⊓ L.U m) z hx, hcoord m]
    exact (u m).isUnit.map _
  refine ⟨fun m => (hunit m).unit, fun m => hcoord m, ?_⟩
  intro x m m' hx hx'
  have hi : D ⊓ L.U m ⊓ L.U m' ≤ D ⊓ L.U m := inf_le_left
  have hj : D ⊓ L.U m ⊓ L.U m' ≤ D ⊓ L.U m' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hij : D ⊓ L.U m ⊓ L.U m' ≤ L.U m ⊓ L.U m' :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have e : res hi (hunit m).unit = res hij (L.g m m') * res hj (hunit m').unit := by
    apply Units.ext
    simp only [Units.val_mul, GlobalTheory.LB.val_res, IsUnit.unit_spec]
    exact SecOn.compat s m m' hi hj hij
  have hxx : (𝟙 X) x ∈ D ⊓ L.U m ⊓ L.U m' := ⟨hx, hx'.2⟩
  have e' := congrArg (gm (𝟙 X) x _) e
  rw [map_mul, gm_res _ x _ hxx, gm_res _ x _ hxx, gm_res _ x _ hxx] at e'
  exact e'

end GlobalTheory.FormalAlg
