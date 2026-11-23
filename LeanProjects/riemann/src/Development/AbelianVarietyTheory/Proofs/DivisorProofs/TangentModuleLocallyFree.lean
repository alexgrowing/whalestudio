import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.WitnessIsFormalParam
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieFreeAway

open GlobalTheory.ChartCompare

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X0 : Scheme.{0}}
  (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

variable {t x0} in

def vecT {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : TanM x0 t.G :=
  mkT (ovT hv) (smT_zero_ovT hv)

theorem comb_iff {n : ℕ} {v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x0 (v j))
    (a : Fin n → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x0 v a w ↔ (tv (∑ j, a j • vecT (hv j))).left = w :=
  GlobalTheory.ChartCompare.comb_iff_sum t x0 (Equiv.refl _) (fun j => vecT (hv j)) a w

theorem bijective_of_unique {n : ℕ} {v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x0 (v j))
    (hb : ∀ w, IsTanAtG t x0 w → ∃! a : Fin n → S, IsCombAtG t x0 v a w) :
    Function.Bijective (Fintype.linearCombination S fun j => vecT (hv j)) := by
  rw [Function.bijective_iff_existsUnique]
  have key : ∀ (W : TanM x0 t.G) (a : Fin n → S), IsCombAtG t x0 v a (tv W).left ↔
      Fintype.linearCombination S (fun j => vecT (hv j)) a = W := fun W a => by
    rw [comb_iff t x0 hv, Fintype.linearCombination_apply]
    exact ⟨fun h => tanM_ext (Over.OverMorphism.ext h), fun h => by rw [h]⟩
  exact fun W => (existsUnique_congr (key W)).1 (hb _ (isTanAtG_of _ (tv_mem W)))

end Tangent

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem tan_free_away : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X) (p : PrimeSpectrum R), ∃ r ∉ p.asIdeal, ∃ (d : ℕ) (D : Fin d → TanM (spMap (algebraMap R (Localization.Away r)) ≫ x) t.G), LinearIndependent (Localization.Away r) D ∧ Submodule.span (Localization.Away r) (Set.range D) = ⊤ := by
  intro E _ _ _ H X t R _ x p
  haveI : Smooth t.G.hom := t.semi.smooth
  obtain ⟨U, hU, hxU, -, n, v₀, hv⟩ := GlobalTheory.exists_affine_lieBasis_baseChange X t.G (x p) ⊤ trivial
  obtain ⟨_, ⟨r, rfl⟩, hpr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := (x ⁻¹ᵁ U).1) hxU (x ⁻¹ᵁ U).2
  refine ⟨r, hpr, ?_⟩
  let R' := Localization.Away r
  let y : Sp R' ⟶ X := spMap (algebraMap R R') ≫ x
  have hrange : Set.range y ⊆ Set.range U.ι := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : PrimeSpectrum.comap (algebraMap R R') q ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range R' r]
      exact ⟨q, rfl⟩
    exact hsub this
  let g : Sp R' ⟶ U.toScheme := IsOpenImmersion.lift U.ι y hrange
  let f : Γ(X, U) ⟶ CommRingCat.of R' := Spec.preimage (g ≫ hU.isoSpec.hom)
  have heq : spMap f.hom ≫ hU.fromSpec = y := by
    have e1 : spMap f.hom = g ≫ hU.isoSpec.hom := Spec.map_preimage _
    rw [e1, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
    exact IsOpenImmersion.lift_fac _ _ _
  have hφ : IsGrpPullback ((Over.pullback y).obj t.G) t.G (spMap f.hom ≫ hU.fromSpec) (Limits.pullback.fst t.G.hom y) := by
    rw [heq]; exact isGrpPullback_pullback t.G y
  obtain ⟨v', -, hv'⟩ := hv R' f.hom _ _ hφ
  obtain ⟨tg, htg⟩ := GlobalTheory.ChartDataChecks.tanBasis_of_lieBasis t y v' hv'
  let e := Fintype.equivFin (Fin n)
  let tg' : Fin (Fintype.card (Fin n)) → (Sp (DualNumber R') ⟶ t.G.left) := fun i => tg (e.symm i)
  have hv1 : ∀ i, IsTanAtG t y (tg' i) := fun i => htg.1 _
  have hb : ∀ w, IsTanAtG t y w → ∃! b : Fin (Fintype.card (Fin n)) → R', IsCombAtG t y tg' b w := by
    intro w hw
    obtain ⟨a, ha, hu⟩ := htg.2 w hw
    refine ⟨fun i => a (e.symm i), ha, fun b hb' => ?_⟩
    have := hu (fun l => b (e l)) (by simpa only [e, Equiv.apply_symm_apply] using hb')
    funext i
    rw [← this]
    simp
  have bij := bijective_of_unique t y hv1 hb
  refine ⟨Fintype.card (Fin n), fun j => vecT (hv1 j),
    linearIndependent_iff_injective_fintypeLinearCombination.mpr bij.1, ?_⟩
  rw [← Fintype.range_linearCombination]
  exact LinearMap.range_eq_top.2 bij.2

end GlobalTheory.LieFreeAway
