import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.QCoh (pullbackSections)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap dualScale)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM

theorem cotMap_list_prod {S : Scheme.{0}} {T G : Over S} [GrpObj G] [QuasiSeparated G.hom] {s : 𝟙_ (Over S) ⟶ T} :
    ∀ {m : ℕ} (z : Fin m → (T ⟶ G)) (hz : ∀ i, s ≫ z i = η) (h : s ≫ (List.ofFn z).prod = η),
      cotMap (List.ofFn z).prod h = ∑ i, cotMap (z i) (hz i)
  | 0, z, hz, h => by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact cotMap_eq_zero (by rw [List.ofFn_zero, List.prod_nil, Hom.one_def]) _
  | m + 1, z, hz, h => by
    have e : (List.ofFn z).prod = z 0 * (List.ofFn fun i : Fin m => z i.succ).prod := by
      rw [List.ofFn_succ, List.prod_cons]
    have h₁ : (η : 𝟙_ (Over S) ⟶ G) = 1 := by rw [Hom.one_def]; simp
    have h' : s ≫ (List.ofFn fun i : Fin m => z i.succ).prod = η := by
      have := h
      rw [e, MonObj.comp_mul, hz 0, h₁, _root_.one_mul] at this
      exact this.trans h₁.symm
    rw [Fin.sum_univ_succ, ← cotMap_list_prod (fun i : Fin m => z i.succ) (fun i => hz _) h',
      ← cotMap_mul (hz 0) h' (e ▸ h)]
    congr 1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
variable {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X}
variable {G' : Over (Sp k)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}

theorem exists_fibre_vector (hp : IsGrpPullback G' t.G x φ) {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    ∃ y : specO k (DualNumber k) ⟶ G', epsZero k ≫ y = η ∧ y.left ≫ φ = v := by
  refine ⟨Over.homMk (hp.1.lift v _ hv.1) (hp.1.lift_snd _ _ _), Over.OverMorphism.ext (hp.1.hom_ext ?_ ?_),
    hp.1.lift_fst _ _ _⟩
  · refine (Category.assoc _ _ _).trans ((congrArg (sec (epsZero k) ≫ ·) (hp.1.lift_fst _ _ _)).trans ?_)
    exact (epsZero_comp_of_isTanAtG t hv).trans (unitSec_comp hp).symm
  · exact (Over.w _).trans (Over.w _).symm

theorem tanForm_eq_fibre (hp : IsGrpPullback G' t.G x φ) {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v)
    {y : specO k (DualNumber k) ⟶ G'} (hy : epsZero k ≫ y = η) (e : y.left ≫ φ = v) :
    tanForm t hv = omegaBase hp ≫ cotMap y hy ≫ (epsIso k).hom := by
  refine Eq.trans (congrArg (· ≫ (epsIso k).hom) ?_) (Category.assoc _ _ _)
  refine pullback_hom_ext (sec_hom η[t.G]) fun W a => ?_
  have k₁ := le_of_sq (unitSec_comp hp) (le_refl (unitSec t.G ⁻¹ᵁ W)) le_rfl
  have k₂ := le_of_sq (epsZero_comp_of_isTanAtG t hv) (le_refl (unitSec t.G ⁻¹ᵁ W)) le_rfl
  have k₃ := (le_preimage_of_comp e).2 (le_refl (v ⁻¹ᵁ W))
  refine (baseMap_d (sec_hom η[t.G]) (sec_hom (epsZero k)) hv.1 (epsZero_comp_of_isTanAtG t hv) le_rfl le_rfl
    k₂ le_rfl a).trans (Eq.symm ?_)
  refine (congrArg ((cotMap y hy).app _) (omegaBase_dUnit hp le_rfl le_rfl k₁ le_rfl a)).trans ?_
  exact (cotMap_d y hy k₁ k₂ k₃ _).trans (congrArg _ (appLE_appLE e _ _ _ a))

theorem tanEv_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V),
    ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i)) (cf : Fin m → k)
      (w : Sp (DualNumber k) ⟶ t.G.left) (hw : IsTanAtG t x w), IsCombAtG t x v cf w →
      ∀ s : Γ(GlobalTheory.LieVB.omega t.G, V), tanEv t hw h s = ∑ i, cf i * tanEv t (hv i) h s := by
  rintro E _ _ _ H X t k _ x V h m v hv cf w hw ⟨u, hu, hw'⟩ s
  have hp := isGrpPullback_pullback t.G x
  have := t.semi
  have : QuasiSeparated ((Over.pullback x).obj t.G).hom := MorphismProperty.of_isPullback hp.1 inferInstance
  choose y hy ey using fun i => exists_fibre_vector t hp (hv i)
  obtain ⟨yw, hyw, eyw⟩ := exists_fibre_vector t hp hw
  let z := fun i => ptMap (dualScale (cf i)) ≫ y i
  have hz (i : Fin m) : epsZero k ≫ z i = η := by
    rw [← Category.assoc, epsZero_dualScale, hy]
  have hu' : u = fun i => pushHom hp _ (z i) := funext fun i => Over.OverMorphism.ext <| by
    refine (hu i).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    rw [ey]
    rfl
  have hprod : yw = (List.ofFn z).prod := by
    refine Over.OverMorphism.ext (hp.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    refine eyw.trans (hw'.symm.trans ?_)
    rw [hu']
    exact (congrArg (fun q => q.left) ((map_list_prod (pushHom hp (specO k (DualNumber k))) (List.ofFn z)).trans
      (congrArg List.prod List.map_ofFn))).symm
  subst hprod
  let σ := (omegaBase hp).app ⊤ (pullbackSections x (omega t.G) h s)
  let F : (conormal (unitSec ((Over.pullback x).obj t.G)) ⟶ conormal (sec (epsZero k))) →+ k :=
    AddMonoidHom.mk' (fun α => (Scheme.ΓSpecIso (.of k)).hom ((epsIso k).hom.app ⊤ (α.app ⊤ σ))) fun α β =>
      (congrArg (Scheme.ΓSpecIso (.of k)).hom (map_add ((epsIso k).hom.app ⊤).hom (α.app ⊤ σ) (β.app ⊤ σ))).trans
        (map_add _ _ _)
  have hF {v' : Sp (DualNumber k) ⟶ t.G.left} (hv' : IsTanAtG t x v') {y'} (hy' : epsZero k ≫ y' = η)
      (e : y'.left ≫ pullback.fst t.G.hom x = v') : tanEv t hv' h s = F (cotMap y' hy') := by
    rw [tanEv, tanForm_eq_fibre t hp hv' hy' e]
    rfl
  rw [hF hw hyw eyw, cotMap_list_prod z hz, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := cotMap_comp (hy i) (epsZero_dualScale (cf i)) rfl (hz i)
  rw [cotMap_dualScale] at e
  rw [hF (hv i) (hy i) (ey i), ← e]
  refine (congrArg (Scheme.ΓSpecIso (.of k)).hom
    ((epsIso k).hom.app_smul (cst k (cf i)) ((cotMap (y i) (hy i)).app ⊤ σ))).trans ?_
  refine (map_mul _ _ _).trans ?_
  rw [Iso.inv_hom_id_apply]
  rfl

end GlobalTheory.LocM
