import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.WitnessIsFormalParam

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiePull

set_option maxHeartbeats 800000 in

theorem exists_lieBasis_of_tanBasis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
    (t : SAB H X0) {K : Type} [CommRing K] (x0 : Sp K ⟶ X0) (A : Over (Sp K)) [GrpObj A] (θ : A.left ⟶ t.G.left)
    (hθ : IsGrpPullback A t.G x0 θ) {m : ℕ} (u : Fin m → (Sp (DualNumber K) ⟶ t.G.left))
    (hu : ∀ j, IsTanAtG t x0 (u j)) (hc : ∀ w, IsTanAtG t x0 w → ∃! c : Fin m → K, IsCombAtG t x0 u c w) :
    ∃ v : Fin m → (epsR K ⟶ A), IsLieBasis v ∧ ∀ j, (v j).left ≫ θ = u j := by
  classical
  let up : ∀ w : Sp (DualNumber K) ⟶ t.G.left, w ≫ t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x0 →
      (epsR K ⟶ A) := fun w h => Over.homMk (hθ.1.lift w _ h) (hθ.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ θ = w := fun w h => hθ.1.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp K)} {a b : T ⟶ A}, a.left ≫ θ = b.left ≫ θ → a = b := fun h =>
    Over.OverMorphism.ext (hθ.1.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp K), (1 : T ⟶ A).left ≫ θ = (1 : Over.mk (T.hom ≫ x0) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hθ T))
  have tan : ∀ w : epsR K ⟶ A, IsTangent w ↔ IsTanAtG t x0 (w.left ≫ θ) := fun w => by
    have e : (1 : Chart.sp (R₀ := K) K ⟶ A).left ≫ θ = (1 : Over.mk x0 ⟶ t.G).left :=
      (one _).trans (congrArg (· ≫ (η[t.G]).left) (show Spec.map (CommRingCat.ofHom (RingHom.id K)) ≫ x0 = x0 by simp))
    rw [← Chart.isTan_iff]
    refine ⟨fun h => ⟨Over.w (pushPt hθ.1.w w), ?_⟩, fun h => inj ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ θ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
  have pr : ∀ {n} (a : Fin n → (epsR K ⟶ A)), (List.ofFn a).prod.left ≫ θ =
      (List.ofFn fun i => (pushPt hθ.1.w (a i) : tEpsG x0 ⟶ t.G)).prod.left := fun a =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hθ (epsR K)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → K) (v : Fin n → (epsR K ⟶ A)) w,
      IsLieComb c v w ↔ IsCombAtG t x0 (fun i => (v i).left ≫ θ) c (w.left ≫ θ) := fun c v w => by
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨fun i => pushPt hθ.1.w (a i), fun i => (congrArg (· ≫ θ) (ha i)).trans (Category.assoc _ _ _), (pr a).symm⟩
    · rintro ⟨a, ha, hw⟩
      refine ⟨fun i => up (a i).left (Over.w _), fun i => hθ.1.hom_ext ?_ ?_, inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((ha i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (a i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (Over.w (Chart.spMap (Chart.scaleD (c i)))).symm
      · have : a = fun i => (pushPt hθ.1.w (up (a i).left (Over.w _)) : tEpsG x0 ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (a i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x0 ⟶ t.G) => (List.ofFn q).prod.left) this
  let v : Fin m → (epsR K ⟶ A) := fun j => up (u j) (hu j).1
  have hv : (fun i => (v i).left ≫ θ) = u := funext fun j => hup _ _
  refine ⟨v, ⟨fun j => (tan _).2 (by rw [hup]; exact hu j), fun w hw => ?_⟩, fun j => hup _ _⟩
  have key : ∀ c, IsLieComb c v w ↔ IsCombAtG t x0 u c (w.left ≫ θ) := fun c => by
    rw [comb, hv]
  obtain ⟨c, hc1, hc2⟩ := hc _ ((tan w).1 hw)
  exact ⟨c, (key c).2 hc1, fun c' h' => hc2 c' ((key c').1 h')⟩

theorem lieBasis_of_tanBasis : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X0 : Scheme.{0}} (t : ReciprocityTheory.ChartRestriction.G.Geo.Tor.SAB H X0) {K : Type} [CommRing K] (x0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ X0) (A : Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (θ : A.left ⟶ t.G.left), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A t.G x0 θ → ∀ {m : ℕ} (u : Fin m → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ t.G.left)), (∀ j, Formalism.L2.Pj.IsTanAtG t x0 (u j)) → (∀ w, Formalism.L2.Pj.IsTanAtG t x0 w → ∃! c : Fin m → K, Formalism.L2.Pj.IsCombAtG t x0 u c w) → ∃ v : Fin m → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR K ⟶ A), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v ∧ ∀ j, (v j).left ≫ θ = u j :=
  by
  intro E _ _ _ H X0 t K _ x0 A _ θ hθ m u hu hc
  exact exists_lieBasis_of_tanBasis t x0 A θ hθ u hu hc

end GlobalTheory.LiePull
