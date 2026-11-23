import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FlagEmb
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagEmb.Stab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X0 : Scheme.{0}}
  (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

set_option maxHeartbeats 800000 in

theorem basis_of_lieBasis {n : ℕ} (v : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)) (hB : IsLieBasis v) :
    (∀ j, IsTanAtG t x0 ((v j).left ≫ pullback.fst t.G.hom x0)) ∧ ∀ w, IsTanAtG t x0 w →
      ∃! a : Fin n → S, IsCombAtG t x0 (fun j => (v j).left ≫ pullback.fst t.G.hom x0) a w := by
  classical
  have hp := isGrpPullback_pullback t.G x0
  let φ := pullback.fst t.G.hom x0
  let up : ∀ w : Sp (DualNumber S) ⟶ t.G.left, w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x0 →
      (epsR S ⟶ (Over.pullback x0).obj t.G) := fun w h => Over.homMk (pullback.lift w _ h) (pullback.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => pullback.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ (Over.pullback x0).obj t.G}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (pullback.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk (T.hom ≫ x0) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have tan : ∀ w : epsR S ⟶ (Over.pullback x0).obj t.G, IsTangent w ↔ IsTanAtG t x0 (w.left ≫ φ) := fun w => by
    have e : (1 : Chart.sp (R₀ := S) S ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk x0 ⟶ t.G).left :=
      (one _).trans (congrArg (· ≫ (η[t.G]).left) (show Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ x0 = x0 by simp))
    rw [← Chart.isTan_iff]
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => inj ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEpsG x0 ⟶ t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)) w,
      IsLieComb c v w ↔ IsCombAtG t x0 (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => pullback.hom_ext ?_ ?_, inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (Over.w (Chart.spMap (Chart.scaleD (c i)))).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEpsG x0 ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x0 ⟶ t.G) => (List.ofFn q).prod.left) this
  refine ⟨fun l => (tan _).1 (hB.1 _), fun w hw => ?_⟩
  obtain ⟨c, hc, hu⟩ := hB.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))
  refine ⟨c, ?_, fun a ha => ?_⟩
  · have := (comb _ _ _).1 hc
    rw [hup] at this
    exact this
  · exact hu a ((comb _ _ _).2 (by rw [hup]; exact ha))

theorem dualMapR_eq {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f = Formalism.L2.Pj.dualMap f := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, Formalism.L2.Pj.dualMap]

theorem spMap_dualMapR_id (R : Type) [CommRing R] :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (RingHom.id R)) = 𝟙 _ := by
  have : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (RingHom.id R) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  rw [this]
  exact Spec.map_id _

theorem exists_stabBasis (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (x : X) :
    ∃ (U : X.affineOpens) (n : ℕ) (v : Fin n → Tn t Γ(X, U.1)), x ∈ U.1 ∧ StabBasis t U.2.fromSpec v := by
  have := t.semi.smooth
  obtain ⟨U, hU, hxU, -, n, v₀, hv⟩ := GlobalTheory.exists_affine_lieBasis_baseChange X t.G x ⊤ trivial
  have key : ∀ (R' : Type) [CommRing R'] (φ : Γ(X, U) →+* R'),
      (∀ j, IsTanAtG t (spMap φ ≫ hU.fromSpec) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR φ) ≫ v₀ j)) ∧
        ∀ w, IsTanAtG t (spMap φ ≫ hU.fromSpec) w → ∃! a : Fin n → R', IsCombAtG t (spMap φ ≫ hU.fromSpec)
          (fun j => spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR φ) ≫ v₀ j) a w := fun R' _ φ => by
    obtain ⟨v', h1, h2⟩ := hv R' φ _ _ (isGrpPullback_pullback t.G (spMap φ ≫ hU.fromSpec))
    have h := basis_of_lieBasis t (spMap φ ≫ hU.fromSpec) v' h2
    have e : (fun j => (v' j).left ≫ pullback.fst t.G.hom (spMap φ ≫ hU.fromSpec)) =
        fun j => spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR φ) ≫ v₀ j := funext h1
    refine ⟨fun j => h1 j ▸ h.1 j, fun w hw => e ▸ h.2 w hw⟩
  refine ⟨⟨U, hU⟩, n, v₀, hxU, fun j => ?_, fun R' _ φ w hw => ?_⟩
  · have h := (key _ (RingHom.id _)).1 j
    have e : spMap (RingHom.id Γ(X, U)) = 𝟙 _ := Spec.map_id _
    rw [spMap_dualMapR_id, e, Category.id_comp, Category.id_comp] at h
    exact h
  · have h := (key R' φ).2 w hw
    rw [dualMapR_eq] at h
    exact h

end GlobalTheory.FlagEmb.Stab
