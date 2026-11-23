import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdryUnit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates

theorem exists_eigEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {O : Type} [CommRing O] {a : OAct O G} {a' : OAct O G'}
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {R : Type} [CommRing R] (x : Sp R ⟶ S')
    (x' : Sp R ⟶ S) (hx : x' = x ≫ f) :
    ∃ e : (epsAt x ⟶ G') ≃ (epsAt x' ⟶ G), (∀ v, (e v).left = v.left ≫ φ) ∧
      ∀ (χ : O →+* R) (n : ℕ) (v : Fin n → (epsAt x ⟶ G')),
        IsEigenBasis a' x χ v ↔ IsEigenBasis a x' χ (fun i => e (v i)) := by
  subst hx
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsAt x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp
  have hR : ∀ (c : R) (u v : epsAt x ⟶ G'), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (epsScaleR c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc c))
  refine ⟨e.toEquiv, he, fun χ n v => ?_⟩
  have hP : ∀ v : epsAt x ⟶ G', IsEigenTangent a' x χ v ↔ IsEigenTangent a (x ≫ f) χ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ G')).symm
      refine (congrArg (spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ·) (Over.w v)).trans ?_
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
    · have E : e (v ≫ a'.act c) = e v ≫ a.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
      rw [hR, E]
  have pr : ∀ u : Fin n → (epsAt x ⟶ G'), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  have hC : ∀ (c : Fin n → R) (w : epsAt x ⟶ G'), IsCombination x c (fun i => (v i).left) w ↔
      IsCombination (x ≫ f) c (fun i => (e (v i)).left) (e w) := fun c w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
      rw [pr, hw]
      simp
  refine and_congr (forall_congr' fun i => hP _) (Iff.trans ?_ e.surjective.forall.symm)
  exact forall_congr' fun w => imp_congr (hP w) (existsUnique_congr fun c => hC c w)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_eigenBasis_sameVec (Y : Model Xo c (RingHom.id c.F)) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n) :
    ∃ v : Fin n → (epsAt ((ptF y ≫ Y.jQ) ≫ pullback.fst _ _) ⟶ Y.t.G),
      IsEigenBasis Y.t.act _ (chr c τ (algebraMap c.F S)) v ∧
      ∀ i : Fin n, ∃ j : Fin (Dw.mult τ), (j : ℕ) = i ∧ SameVec Y y (y.u τ j) (v i).left := by
  subst hn
  obtain ⟨e₀, he₀, hb₀⟩ := exists_eigEquiv Y.m0.toSABMap.cart Y.m0.toSABMap.act (ptF y) y.x
    (pullback.lift_fst _ _ _).symm
  obtain ⟨e, he, hb⟩ := exists_eigEquiv Y.m.cart Y.m.act (ptF y) ((ptF y ≫ Y.jQ) ≫ pullback.fst _ _)
    (Category.assoc _ _ _)
  let u : Fin (Dw.mult τ) → (epsAt y.x ⟶ Xo.univ.t.G) := fun i => Over.homMk (y.u τ i) (y.tan τ i).1
  have hu : IsEigenBasis Xo.univ.t.act y.x (chr c τ (algebraMap c.F S)) u := by
    refine ⟨fun i => ⟨(y.tan τ i).2, fun a => y.eig τ i a⟩, fun w hw => ?_⟩
    refine (existsUnique_congr fun a => ⟨?_, ?_⟩).1 (y.basis τ w.left ⟨Over.w w, hw.1⟩ fun a => hw.2 a)
    · rintro ⟨u', h1, h2⟩
      exact ⟨u', h1, Over.OverMorphism.ext h2.symm⟩
    · rintro ⟨u', h1, h2⟩
      exact ⟨u', h1, congrArg (fun z => z.left) h2.symm⟩
  have hw := (hb₀ (chr c τ (algebraMap c.F S)) _ fun i => e₀.symm (u i)).2
    ((funext fun i => e₀.apply_symm_apply (u i) : (fun i => e₀ (e₀.symm (u i))) = u).symm ▸ hu)
  refine ⟨fun i => e (e₀.symm (u i)), (hb _ _ _).1 hw, fun i => ⟨i, rfl, (e₀.symm (u i)).left,
    ⟨Over.w _, (hw.1 i).1⟩, ?_, (he _).symm⟩⟩
  rw [← he₀, Equiv.apply_symm_apply]
  rfl

theorem exists_matches (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (τ : Psi H) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) (hy : ∀ s, ptF y s ∈ (V : Set (Xo.XF c))) :
    ∃ a : Framed Y V τ.1 S (algebraMap c.F S), Matches Y V τ y a := by
  obtain ⟨v, hv, ev⟩ := exists_eigenBasis_sameVec Y y τ.1 Dw.p (if_pos τ.2)
  obtain ⟨w, hw, ew⟩ := exists_eigenBasis_sameVec Y y (conjEmb τ.1) Dw.q (if_neg (conj_not_mem τ))
  refine ⟨⟨ptF y ≫ Y.jQ, by rw [Category.assoc, Y.jQ_over]; exact pullback.lift_snd _ _ _, ?_, v, w, hv, hw⟩,
    rfl, ev, ew⟩
  rintro _ ⟨z, rfl⟩
  exact subset_closure ⟨ptF y z, hy z, by simp⟩

end GlobalTheory.BdryUnit
