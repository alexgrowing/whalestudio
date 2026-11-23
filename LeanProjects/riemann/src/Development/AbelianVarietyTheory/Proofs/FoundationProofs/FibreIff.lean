import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAbelianGaloisHost
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GeometricComponentEmbedding
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.RamifiedPlacesSplitEigen

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FlatRow

section Lie

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S} {A : Over (Sp R)} [GrpObj A]
  {φ : A.left ⟶ G.left} {m : ℕ}

theorem exists_lift (h : IsGrpPullback A G x φ) (u : FramedFlatCoordinates.epsAt x ⟶ G) :
    ∃ v : epsR R ⟶ A, v.left ≫ φ = u.left :=
  let ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  ⟨e.symm u, by rw [← he, e.apply_symm_apply]⟩

theorem fibre_iff (h : IsGrpPullback A G x φ) {v : Fin m → (epsR R ⟶ A)} {u : Fin m → (FramedFlatCoordinates.epsAt x ⟶ G)}
    (hu : ∀ i, (v i).left ≫ φ = (u i).left) :
    (∀ (c : Fin m → R) (w : epsR R ⟶ A) (w' : FramedFlatCoordinates.epsAt x ⟶ G), w.left ≫ φ = w'.left →
      (IsLieComb c v w ↔ FramedFlatCoordinates.IsCombination x c (fun i => (u i).left) w')) ∧
    ∀ {O : Type} [CommRing O] {a : OAct O A} {b : OAct O G}, (∀ c, (a.act c).left ≫ φ = φ ≫ (b.act c).left) →
      ∀ χ : O →+* R, EigenvectorLieDegree.IsEigBasis a χ v ↔ FramedFlatCoordinates.IsEigenBasis b x χ u := by
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _).symm
  obtain rfl : u = fun i => e (v i) := funext fun i => Over.OverMorphism.ext ((hu i).symm.trans (he _).symm)
  have one : (1 : Over.mk x ⟶ G).left = η[A].left ≫ φ := by
    rw [← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp
  have hR : ∀ (c : R) (u v : epsR R ⟶ A), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (epsScaleR c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    exact (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans (sc c)
  have pr : ∀ u : Fin m → (epsR R ⟶ A), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  have hC : ∀ (c : Fin m → R) (w : epsR R ⟶ A),
      IsLieComb c v w ↔ FramedFlatCoordinates.IsCombination x c (fun i => (e (v i)).left) (e w) := fun c w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
      rw [pr, hw]
      simp
  refine ⟨fun c w w' hw => ?_, fun {O} _ a b hab χ => ?_⟩
  · obtain rfl : w' = e w := Over.OverMorphism.ext (hw.symm.trans (he _).symm)
    exact hC c w
  have hP : ∀ v : epsR R ⟶ A, EigenvectorLieDegree.IsEigVec a χ v ↔ FramedFlatCoordinates.IsEigenTangent b x χ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he, IsTangent]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w η[A]).symm
      exact (congrArg (spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ·) (Over.w v)).trans fs
    · have E : e (v ≫ a.act c) = e v ≫ b.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hab, Category.assoc])
      rw [hR, E]
  refine and_congr (forall_congr' fun i => hP _) (Iff.trans ?_ e.surjective.forall.symm)
  exact forall_congr' fun w => imp_congr (hP w) (existsUnique_congr fun c => hC c w)

end Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

def EigStable {S : Scheme.{0}} (T : SAB H S) (c : Coeff l) : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (j : c.F →+* R) (x : Sp R ⟶ S) (τ : E →+* ℂ) (m : ℕ)
    (v : Fin m → (FramedFlatCoordinates.epsAt x ⟶ T.G)) (v' : Fin m → (FramedFlatCoordinates.epsAt (spMap g ≫ x) ⟶ T.G)),
    FramedFlatCoordinates.IsEigenBasis T.act x (FramedFlatCoordinates.chr c τ j) v →
    (∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left) →
    FramedFlatCoordinates.IsEigenBasis T.act (spMap g ≫ x) (FramedFlatCoordinates.chr c τ (g.comp j)) v'

variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : (Xo.XF c).Opens} {τ : E →+* ℂ}

def IsSqNorm (sig : FramedFlatCoordinates.Rule Y U τ) (s : c.F →+* ℂ) (κ : ℝ) : Prop :=
  ∃ (a : FramedFlatCoordinates.Framed Y U τ ℂ s) (y : Sp ℂ ⟶ Xo.XF c) (t : SAB H (Sp ℂ)) (v : Fin Dw.p → (epsR ℂ ⟶ t.G))
    (w : Fin Dw.q → (epsR ℂ ⟶ t.G)) (g : ℕ) (u : HolUnif t.G t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ)
    (zv : Fin Dw.p → Fin g → ℂ) (zw : Fin Dw.q → Fin g → ℂ),
    LiesOver a y ∧ IsFibre a t v w ∧ u.IsAH Hm χ ∧ (∀ i, u.IsDiff (zv i) (v i)) ∧ (∀ i, u.IsDiff (zw i) (w i)) ∧
    0 < EigenbasisGramSquares.gramSq Hm zv ∧ 0 < EigenbasisGramSquares.gramSq Hm zw ∧
    κ = ‖sig ℂ s a‖ ^ 2 * (EigenbasisGramSquares.gramSq Hm zv / EigenbasisGramSquares.gramSq Hm zw)

def IsValue (sig : FramedFlatCoordinates.Rule Y U τ) {ℓ : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] (i : K →+* ℂ_[ℓ]) (φ : c.F →+* K)
    (x : ℝ) : Prop :=
  ∃ (V : ValuationSubring K) (a : FramedFlatCoordinates.Framed Y U τ K φ) (y : Sp K ⟶ Xo.XF c) (t : SAB H (Sp K))
    (v : Fin Dw.p → (epsR K ⟶ t.G)) (w : Fin Dw.q → (epsR K ⟶ t.G)) (𝒢 : Over (Sp V)) (_ : GrpObj 𝒢)
    (b : OAct (𝓞 E) 𝒢) (ψ : t.G.left ⟶ 𝒢.left) (χ χ' : 𝓞 E →+* V) (u : Fin Dw.p → (epsR V ⟶ 𝒢))
    (u' : Fin Dw.q → (epsR V ⟶ 𝒢)),
    (∀ z : K, z ∈ V ↔ ‖i z‖ ≤ 1) ∧ LiesOver a y ∧ IsFibre a t v w ∧ IsSemiAbelian 𝒢 ∧
    IsGrpPullback t.G 𝒢 (spMap (algebraMap V K)) ψ ∧ (∀ z, (t.act.act z).left ≫ ψ = ψ ≫ (b.act z).left) ∧
    (algebraMap V K).comp χ = FramedFlatCoordinates.chr c τ φ ∧ (algebraMap V K).comp χ' = FramedFlatCoordinates.chr c (conjEmb τ) φ ∧
    EigenvectorLieDegree.IsEigBasis b χ u ∧ EigenvectorLieDegree.IsEigBasis b χ' u' ∧ (∀ k, IsVecOver (algebraMap V K) ψ (u k) (v k)) ∧
    (∀ k, IsVecOver (algebraMap V K) ψ (u' k) (w k)) ∧ ‖i (sig K φ a)‖ = (ℓ : ℝ) ^ (-x)

end GlobalTheory.FlatRow
