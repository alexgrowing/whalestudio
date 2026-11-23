import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace WeierstrassCurve

namespace SmoothNeg

open HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem equation_neg {A : Type*} [CommRing A] {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : V.toProjective.Equation P) : V.toProjective.Equation (V.toProjective.neg P) := by
  rw [WeierstrassCurve.Projective.equation_iff] at h ⊢
  simp only [WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination h

theorem span_le_span_neg {A : Type*} [CommRing A] (V : WeierstrassCurve A) (P : Fin 3 → A) :
    Ideal.span (Set.range P) ≤ Ideal.span (Set.range (V.toProjective.neg P)) := by
  have h0 : P 0 ∈ Ideal.span (Set.range (V.toProjective.neg P)) := Ideal.subset_span ⟨0, rfl⟩
  have h2 : P 2 ∈ Ideal.span (Set.range (V.toProjective.neg P)) := Ideal.subset_span ⟨2, rfl⟩
  have h1 : -P 1 - V.a₁ * P 0 - V.a₃ * P 2 ∈ Ideal.span (Set.range (V.toProjective.neg P)) :=
    Ideal.subset_span ⟨1, rfl⟩
  have h1' : P 1 ∈ Ideal.span (Set.range (V.toProjective.neg P)) := by
    have : P 1 = -((-P 1 - V.a₁ * P 0 - V.a₃ * P 2) + V.a₁ * P 0 + V.a₃ * P 2) := by ring
    rw [this]
    exact neg_mem (add_mem (add_mem h1 (Ideal.mul_mem_left _ _ h0)) (Ideal.mul_mem_left _ _ h2))
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> assumption

theorem isUnimodularSol_neg {A : Type*} [CommRing A] {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : IsUnimodularSol V P) : IsUnimodularSol V (V.toProjective.neg P) :=
  ⟨equation_neg h.equation, top_le_iff.mp (h.span_eq_top.ge.trans (span_le_span_neg V P))⟩

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

def negCoord : Fin 3 → HomRing W := (W.map (algebraMap R (HomRing W))).toProjective.neg (coord W)

theorem negCoord_mem (i : Fin 3) : negCoord W i ∈ grading W 1 := by
  fin_cases i
  · exact coord_mem W 0
  · change -coord W 1 - algebraMap R _ W.a₁ * coord W 0 - algebraMap R _ W.a₃ * coord W 2 ∈ _
    rw [← Algebra.smul_def, ← Algebra.smul_def]
    exact sub_mem (sub_mem (neg_mem (coord_mem W 1)) (Submodule.smul_mem _ _ (coord_mem W 0)))
      (Submodule.smul_mem _ _ (coord_mem W 2))
  · exact coord_mem W 2

def negRingHom : HomRing W →+* HomRing W :=
  evalHom W (algebraMap R (HomRing W)) (negCoord W) (equation_neg (equation_coord W))

def negGraded : grading W →+*ᵍ grading W where
  toRingHom := negRingHom W
  map_mem := by
    rintro n _ ⟨p, hp, rfl⟩
    have hp' : p.IsHomogeneous n := hp
    change MvPolynomial.eval₂ (algebraMap R (HomRing W)) (negCoord W) p ∈ _
    rw [MvPolynomial.eval₂_eq]
    refine Submodule.sum_mem _ fun d hd => ?_
    rw [← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    have := SetLike.prod_pow_mem_graded (grading W) (fun _ => 1) (negCoord W) (F := d.support) d
      (fun i _ => negCoord_mem W i)
    rw [hp'.degree_eq_sum_deg_support hd]
    simpa using this

theorem irrelevant_le_map_negGraded :
    irrelevant (grading W) ≤ (irrelevant (grading W)).map (negGraded W) := by
  rw [← toIdeal_le_toIdeal_iff, irrelevant_eq_span_coord]
  refine (span_le_span_neg (W.map (algebraMap R (HomRing W))) (coord W)).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have : (W.map (algebraMap R (HomRing W))).toProjective.neg (coord W) i =
      negGraded W (coord W i) :=
    (evalHom_coord W (algebraMap R (HomRing W)) (negCoord W)
      (equation_neg (equation_coord W)) i).symm
  rw [this]
  exact Ideal.mem_map_of_mem (negGraded W) (mem_irrelevant_of_mem _ one_pos (coord_mem W i))

def negMap : scheme W ⟶ scheme W := Proj.map (negGraded W) (irrelevant_le_map_negGraded W)

@[reassoc]
theorem ptHom_negMap {A : Type} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) :
    ptHom W ρ P hP ≫ negMap W = ptHom W ρ _ (isUnimodularSol_neg hP) := by
  refine (ProjPoint.ofHom_map (negGraded W) (irrelevant_le_map_negGraded W) _
    (map_irrelevant_evalHom W hP)).trans ?_
  have : (evalHom W ρ P hP.equation).comp (negGraded W).toRingHom =
      evalHom W ρ _ (isUnimodularSol_neg hP).equation := by
    refine homRing_hom_ext W (fun r => ?_) (fun i => ?_)
    · refine (congrArg (evalHom W ρ P hP.equation) (evalHom_algebraMap W _ (negCoord W)
        (equation_neg (equation_coord W)) r)).trans ?_
      rw [evalHom_algebraMap, evalHom_algebraMap]
    refine (congrArg (evalHom W ρ P hP.equation) (evalHom_coord W _ (negCoord W)
      (equation_neg (equation_coord W)) i)).trans ?_
    rw [evalHom_coord]
    fin_cases i
    · exact evalHom_coord W ρ P hP.equation 0
    · change evalHom W ρ P hP.equation
        (-coord W 1 - algebraMap R _ W.a₁ * coord W 0 - algebraMap R _ W.a₃ * coord W 2) =
        -P 1 - ρ W.a₁ * P 0 - ρ W.a₃ * P 2
      simp only [map_sub, map_neg, map_mul, evalHom_coord, evalHom_algebraMap]
    · exact evalHom_coord W ρ P hP.equation 2
  simp only [this]
  rfl

theorem negMap_toSpec : negMap W ≫ toSpec W = toSpec W := by
  apply scheme_hom_ext
  · rw [chartY, pt_eq_ptHom, ptHom_negMap_assoc, ptHom_toSpec, ptHom_toSpec]
  · rw [chartZ, pt_eq_ptHom, ptHom_negMap_assoc, ptHom_toSpec, ptHom_toSpec]

theorem range_subset_of_forall_field {T Y : Scheme.{0}} (f : T ⟶ Y) (U : Y.Opens)
    (h : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), ⊤ ≤ (x ≫ f) ⁻¹ᵁ U) :
    Set.range f ⊆ Set.range U.ι := by
  rintro _ ⟨t, rfl⟩
  have := h (T.residueField t) (T.fromSpecResidueField t)
    (Set.mem_univ (IsLocalRing.closedPoint (T.residueField t)))
  rw [Scheme.Opens.range_ι]
  have e : (T.fromSpecResidueField t ≫ f) (IsLocalRing.closedPoint (T.residueField t)) = f t :=
    (Scheme.Hom.comp_apply _ _ _).trans (congrArg f (Scheme.fromSpecResidueField_apply t _))
  rw [← e]
  exact this

end SmoothNeg

open SmoothNeg in

theorem exists_neg_origin_smoothLocus :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R) (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → ∃ (neg : (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (o : 𝟙_ _ ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))), o.left ≫ U.ι = GlobalTheory.WeierstrassCurve.zero W ∧ ∀ (k : Type) [Field k] (ρ : R →+* k) (x : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.neg P), (x ≫ neg).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h := by
  intro R _ _ _ W U hU
  have hneg : Set.range (U.ι ≫ negMap W) ⊆ Set.range U.ι := by
    refine range_subset_of_forall_field _ U fun k _ x => ?_
    obtain ⟨ρ, hρ⟩ := Spec.map_surjective (x ≫ U.ι ≫ toSpec W)
    obtain ⟨P, hP, e⟩ := exists_eq_ptHom W ρ.hom (x ≫ U.ι) (by simpa using hρ.symm)
    have hns : (W.map ρ.hom).toProjective.Nonsingular P := by
      rw [← hU k ρ.hom P hP, ← e]
      intro y _
      simp
    rw [← Category.assoc, e, ptHom_negMap, hU]
    exact WeierstrassCurve.Projective.nonsingular_neg hns
  have hzero : Set.range (zero W) ⊆ Set.range U.ι := by
    refine range_subset_of_forall_field _ U fun k _ x => ?_
    obtain ⟨ρ, rfl⟩ := Spec.map_surjective x
    have := SpecMap_zero W ρ.hom
    rw [CommRingCat.ofHom_hom] at this
    rw [this, hU]
    exact WeierstrassCurve.Projective.nonsingular_zero
  refine ⟨Over.homMk (IsOpenImmersion.lift U.ι (U.ι ≫ negMap W) hneg) ?_,
    Over.homMk (IsOpenImmersion.lift U.ι (zero W) hzero) ?_, ?_, ?_⟩
  · change IsOpenImmersion.lift U.ι (U.ι ≫ negMap W) hneg ≫ U.ι ≫ toSpec W = U.ι ≫ toSpec W
    rw [IsOpenImmersion.lift_fac_assoc, Category.assoc, negMap_toSpec]
  · change IsOpenImmersion.lift U.ι (zero W) hzero ≫ U.ι ≫ toSpec W = 𝟙 _
    rw [IsOpenImmersion.lift_fac_assoc, zero_toSpec]
  · exact IsOpenImmersion.lift_fac _ _ _
  · intro k _ ρ x P hP e
    refine ⟨isUnimodularSol_neg hP, ?_⟩
    change (x.left ≫ IsOpenImmersion.lift U.ι (U.ι ≫ negMap W) hneg) ≫ U.ι = _
    rw [Category.assoc, IsOpenImmersion.lift_fac, ← ptHom_negMap W ρ P hP, ← e]
    exact (Category.assoc _ _ _).symm

end WeierstrassCurve

end GlobalTheory
