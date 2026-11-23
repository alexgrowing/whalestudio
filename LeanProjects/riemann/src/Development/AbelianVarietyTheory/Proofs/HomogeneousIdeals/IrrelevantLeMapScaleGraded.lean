import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsUnimodularSolTriple
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomExtOfLocalRingPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveFst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

noncomputable section

namespace GlobalTheory.WeightScale

open HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) {u : R} (hu : IsUnit u)
  (hW : curve u W = W)

def scaledCoord (u : R) : Fin 3 → HomRing W := triple (algebraMap R _ u) (coord W)

theorem scaledCoord_mem (u : R) (i : Fin 3) : scaledCoord W u i ∈ grading W 1 := by
  fin_cases i
  · change algebraMap R _ u ^ 2 * coord W 0 ∈ _
    rw [← map_pow, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (coord_mem W 0)
  · change algebraMap R _ u ^ 3 * coord W 1 ∈ _
    rw [← map_pow, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (coord_mem W 1)
  · exact coord_mem W 2

include hW in
theorem equation_scaledCoord :
    (W.map (algebraMap R (HomRing W))).toProjective.Equation (scaledCoord W u) := by
  have := equation_triple (algebraMap R (HomRing W) u) (V := W.map (algebraMap R (HomRing W)))
    (equation_coord W)
  rwa [curve_map_eq _ hW] at this

def scaleGraded : grading W →+*ᵍ grading W where
  toRingHom := evalHom W (algebraMap R (HomRing W)) (scaledCoord W u) (equation_scaledCoord W hW)
  map_mem := by
    rintro n _ ⟨p, hp, rfl⟩
    have hp' : p.IsHomogeneous n := hp
    change MvPolynomial.eval₂ (algebraMap R (HomRing W)) (scaledCoord W u) p ∈ _
    rw [MvPolynomial.eval₂_eq]
    refine Submodule.sum_mem _ fun d hd => ?_
    rw [← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    have := SetLike.prod_pow_mem_graded (grading W) (fun _ => 1) (scaledCoord W u)
      (F := d.support) d (fun i _ => scaledCoord_mem W u i)
    rw [hp'.degree_eq_sum_deg_support hd]
    simpa using this

include hu in
theorem irrelevant_le_map_scaleGraded :
    irrelevant (grading W) ≤ (irrelevant (grading W)).map (scaleGraded W hW) := by
  rw [← toIdeal_le_toIdeal_iff, irrelevant_eq_span_coord]
  refine (span_le_span_triple (hu.map (algebraMap R (HomRing W))) (coord W)).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have : triple (algebraMap R (HomRing W) u) (coord W) i = scaleGraded W hW (coord W i) :=
    (evalHom_coord W (algebraMap R (HomRing W)) (scaledCoord W u)
      (equation_scaledCoord W hW) i).symm
  rw [this]
  exact Ideal.mem_map_of_mem (scaleGraded W hW) (mem_irrelevant_of_mem _ one_pos (coord_mem W i))

def scaleMap : scheme W ⟶ scheme W :=
  Proj.map (scaleGraded W hW) (irrelevant_le_map_scaleGraded W hu hW)

@[reassoc]
theorem ptHom_scaleMap {A : Type} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) :
    ptHom W ρ P hP ≫ scaleMap W hu hW = ptHom W ρ (triple (ρ u) P)
      (isUnimodularSol_triple (hu.map ρ) (curve_map_eq ρ hW) hP) := by
  refine (ProjPoint.ofHom_map (scaleGraded W hW) (irrelevant_le_map_scaleGraded W hu hW) _
    (map_irrelevant_evalHom W hP)).trans ?_
  have : (evalHom W ρ P hP.equation).comp (scaleGraded W hW).toRingHom =
      evalHom W ρ _ (isUnimodularSol_triple (hu.map ρ) (curve_map_eq ρ hW) hP).equation := by
    refine homRing_hom_ext W (fun r => ?_) (fun i => ?_)
    · refine (congrArg (evalHom W ρ P hP.equation) (evalHom_algebraMap W _ (scaledCoord W u)
        (equation_scaledCoord W hW) r)).trans ?_
      rw [evalHom_algebraMap, evalHom_algebraMap]
    refine (congrArg (evalHom W ρ P hP.equation) (evalHom_coord W _ (scaledCoord W u)
      (equation_scaledCoord W hW) i)).trans ?_
    rw [evalHom_coord]
    fin_cases i <;> simp [scaledCoord, triple]
  simp only [this]
  rfl

theorem scaleMap_toSpec : scaleMap W hu hW ≫ toSpec W = toSpec W := by
  apply scheme_hom_ext
  · rw [chartY, pt_eq_ptHom, ptHom_scaleMap_assoc, ptHom_toSpec, ptHom_toSpec]
  · rw [chartZ, pt_eq_ptHom, ptHom_scaleMap_assoc, ptHom_toSpec, ptHom_toSpec]

def scaleOver : schemeOver W ⟶ schemeOver W :=
  Over.homMk (scaleMap W hu hW) (scaleMap_toSpec W hu hW)

theorem ptOver_scaleOver {A : Type} [CommRing A] [Algebra R A] (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.baseChange A) P) :
    ptOver W P hP ≫ scaleOver W hu hW = ptOver W (triple (algebraMap R A u) P)
      (isUnimodularSol_triple (hu.map _) (curve_map_eq (algebraMap R A) hW) hP) :=
  Over.OverMorphism.ext (ptHom_scaleMap W hu hW _ P hP)

omit hu hW in

theorem over_hom_ext_of_isLocalRing {T Y : Over (Spec (.of R))} {f g : T ⟶ Y}
    (h : ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra R A] (x : specOver R A ⟶ T),
      x ≫ f = x ≫ g) : f = g := by
  refine Over.OverMorphism.ext (hom_ext_of_localRing_points _ _ _ _ fun A _ _ t => ?_)
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (t ≫ T.hom)
  let : Algebra R A := ρ.hom.toAlgebra
  exact congrArg (·.left) (h A (Over.homMk t hρ.symm))

omit hu hW in

theorem over_hom_ext_ptOver {Y : Over (Spec (.of R))} {f g : schemeOver W ⟶ Y}
    (h : ∀ (A : Type) [CommRing A] [Algebra R A] (P : Fin 3 → A)
      (hP : IsUnimodularSol (W.baseChange A) P), ptOver W P hP ≫ f = ptOver W P hP ≫ g) : f = g :=
  over_hom_ext_of_isLocalRing fun A _ _ _ x => by
    obtain ⟨P, hP, rfl⟩ := exists_eq_ptOver W x
    exact h A P hP

omit hu hW in
theorem ptOver_congr {A : Type} [CommRing A] [Algebra R A] {P Q : Fin 3 → A}
    {hP : IsUnimodularSol (W.baseChange A) P} {hQ : IsUnimodularSol (W.baseChange A) Q}
    (e : P = Q) : ptOver W P hP = ptOver W Q hQ := by
  subst e; rfl

omit hu hW in

theorem exists_isSumTriple [W.IsElliptic] {A : Type} [CommRing A] [IsLocalRing A] [Algebra R A]
    {P Q : Fin 3 → A} (hP : IsUnimodularSol (W.baseChange A) P)
    (hQ : IsUnimodularSol (W.baseChange A) Q) :
    ∃ S, IsUnimodularSol (W.baseChange A) S ∧ IsSumTriple (W.baseChange A) P Q S := by
  obtain ⟨S, hS, h, -⟩ := exists_ptOver_mul_ptOver_eq W hP hQ
  refine ⟨S, hS, ?_⟩
  rcases h with rfl | rfl
  exacts [isSumTriple_addXYZ hP.equation hQ.equation, isSumTriple_diagXYZ hP.equation hQ.equation]

theorem isMonHom_scaleOver [W.IsElliptic] : IsMonHom (scaleOver W hu hW) := by
  have key : μ[schemeOver W] ≫ scaleOver W hu hW =
      (scaleOver W hu hW ⊗ₘ scaleOver W hu hW) ≫ μ[schemeOver W] :=
    over_hom_ext_of_isLocalRing fun A _ _ _ x => by
      rw [← lift_comp_fst_snd x, lift_map_assoc, ← Category.assoc]
      obtain ⟨P, hP, eP⟩ := exists_eq_ptOver W (x ≫ fst _ _)
      obtain ⟨Q, hQ, eQ⟩ := exists_eq_ptOver W (x ≫ snd _ _)
      obtain ⟨S, hS, h⟩ := exists_isSumTriple W hP hQ
      rw [eP, eQ, ← Hom.mul_def, ← Hom.mul_def, ptOver_mul_ptOver W hP hQ hS h, ptOver_scaleOver,
        ptOver_scaleOver, ptOver_scaleOver]
      exact (ptOver_mul_ptOver W _ _ _ (isSumTriple_triple (curve_map_eq _ hW) h)).symm
  refine ⟨?_, key⟩
  have e : (η[schemeOver W] * η[schemeOver W]) ≫ scaleOver W hu hW =
      (η[schemeOver W] ≫ scaleOver W hu hW) * (η[schemeOver W] ≫ scaleOver W hu hW) := by
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, key, lift_map_assoc]
  have h1 : η[schemeOver W] = 1 := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
  rw [h1] at e ⊢
  rw [_root_.mul_one] at e
  exact mul_eq_left.1 e.symm

omit hu hW in

def AddsByLaws (m : schemeOver W ⊗ schemeOver W ⟶ schemeOver W) : Prop :=
  ∀ (A : Type) [CommRing A] (ρ : R →+* A) (P Q T : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (hT : IsUnimodularSol (W.map ρ) T),
    (Proportional T ((W.map ρ).toProjective.addXYZ P Q) ∧
      Proportional T (diagXYZ (W.map ρ).toProjective P Q)) →
    ∀ x y : Over.mk (spMap ρ) ⟶ schemeOver W, x.left = ptHom W ρ P hP →
      y.left = ptHom W ρ Q hQ → (lift x y ≫ m).left = ptHom W ρ T hT

omit hu hW in

theorem AddsByLaws.unique [W.IsElliptic] {m m' : schemeOver W ⊗ schemeOver W ⟶ schemeOver W}
    (hm : AddsByLaws W m) (hm' : AddsByLaws W m') : m = m' :=
  over_hom_ext_of_isLocalRing fun A _ _ _ x => by
    rw [← lift_comp_fst_snd x]
    obtain ⟨P, hP, eP⟩ := exists_eq_ptOver W (x ≫ fst _ _)
    obtain ⟨Q, hQ, eQ⟩ := exists_eq_ptOver W (x ≫ snd _ _)
    obtain ⟨S, hS, h⟩ := exists_isSumTriple W hP hQ
    rw [eP, eQ]
    exact Over.OverMorphism.ext ((hm A _ P Q S hP hQ hS ⟨h.1, h.2⟩ _ _ rfl rfl).trans
      (hm' A _ P Q S hP hQ hS ⟨h.1, h.2⟩ _ _ rfl rfl).symm)

end GlobalTheory.WeightScale
