import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open HomogeneousIdeal

universe u

noncomputable section

namespace GlobalTheory

section SpecOver

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

def specOverMap (g : A →ₐ[R] B) : specOver R B ⟶ specOver R A :=
  Over.homMk (Spec.map (CommRingCat.ofHom (g : A →+* B))) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, g.comp_algebraMap])

@[simp] theorem specOverMap_left (g : A →ₐ[R] B) :
    (specOverMap g).left = Spec.map (CommRingCat.ofHom (g : A →+* B)) := rfl

theorem exists_eq_specOverMap (x : specOver R B ⟶ specOver R A) :
    ∃ g : A →ₐ[R] B, x = specOverMap g := by
  obtain ⟨g, hg⟩ := Spec.map_surjective x.left
  have h : Spec.map g ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := hg ▸ Over.w x
  rw [← Spec.map_comp] at h
  exact ⟨⟨g.hom, RingHom.congr_fun (congrArg (·.hom) (Spec.map_injective h))⟩,
    Over.OverMorphism.ext hg.symm⟩

theorem exists_specOver_nhds (T : Over (Spec (.of R))) {t : T.left} {V : T.left.Opens}
    (ht : t ∈ V) : ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (j : specOver R A ⟶ T),
      IsOpenImmersion j.left ∧ t ∈ Set.range j.left ∧ j.left ⁻¹ᵁ V = ⊤ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, htU, hUV⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open ht V.2
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (hU.fromSpec ≫ T.hom)
  letI : Algebra R Γ(T.left, U) := ρ.hom.toAlgebra
  refine ⟨Γ(T.left, U), inferInstance, inferInstance, Over.homMk hU.fromSpec hρ.symm,
    IsAffineOpen.isOpenImmersion_fromSpec hU, hU.range_fromSpec.ge htU, ?_⟩
  exact top_le_iff.mp fun y _ => hUV (hU.range_fromSpec.le ⟨y, rfl⟩)

end SpecOver

namespace WeierstrassCurve

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

@[reassoc]
theorem specOverMap_ptOver {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (g : A →ₐ[R] B) (P : Fin 3 → A) (h : IsUnimodularSol (W.baseChange A) P) :
    specOverMap g ≫ ptOver W P h = ptOver W (g ∘ P) (h.baseChange g) :=
  Over.OverMorphism.ext (SpecMap_pt W P h g)

section Linear

variable {W' : WeierstrassCurve R} (L : Fin 3 → HomRing W') (hL : ∀ i, L i ∈ grading W' 1)
  (h : (W.baseChange (HomRing W')).toProjective.Equation L)

def linearGradedMap : grading W →+*ᵍ grading W' where
  toRingHom := evalHom W (algebraMap R (HomRing W')) L h
  map_mem := by
    rintro n _ ⟨p, hp, rfl⟩
    change MvPolynomial.eval₂ _ _ p ∈ _
    rw [MvPolynomial.eval₂_eq]
    refine sum_mem fun d hd => ?_
    rw [← Algebra.smul_def, MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hd]
    refine Submodule.smul_mem _ _ (SetLike.prod_mem_graded _ _ _ fun i _ => ?_)
    simpa using SetLike.pow_mem_graded (d i) (hL i)

variable (hs : ∀ i, coord W' i ∈ Ideal.span (Set.range L))

include hs in

theorem irrelevant_le_map_linearGradedMap :
    irrelevant (grading W') ≤ (irrelevant (grading W)).map (linearGradedMap W L hL h) := by
  rw [← toIdeal_le_toIdeal_iff, irrelevant_eq_span_coord, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  refine (Ideal.span_le.mpr ?_ : Ideal.span (Set.range L) ≤ _) (hs i)
  rintro _ ⟨j, rfl⟩
  rw [← evalHom_coord W (algebraMap R (HomRing W')) L h j]
  exact Ideal.mem_map_of_mem (linearGradedMap W L hL h)
    (mem_irrelevant_of_mem _ one_pos (coord_mem W j))

def linearHom : scheme W' ⟶ scheme W :=
  Proj.map (linearGradedMap W L hL h) (irrelevant_le_map_linearGradedMap W L hL h hs)

variable {A : Type u} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
  (hP : IsUnimodularSol (W'.map ρ) P)

include h hs in

theorem isUnimodularSol_linear :
    IsUnimodularSol (W.map ρ) (evalHom W' ρ P hP.equation ∘ L) := by
  constructor
  · have e : (evalHom W' ρ P hP.equation).comp (algebraMap R (HomRing W')) = ρ :=
      RingHom.ext (evalHom_algebraMap W' ρ P hP.equation)
    have := h.map (evalHom W' ρ P hP.equation)
    change (W.map ((evalHom W' ρ P hP.equation).comp
      (algebraMap R (HomRing W')))).toProjective.Equation _ at this
    rwa [e] at this
  · rw [Set.range_comp, ← Ideal.map_span, _root_.eq_top_iff, ← hP.span_eq_top, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [← evalHom_coord W' ρ P hP.equation i]
    exact Ideal.mem_map_of_mem _ (hs i)

@[reassoc]
theorem ptHom_linearHom : ptHom W' ρ P hP ≫ linearHom W L hL h hs =
    ptHom W ρ (evalHom W' ρ P hP.equation ∘ L) (isUnimodularSol_linear W L h hs ρ P hP) := by
  refine (ProjPoint.ofHom_map (linearGradedMap W L hL h)
    (irrelevant_le_map_linearGradedMap W L hL h hs) _ (map_irrelevant_evalHom W' hP)).trans ?_
  have : (evalHom W' ρ P hP.equation).comp (linearGradedMap W L hL h).toRingHom =
      evalHom W ρ _ (isUnimodularSol_linear W L h hs ρ P hP).equation :=
    homRing_hom_ext W
      (fun r => ((congrArg (evalHom W' ρ P hP.equation)
        (evalHom_algebraMap W (algebraMap R (HomRing W')) L h r)).trans
          (evalHom_algebraMap ..)).trans (evalHom_algebraMap ..).symm)
      (fun i => (congrArg (evalHom W' ρ P hP.equation)
        (evalHom_coord W (algebraMap R (HomRing W')) L h i)).trans (evalHom_coord W ρ
          (evalHom W' ρ P hP.equation ∘ L)
          (isUnimodularSol_linear W L h hs ρ P hP).equation i).symm)
  simp only [this]
  rfl

@[reassoc (attr := simp)]
theorem linearHom_toSpec : linearHom W L hL h hs ≫ toSpec W = toSpec W' := by
  apply scheme_hom_ext
  · rw [chartY, pt_toSpec, pt_eq_ptHom, ptHom_linearHom_assoc, ptHom_toSpec]
  · rw [chartZ, pt_toSpec, pt_eq_ptHom, ptHom_linearHom_assoc, ptHom_toSpec]

end Linear

section Neg

variable {A : Type*} [CommRing A]

theorem equation_neg {V : WeierstrassCurve A} {P : Fin 3 → A} (h : V.toProjective.Equation P) :
    V.toProjective.Equation (V.toProjective.neg P) := by
  rw [WeierstrassCurve.Projective.equation_iff] at h ⊢
  simp only [WeierstrassCurve.Projective.neg_X, WeierstrassCurve.Projective.neg_Y,
    WeierstrassCurve.Projective.neg_Z, WeierstrassCurve.Projective.negY]
  linear_combination h

theorem mem_span_neg (V : WeierstrassCurve A) (P : Fin 3 → A) (i : Fin 3) :
    P i ∈ Ideal.span (Set.range (V.toProjective.neg P)) := by
  have h : ∀ j, V.toProjective.neg P j ∈ Ideal.span (Set.range (V.toProjective.neg P)) :=
    fun j => Ideal.subset_span ⟨j, rfl⟩
  fin_cases i
  · exact h 0
  · have e : P 1 = -V.toProjective.neg P 1 - V.a₁ * V.toProjective.neg P 0
        - V.a₃ * V.toProjective.neg P 2 := by
      simp only [WeierstrassCurve.Projective.neg_X, WeierstrassCurve.Projective.neg_Y,
        WeierstrassCurve.Projective.neg_Z, WeierstrassCurve.Projective.negY]
      ring
    change P 1 ∈ _
    rw [e]
    exact sub_mem (sub_mem (neg_mem (h 1)) (Ideal.mul_mem_left _ _ (h 0)))
      (Ideal.mul_mem_left _ _ (h 2))
  · exact h 2

theorem IsUnimodularSol.neg {V : WeierstrassCurve A} {P : Fin 3 → A} (h : IsUnimodularSol V P) :
    IsUnimodularSol V (V.toProjective.neg P) := by
  refine ⟨equation_neg h.equation, ?_⟩
  rw [_root_.eq_top_iff, ← h.span_eq_top, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact mem_span_neg V P i

theorem neg_coord_mem (i : Fin 3) :
    (W.baseChange (HomRing W)).toProjective.neg (coord W) i ∈ grading W 1 := by
  fin_cases i
  · exact coord_mem W 0
  · change -coord W 1 - algebraMap R _ W.a₁ * coord W 0 - algebraMap R _ W.a₃ * coord W 2 ∈ _
    rw [← Algebra.smul_def, ← Algebra.smul_def]
    exact sub_mem (sub_mem (neg_mem (coord_mem W 1)) (Submodule.smul_mem _ _ (coord_mem W 0)))
      (Submodule.smul_mem _ _ (coord_mem W 2))
  · exact coord_mem W 2

def negHom : scheme W ⟶ scheme W :=
  linearHom W _ (neg_coord_mem W) (equation_neg (equation_coord W)) (mem_span_neg _ _)

@[reassoc]
theorem ptHom_negHom {A : Type u} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) :
    ptHom W ρ P hP ≫ negHom W = ptHom W ρ ((W.map ρ).toProjective.neg P) hP.neg := by
  rw [negHom, ptHom_linearHom]
  refine ptHom_congr W _ _ _ rfl ?_ _
  ext i
  fin_cases i <;>
    simp [WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY,
      WeierstrassCurve.baseChange]

@[reassoc (attr := simp)]
theorem negHom_toSpec : negHom W ≫ toSpec W = toSpec W := linearHom_toSpec ..

def negOver : schemeOver W ⟶ schemeOver W := Over.homMk (negHom W) (negHom_toSpec W)

@[simp] theorem negOver_left : (negOver W).left = negHom W := rfl

@[reassoc]
theorem ptOver_negOver {A : Type u} [CommRing A] [Algebra R A] (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.baseChange A) P) :
    ptOver W P hP ≫ negOver W = ptOver W ((W.baseChange A).toProjective.neg P) hP.neg :=
  Over.OverMorphism.ext (ptHom_negHom W _ P hP)

@[reassoc]
theorem negHom_mapHom {R' : Type u} [CommRing R'] {W' : WeierstrassCurve R'} (f : R →+* R')
    (h : W.map f = W') : negHom W' ≫ mapHom W f h = mapHom W f h ≫ negHom W := by
  subst h
  apply scheme_hom_ext
  · rw [chartY, pt_eq_ptHom, ptHom_negHom_assoc, ptHom_mapHom, ptHom_mapHom_assoc, ptHom_negHom]
    rfl
  · rw [chartZ, pt_eq_ptHom, ptHom_negHom_assoc, ptHom_mapHom, ptHom_mapHom_assoc, ptHom_negHom]
    rfl

def zeroUnit : 𝟙_ (Over (Spec (.of R))) ⟶ schemeOver W := Over.homMk (zero W) (zero_toSpec W)

@[simp] theorem zeroUnit_left : (zeroUnit W).left = zero W := rfl

theorem toUnit_zeroUnit (A : Type u) [CommRing A] [Algebra R A] :
    toUnit (specOver R A) ≫ zeroUnit W = zeroOver W A := rfl

end Neg

section Sum

open AddLaw

variable {A B : Type*} [CommRing A] [CommRing B]

structure IsSumTriple (V : WeierstrassCurve A) (P Q T : Fin 3 → A) : Prop where

  add : Proportional T (V.toProjective.addXYZ P Q)

  diag : Proportional T (diagXYZ V.toProjective P Q)

variable {V : WeierstrassCurve A} {P Q T : Fin 3 → A}

theorem isSumTriple_addXYZ (hP : V.toProjective.Equation P) (hQ : V.toProjective.Equation Q) :
    IsSumTriple V P Q (V.toProjective.addXYZ P Q) :=
  ⟨fun _ _ => mul_comm _ _, (proportional_diagXYZ_addXYZ hP hQ).symm⟩

theorem isSumTriple_diagXYZ (hP : V.toProjective.Equation P) (hQ : V.toProjective.Equation Q) :
    IsSumTriple V P Q (diagXYZ V.toProjective P Q) :=
  ⟨proportional_diagXYZ_addXYZ hP hQ, fun _ _ => mul_comm _ _⟩

theorem IsSumTriple.map (h : IsSumTriple V P Q T) (g : A →+* B) :
    IsSumTriple (V.map g) (g ∘ P) (g ∘ Q) (g ∘ T) := by
  constructor
  · have e : (V.map g).toProjective.addXYZ (g ∘ P) (g ∘ Q) = g ∘ V.toProjective.addXYZ P Q :=
      WeierstrassCurve.Projective.map_addXYZ ..
    rw [e]
    exact fun i j => by simpa using congrArg g (h.add i j)
  · have e : diagXYZ (V.map g).toProjective (g ∘ P) (g ∘ Q) = g ∘ diagXYZ V.toProjective P Q :=
      map_diagXYZ ..
    rw [e]
    exact fun i j => by simpa using congrArg g (h.diag i j)

theorem IsSumTriple.baseChange {R : Type*} [CommRing R] [Algebra R A] [Algebra R B]
    {W : WeierstrassCurve R} (h : IsSumTriple (W.baseChange A) P Q T) (g : A →ₐ[R] B) :
    IsSumTriple (W.baseChange B) (g ∘ P) (g ∘ Q) (g ∘ T) := by
  have := h.map (g : A →+* B)
  rwa [WeierstrassCurve.map_baseChange] at this

open WeierstrassCurve.Projective in

theorem IsSumTriple.equiv_add {k : Type*} [Field k] {V : WeierstrassCurve k} {P Q T : Fin 3 → k}
    (h : IsSumTriple V P Q T) (hP : V.toProjective.Nonsingular P)
    (hQ : V.toProjective.Nonsingular Q) (hT : T ≠ 0) : T ≈ V.toProjective.add P Q :=
  equiv_add_of_proportional hP hQ h.add h.diag hT

theorem exists_law_notMem [V.IsElliptic] (hP : IsUnimodularSol V P) (hQ : IsUnimodularSol V Q)
    (p : Ideal A) [p.IsPrime] :
    (∃ i, V.toProjective.addXYZ P Q i ∉ p) ∨ ∃ i, diagXYZ V.toProjective P Q i ∉ p := by
  let g := algebraMap A p.ResidueField
  have e₁ : (V.map g).toProjective.addXYZ (g ∘ P) (g ∘ Q) = g ∘ V.toProjective.addXYZ P Q :=
    WeierstrassCurve.Projective.map_addXYZ ..
  have e₂ : diagXYZ (V.map g).toProjective (g ∘ P) (g ∘ Q) = g ∘ diagXYZ V.toProjective P Q :=
    map_diagXYZ ..
  have h := addXYZ_ne_zero_or_diagXYZ_ne_zero (hP.map g).nonsingular (hQ.map g).nonsingular
  rw [e₁, e₂] at h
  refine h.imp (fun h => ?_) (fun h => ?_) <;>
    exact (Function.ne_iff.mp h).imp fun i hi hp =>
      hi (Ideal.algebraMap_residueField_eq_zero.mpr hp)

theorem IsSumTriple.equation_of_isReduced {A : Type u} [CommRing A] [_root_.IsReduced A]
    {V : WeierstrassCurve A} [V.IsElliptic] {P Q T : Fin 3 → A} (h : IsSumTriple V P Q T)
    (hP : IsUnimodularSol V P) (hQ : IsUnimodularSol V Q) : V.toProjective.Equation T := by
  refine equation_of_forall_field fun k _ φ => ?_
  by_cases h0 : φ ∘ T = 0
  · rw [h0, WeierstrassCurve.Projective.equation_iff]
    simp
  · have hP' := (hP.map φ).nonsingular
    have hQ' := (hQ.map φ).nonsingular
    exact (WeierstrassCurve.Projective.equation_of_equiv ((h.map φ).equiv_add hP' hQ' h0)).mpr
      (WeierstrassCurve.Projective.nonsingular_add hP' hQ').left

end Sum

section Reduced

variable [W.IsElliptic]

def fieldAdd (k : Type u) [Field k] [Algebra R k] (a b : specOver R k ⟶ schemeOver W) :
    specOver R k ⟶ schemeOver W :=
  projectivePointEquiv W k ((projectivePointEquiv W k).symm a + (projectivePointEquiv W k).symm b)

theorem fieldAdd_ptOver {k : Type u} [Field k] [Algebra R k] {P Q T : Fin 3 → k}
    (hP : IsUnimodularSol (W.baseChange k) P) (hQ : IsUnimodularSol (W.baseChange k) Q)
    (hT : IsUnimodularSol (W.baseChange k) T) (h : IsSumTriple (W.baseChange k) P Q T) :
    fieldAdd W k (ptOver W P hP) (ptOver W Q hQ) = ptOver W T hT := by
  rw [fieldAdd, projectivePointEquiv_symm_ptOver, projectivePointEquiv_symm_ptOver]
  obtain ⟨v, hv⟩ := h.equiv_add hP.nonsingular hQ.nonsingular
    (isUnimodularSol_iff_ne_zero.mp hT).right
  exact (ptOver_eq_ptOver_iff W (.of_nonsingular
    (WeierstrassCurve.Projective.nonsingular_add hP.nonsingular hQ.nonsingular)) hT).mpr
    ⟨v, hv.symm⟩

theorem comp_ptOver_eq_fieldAdd {A : Type u} [CommRing A] [Algebra R A] {P Q T : Fin 3 → A}
    (hP : IsUnimodularSol (W.baseChange A) P) (hQ : IsUnimodularSol (W.baseChange A) Q)
    (hT : IsUnimodularSol (W.baseChange A) T) (h : IsSumTriple (W.baseChange A) P Q T)
    (k : Type u) [Field k] [Algebra R k] (x : specOver R k ⟶ specOver R A) :
    x ≫ ptOver W T hT = fieldAdd W k (x ≫ ptOver W P hP) (x ≫ ptOver W Q hQ) := by
  obtain ⟨g, rfl⟩ := exists_eq_specOverMap x
  rw [specOverMap_ptOver, specOverMap_ptOver, specOverMap_ptOver]
  exact (fieldAdd_ptOver W _ _ _ (h.baseChange g)).symm

omit [W.IsElliptic] in

theorem exists_nhds_eq_ptOver {T : Over (Spec (.of R))} (p q : T ⟶ schemeOver W) (t : T.left) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (j : specOver R A ⟶ T) (P Q : Fin 3 → A)
      (hP : IsUnimodularSol (W.baseChange A) P) (hQ : IsUnimodularSol (W.baseChange A) Q),
      IsOpenImmersion j.left ∧ t ∈ Set.range j.left ∧ j ≫ p = ptOver W P hP ∧
        j ≫ q = ptOver W Q hQ := by
  have hc : ∀ x : scheme W, ∃ i, x ∈ coordOpen W i := fun x => by
    rcases (coordOpen_one_sup_coordOpen_two W).ge (Set.mem_univ x) with h | h
    exacts [⟨_, h⟩, ⟨_, h⟩]
  obtain ⟨a, ha⟩ := hc (p.left t)
  obtain ⟨b, hb⟩ := hc (q.left t)
  obtain ⟨A, _, _, j, hj, ht, hV⟩ := exists_specOver_nhds T
    (V := p.left ⁻¹ᵁ coordOpen W a ⊓ q.left ⁻¹ᵁ coordOpen W b) ⟨ha, hb⟩
  obtain ⟨P, hP, -, eP⟩ := exists_eq_ptHom_of_preimage_eq_top W (algebraMap R A) (j ≫ p).left
    (Over.w (j ≫ p)) a (top_le_iff.mp fun y hy => (hV.ge hy).left)
  obtain ⟨Q, hQ, -, eQ⟩ := exists_eq_ptHom_of_preimage_eq_top W (algebraMap R A) (j ≫ q).left
    (Over.w (j ≫ q)) b (top_le_iff.mp fun y hy => (hV.ge hy).right)
  exact ⟨A, _, _, j, P, Q, hP, hQ, hj, ht, Over.OverMorphism.ext eP, Over.OverMorphism.ext eQ⟩

theorem exists_sum {T : Over (Spec (.of R))} [IsReduced T.left] (p q : T ⟶ schemeOver W) :
    ∃ s : T ⟶ schemeOver W, ∀ (k : Type u) [Field k] [Algebra R k] (x : specOver R k ⟶ T),
      x ≫ s = fieldAdd W k (x ≫ p) (x ≫ q) := by
  have : IsSeparated (schemeOver W).hom := inferInstanceAs (IsSeparated (toSpec W))
  refine exists_over_hom_of_locally (fun k _ _ x => fieldAdd W k (x ≫ p) (x ≫ q)) fun t => ?_
  obtain ⟨A, _, _, j, P, Q, hP, hQ, hj, ⟨y, rfl⟩, eP, eQ⟩ := exists_nhds_eq_ptOver W p q t
  have : _root_.IsReduced A :=
    (affine_isReduced_iff (.of A)).mp (isReduced_of_isOpenImmersion j.left)
  obtain ⟨S, hS, i, hi⟩ : ∃ S, IsSumTriple (W.baseChange A) P Q S ∧ ∃ i, S i ∉ y.asIdeal := by
    rcases @exists_law_notMem _ _ _ _ _ _ hP hQ y.asIdeal y.isPrime with h | h
    exacts [⟨_, isSumTriple_addXYZ hP.equation hQ.equation, h⟩,
      ⟨_, isSumTriple_diagXYZ hP.equation hQ.equation, h⟩]
  let g : A →ₐ[R] Localization.Away (S i) := IsScalarTower.toAlgHom R A _
  have hS' : IsUnimodularSol (W.baseChange (Localization.Away (S i))) (g ∘ S) :=
    .of_isUnit ((hS.baseChange g).equation_of_isReduced (hP.baseChange g) (hQ.baseChange g)) i
      (IsLocalization.Away.algebraMap_isUnit (S i))
  have hg : IsOpenImmersion (specOverMap g).left := IsOpenImmersion.of_isLocalization (S i)
  refine ⟨_, specOverMap g ≫ j, inferInstanceAs (IsOpenImmersion ((specOverMap g).left ≫ j.left)),
    ptOver W _ hS', ?_, fun k _ _ x => ?_⟩
  · obtain ⟨z, hz⟩ :=
      (PrimeSpectrum.localization_away_comap_range (Localization.Away (S i)) (S i)).ge hi
    exact ⟨z, congrArg j.left hz⟩
  · simp only [Category.assoc, eP, eQ, specOverMap_ptOver]
    exact comp_ptOver_eq_fieldAdd W _ _ _ (hS.baseChange g) k x

end Reduced

end WeierstrassCurve

end GlobalTheory
