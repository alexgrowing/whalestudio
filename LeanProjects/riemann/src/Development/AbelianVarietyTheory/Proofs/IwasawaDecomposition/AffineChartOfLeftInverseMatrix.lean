import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MvPolynomial GlobalTheory.ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.SplitCells

variable {R : Type} [CommRing R] {N r : ℕ}

def lin (a : Fin (N + 1) → R) : MvPolynomial (Fin (N + 1)) R := ∑ j, C (a j) * X j

theorem lin_hom (a : Fin (N + 1) → R) : (lin a).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X R j).C_mul _

theorem eval₂_lin {m : Type} {A : Type} [CommRing A] (c : R →+* A) (M : Matrix m (Fin (N + 1)) R) (k : m)
    (w : Fin (N + 1) → A) : eval₂ c w (lin (M k)) = (M.map c).mulVec w k := by
  simp [lin, eval₂_sum, Matrix.mulVec, dotProduct]

abbrev tv (R : Type) [CommRing R] (c : Fin (r + 1)) : Fin (r + 1) → MvPolynomial (Fin r) R :=
  Fin.insertNth (α := fun _ => MvPolynomial (Fin r) R) c 1 X

def res (Q : Matrix (Fin (N + 1)) (Fin (r + 1)) R) (Q' : Matrix (Fin (r + 1)) (Fin (N + 1)) R) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R := 1 - Q * Q'

theorem mulVec_inv {A : Type} [CommRing A] (c : R →+* A) {Q : Matrix (Fin (N + 1)) (Fin (r + 1)) R}
    {Q' : Matrix (Fin (r + 1)) (Fin (N + 1)) R} (h : Q' * Q = 1) (v : Fin (r + 1) → A) :
    (Q'.map c).mulVec ((Q.map c).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero c) (map_one c), Matrix.one_mulVec]

section
variable {Q : Matrix (Fin (N + 1)) (Fin (r + 1)) R} {Q' : Matrix (Fin (r + 1)) (Fin (N + 1)) R} (h : Q' * Q = 1)
include h

theorem isImmersion_cell (c : Fin (r + 1)) (hv) :
    IsImmersion (pt (C : R →+* MvPolynomial (Fin r) R) ((Q.map C).mulVec (tv R c)) hv) := by
  have he : ∀ k, eval₂Hom (C : R →+* MvPolynomial (Fin r) R) ((Q.map C).mulVec (tv R c)) (lin (Q' k)) = tv R c k :=
    fun k => by rw [coe_eval₂Hom, eval₂_lin, mulVec_inv _ h]
  have h1 : eval₂Hom (C : R →+* MvPolynomial (Fin r) R) ((Q.map C).mulVec (tv R c)) (lin (Q' c)) = 1 := by
    rw [he, tv, Fin.insertNth_apply_same]
  have hu : IsUnit (eval₂Hom (C : R →+* MvPolynomial (Fin r) R) ((Q.map C).mulVec (tv R c)) (lin (Q' c))) :=
    h1 ▸ isUnit_one
  have hm : lin (Q' c) ∈ grading R N 1 := lin_hom _
  rw [pt, ProjPoint.ofHom_eq_awayι _ _ _ one_pos hm hu]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (ProjPoint.awayLift (grading R N) _ _ hu))) := by
    refine IsClosedImmersion.spec_of_surjective _ fun p => ?_
    change p ∈ (ProjPoint.awayLift (grading R N) _ _ hu).range
    induction p using MvPolynomial.induction_on with
    | C a =>
      have := ProjPoint.awayLift_mk_mul (grading R N) _ hu hm 0 (C a) (isHomogeneous_C _ a)
      rw [pow_zero, mul_one, eval₂Hom_C] at this
      exact ⟨_, this⟩
    | add F G hF hG => exact add_mem hF hG
    | mul_X F k hF =>
      refine mul_mem hF ?_
      have := ProjPoint.awayLift_mk_mul (grading R N) _ hu hm 1 (lin (Q' (c.succAbove k))) (lin_hom _)
      rw [h1, one_pow, mul_one, he] at this
      exact ⟨_, this.trans (Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (Fin r) R) c 1 X k)⟩
  infer_instance

omit h in
theorem exists_pt (x : PSpace R N) : ∃ (K : Type) (_ : Field K) (c : R →+* K) (w : Fin (N + 1) → K) (hw : _)
    (y : Sp K), pt c w hw y = x := by
  let φ := (PSpace R N).fromSpecResidueField x
  let K : Type := (PSpace R N).residueField x
  obtain ⟨w, hw, e⟩ := exists_eq_pt (A := K) (Spec.preimage (φ ≫ PSpace.str R N)).hom φ (Spec.map_preimage _).symm
  exact ⟨K, inferInstance, _, w, hw, IsLocalRing.closedPoint _, by rw [← e]; exact Scheme.fromSpecResidueField_apply x _⟩

omit h in
theorem pt_mem {m A : Type} [CommRing A] (c : R →+* A) (w : Fin (N + 1) → A) (hw) (y : Sp A)
    (M : Matrix m (Fin (N + 1)) R) (k : m) :
    pt c w hw y ∈ Proj.basicOpen (grading R N) (lin (M k)) ↔ (M.map c).mulVec w k ∉ y.asIdeal := by
  rw [← mem_spOpen, ← eval₂_lin, ← pt_preimage_basicOpen c w hw one_pos (lin_hom _)]
  rfl

omit h in
theorem pt_mem_field {m K : Type} [Field K] (c : R →+* K) (w : Fin (N + 1) → K) (hw) (y : Sp K)
    (M : Matrix m (Fin (N + 1)) R) (k : m) :
    pt c w hw y ∈ Proj.basicOpen (grading R N) (lin (M k)) ↔ (M.map c).mulVec w k ≠ 0 := by
  rw [pt_mem, (Ideal.eq_bot_or_top y.asIdeal).resolve_right y.isPrime.ne_top, Ideal.mem_bot]

omit h in
theorem fix_of_not_mem {K : Type} [Field K] (c : R →+* K) (w : Fin (N + 1) → K) (hw) (y : Sp K)
    (H : ∀ k, pt c w hw y ∉ Proj.basicOpen (grading R N) (lin (res Q Q' k))) :
    (Q.map c).mulVec ((Q'.map c).mulVec w) = w := by
  have : ((res Q Q').map c).mulVec w = 0 := funext fun k => by
    have := H k
    rwa [pt_mem_field, not_not] at this
  rw [res, Matrix.map_sub _ (map_sub c), Matrix.map_one _ (map_zero c) (map_one c), Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.map_mul, ← Matrix.mulVec_mulVec, sub_eq_zero] at this
  exact this.symm

theorem mem_range_cell (c : Fin (r + 1)) (hv) (x : PSpace R N) :
    x ∈ Set.range (pt (C : R →+* MvPolynomial (Fin r) R) ((Q.map C).mulVec (tv R c)) hv) ↔
      (∀ k, x ∉ Proj.basicOpen (grading R N) (lin (res Q Q' k))) ∧
        x ∈ Proj.basicOpen (grading R N) (lin (Q' c)) := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨fun k => ?_, ?_⟩
    · rw [pt_mem, not_not, Matrix.mulVec_mulVec, ← Matrix.map_mul, res, Matrix.sub_mul, Matrix.mul_assoc, h,
        Matrix.one_mul, Matrix.mul_one, sub_self, Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]
      exact zero_mem _
    · rw [pt_mem, mulVec_inv _ h, tv, Fin.insertNth_apply_same]
      exact fun h1 => y.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · rintro ⟨h1, h2⟩
    obtain ⟨K, _, b, w, hw, y, rfl⟩ := exists_pt x
    have h3 := fix_of_not_mem b w hw y h1
    rw [pt_mem_field] at h2
    set u := (Q'.map b).mulVec w
    let ψ : MvPolynomial (Fin r) R →+* K := eval₂Hom b fun k => (u c)⁻¹ * u (c.succAbove k)
    have hb : ψ.comp C = b := RingHom.ext fun a => eval₂Hom_C _ _ a
    have h4 : ψ ∘ tv R c = (u c)⁻¹ • u := by
      funext k
      refine Fin.succAboveCases c ?_ (fun k => ?_) k
      · simp [h2]
      · simp [ψ]
    have h5 : ψ ∘ (Q.map C).mulVec (tv R c) = (u c)⁻¹ • w := by
      funext k
      rw [Function.comp_apply, RingHom.map_mulVec, Matrix.map_map, ← RingHom.coe_comp, hb, h4,
        Matrix.mulVec_smul, h3]
    refine ⟨spMap ψ y, ?_⟩
    rw [← Scheme.Hom.comp_apply, spMap_pt]
    have h6 : ∀ (b' : R →+* K) (w' : Fin (N + 1) → K) (hw' : _), b' = b → w' = (u c)⁻¹ • w →
        pt b' w' hw' = pt b w hw := by
      rintro _ w' hw' rfl e
      exact ((pt_eq_pt_iff _ hw hw').2 ⟨(Units.mk0 _ h2)⁻¹, e⟩).symm
    rw [h6 _ _ _ hb h5]

omit h in
theorem exists_mem (x : PSpace R N) (H : ∀ k, x ∉ Proj.basicOpen (grading R N) (lin (res Q Q' k))) :
    ∃ c, x ∈ Proj.basicOpen (grading R N) (lin (Q' c)) := by
  obtain ⟨K, _, b, w, hw, y, rfl⟩ := exists_pt x
  have h3 := fix_of_not_mem b w hw y H
  by_contra! hc
  have : (Q'.map b).mulVec w = 0 := funext fun k => by
    have := hc k
    rwa [pt_mem_field, not_not] at this
  rw [this, Matrix.mulVec_zero] at h3
  exact span_range_eq_top_iff_ne_zero.1 hw h3.symm

end

theorem cells_locallyClosed : ∀ (O : Type) [CommRing O] (Z P : Scheme.{0}) (s : Z ⟶ Sp O) (N r : ℕ) (p₁ : P ⟶ Z) (p₂ : P ⟶ PSpace O N), IsPullback p₁ p₂ s (PSpace.str O N) → ∀ (R : Type) [CommRing R] (χ : Sp R ⟶ Z) (g : O →+* R) (Q : Matrix (Fin (N + 1)) (Fin (r + 1)) R) (Q' : Matrix (Fin (r + 1)) (Fin (N + 1)) R) (i : Fin (r + 1) → (Sp (MvPolynomial (Fin r) R) ⟶ P)), IsOpenImmersion χ → χ ≫ s = spMap g → Q' * Q = 1 → (∀ c, i c ≫ p₁ = spMap (MvPolynomial.C : R →+* MvPolynomial (Fin r) R) ≫ χ) → (∀ c, ∃ hv, i c ≫ p₂ = GlobalTheory.ProjSpace.pt ((MvPolynomial.C : R →+* MvPolynomial (Fin r) R).comp g) ((Q.map (MvPolynomial.C : R →+* MvPolynomial (Fin r) R)).mulVec (Fin.insertNth (α := fun _ => MvPolynomial (Fin r) R) c 1 MvPolynomial.X)) hv) → (∀ c, IsImmersion (i c)) ∧ (∀ c, ∃ U : P.Opens, Set.range (i c) = (⋃ c', Set.range (i c')) ∩ (U : Set P)) ∧ ∃ T : Set P, IsClosed T ∧ ⋃ c, Set.range (i c) = T ∩ p₁ ⁻¹' Set.range χ := by
  intro O _ Z P s N r p₁ p₂ hP R _ χ g Q Q' i hχ hg h hi₁ hi₂
  have hb := isPullback_baseChange N g
  rw [← hg] at hb
  let e : PSpace R N ⟶ P := hP.flip.lift (baseChange N g) (PSpace.str R N ≫ χ) (by rw [hb.w, Category.assoc])
  have he : IsPullback e (PSpace.str R N) p₁ χ := hb.of_right' hP.flip
  have he₂ : e ≫ p₂ = baseChange N g := hP.flip.lift_fst _ _ _
  have heo : IsOpenImmersion e := MorphismProperty.of_isPullback he.flip hχ
  have hr : Set.range e = p₁ ⁻¹' Set.range χ := by
    rw [← Scheme.Pullback.range_fst, ← he.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact he.isoPullback.hom.surjective.range_comp _
  choose hv hi₂ using hi₂
  have hj : ∀ c, i c = pt C ((Q.map C).mulVec (tv R c)) (hv c) ≫ e := fun c =>
    hP.hom_ext (by rw [hi₁, Category.assoc, he.w, pt_str_assoc]) (by rw [hi₂, Category.assoc, he₂, pt_baseChange])
  have hm : ∀ c x, x ∈ Set.range (i c) ↔ ∃ y, ((∀ k, y ∉ Proj.basicOpen (grading R N) (lin (res Q Q' k))) ∧
      y ∈ Proj.basicOpen (grading R N) (lin (Q' c))) ∧ e y = x := fun c x => by
    simp only [← mem_range_cell h c (hv c)]
    rw [hj, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rfl
  have hinj := e.isOpenEmbedding.injective
  refine ⟨fun c => ?_, fun c => ⟨e ''ᵁ Proj.basicOpen (grading R N) (lin (Q' c)), Set.ext fun x => ?_⟩,
    (e ''ᵁ ⨆ k, Proj.basicOpen (grading R N) (lin (res Q Q' k)) : Set P)ᶜ, (TopologicalSpace.Opens.isOpen _).isClosed_compl,
    Set.ext fun x => ?_⟩
  · have := isImmersion_cell h c (hv c)
    rw [hj]
    infer_instance
  · simp only [Set.mem_inter_iff, Set.mem_iUnion, hm]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨c, y, hy, rfl⟩, y, hy.2, rfl⟩
    · rintro ⟨⟨c', y, hy, rfl⟩, y', hy', e'⟩
      obtain rfl := hinj e'
      exact ⟨y', ⟨hy.1, hy'⟩, rfl⟩
  · simp only [Set.mem_inter_iff, Set.mem_iUnion, hm, ← hr]
    constructor
    · rintro ⟨c, y, hy, rfl⟩
      refine ⟨?_, y, rfl⟩
      rintro ⟨y', hy', e'⟩
      obtain rfl := hinj e'
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
      exact hy.1 k hk
    · rintro ⟨hx, y, rfl⟩
      have hy : ∀ k, y ∉ Proj.basicOpen (grading R N) (lin (res Q Q' k)) := fun k hk =>
        hx ⟨y, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩, rfl⟩
      obtain ⟨c, hc⟩ := exists_mem y hy
      exact ⟨c, y, ⟨hy, hc⟩, rfl⟩

end GlobalTheory.SplitCells
