import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHodgeCohomologyEquivCechDifferentials
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteCoverProjSpaceReducedFibreOriginStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsChartLiftOfFiniteCover
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EFam
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsSeparatedOfProj
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteDimensionalHodgeCohomologyOfSmoothProj
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceSectionsStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.ComplexPointsBijectiveAlgHomAffineOpen
import Development.AutomorphicArithmetic.CommutativeAlgebra.ComplexPointEvalPullbackSection
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceComplexPointsStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceDifferentialsStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceFieldExtensionStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsRegularParametersOfReducedQuotient
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceLocalParametersStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceFamilyStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1
open GlobalTheory.PD GlobalTheory.WH

namespace UpperTheory.A

private theorem ring_one {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℂ} [Algebra ℂ X.functionField] {ι : Type} {U : ι → X.Opens}
    {B : Finset ι → Subalgebra ℂ X.functionField} (hU : IsAffCover p U B) (i : ι) (hg : genericPoint X ∈ U i)
    (y : X.functionField) : y ∈ B {i} ↔ ∃ f : Γ(X, U i), (X.presheaf.germ (U i) (genericPoint X) hg).hom f = y := by
  have key : ∀ (W : X.Opens) (_ : W = ({i} : Finset ι).inf U) (hg : genericPoint X ∈ W),
      y ∈ B {i} ↔ ∃ f : Γ(X, W), (X.presheaf.germ W (genericPoint X) hg).hom f = y := by
    intro W hW hg
    subst hW
    exact hU.ring {i} ⟨i, Finset.mem_singleton_self i⟩ y
  exact key _ (by simp) hg

private theorem affine_one {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℂ} [Algebra ℂ X.functionField] {ι : Type} {U : ι → X.Opens}
    {B : Finset ι → Subalgebra ℂ X.functionField} (hU : IsAffCover p U B) (i : ι) : IsAffineOpen (U i) := by
  simpa using hU.affine {i} ⟨i, Finset.mem_singleton_self i⟩

private theorem generic_one {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℂ} [Algebra ℂ X.functionField] {ι : Type} {U : ι → X.Opens}
    {B : Finset ι → Subalgebra ℂ X.functionField} (hU : IsAffCover p U B) (i : ι) : genericPoint X ∈ U i := by
  simpa using hU.ne {i}

private theorem conj_inv {d : ℕ} (A M P : Matrix (Fin d) (Fin d) ℂ) (hP : IsUnit P.det) (hM : M = P * A * P⁻¹) (a : ℕ) :
    (1 - M).det = (1 - A).det ∧
      (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)).coeff a =
        (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C)).coeff a := by
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hdet : P.det * P⁻¹.det = 1 := by rw [← Matrix.det_mul, hPi, Matrix.det_one]
  constructor
  · have e : 1 - M = P * (1 - A) * P⁻¹ := by
      rw [hM, Matrix.mul_sub, Matrix.sub_mul, mul_one, hPi]
    rw [e, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, mul_comm _ P.det, hdet, one_mul]
  · set Q := P.map (Polynomial.C : ℂ →+* Polynomial ℂ) with hQ
    set Q' := P⁻¹.map (Polynomial.C : ℂ →+* Polynomial ℂ) with hQ'
    have h1 : Q * Q' = 1 := by
      rw [hQ, hQ', ← Matrix.map_mul, hPi]; simp
    have hd : Q.det * Q'.det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
    have e : 1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C =
        Q * (1 + (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C) * Q' := by
      rw [hM, Matrix.map_mul, Matrix.map_mul, Matrix.mul_add, Matrix.add_mul, mul_one, h1,
        Matrix.mul_smul, Matrix.smul_mul]
    rw [e, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, mul_comm _ Q.det, hd, one_mul]

private theorem rB_map {F K L : Type} [Field F] [Field K] [Field L] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ L] [Algebra F K] [Algebra F L]
    [Algebra K L] [IsScalarTower ℂ F K] [IsScalarTower ℂ F L] [IsScalarTower ℂ K L] [IsScalarTower F K L] {d : ℕ}
    (x : Fin (d + 1) → F) (I : Finset (Fin (d + 1))) {b : K} (hb : b ∈ rB ℂ K x I) : algebraMap K L b ∈ rB ℂ L x I := by
  have hb' : IsIntegral (rA ℂ x I) b := hb
  have h : IsIntegral (rA ℂ x I) (algebraMap K L b) := hb'.algebraMap
  exact h

end UpperTheory.A

theorem UpperTheory.Cb.holomorphic_lefschetz_finiteEtale_integral :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s], IsProjOver s →
      ∀ (Y : Scheme.{0}) [IsIntegral Y] (s' : Y ⟶ Sp ℂ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1], IsFinite c2 → Etale c2 →
      ∀ (F : Finset (CxPts s' (RingHom.id ℂ))), (∀ y, y ∈ F ↔ y.1 ≫ c1 = y.1 ≫ c2) →
      ∀ A : CxPts s' (RingHom.id ℂ) → Matrix (Fin d) (Fin d) ℂ, (∀ y ∈ F, GlobalTheory.W1.IsTan d c1 c2 h1 h2 y (A y) ∧ (1 - A y).det ≠ 0) →
      ∀ a : ℕ, (∀ b, FiniteDimensional ℂ (hodgeH s a b)) ∧
        ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _ (hodgeTrace h1 a b ∘ₗ hodgePull h2 a b) =
          ∑ y ∈ F, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a / (1 - A y).det := by
  classical
  intro Z _ s d _ hP Y _ s' c1 c2 h1 h2 _ _ hf2 he2 Fx hF A hA a
  haveI := hf2
  haveI := he2
  haveI : SmoothOfRelativeDimension d s' := by
    subst h1
    have h0 : SmoothOfRelativeDimension 0 c1 := (Etale.iff_smoothOfRelativeDimension_zero c1).1 inferInstance
    have h3 : SmoothOfRelativeDimension (0 + d) (c1 ≫ s) := smoothOfRelativeDimension_comp 0 d c1 s
    rwa [Nat.zero_add] at h3
  have hfin := fun b => UpperTheory.finiteDimensional_hodgeCohomology_of_smooth_proj Z s d hP a b
  refine ⟨hfin, ?_⟩
  letI iK : Algebra ℂ Z.functionField := ffAlg s
  letI iL : Algebra ℂ Y.functionField := ffAlg s'
  obtain ⟨ψ, hψ⟩ := UpperTheory.A.exists_ffMap s s' c1 h1 rfl rfl
  obtain ⟨j2, g2⟩ := UpperTheory.A.exists_ffMap s s' c2 h2 rfl rfl
  letI : Algebra Z.functionField Y.functionField := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ Z.functionField Y.functionField := .of_algebraMap_eq fun c => (ψ.commutes c).symm
  have g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)),
      (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) =
        algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g) :=
    fun V hV hV' g => (hψ V hV hV' g).symm
  obtain ⟨F, x, U, hx, hU, hred, hS⟩ := GlobalTheory.T.exists_finiteCover_projSpace_reduced_fibre_origin Z s d rfl hP (Fx.image (UpperTheory.A.zpt c1 h1))
  letI : Algebra F Y.functionField := ((algebraMap Z.functionField Y.functionField).comp (algebraMap F Z.functionField)).toAlgebra
  haveI : @IsScalarTower F Z.functionField Y.functionField Algebra.toSMul Algebra.toSMul Algebra.toSMul := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : @IsScalarTower ℂ F Y.functionField Algebra.toSMul Algebra.toSMul Algebra.toSMul := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply ℂ Z.functionField Y.functionField c, IsScalarTower.algebraMap_apply ℂ F Z.functionField c]
    rfl
  obtain ⟨hxY, hUY⟩ := UpperTheory.A.isFinCover_pull (instK := iK) (instL := iL) (c := c1) (p := s) (p' := s') (F := F) (x := x) (U := U) h1 rfl rfl g1 hx hU
  have hredY := UpperTheory.etaleCorrespondence_fieldExtension_statement d Z Y s s' hP c1 c2 h1 h2 rfl rfl g1 j2 g2 F x U hx hU hred
  have hgen : ∀ i, genericPoint Y ∈ c1 ⁻¹ᵁ U i := fun i => UpperTheory.A.generic_one hUY i
  have pa := fun i => UpperTheory.complexPoints_bijective_algHom_affineOpen Y s' rfl (c1 ⁻¹ᵁ U i) (UpperTheory.A.affine_one hUY i) (hgen i) (rB ℂ Y.functionField x {i})
    (UpperTheory.A.ring_one hUY i (hgen i))
  have fixI := fun i => UpperTheory.etaleCorrespondence_complexPoints_statement d Z Y s s' hP c1 c2 h1 h2 rfl rfl g1 j2 g2 F x U hx hU i (hgen i)
  have hin : ∀ y ∈ Fx, y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) := fun y hy =>
    CxPts.mem_ptsIn.2 (CxPts.mem_ptsIn.1 (hS _ (Finset.mem_image_of_mem _ hy)).1)
  have hz : ∀ y ∈ Fx, ∀ e : rB ℂ Y.functionField x {0} →ₐ[ℂ] ℂ, UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U 0) (hgen 0) _ e y →
      ∀ j : Fin d, e ⟨_, tco_mem ℂ Y.functionField x j⟩ = 0 := by
    intro y hy e he j
    have hg0 := UpperTheory.A.generic_one hU 0
    obtain ⟨f, hf⟩ := (UpperTheory.A.ring_one hU 0 hg0 _).1 (tco_mem ℂ Z.functionField x j)
    have hev := (hS _ (Finset.mem_image_of_mem _ hy)).2 j hg0 f hf
    have hgerm : (Y.presheaf.germ (c1 ⁻¹ᵁ U 0) (genericPoint Y) (hgen 0)).hom ((c1.app (U 0)).hom f) =
        algebraMap F Y.functionField (x j.succ / x 0) := by
      rw [g1 _ hg0, hf]; rfl
    have hm : (Y.presheaf.germ (c1 ⁻¹ᵁ U 0) (genericPoint Y) (hgen 0)).hom ((c1.app (U 0)).hom f) ∈
        rB ℂ Y.functionField x {0} := hgerm ▸ tco_mem ℂ Y.functionField x j
    have h3 := he.2 _ hm
    rw [UpperTheory.complexPoint_eval_pullback_section Z Y s s' c1 h1 _ f y he.1] at h3
    rw [hev] at h3
    rw [← h3]
    exact congrArg e (Subtype.ext hgerm.symm)
  have hex : ∀ y : {y // y ∈ Fx}, ∃ e : fib ℂ Y.functionField x, UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U 0) (hgen 0) _ e.1 y.1 := by
    rintro ⟨y, hy⟩
    obtain ⟨e, he, -⟩ := (pa 0).2 y (hin y hy)
    exact ⟨⟨e, hz y hy e he⟩, he⟩
  choose ef hef using hex
  have hefu : ∀ (y : {y // y ∈ Fx}) (e : fib ℂ Y.functionField x), UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U 0) (hgen 0) _ e.1 y.1 → e = ef y :=
    fun y e he => Subtype.ext (((pa 0).2 y.1 (hin y.1 y.2)).unique he (hef y))
  have hinj : Function.Injective ef := by
    intro y y' h
    have h' : UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U 0) (hgen 0) _ (ef y).1 y'.1 := h ▸ hef y'
    exact Subtype.ext (((pa 0).1 (ef y).1).unique (hef y) h')
  let Fx' : Finset (fib ℂ Y.functionField x) := Finset.univ.image ef
  have hFx' : ∀ e : fib ℂ Y.functionField x, e ∈ Fx' ↔ IsFix (rB ℂ Y.functionField x {0}) e.1 j2 (rB ℂ Z.functionField x {0}) := by
    intro e
    constructor
    · intro he
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 he
      exact (fixI 0 _ y.1 (hef y)).2 ((hF y.1).1 y.2)
    · intro he
      obtain ⟨y, hy, -⟩ := (pa 0).1 e.1
      have hyF : y ∈ Fx := (hF y).2 ((fixI 0 _ y hy).1 he)
      exact Finset.mem_image.2 ⟨⟨y, hyF⟩, Finset.mem_univ _, (hefu ⟨y, hyF⟩ e hy).symm⟩
  have hmg := fun (e : fib ℂ Y.functionField x) =>
    UpperTheory.exists_regular_parameters_of_reduced_quotient F Y.functionField d x hxY hredY e.1 e.2

  have hrow : ∀ e : fib ℂ Y.functionField x, ∃ M : Matrix (Fin d) (Fin d) ℂ, e ∈ Fx' → ∀ m : Fin d,
      ∃ (c : Y.functionField) (hc : c ∈ rB ℂ Y.functionField x {0}) (g : Fin d → Y.functionField)
        (hg : ∀ l, g l ∈ rB ℂ Y.functionField x {0}), e.1 ⟨c, hc⟩ ≠ 0 ∧
        c * j2 (algebraMap F Z.functionField (x m.succ / x 0)) = ∑ l, g l * algebraMap F Y.functionField (x l.succ / x 0) ∧
        ∀ l, e.1 ⟨g l, hg l⟩ = e.1 ⟨c, hc⟩ * M m l := by
    intro e
    by_cases he : e ∈ Fx'
    · have hfix := (hFx' e).1 he
      have row : ∀ m : Fin d, ∃ r : Fin d → ℂ,
          ∃ (c : Y.functionField) (hc : c ∈ rB ℂ Y.functionField x {0}) (g : Fin d → Y.functionField)
            (hg : ∀ l, g l ∈ rB ℂ Y.functionField x {0}), e.1 ⟨c, hc⟩ ≠ 0 ∧
            c * j2 (algebraMap F Z.functionField (x m.succ / x 0)) = ∑ l, g l * algebraMap F Y.functionField (x l.succ / x 0) ∧
            ∀ l, e.1 ⟨g l, hg l⟩ = e.1 ⟨c, hc⟩ * r l := by
        intro m
        obtain ⟨b0, hb0, hbv, hne, hval⟩ := hfix _ (tco_mem ℂ Z.functionField x m)
          (UpperTheory.A.rB_map x {0} (tco_mem ℂ Z.functionField x m))
        have h0 : e.1 ⟨_, UpperTheory.A.rB_map x {0} (tco_mem ℂ Z.functionField x m)⟩ = 0 := by
          exact (congrArg e.1 (Subtype.ext (IsScalarTower.algebraMap_apply F Z.functionField Y.functionField _).symm)).trans
            (e.2 m)
        rw [h0, mul_zero] at hval
        obtain ⟨c', g', hc', hcg⟩ := hmg e ⟨_, hbv⟩ hval
        have hcg' := congrArg Subtype.val hcg
        refine ⟨fun l => e.1 (g' l) / e.1 (c' * ⟨b0, hb0⟩), (c' : Y.functionField) * b0, (c' * ⟨b0, hb0⟩ : rB ℂ Y.functionField x {0}).2,
          fun l => (g' l : Y.functionField), fun l => (g' l).2, ?_, ?_, ?_⟩
        · change e.1 (c' * ⟨b0, hb0⟩) ≠ 0
          rw [map_mul]
          exact mul_ne_zero hc' hne
        · rw [mul_assoc]
          simpa using hcg'
        · intro l
          have hne' : e.1 (c' * ⟨b0, hb0⟩) ≠ 0 := by
            rw [map_mul]
            exact mul_ne_zero hc' hne
          change e.1 (g' l) = e.1 (c' * ⟨b0, hb0⟩) * (e.1 (g' l) / e.1 (c' * ⟨b0, hb0⟩))
          field_simp
      choose r hr using row
      exact ⟨Matrix.of r, fun _ m => hr m⟩
    · exact ⟨0, fun h => absurd h he⟩
  choose A' hA' using hrow
  have hconj : ∀ y : {y // y ∈ Fx}, ∃ P : Matrix (Fin d) (Fin d) ℂ, IsUnit P.det ∧ A' (ef y) = P * A y.1 * P⁻¹ := fun y =>
    UpperTheory.etaleCorrespondence_local_parameters_statement d Z Y s s' hP c1 c2 h1 h2 rfl rfl g1 j2 g2 F x U hx hU hred y.1 ((hF y.1).1 y.2) (A y.1) (hA y.1 y.2).1
      (hgen 0) (ef y).1 (hef y) (ef y).2 (A' (ef y)) (hA' (ef y) (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hinv : ∀ y : {y // y ∈ Fx}, (1 - A' (ef y)).det = (1 - A y.1).det ∧
      (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A' (ef y)).map Polynomial.C)).coeff a =
        (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y.1).map Polynomial.C)).coeff a := fun y => by
    obtain ⟨P, hPu, hPe⟩ := hconj y
    exact UpperTheory.A.conj_inv (A y.1) (A' (ef y)) P hPu hPe a
  obtain ⟨E, nP, nT⟩ := GlobalTheory.T.exists_hodge_cohomology_equiv_cech_differentials
  have key := GlobalTheory.T.exists_chart_lift_of_finite_cover d a F Z.functionField Y.functionField x j2 hx hxY
    (UpperTheory.etaleCorrespondence_sections_statement d Z Y s s' hP c1 c2 h1 h2 rfl rfl g1 j2 g2 F x U hx hU) hredY
    (by
      intro i hi e hfix
      obtain ⟨l, rfl⟩ := Fin.exists_succ_eq.2 hi
      obtain ⟨y, hy, -⟩ := (pa l.succ).1 e
      have hyF : y ∈ Fx := (hF y).2 ((fixI l.succ e y hy).1 hfix)
      exact UpperTheory.etaleCorrespondence_differentials_statement d Z Y s s' hP c1 c2 h1 h2 rfl rfl g1 j2 g2 F x U hx hU l (hgen _) (hgen 0) e (ef ⟨y, hyF⟩).1 y hy
        (hef ⟨y, hyF⟩) ((ef ⟨y, hyF⟩).2 l))
    (by
      intro e hfix
      obtain ⟨y, hy, -⟩ := (pa 0).1 e
      exact hz y ((hF y).2 ((fixI 0 e y hy).1 hfix)) e hy)
    Fx' hFx'
    (by
      intro e _ b hb1 hb hb0
      let ι : rB ℂ Z.functionField x {0} →ₐ[ℂ] rB ℂ Y.functionField x {0} :=
        ((IsScalarTower.toAlgHom ℂ Z.functionField Y.functionField).comp (rB ℂ Z.functionField x {0}).val).codRestrict _
          fun v => UpperTheory.A.rB_map x {0} v.2
      obtain ⟨c, g, hc, hcg⟩ := UpperTheory.exists_regular_parameters_of_reduced_quotient F Z.functionField d x hx hred (e.1.comp ι)
        (fun j => (congrArg e.1 (Subtype.ext
          (IsScalarTower.algebraMap_apply F Z.functionField Y.functionField _).symm)).trans (e.2 j)) ⟨b, hb⟩ hb0
      refine ⟨c, (ι c).2, c.2, hc, fun l => g l, fun l => (g l).2, ?_⟩
      simpa using congrArg Subtype.val hcg)
    A' hA'
    (by
      intro e he
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 he
      rw [(hinv y).1]
      exact (hA y.1 y.2).2)
    (fun p => (E d Z s _ U (rB ℂ Z.functionField x) rfl hU a p).conj (hodgeTrace h1 a p ∘ₗ hodgePull h2 a p))
    (fun p b hb => UpperTheory.etaleCorrespondence_family_statement E nP nT d Z Y s s' hP c1 c2 h1 h2 rfl rfl g1 j2 g2 F x U hx hU hUY a p b hb)
    (fun p => haveI := hfin p; Module.Finite.equiv (E d Z s _ U (rB ℂ Z.functionField x) rfl hU a p))
  calc _ = _ := Finset.sum_congr rfl fun p _ => by
          haveI := hfin p
          rw [← LinearMap.trace_conj' (hodgeTrace h1 a p ∘ₗ hodgePull h2 a p) (E d Z s _ U (rB ℂ Z.functionField x) rfl hU a p)]
    _ = _ := key
    _ = _ := by
      rw [Finset.sum_image fun y _ y' _ h => hinj h, ← Finset.sum_coe_sort Fx]
      exact Finset.sum_congr rfl fun y _ => by rw [(hinv y).1, (hinv y).2]
