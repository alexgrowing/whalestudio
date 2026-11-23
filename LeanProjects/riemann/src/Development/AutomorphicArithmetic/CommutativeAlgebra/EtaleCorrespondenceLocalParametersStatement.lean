import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EFam
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsSeparatedOfProj
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFiniteQCOmega
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.TanConjEt
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsUnitMulMemSpanOfReducedIsolatedZero
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteEtaleFunctionFieldGermCompatOfSmooth
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCotangentMapLocalizationAway
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCotangentMapDualBasisOfParameters
import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteFiberOfFiniteTypeParameterRing
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 KaehlerDifferential
open scoped TensorProduct
set_option autoImplicit false

namespace UpperTheory.EvaluationRestriction

section Pts

variable {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} {y : CxPts s' (RingHom.id ℂ)}

private theorem ev_r {V W : Y.Opens} (h : W ≤ V) (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) W) (f : Sec s' V) :
    CxPts.ev s' (RingHom.id ℂ) W (Sec.res s' h f) y = CxPts.ev s' (RingHom.id ℂ) V f y :=
  CxPts.ev_res h hy f

private noncomputable def evA {V : Y.Opens} (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) : Sec s' V →ₐ[ℂ] ℂ :=
  { (CxPts.evHom hy : Sec s' V →+* ℂ) with
    commutes' := fun a => by
      have h := CxPts.ev_algX (p := s') (σ := RingHom.id ℂ) hy a
      rw [CxPts.ev_eq hy] at h
      exact h }

private theorem evA_apply {V : Y.Opens} (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) (b : Sec s' V) :
    evA hy b = CxPts.ev s' (RingHom.id ℂ) V b y := (CxPts.ev_eq hy b).symm

private theorem res_self (V : Y.Opens) (b : Sec s' V) : Sec.res s' (le_refl V) b = b := by
  change (Y.presheaf.map (homOfLE (le_refl V)).op).hom b = b
  simp
  rfl

private def Fr (y : CxPts s' (RingHom.id ℂ)) {V0 W : Y.Opens} (h : W ≤ V0) : Prop :=
  ∀ w : Sec s' W, ∃ a p : Sec s' V0, CxPts.ev s' (RingHom.id ℂ) V0 p y ≠ 0 ∧ Sec.res s' h a = Sec.res s' h p * w

private theorem fr_refl (V0 : Y.Opens) (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V0) : Fr y (le_refl V0) := fun w => by
  refine ⟨w, 1, ?_, ?_⟩
  · rw [← evA_apply hy, map_one]; exact one_ne_zero
  · rw [map_one, one_mul, res_self]

private theorem fr_step {V0 V : Y.Opens} (hV : IsAffineOpen V) (h : V ≤ V0) (H : Fr y h) (f : Γ(Y, V))
    (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (Y.basicOpen f)) : Fr y ((Y.basicOpen_le f).trans h) := by
  intro w
  have hyV : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V := CxPts.ptsIn_mono (Y.basicOpen_le f) hy
  have hy0 : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V0 := CxPts.ptsIn_mono h hyV
  have hL := hV.isLocalization_basicOpen f
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f (show Γ(Y, Y.basicOpen f) from w)
  have hf0 : CxPts.ev s' (RingHom.id ℂ) V f y ≠ 0 := (CxPts.mem_ptsIn_basicOpen hyV f).1 hy
  obtain ⟨F, hF⟩ : ∃ F : Sec s' V, F = f := ⟨f, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Sec s' V, A = a := ⟨a, rfl⟩
  have ha' : w * Sec.res s' (Y.basicOpen_le f) F ^ n = Sec.res s' (Y.basicOpen_le f) A := by
    rw [hF, hA]; exact ha
  rw [← hF] at hf0
  obtain ⟨a0, p0, h0, e0⟩ := H A
  obtain ⟨a1, p1, h1, e1⟩ := H F
  have ha1 : evA hy0 a1 ≠ 0 := by
    have := congrArg (evA hyV) e1
    rw [map_mul, evA_apply hyV, evA_apply hyV, evA_apply hyV, ev_r h hyV, ev_r h hyV] at this
    rw [evA_apply hy0, this]
    exact mul_ne_zero h1 hf0
  refine ⟨p1 ^ n * a0, a1 ^ n * p0, ?_, ?_⟩
  · rw [← evA_apply hy0, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero n ha1) (by rwa [evA_apply hy0])
  · simp only [Sec.res_res s' h (Y.basicOpen_le f), map_mul, map_pow, e0, e1]
    rw [← ha']
    ring

private def Pd (d : ℕ) (y : CxPts s' (RingHom.id ℂ)) (V : Y.Opens) : Prop :=
  ∃ φ : Ω[Sec s' V⁄ℂ] →ₗ[ℂ] (Fin d → ℂ),
    (∀ (b : Sec s' V) (ω : Ω[Sec s' V⁄ℂ]), φ (b • ω) = CxPts.ev s' (RingHom.id ℂ) V b y • φ ω) ∧
    Function.Surjective φ ∧
    ∀ ω : Ω[Sec s' V⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → Sec s' V) (ω' : Fin m → Ω[Sec s' V⁄ℂ]),
        (∀ i, CxPts.ev s' (RingHom.id ℂ) V (b i) y = 0) ∧ ω = ∑ i, b i • ω' i

private theorem pd_step {d : ℕ} {V : Y.Opens} (hV : IsAffineOpen V) (f : Γ(Y, V))
    (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (Y.basicOpen f)) (H : Pd d y V) : Pd d y (Y.basicOpen f) := by
  obtain ⟨φ, h1, h2, h3⟩ := H
  letI : Algebra (Sec s' V) (Sec s' (Y.basicOpen f)) := (Sec.res s' (Y.basicOpen_le f)).toRingHom.toAlgebra
  haveI : IsScalarTower ℂ (Sec s' V) (Sec s' (Y.basicOpen f)) :=
    .of_algebraMap_eq fun r => ((Sec.res s' (Y.basicOpen_le f)).commutes r).symm
  haveI : IsLocalization.Away (show Sec s' V from f) (Sec s' (Y.basicOpen f)) := hV.isLocalization_basicOpen f
  have hal : ∀ b : Sec s' V, CxPts.ev s' (RingHom.id ℂ) V b y =
      (evA hy).toRingHom (algebraMap (Sec s' V) (Sec s' (Y.basicOpen f)) b) := fun b => by
    change _ = evA hy (Sec.res s' (Y.basicOpen_le f) b)
    rw [evA_apply, ev_r _ hy]
  obtain ⟨ψ, g1, g2, g3⟩ := UpperTheory.exists_cotangent_map_localization_away (R := Sec s' V) (S := Sec s' (Y.basicOpen f)) (show Sec s' V from f)
    (evA hy).toRingHom φ (fun b ω => by rw [h1, hal]) (fun ω hω => by
      obtain ⟨m, b, ω', e1, e2⟩ := h3 ω hω
      exact ⟨m, b, ω', fun i => by rw [← hal]; exact e1 i, e2⟩)
  refine ⟨ψ, fun b ω => ?_, fun v => ?_, fun ω hω => ?_⟩
  · rw [g1]; congr 1; exact evA_apply hy b
  · obtain ⟨ω, rfl⟩ := h2 v
    exact ⟨_, g2 ω⟩
  · obtain ⟨m, b, ω', e1, e2⟩ := g3 ω hω
    exact ⟨m, b, ω', fun i => (evA_apply hy _).symm.trans (e1 i), e2⟩

end Pts

end UpperTheory.EvaluationRestriction

namespace UpperTheory.EvaluationRestriction

section Charts

variable {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℂ} [Algebra ℂ X.functionField] {ι : Type} {U : ι → X.Opens}
  {B : Finset ι → Subalgebra ℂ X.functionField}

private theorem chart_mem (h : IsAffCover p U B) (i : ι) (hg : genericPoint X ∈ U i) (b : X.functionField) :
    b ∈ B {i} ↔ ∃ f : Γ(X, U i), (X.presheaf.germ (U i) (genericPoint X) hg).hom f = b := by
  have key : ∀ (W : X.Opens) (_ : W = U i) (hn : genericPoint X ∈ W),
      (∃ f : Γ(X, W), (X.presheaf.germ W (genericPoint X) hn).hom f = b) ↔
        ∃ f : Γ(X, U i), (X.presheaf.germ (U i) (genericPoint X) hg).hom f = b := by
    rintro _ rfl _; rfl
  rw [h.ring {i} (by simp)]
  exact key _ (Finset.inf_singleton ..) _

private theorem chart_aff (h : IsAffCover p U B) (i : ι) : IsAffineOpen (U i) := by
  have := h.affine {i} (by simp)
  rwa [Finset.inf_singleton] at this

private theorem chart_gen (h : IsAffCover p U B) (i : ι) : genericPoint X ∈ U i := by
  have := h.ne {i}
  rwa [Finset.inf_singleton] at this

end Charts

section Germ

variable {Y : Scheme.{0}} [IsIntegral Y] (s' : Y ⟶ Sp ℂ)

private noncomputable def gm {V : Y.Opens} (hg : genericPoint Y ∈ V) : Sec s' V →+* Y.functionField :=
  (Y.presheaf.germ V (genericPoint Y) hg).hom

private theorem gm_res {V W : Y.Opens} (h : W ≤ V) (hg : genericPoint Y ∈ V) (hW : genericPoint Y ∈ W) (b : Sec s' V) :
    gm s' hW (Sec.res s' h b) = gm s' hg b :=
  Y.presheaf.germ_res_apply (homOfLE h) _ hW b

private theorem gm_inj {V : Y.Opens} (hg : genericPoint Y ∈ V) : Function.Injective (gm s' hg) :=
  germ_injective_of_isIntegral Y _ hg

private theorem gm_alg [inst : Algebra ℂ Y.functionField]
    (hi : algebraMap ℂ Y.functionField = @algebraMap ℂ Y.functionField _ _ (ffAlg s')) {V : Y.Opens}
    (hg : genericPoint Y ∈ V) (r : ℂ) : gm s' hg (algebraMap ℂ (Sec s' V) r) = algebraMap ℂ Y.functionField r := by
  rw [hi]
  change (Y.presheaf.germ V _ hg).hom ((s'.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) =
    (Y.presheaf.germ ⊤ _ trivial).hom (s'.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r))
  exact Y.presheaf.germ_res_apply (homOfLE le_top) _ hg (s'.appTop.hom _)

end Germ

end UpperTheory.EvaluationRestriction

open UpperTheory.EvaluationRestriction in
theorem UpperTheory.etaleCorrespondence_local_parameters_statement :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)), IsReduced ((rB ℂ Z.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ Z.functionField x j⟩ : rB ℂ Z.functionField x {0})))) → ∀ (y : CxPts s' (RingHom.id ℂ)), y.1 ≫ c1 = y.1 ≫ c2 → ∀ A : Matrix (Fin d) (Fin d) ℂ, IsTan d c1 c2 h1 h2 y A → ∀ (hg : genericPoint Y ∈ c1 ⁻¹ᵁ U 0) (e : rB ℂ Y.functionField x {0} →ₐ[ℂ] ℂ), UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U 0) hg _ e y → (∀ j : Fin d, e ⟨_, tco_mem ℂ Y.functionField x j⟩ = 0) → ∀ M : Matrix (Fin d) (Fin d) ℂ, (∀ m : Fin d, ∃ (c : Y.functionField) (hc : c ∈ rB ℂ Y.functionField x {0}) (g : Fin d → Y.functionField) (hgl : ∀ l, g l ∈ rB ℂ Y.functionField x {0}), e ⟨c, hc⟩ ≠ 0 ∧ c * j2 (algebraMap F Z.functionField (x m.succ / x 0)) = ∑ l, g l * algebraMap F Y.functionField (x l.succ / x 0) ∧ ∀ l, e ⟨g l, hgl l⟩ = e ⟨c, hc⟩ * M m l) → ∃ P : Matrix (Fin d) (Fin d) ℂ, IsUnit P.det ∧ M = P * A * P⁻¹ := by
  intro d Z Y _ _ s s' _ _ hPr c1 c2 h1 h2 _ _ _ _ inst inst' hinst hinst' _ _ g1 j2 hj2 F _ _ _ _ _ _ _ x U hFC hAC hredZ y hfix A hA hg0 e hMt hz M hM
  have hj1 := fun V hV hV' g => (g1 V hV hV' g).symm
  have hAC' := (UpperTheory.A.isFinCover_pull h1 hinst hinst' g1 hFC hAC).2
  have hred := UpperTheory.Cb.finite_etale_function_field_germ_compat_of_smooth d Z Y s s' c1 h1 inferInstance inferInstance hinst hinst' hj1 F x U hFC hAC hAC' hredZ
  have hy := hMt.1
  have he := fun (_ : genericPoint Y ∈ c1 ⁻¹ᵁ U 0) => hMt.2
  have hgZ : genericPoint Z ∈ U 0 := chart_gen hAC 0
  have hgY : genericPoint Y ∈ c1 ⁻¹ᵁ U 0 := chart_gen hAC' 0
  have hV0 : IsAffineOpen (c1 ⁻¹ᵁ U 0) := chart_aff hAC' 0
  have hU0 : IsAffineOpen (U 0) := chart_aff hAC 0
  choose τ hτ using fun l : Fin d => (chart_mem hAC 0 hgZ _).1 (tco_mem ℂ Z.functionField x l)
  have memB : ∀ f : Sec s' (c1 ⁻¹ᵁ U 0), gm s' hgY f ∈ rB ℂ Y.functionField x {0} := fun f =>
    (chart_mem hAC' 0 hgY _).2 ⟨f, rfl⟩
  have evB : ∀ f : Sec s' (c1 ⁻¹ᵁ U 0), e ⟨gm s' hgY f, memB f⟩ = CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) f y :=
    fun f => he hgY f (memB f)
  have germT : ∀ l : Fin d, gm s' hgY (appSec s s' c1 (U 0) (τ l)) = algebraMap F Y.functionField (x l.succ / x 0) := fun l => by
    change (Y.presheaf.germ (c1 ⁻¹ᵁ U 0) (genericPoint Y) hgY).hom (c1.app (U 0) (τ l)) = _
    rw [← hj1 (U 0) hgZ hgY (τ l), hτ, ← IsScalarTower.algebraMap_apply]
  have evT : ∀ l : Fin d, CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) (appSec s s' c1 (U 0) (τ l)) y = 0 := fun l => by
    rw [← evB, ← hz l]
    exact congrArg e (Subtype.ext (germT l))

  have hftB : Algebra.FiniteType ℂ (rB ℂ Y.functionField x {0}) := by
    haveI : Smooth s' := SmoothOfRelativeDimension.smooth d s'
    haveI := GlobalTheory.HodgeFin.finiteType_sec s' hV0
    let gA : Sec s' (c1 ⁻¹ᵁ U 0) →ₐ[ℂ] rB ℂ Y.functionField x {0} :=
      { toFun := fun f => ⟨gm s' hgY f, memB f⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun a b => Subtype.ext (map_mul _ a b)
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun a b => Subtype.ext (map_add _ a b)
        commutes' := fun r => Subtype.ext (gm_alg s' hAC'.alg hgY r) }
    refine Algebra.FiniteType.of_surjective gA fun b => ?_
    obtain ⟨f, hf⟩ := (chart_mem hAC' 0 hgY _).1 b.2
    exact ⟨f, Subtype.ext hf⟩
  have hQ0 : ∀ u : Sec s' (c1 ⁻¹ᵁ U 0), CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) u y = 0 →
      ∃ (c : Sec s' (c1 ⁻¹ᵁ U 0)) (g : Fin d → Sec s' (c1 ⁻¹ᵁ U 0)),
        CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) c y ≠ 0 ∧ c * u = ∑ l, g l * appSec s s' c1 (U 0) (τ l) := by
    intro u hu
    have hfin := UpperTheory.finite_fiber_of_finiteType_parameter_ring F Y.functionField d x hFC.pd hftB
    obtain ⟨c, g, hc, hcg⟩ := UpperTheory.Cb.exists_unit_mul_mem_span_of_reduced_isolated_zero (rB ℂ Y.functionField x {0}) d
      (fun j => ⟨_, tco_mem ℂ Y.functionField x j⟩) hred hfin e hz ⟨gm s' hgY u, memB u⟩ (by rw [evB]; exact hu)
    have onto : ∀ b : rB ℂ Y.functionField x {0}, ∃ f : Sec s' (c1 ⁻¹ᵁ U 0), gm s' hgY f = b := fun b =>
      (chart_mem hAC' 0 hgY _).1 b.2
    obtain ⟨c', hc'⟩ := onto c
    choose g' hg' using fun l => onto (g l)
    refine ⟨c', g', ?_, ?_⟩
    · rw [← evB]
      have : (⟨gm s' hgY c', memB c'⟩ : rB ℂ Y.functionField x {0}) = c := Subtype.ext hc'
      rw [this]; exact hc
    · apply gm_inj s' hgY
      have h := congrArg Subtype.val hcg
      simp only [Subalgebra.coe_mul, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul] at h
      rw [map_mul, map_sum]
      simp only [map_mul]
      refine Eq.trans ?_ (h.trans ?_)
      · exact congrArg (· * gm s' hgY u) hc'
      · exact Finset.sum_congr rfl fun l _ => by rw [germT]; exact congrArg (· * _) (hg' l).symm

  have hA0 := hA
  obtain ⟨UA, VA, hA1, hA2, tA, hyA, hUA, hVA, φA, hφs, hφ1, hφ2, hφk⟩ := hA
  have pdVA : Pd d y VA := by
    refine ⟨φA, hφs, fun v => ⟨∑ l, v l • D ℂ (Sec s' VA) (Sec.res s' hA1 (appSec s s' c1 UA (tA l))), ?_⟩, hφk⟩
    rw [map_sum]
    simp only [map_smul, hφ1]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]

  have hpt : ∀ W : Y.Opens, y ∈ CxPts.ptsIn s' (RingHom.id ℂ) W ↔ y.1 (IsLocalRing.closedPoint ℂ) ∈ W := fun W => CxPts.mem_ptsIn
  have hy2 : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c2 ⁻¹ᵁ U 0) := by
    rw [hpt]
    have h0 := (hpt _).1 hy
    have h3 : c2 (y.1 (IsLocalRing.closedPoint ℂ)) = c1 (y.1 (IsLocalRing.closedPoint ℂ)) := by
      have := congrArg (fun q : Sp ℂ ⟶ Z => q (IsLocalRing.closedPoint ℂ)) hfix
      simpa [Function.comp] using this.symm
    change c2 (y.1 (IsLocalRing.closedPoint ℂ)) ∈ U 0
    rw [h3]
    exact h0

  obtain ⟨hh, hhle, hhy⟩ := hV0.exists_basicOpen_le (V := c2 ⁻¹ᵁ U 0) ⟨_, (hpt _).1 hy2⟩ ((hpt _).1 hy)
  have hV1 : IsAffineOpen (Y.basicOpen hh) := hV0.basicOpen hh
  obtain ⟨f, g, hfg, hfy⟩ := exists_basicOpen_le_affine_inter hVA hV1 (y.1 (IsLocalRing.closedPoint ℂ)) ⟨(hpt _).1 hyA, hhy⟩
  have hW : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (Y.basicOpen g) := (hpt _).2 (hfg ▸ hfy)
  have pdW : Pd d y (Y.basicOpen g) := hfg ▸ pd_step hVA f ((hpt _).2 hfy) pdVA
  have frV1 : Fr y ((Y.basicOpen_le hh).trans (le_refl (c1 ⁻¹ᵁ U 0))) :=
    fr_step hV0 le_rfl (fr_refl _ hy) hh ((hpt _).2 hhy)
  have hWle : Y.basicOpen g ≤ c1 ⁻¹ᵁ U 0 := (Y.basicOpen_le g).trans ((Y.basicOpen_le hh).trans (le_refl _))
  have frW : Fr y hWle := fr_step hV1 _ frV1 g hW
  have hW2 : Y.basicOpen g ≤ c2 ⁻¹ᵁ U 0 := (Y.basicOpen_le g).trans hhle
  have hVW : IsAffineOpen (Y.basicOpen g) := hV1.basicOpen g
  have hy0W : ∀ b : Sec s' (c1 ⁻¹ᵁ U 0), evA hW (Sec.res s' hWle b) = CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) b y :=
    fun b => by rw [evA_apply, ev_r hWle hW]
  obtain ⟨t, ht⟩ : ∃ t : Fin d → Sec s' (Y.basicOpen g), t = fun l => Sec.res s' hWle (appSec s s' c1 (U 0) (τ l)) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Fin d → Sec s' (Y.basicOpen g), u = fun m => Sec.res s' hW2 (appSec s s' c2 (U 0) (τ m)) := ⟨_, rfl⟩
  have evt : ∀ l, evA hW (t l) = 0 := fun l => by rw [ht]; exact (hy0W _).trans (evT l)
  have evu : ∀ m, evA hW (u m) = 0 := fun m => by
    rw [hu]
    refine (evA_apply hW _).trans ((ev_r hW2 hW _).trans ?_)
    refine Eq.trans ?_ (evT m)
    change valR y.1 (c2 ⁻¹ᵁ U 0) (c2.app (U 0) (τ m)) = valR y.1 (c1 ⁻¹ᵁ U 0) (c1.app (U 0) (τ m))
    rw [← GlobalTheory.Points.valR_comp, ← GlobalTheory.Points.valR_comp, hfix]
  have hQW : ∀ w : Sec s' (Y.basicOpen g), evA hW w = 0 → ∃ (c : Sec s' (c1 ⁻¹ᵁ U 0)) (q : Fin d → Sec s' (c1 ⁻¹ᵁ U 0)),
      CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) c y ≠ 0 ∧
        Sec.res s' hWle c * w = ∑ l, Sec.res s' hWle (q l) * t l := by
    intro w hw
    obtain ⟨a, p, hp, hap⟩ := frW w
    have ha : CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) a y = 0 := by
      rw [← hy0W, hap, map_mul, hw, mul_zero]
    obtain ⟨c, q, hc, hcq⟩ := hQ0 a ha
    refine ⟨c * p, q, ?_, ?_⟩
    · rw [← hy0W, map_mul, map_mul, hy0W, hy0W]
      exact mul_ne_zero hc hp
    · rw [map_mul, mul_assoc, ← hap, ← map_mul, hcq, map_sum, ht]
      simp only [map_mul]
  obtain ⟨ψ, p1, p2, p3⟩ := pdW
  obtain ⟨φ, q1, q2, q3, q4⟩ := UpperTheory.exists_cotangent_map_dual_basis_of_parameters (evA hW) t ψ (fun b ω => by rw [p1, evA_apply]) p2 evt
    (fun w hw => by
      obtain ⟨c, q, hc, hcq⟩ := hQW w hw
      exact ⟨Sec.res s' hWle c, fun l => Sec.res s' hWle (q l), by rwa [hy0W], hcq⟩)
  obtain ⟨A', hA'⟩ : ∃ A' : Matrix (Fin d) (Fin d) ℂ, ∀ m, (fun l => A' m l) = φ (D ℂ (Sec s' (Y.basicOpen g)) (u m)) :=
    ⟨Matrix.of fun m l => φ (D ℂ (Sec s' (Y.basicOpen g)) (u m)) l, fun m => rfl⟩
  have hTan : IsTan d c1 c2 h1 h2 y A' := by
    refine ⟨U 0, Y.basicOpen g, hWle, hW2, τ, hW, hU0, hVW, φ, fun b ω => ?_, fun l => ?_, fun j => ?_, fun ω hω => ?_⟩
    · rw [q1, evA_apply]
    · have := q2 l
      rw [ht] at this
      exact this
    · have := hA' j
      rw [hu] at this
      exact this.symm
    · exact p3 ω (q3 ω hω)
  obtain ⟨P, hP, hAP⟩ := UpperTheory.Gal.productCup_of_system.tanConj_etale Z Y s s' d c1 c2 h1 h2 y ‹Etale c1› hfix A A' hA0 hTan
  refine ⟨P, hP, Eq.trans ?_ hAP⟩
  ext m l
  obtain ⟨c0, hc0, g0, hg0', hc, hcq0, hval⟩ := hM m
  obtain ⟨c, hc'⟩ : ∃ f : Sec s' (c1 ⁻¹ᵁ U 0), gm s' hgY f = c0 := (chart_mem hAC' 0 hgY _).1 hc0
  choose q hq using fun l => (show ∃ f : Sec s' (c1 ⁻¹ᵁ U 0), gm s' hgY f = g0 l from (chart_mem hAC' 0 hgY _).1 (hg0' l))
  have hgW : genericPoint Y ∈ Y.basicOpen g :=
    ((genericPoint_spec Y).mem_open_set_iff (Y.basicOpen g).isOpen).2 ⟨_, trivial, (hpt _).1 hW⟩
  have hg2 : genericPoint Y ∈ c2 ⁻¹ᵁ U 0 := hW2 hgW
  have hju : gm s' hgW (u m) = j2 (algebraMap F Z.functionField (x m.succ / x 0)) := by
    rw [hu]
    refine (gm_res s' hW2 hg2 hgW _).trans ?_
    rw [← hτ m]
    exact (hj2 (U 0) hgZ hg2 (τ m)).symm
  have htl : ∀ l, gm s' hgW (t l) = algebraMap F Y.functionField (x l.succ / x 0) := fun l => by
    rw [ht]
    exact (gm_res s' hWle hgY hgW _).trans (germT l)
  have hcq : Sec.res s' hWle c * u m = ∑ l, Sec.res s' hWle (q l) * t l := by
    apply gm_inj s' hgW
    rw [map_mul, map_sum, gm_res s' hWle hgY hgW, hju, hc', hcq0]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, gm_res s' hWle hgY hgW, htl, hq]
  have ec : CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) c y = e ⟨c0, hc0⟩ := by
    rw [← evB]; exact congrArg e (Subtype.ext hc')
  have eq : CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) (q l) y = e ⟨g0 l, hg0' l⟩ := by
    rw [← evB]; exact congrArg e (Subtype.ext (hq l))
  have h := q4 (u m) (Sec.res s' hWle c) (fun l => Sec.res s' hWle (q l)) (evu m) (by rw [hy0W, ec]; exact hc) hcq l
  rw [hy0W, hy0W, ec, eq, hval l] at h
  exact (mul_left_cancel₀ hc h).trans (congrFun (hA' m) l).symm
