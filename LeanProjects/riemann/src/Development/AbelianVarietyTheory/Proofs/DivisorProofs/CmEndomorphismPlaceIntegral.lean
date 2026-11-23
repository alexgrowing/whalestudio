import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullByCompAlt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendsTo
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionOfFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIsogenousDedekind
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFieldExtensionBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPolarisedAbelianSchemeBaseChangeRingAction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.BirigidLift
open scoped nonZeroDivisors
open scoped CategoryTheory.Obj

namespace GlobalTheory.PlaceModel

set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
attribute [local instance] Over.cartesianMonoidalCategory in
open scoped nonZeroDivisors in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.PlaceModel.exists_factor_pullback {S S' S'' : Scheme.{0}} {G : Over S}
    {G' : Over S'} {G'' : Over S''} [GrpObj G]
    [GrpObj G'] [GrpObj G''] {f : S' ⟶ S} {c : S'' ⟶ S} {φ : G'.left ⟶ G.left}
    {ψ : G''.left ⟶ G.left}
    (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f φ) (n : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G c ψ) (g : S'' ⟶ S') (e : g ≫ f = c) :
    ∃ φ' : G''.left ⟶ G'.left, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G' g φ' ∧ φ' ≫ φ = ψ := by
  subst e
  obtain ⟨hφ, hφm⟩ := h
  obtain ⟨hψ, hψm⟩ := n
  refine ⟨hφ.lift ψ (G''.hom ≫ g) (by rw [hψ.w, Category.assoc]), ⟨?_, ?_⟩, hφ.lift_fst _ _ _⟩
  · refine IsPullback.of_right ?_ (hφ.lift_snd _ _ _) hφ
    rwa [hφ.lift_fst]
  · intro T x y x₀ y₀ hx hy
    apply hφ.hom_ext
    · rw [Category.assoc, hφ.lift_fst]
      let u : Over.mk ((T.hom ≫ g) ≫ f) ⟶ Over.mk (T.hom ≫ g ≫ f) :=
        Over.homMk (𝟙 T.left) (by simp)
      let x₁ : Over.mk (T.hom ≫ g ≫ f) ⟶ G := Over.homMk (x.left ≫ ψ) (by
        simp only [Over.mk_hom, Category.assoc, hψ.w]; simp only [← Category.assoc, Over.w])
      let y₁ : Over.mk (T.hom ≫ g ≫ f) ⟶ G := Over.homMk (y.left ≫ ψ) (by
        simp only [Over.mk_hom, Category.assoc, hψ.w]; simp only [← Category.assoc, Over.w])
      have hψxy := hψm T x y x₁ y₁ rfl rfl
      have hφxy := hφm (Over.mk (T.hom ≫ g)) x₀ y₀ (u ≫ x₁) (u ≫ y₁)
        (by simp [u, x₁, hx, hφ.lift_fst]) (by simp [u, y₁, hy, hφ.lift_fst])
      rw [← hφxy, ← hψxy, ← comp_mul]
      simp [u]
    · rw [Category.assoc, hφ.lift_snd, ← Category.assoc, Over.w, Over.w]
      rfl

theorem descends_of_generators : ∀ {U S : Scheme.{0}} (j : U ⟶ S) {G H : Over S} [GrpObj G] [GrpObj H] {G' H' : Over U} [GrpObj G']
    [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}, IsGrpPullback G' G j φ → IsGrpPullback H' H j ψ →
    ∀ (M : Type) [AddCommGroup M] (s : Set M), Submodule.span ℤ s = ⊤ → ∀ (e : M → (G' ⟶ H')),
    (∀ x y, e (x + y) = e x * e y) → (∀ x ∈ s, ∃ F : G ⟶ H, (e x).left ≫ ψ = φ ≫ F.left) →
    ∀ x, ∃ F : G ⟶ H, (e x).left ≫ ψ = φ ≫ F.left := by
  intro U S j G H _ _ G' H' _ _ φ ψ hG hH M _ s hs e he hgen x
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hG.1.w
  let θ : (G' ⟶ H') → (Over.mk (G'.hom ≫ j) ⟶ H) := fun f ↦ Over.homMk (f.left ≫ ψ) (by
    change (f.left ≫ ψ) ≫ H.hom = G'.hom ≫ j
    rw [Category.assoc, hH.1.w, ← Category.assoc, Over.w f])
  let Θ : (G' ⟶ H') →* (Over.mk (G'.hom ≫ j) ⟶ H) := MonoidHom.mk' θ fun a b ↦
    Over.OverMorphism.ext (hH.2 G' a b (θ a) (θ b) rfl rfl).symm
  let Ξ : (G ⟶ H) →* (Over.mk (G'.hom ≫ j) ⟶ H) := MonoidHom.mk' (fun F ↦ φ₀ ≫ F) fun a b ↦ MonObj.comp_mul _ _ _
  have e0 : e 0 = 1 := by
    have h := he 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  let K : AddSubgroup M :=
    { carrier := {x | Θ (e x) ∈ Ξ.range}
      zero_mem' := by
        change Θ (e 0) ∈ Ξ.range
        rw [e0, map_one]; exact one_mem _
      add_mem' := fun {a b} ha hb ↦ by
        change Θ (e (a + b)) ∈ Ξ.range
        rw [he, map_mul]; exact mul_mem ha hb
      neg_mem' := fun {a} ha ↦ by
        change Θ (e (-a)) ∈ Ξ.range
        have h := he (-a) a
        rw [neg_add_cancel, e0] at h
        rw [eq_inv_of_mul_eq_one_left h.symm, map_inv]; exact inv_mem ha }
  have hK : Submodule.span ℤ s ≤ AddSubgroup.toIntSubmodule K := Submodule.span_le.2 fun y hy ↦ by
    obtain ⟨F, hF⟩ := hgen y hy
    exact ⟨F, Over.OverMorphism.ext hF.symm⟩
  obtain ⟨F, hF⟩ : Θ (e x) ∈ Ξ.range := hK (hs ▸ Submodule.mem_top)
  exact ⟨F, (congrArg (fun z ↦ z.left) hF).symm⟩

theorem relAmple_of_algebraic_fibre : ∀ (R₀ R : Type) [CommRing R₀] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ic : R₀ →+* R) (j : R →+* Qb),
    Function.Injective j → ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
    IsFinite Ψ₀.left → Flat Ψ₀.left → Surjective Ψ₀.left →
    ∀ (A : Over (Sp R)) [GrpObj A] (g : A.left ⟶ G₀.left), IsGrpPullback A G₀ (spMap ic) g → IsAbelianScheme A →
    ∀ (AQ : Over (Sp Qb)) [GrpObj AQ] (pj : AQ.left ⟶ A.left), IsGrpPullback AQ A (spMap j) pj →
    ∀ (M : LB A.left) (MQ : LB AQ.left), M.IsLB → MQ.IsLB → LBIso MQ (M.pull pj) → Out.RelAmple AQ MQ → Out.RelAmple A M := by
  intro R₀ R _ _ _ _ ic j hj G₀ _ P₀ Ψ₀ hfin hfl hsurj A _ g hg hA AQ _ pj hpj M MQ hM hMQ e amp
  let K := FractionRing R
  let i : K →+* Qb := IsFractionRing.lift hj
  have hi : ∀ r, i (algebraMap R K r) = j r := fun r ↦ IsFractionRing.lift_algebraMap hj r
  have hs : spMap i ≫ spMap (algebraMap R K) = spMap j := by
    rw [HomDescent.spMap_comp]
    exact congrArg spMap (RingHom.ext hi)
  have hK := isGrpPullback_pullback A (spMap (algebraMap R K))
  obtain ⟨a, ha, ea⟩ := exists_factor_pullback hK hpj _ hs
  have hM₀ := pull_isLB hM (pullback.fst A.hom (spMap (algebraMap R K)))
  have amp₀ := AmpleDescent.relAmple_of_fieldExtension K Qb i ((Over.pullback (spMap (algebraMap R K))).obj A) AQ a
    (M.pull (pullback.fst A.hom (spMap (algebraMap R K)))) MQ
    (PolPull.isAbelianScheme_of_isGrpPullback hA hK) ha hM₀ hMQ ((cls_eq_iff hMQ (pull_isLB hM₀ _)).1 (by
      rw [cls_pull hM₀, cls_pull hM, ← pull_comp, ea, ← cls_pull hM _ (pull_isLB hM _)]
      exact (cls_eq_iff _ _).2 e)) amp
  obtain ⟨P, φ, hφ, -⟩ := exists_polBaseChange_oAct R₀ R ic P₀
  have w : (φ ≫ Ψ₀.left) ≫ G₀.hom = P.A.hom ≫ spMap ic := by rw [Category.assoc, Over.w Ψ₀, hφ.1.w]
  let Ψ : P.A ⟶ A := Over.homMk (hg.1.lift _ _ w) (hg.1.lift_snd _ _ _)
  have e₁ : Ψ.left ≫ g = φ ≫ Ψ₀.left := hg.1.lift_fst _ _ _
  have sq : IsPullback φ Ψ.left Ψ₀.left g := by
    refine IsPullback.of_bot ?_ e₁.symm hg.1
    rw [Over.w Ψ, Over.w Ψ₀]
    exact hφ.1
  exact AmpleDedekind.relAmple_of_generic_of_isogenous abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 R K P A Ψ M _ _ _
    hA hM hM₀ (MorphismProperty.of_isPullback (P := @IsFinite) sq hfin)
    (MorphismProperty.of_isPullback (P := @Flat) sq hfl) (MorphismProperty.of_isPullback (P := @Surjective) sq hsurj)
    hK ((cls_eq_iff hM₀ hM₀).1 rfl) amp₀

theorem exists_factor_isogeny {K : Type} [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g : ℕ)
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hAg : SmoothOfRelativeDimension g A.hom)
    (hBg : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) (hf : IsMonHom f) (m : ℕ) (hm : 0 < m)
    (hker : ∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ f = 1 → x ^ m = 1) (u : A ⟶ A) (hu : IsMonHom u)
    (h : ∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ f = 1 → x ≫ u = 1) : ∃ w : B ⟶ A, IsMonHom w ∧ f ≫ w = u := by
  have := hA.smooth
  have := hB.smooth
  have := hA.proper
  have := hB.proper
  have := hA.comm
  have : LocallyOfFiniteType (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp _ B.hom
  have hSA := isSemiAbelian_of_isAbelianScheme A hA
  have : LocallyQuasiFinite f.left :=
    locallyQuasiFinite_of_finite_geometric_ker _ A B f hf inferInstance inferInstance
      fun Ω _ _ t ↦ by
        have := HomExt.finite_torsion_points hSA t hm
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ m = 1})
          (fun x ↦ ⟨x.1, hker _ x.1 x.2⟩)
          fun a b e ↦ Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ m = 1} ↦ z.1) e)
  obtain ⟨h₁, h₂⟩ := IsogenyQuasiInverse.flat_surjective_of_field A B g hA hB hAg hBg f
  exact (exists_monHom_factor_of_flat_surjective _ A B A f u hf hu h₁ h₂ inferInstance h).1

theorem span_conductors {F : Type} [Field F] [NumberField F] (𝔠 : FracId F) :
    (1 : 𝓞 F) ∈ Ideal.span {a : 𝓞 F | a ≠ 0 ∧ ∃ d : 𝔠.elt, ∀ d' : 𝔠.elt, ∃ b : 𝓞 F, a • d' = b • d} := by
  have int : ∀ d ∈ (𝔠 : FractionalIdeal (𝓞 F)⁰ F), ∀ e ∈ ((𝔠⁻¹ : FracId F) : FractionalIdeal (𝓞 F)⁰ F),
      ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = d * e := fun d hd e he ↦ by
    have h := FractionalIdeal.mul_mem_mul hd he
    rw [Units.mul_inv] at h
    exact (FractionalIdeal.mem_one_iff _).1 h
  have h1 : (1 : F) ∈ (𝔠 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔠⁻¹ : FracId F) : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [Units.mul_inv]; exact FractionalIdeal.one_mem_one _
  obtain ⟨a, ha, e⟩ : ∃ a ∈ Ideal.span {a : 𝓞 F | a ≠ 0 ∧ ∃ d : 𝔠.elt, ∀ d' : 𝔠.elt, ∃ b : 𝓞 F, a • d' = b • d},
      algebraMap (𝓞 F) F a = 1 := by
    refine FractionalIdeal.mul_induction_on
      (C := fun w ↦ ∃ a ∈ Ideal.span {a : 𝓞 F | a ≠ 0 ∧ ∃ d : 𝔠.elt, ∀ d' : 𝔠.elt, ∃ b : 𝓞 F, a • d' = b • d},
        algebraMap (𝓞 F) F a = w) h1 (fun d hd e he ↦ ?_) ?_
    · obtain ⟨a, ha⟩ := int d hd e he
      refine ⟨a, ?_, ha⟩
      by_cases h0 : a = 0
      · rw [h0]; exact zero_mem _
      refine Ideal.subset_span ⟨h0, ⟨d, hd⟩, fun d' ↦ ?_⟩
      obtain ⟨b, hb⟩ := int d' d'.2 e he
      refine ⟨b, Subtype.ext ?_⟩
      change a • (d' : F) = b • d
      rw [Algebra.smul_def, Algebra.smul_def, ha, hb]
      ring
    · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, add_mem ha hb, map_add _ _ _⟩
  rwa [← FaithfulSMul.algebraMap_injective (𝓞 F) F (e.trans (map_one _).symm)]

theorem exists_hom_from_dual : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (XQ : Obj F 𝔠 (Sp Qb)) (DQ : Over (Sp Qb)) [GrpObj DQ]
    (QQ : LB (XQ.A ⊗ DQ).left), IsAbelianScheme DQ → SmoothOfRelativeDimension (Module.finrank ℚ F) DQ.hom →
    IsDual XQ.A DQ QQ → ∀ x : 𝔠.elt → (XQ.A ⟶ DQ), (∀ c, IsMonHom (x c)) →
    (∀ c, LBIso (XQ.P c) (ev QQ (fst XQ.A XQ.A) (snd XQ.A XQ.A ≫ x c))) →
    ∃ t : Finset (𝓞 F), Ideal.span (t : Set (𝓞 F)) = ⊤ ∧
      ∀ a ∈ t, ∃ (d : 𝔠.elt) (w : DQ ⟶ XQ.A), IsMonHom w ∧ x d ≫ w = XQ.rm.act a := by
  intro F _ _ 𝔠 XQ DQ _ QQ hD gD q x hx ex
  haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  obtain ⟨t, ht, h1⟩ := Submodule.mem_span_finite_of_mem_span (span_conductors 𝔠)
  refine ⟨t, (Ideal.eq_top_iff_one _).2 h1, fun a ha ↦ ?_⟩
  obtain ⟨a0, d, hd⟩ := ht ha
  have k : ∀ (T : Over (Sp Qb)) (z : T ⟶ XQ.A), z ≫ x d = 1 → z ≫ XQ.rm.act a = 1 := fun T z hz ↦ by
    refine XQ.ker d T z ((triv_ev_iff (XQ.isLB d) _ _).2 ?_) a hd
    rw [evc_of_cls q.isLB (XQ.isLB d) ((cls_eq_iff _ (pull_isLB q.isLB _)).2 (ex d)), Category.assoc, hz,
      MonObj.comp_one]
    exact evc_one_right q.isLB q.zero _
  have hn : ∀ n : ℕ, XQ.rm.act n = 𝟙 XQ.A ^ n := fun n ↦ by
    induction n with
    | zero =>
      have e := XQ.rm.add 0 0
      rw [add_zero] at e
      rw [Nat.cast_zero, pow_zero, left_eq_mul.1 e]
    | succ n ih => rw [Nat.cast_succ, XQ.rm.add, ih, XQ.rm.one, pow_succ]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  have hm : 0 < Ideal.absNorm (Ideal.span {a}) :=
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact a0)
  refine ⟨d, exists_factor_isogeny XQ.A DQ _ XQ.ab hD XQ.dim gD (x d) (hx d) _ hm (fun T z hz ↦ ?_) _ (XQ.rm.hom a) k⟩
  haveI := XQ.rm.hom b
  have e : z ≫ XQ.rm.act (b * a) = 1 := by rw [mul_comm, XQ.rm.mul, ← Category.assoc, k T z hz, MonObj.one_comp]
  rwa [hb, hn, MonObj.comp_pow, Category.comp_id] at e

theorem eventually_descendsTo : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k₀ : IntermediateField ℚ ℂ)
    (R₀ : Subring ℂ), FiniteDimensional ℚ k₀ → IsPlaceOver l lam k₀ R₀ → (∀ x ∈ R₀, x ∈ k₀) →
    ∀ (σ : R₀ →+* Qb), (∀ x, ((σ x : Qb) : ℂ) = x) →
    ∀ (G₀ H₀ : Over (Sp R₀)) [GrpObj G₀] [GrpObj H₀], IsAbelianScheme G₀ → IsAbelianScheme H₀ →
    ∀ (GQ HQ : Over (Sp Qb)) [GrpObj GQ] [GrpObj HQ] (gQ : GQ.left ⟶ G₀.left) (hQ : HQ.left ⟶ H₀.left),
      IsGrpPullback GQ G₀ (spMap σ) gQ → IsGrpPullback HQ H₀ (spMap σ) hQ →
    ∀ f : GQ ⟶ HQ, IsMonHom f →
    Eventually l lam fun R ↦ ∀ (ic : R₀ →+* R) (j : R →+* Qb), (∀ x, ((ic x : R) : ℂ) = x) →
      (∀ x, ((j x : Qb) : ℂ) = x) → GlobalTheory.PlaceModel.DescendsTo ic j gQ hQ f := by
  intro l _ lam k₀ R₀ _ _ _ σ hσ G₀ H₀ _ _ hG₀ hH₀ GQ HQ _ _ gQ hQ hgQ hhQ f hf
  classical
  letI : Algebra R₀ Qb := σ.toAlgebra
  haveI := hG₀.smooth
  haveI := hG₀.proper
  haveI := hH₀.smooth
  haveI := hH₀.proper
  have cG := isGrpPullback_pullback G₀ (spMap (algebraMap R₀ Qb))
  have cH := isGrpPullback_pullback H₀ (spMap (algebraMap R₀ Qb))
  obtain ⟨u, hu, eu⟩ := exists_factor_pullback hgQ cG (𝟙 _) (Category.id_comp _)
  obtain ⟨v, hv, ev'⟩ := exists_factor_pullback hhQ cH (𝟙 _) (Category.id_comp _)
  obtain ⟨u', hu', eu'⟩ := exists_factor_pullback cG hgQ (𝟙 _) (Category.id_comp _)
  have uu : u' ≫ u = 𝟙 _ := hgQ.1.hom_ext (by rw [Category.assoc, eu, eu', Category.id_comp])
    (by rw [Category.assoc, hu.1.w, ← Category.assoc, hu'.1.w]; simp)
  obtain ⟨f', hf', ef'⟩ := HomDescent.exists_isMonHom_pull hu hv f
  obtain ⟨R₁, g₁, ⟨s, hs⟩, hg₁, eg₁⟩ := HomDescent.exists_fg_isMonHom (k := R₀) (C := Qb) f'
  let s' : Set ℂ := (fun z : Qb ↦ (z : ℂ)) '' s
  haveI : Finite s' := (s.finite_toSet.image _).to_subtype
  refine ⟨IntermediateField.adjoin ℚ s', IntermediateField.finiteDimensional_adjoin ?_, fun R hR ic j hic hj ↦ ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact (mem_algebraicClosure_iff.1 z.2).isIntegral
  intro G H _ _ g h pG pH hg hh hpG hpH epG epH
  haveI : IsDiscreteValuationRing R := hR.1
  have hji : Function.Injective j := fun a b h ↦ by
    have e := congrArg (fun z : Qb ↦ (z : ℂ)) h
    simp only [hj] at e
    exact Subtype.ext e
  let K := FractionRing R
  let i : K →+* Qb := IsFractionRing.lift hji
  have hi : ∀ r, i (algebraMap R K r) = j r := fun r ↦ IsFractionRing.lift_algebraMap hji r
  have hjic : ∀ y, j (ic y) = σ y := fun y ↦ Subtype.ext (by rw [hj, hic, hσ])
  have small : ∀ z : Qb, (z : ℂ) ∈ IntermediateField.adjoin ℚ s' → ‖lam z‖ ≤ 1 → z ∈ i.fieldRange := fun z hz hn ↦
    ⟨algebraMap R K ⟨z, hR.2.2 _ hz ⟨z.2, by rw [Real.rpow_zero]; exact hn⟩⟩, by rw [hi]; exact Subtype.ext (hj _)⟩
  have mem : ∀ r ∈ R₁, r ∈ i.fieldRange := fun r hr ↦ by
    rw [← hs] at hr
    induction hr using Algebra.adjoin_induction with
    | mem z hz =>
      have hz' : (z : ℂ) ∈ IntermediateField.adjoin ℚ s' := IntermediateField.subset_adjoin _ _ ⟨z, hz, rfl⟩
      rcases le_total ‖lam z‖ 1 with hn | hn
      · exact small z hz' hn
      · exact inv_mem_iff.1 (small z⁻¹ (inv_mem hz') (by rw [map_inv₀, norm_inv]; exact inv_le_one_of_one_le₀ hn))
    | algebraMap y => exact ⟨algebraMap R K (ic y), (hi _).trans (hjic y)⟩
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  choose ρ₀ hρ₀ using fun r : R₁ ↦ mem r.1 r.2
  have hρ₀' : ∀ r, i (ρ₀ r) = r := hρ₀
  let ρ : R₁ →+* K :=
    { toFun := ρ₀
      map_one' := i.injective (by rw [hρ₀', map_one]; rfl)
      map_mul' := fun a b ↦ i.injective (by rw [map_mul, hρ₀', hρ₀', hρ₀']; rfl)
      map_zero' := i.injective (by rw [hρ₀', map_zero]; rfl)
      map_add' := fun a b ↦ i.injective (by rw [map_add, hρ₀', hρ₀', hρ₀']; rfl) }
  have s₁ : spMap i ≫ spMap (algebraMap R K) = spMap j := by
    rw [HomDescent.spMap_comp]
    congr 1
    exact RingHom.ext hi
  have s₂ : spMap ρ ≫ spMap (algebraMap R₀ R₁) = spMap (algebraMap R K) ≫ spMap ic := by
    rw [HomDescent.spMap_comp, HomDescent.spMap_comp]
    congr 1
    exact RingHom.ext fun y ↦ i.injective ((hρ₀' _).trans ((hi _).trans (hjic y)).symm)
  have s₃ : spMap i ≫ spMap ρ = spMap R₁.val.toRingHom := by
    rw [HomDescent.spMap_comp]
    congr 1
    exact RingHom.ext hρ₀'
  have kG := isGrpPullback_pullback G (spMap (algebraMap R K))
  have kH := isGrpPullback_pullback H (spMap (algebraMap R K))
  obtain ⟨φ, hφ, eφ⟩ := exists_factor_pullback (isGrpPullback_pullback G₀ (spMap (algebraMap R₀ R₁))) (kG.comp hg) _ s₂
  obtain ⟨ψ, hψ, eψ⟩ := exists_factor_pullback (isGrpPullback_pullback H₀ (spMap (algebraMap R₀ R₁))) (kH.comp hh) _ s₂
  obtain ⟨gK, hgK, egK⟩ := HomDescent.exists_isMonHom_pull hφ hψ g₁
  obtain ⟨Φ, ⟨-, eΦ⟩, -⟩ := Published.AbelianDualCrystal.hom_extends (K := K)
    (PolPull.isAbelianScheme_of_isGrpPullback hG₀ hg) (PolPull.isAbelianScheme_of_isGrpPullback hH₀ hh) gK
  have eΦ' : gK.left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Φ.left := by
    rw [← eΦ]; exact ExtUnique.pullback_map_left_fst _ Φ
  obtain ⟨a, ha, ea⟩ := exists_factor_pullback kG hpG _ s₁
  have ab : a ≫ φ = u' ≫ Spread.bcMap G₀.hom R₁.val := by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      erw [eφ, Spread.bcMap_fst, eu', ← Category.assoc, ea, epG]
    · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      have b₁ := congrArg (a ≫ ·) hφ.1.w
      have b₂ := congrArg (· ≫ spMap ρ) ha.1.w
      have b₃ := congrArg (u' ≫ ·) (Spread.bcMap_snd G₀.hom R₁.val)
      have b₄ := congrArg (· ≫ spMap R₁.val.toRingHom) (hu'.1.w.trans (Category.comp_id _))
      exact b₁.trans ((Category.assoc _ _ _).symm.trans (b₂.trans ((Category.assoc _ _ _).trans
        ((congrArg (GQ.hom ≫ ·) s₃).trans (b₄.symm.trans ((Category.assoc _ _ _).trans b₃.symm))))))
  refine ⟨Φ, hh.1.hom_ext ?_ ?_⟩
  · have c₁ : pG ≫ Φ.left = a ≫ gK.left ≫ pullback.fst _ _ := by rw [eΦ', ← ea, Category.assoc]
    have c₂ : (a ≫ gK.left ≫ pullback.fst _ _) ≫ h = a ≫ (gK.left ≫ ψ) ≫ pullback.fst _ _ := by
      simp only [Category.assoc]
      exact congrArg (fun z ↦ a ≫ gK.left ≫ z) eψ.symm
    have c₃ : a ≫ (gK.left ≫ ψ) ≫ pullback.fst _ _ = u' ≫ f'.left ≫ pullback.fst _ _ := by
      rw [egK, ← eg₁, ← Category.assoc, ← Category.assoc, ab]
      simp only [Category.assoc]
    have c₄ : u' ≫ f'.left ≫ pullback.fst _ _ = f.left ≫ hQ := by
      have := congrArg (fun z ↦ u' ≫ f'.left ≫ z) ev'.symm
      refine this.trans ?_
      rw [← Category.assoc f'.left, ef', Category.assoc, ← Category.assoc, uu, Category.id_comp]
    rw [c₁, c₂, c₃, c₄, Category.assoc, epH]
  · rw [Category.assoc, Category.assoc, hpH.1.w, Over.w Φ, hpG.1.w, ← Category.assoc, Over.w f]

end GlobalTheory.PlaceModel

namespace GlobalTheory.PlaceModel

theorem cls_eq_of_pull_dominant {S S' : Scheme.{0}} {b : S' ⟶ S} [QuasiCompact b] [IsSchemeTheoreticallyDominant b]
    {A B D : Over S} [GrpObj A] [GrpObj D] [Flat B.hom] [IsSeparated D.hom]
    {A' B' D' : Over S'} [GrpObj A'] [GrpObj D'] {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left} {d : D'.left ⟶ D.left}
    {l : (A' ⊗ B').left ⟶ (A ⊗ B).left} {m : (A' ⊗ D').left ⟶ (A ⊗ D).left}
    (hg : IsPullback g B'.hom B.hom b) (hd : IsGrpPullback D' D b d)
    (l₁ : l ≫ (fst A B).left = (fst A' B').left ≫ f) (l₂ : l ≫ (snd A B).left = (snd A' B').left ≫ g)
    (m₁ : m ≫ (fst A D).left = (fst A' D').left ≫ f) (m₂ : m ≫ (snd A D).left = (snd A' D').left ≫ d)
    {Q : LB (A ⊗ D).left} (q : IsDual A D Q) (q' : IsDual A' D' (Q.pull m))
    {P P' : LB (A ⊗ B).left} (hP : P.IsLB) (hP' : P'.IsLB) (a : IsAdditive P) (a' : IsAdditive P')
    (e : CechPic.pull l (cls P hP) = CechPic.pull l (cls P' hP')) : cls P hP = cls P' hP' := by
  obtain ⟨x, hx, -⟩ := q.univ B P hP a
  obtain ⟨x', hx', -⟩ := q.univ B P' hP' a'
  have ex : cls P hP = evc q.isLB (fst A B) (snd A B ≫ x) := (cls_eq_iff hP (pull_isLB q.isLB _)).2 hx
  have ex' : cls P' hP' = evc q.isLB (fst A B) (snd A B ≫ x') := (cls_eq_iff hP' (pull_isLB q.isLB _)).2 hx'
  have ly : ∀ y : B ⟶ D, ∃ y' : B' ⟶ D', g ≫ y.left = y'.left ≫ d := fun y ↦
    ⟨_, (liftPt_left hd B'.hom (g ≫ y.left) (by rw [Category.assoc, Over.w y, hg.w])).symm⟩
  obtain ⟨y, ey⟩ := ly x
  obtain ⟨y', ey'⟩ := ly x'
  obtain rfl : y = y' := dual_ext q' <| by
    rw [← pull_evc_eq l₁ l₂ m₁ m₂ q.isLB q'.isLB ey, ← pull_evc_eq l₁ l₂ m₁ m₂ q.isLB q'.isLB ey', ← ex, ← ex', e]
  obtain rfl : x = x' := ExtUnique.over_hom_ext_of_isPullback hg (ey.trans ey'.symm)
  exact ex.trans ex'.symm

theorem exists_obj_of_homs {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S U : Scheme.{0}} {j : U ⟶ S}
    [QuasiCompact j] [IsSchemeTheoreticallyDominant j] (X : Obj F 𝔠 U) (A₀ : Over S) [GrpObj A₀]
    (p : X.A.left ⟶ A₀.left) (hA₀ : IsAbelianScheme A₀) (gA₀ : SmoothOfRelativeDimension (Module.finrank ℚ F) A₀.hom)
    (hp : IsGrpPullback X.A A₀ j p) (rm : OAct (𝓞 F) A₀) (hrm : ∀ a, (X.rm.act a).left ≫ p = p ≫ (rm.act a).left)
    {D₀ : Over S} [GrpObj D₀] {Q : LB (A₀ ⊗ D₀).left} {D : Over U} [GrpObj D] {d : D.left ⟶ D₀.left}
    {m : (X.A ⊗ D).left ⟶ (A₀ ⊗ D₀).left} (hD₀ : IsAbelianScheme D₀) (q₀ : IsDual A₀ D₀ Q)
    (q₀' : IsAdditive (swap Q)) (hd : IsGrpPullback D D₀ j d)
    (m₁ : m ≫ (fst A₀ D₀).left = (fst X.A D).left ≫ p) (m₂ : m ≫ (snd A₀ D₀).left = (snd X.A D).left ≫ d)
    (q : IsDual X.A D (Q.pull m)) (x : 𝔠.elt → (X.A ⟶ D)) (y : 𝔠.elt → (A₀ ⟶ D₀)) (hy : ∀ c, IsMonHom (y c))
    (e₀ : ∀ c, (x c).left ≫ d = p ≫ (y c).left)
    (ex : ∀ c, cls (X.P c) (X.isLB c) = evc q.isLB (fst X.A X.A) (snd X.A X.A ≫ x c))
    (hpos : ∀ (M : LB A₀.left) (M' : LB X.A.left), M.IsLB → M'.IsLB → LBIso M' (M.pull p) → Out.RelAmple X.A M' →
      Out.RelAmple A₀ M)
    (hz : ∀ (T : Over S) (z : T ⟶ A₀), (∀ c, z ≫ y c = 1) → z = 1)
    {S₁ : Scheme.{0}} {b : S ⟶ S₁} {G₁ : Over S₁} [GrpObj G₁] {g : A₀.left ⟶ G₁.left} (hg : IsGrpPullback A₀ G₁ b g)
    {O : Type} [CommRing O] (ofO : 𝓞 F → O) (cmQ : OAct O X.A) (cm : OAct O A₀) (h₁ : ∀ a, cm.act (ofO a) = rm.act a)
    (h₂ : ∀ a, (cmQ.act a).left ≫ p = p ≫ (cm.act a).left) :
    ∃ (X₀ : Obj F 𝔠 S) (p' : X.A.left ⟶ X₀.A.left) (g' : X₀.A.left ⟶ G₁.left) (cm' : OAct O X₀.A),
      X.IsPullBy X₀ j p' ∧ IsGrpPullback X₀.A G₁ b g' ∧ p' ≫ g' = p ≫ g ∧
      (∀ a, cm'.act (ofO a) = X₀.rm.act a) ∧ ∀ a, (cmQ.act a).left ≫ p' = p' ≫ (cm'.act a).left := by
  haveI := hA₀.comm
  haveI := hA₀.smooth
  haveI := hD₀.proper
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback hp hp
  have hx : ∀ c : 𝔠.elt, ∃ P₀ : LB (A₀ ⊗ A₀).left, ∃ h : P₀.IsLB, IsAdditive P₀ ∧ IsAdditive (swap P₀) ∧
      CechPic.pull l (cls P₀ h) = cls (X.P c) (X.isLB c) ∧
      cls P₀ h = evc q₀.isLB (fst A₀ A₀) (snd A₀ A₀ ≫ y c) := fun c ↦ by
    haveI := hy c
    obtain ⟨b₁, b₂⟩ := additive_ev q₀.isLB q₀.additive q₀' (y c)
    refine ⟨_, pull_isLB q₀.isLB _, b₁, b₂, ?_, rfl⟩
    rw [cls_ev q₀.isLB, ex]
    exact pull_evc_eq l₁ l₂ m₁ m₂ q₀.isLB q.isLB (e₀ c).symm
  choose P₀ hP₀ a₁ a₂ eP eQ using hx
  have inj : ∀ {P P' : LB (A₀ ⊗ A₀).left} (hP : P.IsLB) (hP' : P'.IsLB), IsAdditive P → IsAdditive P' →
      CechPic.pull l (cls P hP) = CechPic.pull l (cls P' hP') → LBIso P P' := fun hP hP' a a' e ↦
    (cls_eq_iff hP hP').1 (cls_eq_of_pull_dominant hp.1 hd l₁ l₂ m₁ m₂ q₀ q hP hP' a a' e)
  have val : ∀ (c : 𝔠.elt) {Y₀ : Over S} {Y : Over U} (r : Y.left ⟶ Y₀.left) (a₀ t₀ : Y₀ ⟶ A₀)
      (a t : Y ⟶ X.A), a.left ≫ p = r ≫ a₀.left → t.left ≫ p = r ≫ t₀.left →
      CechPic.pull r (evc (hP₀ c) a₀ t₀) = evc (X.isLB c) a t := fun c Y₀ Y r a₀ t₀ a t ha ht ↦ by
    rw [evc, evc, ← eP, ← pull_comp, ← pull_comp]
    congr 2
    apply left_ext
    · rw [Category.assoc, Category.assoc, lift_left_fst, l₁, lift_left_fst_assoc, ha]
    · rw [Category.assoc, Category.assoc, lift_left_snd, l₂, lift_left_snd_assoc, ht]
  have hsymm : ∀ c, LBIso (P₀ c) ((P₀ c).pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := fun c ↦ by
    refine inj (hP₀ c) (pull_isLB (hP₀ c) _) (a₁ c) (a₂ c) ?_
    rw [eP, cls_ev (hP₀ c), val c l _ _ _ _ l₂.symm l₁.symm]
    exact (cls_eq_iff _ (pull_isLB (X.isLB c) _)).2 (X.symm c)
  have hsmul : ∀ (a : 𝓞 F) c, LBIso (P₀ (a • c)) ((P₀ c).pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ rm.act a)).left) :=
    fun a c ↦ by
    have hq : (ev (P₀ c) (fst A₀ A₀) (snd A₀ A₀ ≫ rm.act a)).IsLB := pull_isLB (hP₀ c) _
    refine inj (hP₀ _) hq (a₁ _) ((isAdditive_iff hq).2 fun Y u u' t ↦ ?_) ?_
    · simp only [evc_ev (hP₀ c), lift_fst, lift_snd_assoc]
      exact (isAdditive_iff (hP₀ c)).1 (a₁ c) _ _ _ _
    · rw [eP, cls_ev (hP₀ c), val c l _ _ (fst X.A X.A) (snd X.A X.A ≫ X.rm.act a) l₁.symm (by
        rw [Over.comp_left, Over.comp_left, Category.assoc, hrm, ← Category.assoc, ← Category.assoc, l₂])]
      exact (cls_eq_iff _ (pull_isLB (X.isLB c) _)).2 (X.smul a c)
  have vsymm : ∀ c {Y : Over S} (u v : Y ⟶ A₀), evc (hP₀ c) u v = evc (hP₀ c) v u := fun c Y u v ↦ by
    have e : cls (P₀ c) (hP₀ c) = evc (hP₀ c) (snd A₀ A₀) (fst A₀ A₀) :=
      (cls_eq_iff _ (pull_isLB (hP₀ c) _)).2 (hsymm c)
    rw [evc, e, pull_evc, lift_fst, lift_snd]
  have vsmul : ∀ (a : 𝓞 F) c {Y : Over S} (u v : Y ⟶ A₀),
      evc (hP₀ (a • c)) u v = evc (hP₀ c) u (v ≫ rm.act a) := fun a c Y u v ↦ by
    have e : cls (P₀ (a • c)) (hP₀ _) = evc (hP₀ c) (fst A₀ A₀) (snd A₀ A₀ ≫ rm.act a) :=
      (cls_eq_iff _ (pull_isLB (hP₀ c) _)).2 (hsmul a c)
    rw [evc, e, pull_evc, lift_fst, lift_snd_assoc]
  refine ⟨{ A := A₀
            ab := hA₀
            dim := gA₀
            rm := rm
            P := P₀
            isLB := hP₀
            rig₁ := fun c ↦ triv_left (hP₀ c) (a₁ c)
            rig₂ := fun c ↦ triv_right (hP₀ c) (a₂ c)
            symm := hsymm
            add := fun c c' ↦ ?_
            smul := hsmul
            pos := fun c hc ↦ ?_
            ker := fun c T z hzc a ha ↦ ?_ }, p, g, cm, ⟨hp, hrm, l, ⟨l₁, l₂⟩, fun c ↦ ?_⟩, hg, rfl, h₁, h₂⟩
  · have hq := LB.isLB_div (hP₀ (c + c')) (hP₀ c)
    have ev' : ∀ (Y : Over S) (a t : Y ⟶ A₀), evc hq a t = evc (hP₀ (c + c')) a t - evc (hP₀ c) a t :=
      fun Y a t ↦ by rw [evc, cls_div (hP₀ (c + c')) (hP₀ c), map_sub]; rfl
    refine inj (hP₀ c') hq (a₁ c') ((isAdditive_iff hq).2 fun Y a a' t ↦ ?_) ?_
    · rw [ev', ev', ev', (isAdditive_iff (hP₀ _)).1 (a₁ _), (isAdditive_iff (hP₀ _)).1 (a₁ _)]
      abel
    · rw [cls_div (hP₀ (c + c')) (hP₀ c), map_sub, eP, eP, eP, ← cls_div (X.isLB (c + c')) (X.isLB c)
        (LB.isLB_div (X.isLB (c + c')) (X.isLB c))]
      exact (cls_eq_iff _ _).2 (X.add c c')
  · refine hpos _ _ (pull_isLB (hP₀ c) _) (pull_isLB (X.isLB c) _)
      ((cls_eq_iff (pull_isLB (X.isLB c) _) (pull_isLB (pull_isLB (hP₀ c) _) _)).1 ?_) (X.pos c hc)
    rw [cls_pull (pull_isLB (hP₀ c) _), cls_ev (hP₀ c), cls_ev (X.isLB c)]
    exact (val c p _ _ _ _ (by simp) (by simp)).symm
  · have z₀ : evc (hP₀ c) (fst A₀ T) (snd A₀ T ≫ z) = 0 := (triv_ev_iff (hP₀ c) _ _).1 hzc
    refine hz T _ fun c' ↦ q₀.eq_one _ ((triv_ev_iff q₀.isLB _ _).2 ?_)
    obtain ⟨b', hb'⟩ := ha c'
    have z₁ := congrArg (CechPic.pull (lift (fst A₀ T ≫ rm.act b') (snd A₀ T)).left) z₀
    rw [pull_evc, map_zero, lift_fst, lift_snd_assoc] at z₁
    rw [← Category.assoc, ← evc_of_cls q₀.isLB (hP₀ c') (eQ c'), ← Category.assoc, ← vsmul, hb', vsymm, vsmul, vsymm]
    exact z₁
  · exact (cls_eq_iff (X.isLB c) (pull_isLB (hP₀ c) _)).1 (by rw [cls_pull (hP₀ c)]; exact (eP c).symm)

end GlobalTheory.PlaceModel

namespace GlobalTheory.PlaceModel

theorem totPos {F : Type} [Field F] [NumberField F] (𝔠 : FracId F) : ∃ c : 𝔠.elt, IsTotPos (c : F) := by
  have hne : (𝔠.elt : Submodule (𝓞 F) F) ≠ ⊥ := by
    intro h
    apply 𝔠.ne_zero
    exact (FractionalIdeal.coeToSubmodule_eq_bot).mp h
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
  obtain ⟨a, ha, hint⟩ := (𝔠 : FractionalIdeal (𝓞 F)⁰ F).isFractional
  obtain ⟨y, hy⟩ := hint x hx
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hy0 : (algebraMap (𝓞 F) F y) ≠ 0 := by
    rw [hy, Algebra.smul_def]
    exact mul_ne_zero ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr ha0) hx0
  refine ⟨⟨(a * y) • x, Submodule.smul_mem _ _ hx⟩, ?_⟩
  intro τ
  have hval : ((a * y) • x : F) = algebraMap (𝓞 F) F y * algebraMap (𝓞 F) F y := by
    rw [mul_comm a y, mul_smul, ← hy, Algebra.smul_def]
  show 0 < τ ((a * y) • x)
  rw [hval, map_mul]
  have : τ (algebraMap (𝓞 F) F y) ≠ 0 := (map_ne_zero τ).mpr hy0
  exact mul_self_pos.mpr this

theorem exists_obj_eventually : GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.Published.AbelianDeRham →
  ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (O : Type) [CommRing O] (ofO : 𝓞 F → O) (l : ℕ) [Fact l.Prime]
    (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), Module.Finite ℤ O →
    FiniteDimensional ℚ k₀ → IsPlaceOver l lam k₀ R₀ → (∀ x ∈ R₀, x ∈ k₀) →
    ∀ (σ : R₀ →+* Qb), (∀ x, ((σ x : Qb) : ℂ) = x) →
    ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
      IsAbelianScheme G₀ → IsMonHom Ψ₀ → IsFinite Ψ₀.left → Flat Ψ₀.left → Surjective Ψ₀.left →
    ∀ (XQ : Obj F 𝔠 (Sp Qb)) (gQ : XQ.A.left ⟶ G₀.left) (cmQ : OAct O XQ.A), IsGrpPullback XQ.A G₀ (spMap σ) gQ →
      (∀ a, cmQ.act (ofO a) = XQ.rm.act a) →
      Eventually l lam fun R ↦ ∀ (ic : R₀ →+* R) (j : R →+* Qb), (∀ x, ((ic x : R) : ℂ) = x) → (∀ x, ((j x : Qb) : ℂ) = x) →
        ∃ (X₀ : Obj F 𝔠 (Sp R)) (pj : XQ.A.left ⟶ X₀.A.left) (g : X₀.A.left ⟶ G₀.left) (cm : OAct O X₀.A),
          XQ.IsPullBy X₀ (spMap j) pj ∧ IsGrpPullback X₀.A G₀ (spMap ic) g ∧ pj ≫ g = gQ ∧
          (∀ a, cm.act (ofO a) = X₀.rm.act a) ∧ ∀ a, (cmQ.act a).left ≫ pj = pj ≫ (cm.act a).left := by
  intro HDC HdR F _ _ 𝔠 O _ ofO l _ lam k₀ R₀ hO hk₀ hR₀ hR₀k σ hσ G₀ _ P₀ Ψ₀ hG₀ hΨ hfin hfl hsurj XQ gQ cmQ hgQ hcm
  have gG₀ : SmoothOfRelativeDimension (Module.finrank ℚ F) G₀.hom :=
    GlobalTheory.CM.smoothOfRelativeDimension_of_fibre R₀ Qb σ G₀ _ gQ _ _ hG₀ hgQ.1 XQ.dim
  obtain ⟨D₀, _, Q₀, DQ, _, dQ, mQ, hD₀, gD₀, q₀, q₀', hdQ, mQ₁, mQ₂, qQ, qQ'⟩ := exists_dual_pair HDC.1 hG₀ gG₀ hgQ
  obtain ⟨c₀, hc₀⟩ := totPos 𝔠
  obtain ⟨H, hH, aH⟩ := exists_relAmple_prod XQ.ab XQ.ab (pull_isLB (XQ.isLB c₀) _) (XQ.pos c₀ hc₀)
    (pull_isLB (XQ.isLB c₀) _) (XQ.pos c₀ hc₀)
  have hx : ∀ c : 𝔠.elt, ∃ x : XQ.A ⟶ DQ, IsMonHom x ∧
      cls (XQ.P c) (XQ.isLB c) = evc qQ.isLB (fst XQ.A XQ.A) (snd XQ.A XQ.A ≫ x) := fun c ↦ by
    obtain ⟨a₁, a₂⟩ := additive_of_triv XQ.ab XQ.ab hH aH (XQ.isLB c) (XQ.rig₁ c) (XQ.rig₂ c)
    exact exists_hom qQ qQ' (XQ.isLB c) a₁ a₂
  choose x hxm hxe using hx
  have hxi : ∀ c, LBIso (XQ.P c) (ev (Q₀.pull mQ) (fst XQ.A XQ.A) (snd XQ.A XQ.A ≫ x c)) := fun c ↦
    (cls_eq_iff (XQ.isLB c) (pull_isLB qQ.isLB _)).1 (hxe c)
  have hxa : ∀ c c', x (c + c') = x c * x c' := fun c c' ↦ by
    refine dual_ext qQ ?_
    rw [MonObj.comp_mul, (isAdditive_swap_iff qQ.isLB).1 qQ', ← hxe, ← hxe, ← hxe]
    have e := (cls_eq_iff (XQ.isLB c') (LB.isLB_div (XQ.isLB (c + c')) (XQ.isLB c))).2 (XQ.add c c')
    rw [cls_div (XQ.isLB (c + c')) (XQ.isLB c)] at e
    rw [e]
    abel
  obtain ⟨sO, hsO⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ O).FG)
  haveI : Module.Finite (𝓞 F) 𝔠.elt :=
    Module.Finite.iff_fg.2 (FractionalIdeal.fg_of_isNoetherianRing le_rfl (𝔠 : FractionalIdeal (𝓞 F)⁰ F))
  haveI : Module.Finite ℤ 𝔠.elt := Module.Finite.trans (𝓞 F) 𝔠.elt
  obtain ⟨s𝔠, hs𝔠⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ 𝔠.elt).FG)
  have evFin : ∀ {α : Type} (s : Finset α) (P : α → Subring ℂ → Prop), (∀ a ∈ s, Eventually l lam (P a)) →
      Eventually l lam fun R ↦ ∀ a ∈ s, P a R := by
    intro α s P h
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨k₀, hk₀, fun R _ a ha ↦ by simp at ha⟩
    | insert a s ha ih =>
      refine ((h a (Finset.mem_insert_self a s)).and (ih fun b hb ↦ h b (Finset.mem_insert_of_mem hb))).mono
        fun R hR b hb ↦ ?_
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact hR.1
      · exact hR.2 b hb
  have E1 := evFin sO _ fun a _ ↦ eventually_descendsTo l lam k₀ R₀ hk₀ hR₀ hR₀k σ hσ G₀ G₀ hG₀ hG₀ XQ.A XQ.A gQ gQ hgQ hgQ
    (cmQ.act a) (cmQ.hom a)
  have E2 := evFin s𝔠 _ fun c _ ↦ eventually_descendsTo l lam k₀ R₀ hk₀ hR₀ hR₀k σ hσ G₀ D₀ hG₀ hD₀ XQ.A DQ gQ dQ hgQ hdQ
    (x c) (hxm c)
  have hDQ : IsAbelianScheme DQ := PolPull.isAbelianScheme_of_isGrpPullback hD₀ hdQ
  have gDQ : SmoothOfRelativeDimension (Module.finrank ℚ F) DQ.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hdQ.1 gD₀
  obtain ⟨t, ht, hw⟩ := exists_hom_from_dual F 𝔠 XQ DQ _ hDQ gDQ qQ x hxm hxi
  choose! dd w hwm hwe using hw
  have E3 := evFin t.attach _ fun a _ ↦ eventually_descendsTo l lam k₀ R₀ hk₀ hR₀ hR₀k σ hσ D₀ G₀ hD₀ hG₀ DQ XQ.A dQ gQ hdQ hgQ
    (w a.1) (hwm a.1 a.2)
  obtain ⟨k, hk, H⟩ := (E1.and E2).and E3
  refine ⟨k, hk, fun R hR ic j hic hj ↦ ?_⟩
  haveI : IsDiscreteValuationRing R := hR.1
  have hji : Function.Injective j := fun a b h ↦ by
    have e := congrArg (fun z : Qb ↦ (z : ℂ)) h
    simp only [hj] at e
    exact Subtype.ext e
  have hjic : ∀ y, j (ic y) = σ y := fun y ↦ Subtype.ext (by rw [hj, hic, hσ])
  obtain ⟨⟨H1, H2⟩, H3⟩ := H R hR
  have D1 : ∀ a, DescendsTo ic j gQ gQ (cmQ.act a) := by
    intro a G G' _ _ g g' pG pG' h1 h2 h3 h4 h5 h6
    exact descends_of_generators (spMap j) h3 h4 O sO hsO (fun a ↦ cmQ.act a) (fun a b ↦ cmQ.add a b)
      (fun b hb ↦ H1 b hb ic j hic hj G G' g g' pG pG' h1 h2 h3 h4 h5 h6) a
  have D2 : ∀ c, DescendsTo ic j gQ dQ (x c) := by
    intro c G G' _ _ g g' pG pG' h1 h2 h3 h4 h5 h6
    exact descends_of_generators (spMap j) h3 h4 𝔠.elt s𝔠 hs𝔠 x hxa
      (fun b hb ↦ H2 b hb ic j hic hj G G' g g' pG pG' h1 h2 h3 h4 h5 h6) c
  have hs : spMap j ≫ spMap ic = spMap σ := by
    rw [← RingHom.ext hjic (f := j.comp ic)]
    exact (Spec.map_comp _ _).symm
  haveI : IsSchemeTheoreticallyDominant (spMap j) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom j) hji
  have bc : ∀ (B₀ : Over (Sp R₀)) [GrpObj B₀] (BQ : Over (Sp Qb)) [GrpObj BQ] (bQ : BQ.left ⟶ B₀.left),
      IsGrpPullback BQ B₀ (spMap σ) bQ → ∃ (B : Over (Sp R)) (_ : GrpObj B) (b : B.left ⟶ B₀.left)
        (p : BQ.left ⟶ B.left), IsGrpPullback B B₀ (spMap ic) b ∧ IsGrpPullback BQ B (spMap j) p ∧ p ≫ b = bQ := by
    intro B₀ _ BQ _ bQ h
    rw [← hs] at h
    exact ⟨_, _, _, _, isGrpPullback_pullback B₀ (spMap ic), ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor _ _ h, pullback.lift_fst _ _ _⟩
  obtain ⟨A, _, g, pj, hg, hpj, epj⟩ := bc G₀ XQ.A gQ hgQ
  obtain ⟨D, _, dR, d, hdR, hd, ed⟩ := bc D₀ DQ dQ hdQ
  have hA : IsAbelianScheme A := PolPull.isAbelianScheme_of_isGrpPullback hG₀ hg
  have hD : IsAbelianScheme D := PolPull.isAbelianScheme_of_isGrpPullback hD₀ hdR
  have gA : SmoothOfRelativeDimension (Module.finrank ℚ F) A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hg.1 gG₀
  haveI := hA.smooth
  haveI := hA.proper
  haveI := hD.proper
  obtain ⟨n, n₁, n₂⟩ := exists_prod_pullback hg hdR
  obtain ⟨m, m₁, m₂⟩ := exists_prod_pullback hpj hd
  have hQ := pull_isLB q₀.isLB n
  have hQ' := pull_isLB hQ m
  have q : IsDual A D (Q₀.pull n) := q₀.baseChange hg hdR n₁ n₂ hQ ((cls_eq_iff hQ hQ).1 rfl)
  have q₂ : IsAdditive (swap (Q₀.pull n)) :=
    (additive_pull hg hdR n₁ n₂ q₀.isLB hQ ((cls_eq_iff hQ hQ).1 rfl) q₀.additive q₀'.additive).2
  have q' : IsDual XQ.A DQ ((Q₀.pull n).pull m) := q.baseChange hpj hd m₁ m₂ hQ' ((cls_eq_iff hQ' hQ').1 rfl)
  have emn : m ≫ n = mQ := by
    apply left_ext
    · rw [Category.assoc, n₁, ← Category.assoc, m₁, Category.assoc, epj, mQ₁]
    · rw [Category.assoc, n₂, ← Category.assoc, m₂, Category.assoc, ed, mQ₂]
  have ecls : cls _ q'.isLB = cls _ qQ.isLB := by
    rw [cls_pull hQ, cls_pull q₀.isLB, cls_pull q₀.isLB, ← pull_comp, emn]
  obtain ⟨cm, hcmR, -⟩ := ExtUnique.existsUnique_oAct_of_isGrpPullback hpj cmQ fun a ↦
    D1 a A A g g pj pj hg hg hpj hpj epj epj
  obtain ⟨rm, hrm, -⟩ := ExtUnique.existsUnique_oAct_of_isGrpPullback hpj XQ.rm fun a ↦
    ⟨cm.act (ofO a), by rw [← hcm]; exact hcmR _⟩
  choose y hy using fun c ↦ D2 c A D g dR pj d hg hdR hpj hd epj ed
  have hym : ∀ c, IsMonHom (y c) := fun c ↦ by
    haveI := hxm c
    exact ExtUnique.isMonHom_of_isGrpPullback hpj hd (x c) (y c) (hy c)
  have hz : ∀ (T : Over (Sp R)) (z : T ⟶ A), (∀ c, z ≫ y c = 1) → z = 1 := fun T z hz ↦ by
    have key : ∀ a ∈ Ideal.span (t : Set (𝓞 F)), z ≫ rm.act a = 1 := fun a ha ↦ by
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨W, hW⟩ := H3 ⟨a, ha⟩ (Finset.mem_attach _ _) ic j hic hj D A dR g d pj hdR hg hd hpj ed epj
        haveI := hwm a ha
        haveI := hD.smooth
        haveI : IsMonHom W := ExtUnique.isMonHom_of_isGrpPullback hd hpj (w a) W hW
        have e : y (dd a) ≫ W = rm.act a := ExtUnique.over_hom_ext_of_isPullback hpj.1 (by
          rw [Over.comp_left, ← Category.assoc, ← hy, Category.assoc, ← hW, ← Category.assoc, ← Over.comp_left,
            hwe a ha, hrm])
        rw [← e, ← Category.assoc, hz, MonObj.one_comp]
      | zero =>
        have e := rm.add 0 0
        rw [add_zero] at e
        rw [left_eq_mul.1 e, MonObj.comp_one]
      | add a b _ _ ha hb => rw [rm.add, MonObj.comp_mul, ha, hb, _root_.mul_one]
      | smul a b _ hb =>
        haveI := rm.hom a
        rw [smul_eq_mul, mul_comm, rm.mul, ← Category.assoc, hb, MonObj.one_comp]
    have e := key 1 (ht ▸ Submodule.mem_top)
    rwa [rm.one, Category.comp_id] at e
  obtain ⟨X₀, p', g', cm', h1, h2, h3, h4, h5⟩ := exists_obj_of_homs XQ A pj hA gA hpj rm hrm hD q q₂ hd m₁ m₂ q' x y
    hym hy (fun c ↦ by rw [hxe, evc, evc, ecls])
    (relAmple_of_algebraic_fibre R₀ R ic j hji G₀ P₀ Ψ₀ hfin hfl hsurj A g hg hA XQ.A pj hpj) hz hg ofO cmQ cm
    (fun a ↦ ExtUnique.over_hom_ext_of_isPullback hpj.1 (by rw [← hcmR, ← hrm, hcm])) hcmR
  exact ⟨X₀, p', g', cm', h1, h2, h3.trans epj, h4, h5⟩

end GlobalTheory.PlaceModel
