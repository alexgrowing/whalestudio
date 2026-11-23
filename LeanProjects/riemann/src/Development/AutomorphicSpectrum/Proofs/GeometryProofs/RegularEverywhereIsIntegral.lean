import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationCentreRegularUnitStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem germ_top_stalk_closed_point {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {q : X}
    (hq : ξ (IsLocalRing.closedPoint Ω) ⤳ q) :
    X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial) ≫ X.presheaf.stalkSpecializes hq ≫ Scheme.stalkClosedPointTo ξ
      = ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
  have e : ∀ (f : (⊤ : (Spec (CommRingCat.of Ω)).Opens) ⟶ ξ ⁻¹ᵁ ⊤),
      (Spec (CommRingCat.of Ω)).presheaf.map f.op = 𝟙 _ := fun f => (Spec (CommRingCat.of Ω)).presheaf.map_id _
  erw [e]
  simp

theorem algebraMap_mem_regAt' {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {O : Type} [CommRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    (h : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) (p : Cpt ξ) (o : O) :
    algebraMap O Ω o ∈ regAt ξ p := by
  obtain ⟨q, hq⟩ := p
  refine ⟨X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial) (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)), ?_⟩
  have h1 := germ_top_stalk_closed_point ξ hq
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ s.appTop ≫ ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
      = CommRingCat.ofHom (algebraMap O Ω) := by
    have : s.appTop ≫ ξ.appTop = (ξ ≫ s).appTop := by simp
    rw [reassoc_of% this, h]
    simp
  have h3 := congrArg (fun f => f.hom o) h2
  have h4 := congrArg (fun f => f.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4
  rw [CommRingCat.hom_ofHom] at h3
  refine Eq.trans ?_ (h4.trans h3)
  rfl

theorem isIntegral_of_forall_valuationSubring' {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]
    (hf : Function.Injective (algebraMap R Ω)) (a : Ω)
    (H : ∀ V : ValuationSubring Ω, (∀ r : R, algebraMap R Ω r ∈ V) → a ∈ V) : IsIntegral R a := by
  have hall : a ∈ ⨅ V : {V : ValuationSubring Ω // Set.range (algebraMap R Ω) ⊆ V.toSubring}, V.1.toSubring :=
    Subring.mem_iInf.mpr fun V => H V.1 fun r => V.2 ⟨r, rfl⟩
  rw [iInf_valuationSubring_superset, Subalgebra.mem_toSubring, mem_integralClosure_iff] at hall
  let g : R →+* Subring.closure (Set.range (algebraMap R Ω)) :=
    (algebraMap R Ω).codRestrict _ fun r => Subring.subset_closure ⟨r, rfl⟩
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => hf (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨y, hy⟩
    have hle : Subring.closure (Set.range (algebraMap R Ω)) ≤ (algebraMap R Ω).range :=
      Subring.closure_le.mpr fun z hz => hz
    obtain ⟨r, rfl⟩ := hle hy
    exact ⟨r, rfl⟩
  let e := RingEquiv.ofBijective g hg
  have hcomp : (algebraMap R Ω).comp (e.symm : _ →+* R) =
      (RingHom.id Ω).comp (algebraMap (Subring.closure (Set.range (algebraMap R Ω))) Ω) := by
    ext x
    have : g (e.symm x) = x := e.apply_symm_apply x
    exact congrArg Subtype.val this
  exact IsIntegral.map_of_comp_eq (e.symm : _ →+* R) (RingHom.id Ω) hcomp hall

theorem isIntegral_and_isAlgebraic_of_regular : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ a : Ω, ((∀ p : Cpt ξ, a ∈ regAt ξ p) → IsIntegral O a) ∧ ((∀ p ∈ genFibre O ξ, a ∈ regAt ξ p) → IsAlgebraic O a) := by
  intro X Ω _ ξ O _ _ _ s _ h hinj _ a
  refine ⟨fun ha => isIntegral_of_forall_valuationSubring' hinj a fun V hV => ?_, fun ha => ?_⟩
  · obtain ⟨p, hp, -⟩ := GlobalTheory.T.valuation_centre_regular_unit X Ω ξ O s h V hV
    exact hp (ha p)
  · haveI : FaithfulSMul O Ω := (faithfulSMul_iff_algebraMap_injective O Ω).2 hinj
    letI := FractionRing.liftAlgebra O Ω
    haveI : IsScalarTower O (FractionRing O) Ω := inferInstance
    refine (IsFractionRing.isAlgebraic_iff O (FractionRing O) Ω).2 (IsIntegral.isAlgebraic
      (isIntegral_of_forall_valuationSubring' (algebraMap (FractionRing O) Ω).injective a fun V hV => ?_))
    have hO : ∀ o : O, algebraMap O Ω o ∈ V := fun o => by
      rw [IsScalarTower.algebraMap_apply O (FractionRing O) Ω]
      exact hV _
    obtain ⟨p, hp, hu⟩ := GlobalTheory.T.valuation_centre_regular_unit X Ω ξ O s h V hO
    refine hp (ha p fun o ho => ?_)
    have hne : algebraMap O Ω o ≠ 0 := fun h0 => ho (hinj (by simpa using h0))
    have hreg := algebraMap_mem_regAt' ξ s h p o
    have hinv : (algebraMap O Ω o)⁻¹ ∈ V := by
      rw [IsScalarTower.algebraMap_apply O (FractionRing O) Ω, ← map_inv₀]
      exact hV _
    obtain ⟨g, hg, hga⟩ := hu _ hreg hne hinv
    obtain ⟨u, rfl⟩ := hg
    refine ⟨hne, hreg, ⟨(u⁻¹ : (X.presheaf.stalk p.1)ˣ).1, ?_⟩⟩
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hga, ← map_mul, Units.inv_mul, map_one]

end GlobalTheory.CompanionTheory.Ar.Flat
