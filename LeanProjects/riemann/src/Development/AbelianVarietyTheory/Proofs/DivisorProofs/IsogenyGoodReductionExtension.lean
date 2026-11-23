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
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAbelianSchemeModelOfIsogenyDedekind
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueFactorThroughEtaleIsogenyReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumUnramifiedAlmostAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismTrivialOnReducedKernel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotModel

theorem mem_or_inv_mem {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {k : IntermediateField ℚ ℂ}
    (hk : FiniteDimensional ℚ k) {R : Subring ℂ} (hR : IsPlaceOver l lam k R) {x : ℂ} (hx : x ∈ k) :
    x ∈ R ∨ x⁻¹ ∈ R := by
  have halg : x ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff']
    exact (IntermediateField.isIntegral_iff (x := (⟨x, hx⟩ : k))).1 (Algebra.IsIntegral.isIntegral _)
  rcases le_total ‖lam ⟨x, halg⟩‖ 1 with h | h
  · exact Or.inl (hR.2.2 x hx ⟨halg, by simpa using h⟩)
  · refine Or.inr (hR.2.2 _ (inv_mem hx) ⟨inv_mem halg, ?_⟩)
    have : (⟨x⁻¹, inv_mem halg⟩ : algebraicClosure ℚ ℂ) = (⟨x, halg⟩ : algebraicClosure ℚ ℂ)⁻¹ := rfl
    rw [this, map_inv₀, norm_inv, Real.rpow_zero]
    exact inv_le_one_of_one_le₀ h

theorem exists_place (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k : IntermediateField ℚ ℂ)
    (hk : FiniteDimensional ℚ k) : ∃ R : Subring ℂ, IsPlaceOver l lam k R ∧ ∀ x ∈ R, x ∈ k := by
  obtain ⟨S, hS, hS1, hS2⟩ := GlobalTheory.PlaceRingExists.exists_isPlaceOver l lam k hk
  let R : Subring ℂ := S ⊓ k.toSubfield.toSubring
  have hRS : R ≤ S := inf_le_left
  let j : R →+* S := Subring.inclusion hRS
  have hj : Function.Injective j := Subring.inclusion_injective hRS
  have hdvd : ∀ a b : R, j a ∣ j b → a ∣ b := by
    rintro a b ⟨c, hc⟩
    by_cases ha : a = 0
    · subst ha
      have : b = 0 := hj (by simpa using hc)
      simp [this]
    · have ha' : (a : ℂ) ≠ 0 := fun h => ha (Subtype.ext h)
      have hc' : (b : ℂ) = a * c := congrArg Subtype.val hc
      have hck : (c : ℂ) ∈ k := by
        have : (c : ℂ) = (a : ℂ)⁻¹ * b := by rw [hc']; field_simp
        rw [this]
        exact mul_mem (inv_mem a.2.2) b.2.2
      exact ⟨⟨c, c.2, hck⟩, Subtype.ext hc'⟩
  have hunit : ∀ a : R, IsUnit (j a) → IsUnit a := fun a h =>
    isUnit_of_dvd_one (hdvd a 1 (by simpa using h.dvd))
  haveI : IsLocalRing R := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (j a) with h | h
    · exact Or.inl (hunit a h)
    · exact Or.inr (hunit _ (by simpa using h))
  haveI : IsPrincipalIdealRing R := ⟨fun I => by
    obtain ⟨a, ha, hmin⟩ := (InvImage.wf (fun a : R => IsDiscreteValuationRing.addVal S (j a))
      (wellFounded_lt (α := ℕ∞))).has_min (I : Set R) ⟨0, I.zero_mem⟩
    refine ⟨a, le_antisymm (fun b hb => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ha)⟩
    exact Ideal.mem_span_singleton.2 (hdvd a b (IsDiscreteValuationRing.addVal_le_iff_dvd.1
      (not_lt.1 (hmin b hb))))⟩
  refine ⟨R, ⟨⟨?_⟩, fun x hx => hS1 x hx.1, fun x hx hs => ⟨hS2 x hx hs, hx⟩⟩, fun x hx => hx.2⟩
  intro hbot
  have hl : (l : R) ≠ 0 := by
    intro h
    have : (l : ℂ) = 0 := by simpa using congrArg Subtype.val h
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  have hu : IsUnit (l : R) := by
    by_contra hn
    have : (l : R) ∈ IsLocalRing.maximalIdeal R := hn
    rw [hbot] at this
    exact hl this
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  obtain ⟨hb1, hb2⟩ := hS1 b b.2.1
  have hb' : (l : algebraicClosure ℚ ℂ) * ⟨b, hb1⟩ = 1 := Subtype.ext (by simpa using congrArg Subtype.val hb)
  have h1 := congrArg (fun z => ‖lam z‖) hb'
  simp only [map_mul, map_natCast, norm_mul, map_one, norm_one] at h1
  have h2 := GlobalTheory.PlaceRingExists.norm_prime_lt_one l
  rw [Real.rpow_zero] at hb2
  nlinarith [norm_nonneg (lam ⟨b, hb1⟩), norm_nonneg ((l : ℂ_[l]))]

theorem exists_field_of_finite (k₁ : IntermediateField ℚ ℂ) (hk : FiniteDimensional ℚ k₁) (R₁ : Subring ℂ)
    (hR : ∀ x ∈ R₁, x ∈ k₁) (S : Type) [CommRing S] (a : R₁ →+* S) (ha : a.Finite) :
    ∃ k : IntermediateField ℚ ℂ, FiniteDimensional ℚ k ∧ k₁ ≤ k ∧
      ∀ φ : S →+* ℂ, φ.comp a = R₁.subtype → ∀ s, φ s ∈ k := by
  classical
  letI := a.toAlgebra
  haveI : Module.Finite R₁ S := ha
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule R₁ S).FG)
  have hint : ∀ s : S, IsIntegral R₁ s := fun s => Algebra.IsIntegral.isIntegral s
  choose p hp1 hp2 using hint
  let Z : Finset ℂ := t.biUnion fun s => ((p s).map R₁.subtype).roots.toFinset
  have hZ : ∀ z ∈ (Z : Set ℂ), IsIntegral ℚ z := by
    intro z hz
    obtain ⟨s, -, hs⟩ := Finset.mem_biUnion.1 hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots ((hp1 s).map _).ne_zero] at hs
    have h1 : IsIntegral k₁ z := by
      refine ⟨(p s).map (R₁.subtype.codRestrict k₁ fun x => hR x x.2), (hp1 s).map _, ?_⟩
      rw [Polynomial.eval₂_map]
      rw [Polynomial.IsRoot, Polynomial.eval_map] at hs
      exact hs
    exact isIntegral_trans z h1
  haveI := IntermediateField.finiteDimensional_adjoin hZ
  refine ⟨k₁ ⊔ IntermediateField.adjoin ℚ (Z : Set ℂ), IntermediateField.finiteDimensional_sup _ _,
    le_sup_left, fun φ hφ s => ?_⟩
  have hs : s ∈ Submodule.span R₁ (t : Set S) := by rw [ht]; trivial
  induction hs using Submodule.span_induction with
  | mem x hx =>
    refine (le_sup_right : _ ≤ k₁ ⊔ _) (IntermediateField.subset_adjoin _ _ ?_)
    refine Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨x, hx, ?_⟩)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots ((hp1 x).map _).ne_zero, Polynomial.IsRoot,
      Polynomial.eval_map, ← hφ, ← Polynomial.hom_eval₂]
    have := hp2 x
    rw [show algebraMap R₁ S = a from rfl] at this
    rw [this, map_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Algebra.smul_def, map_mul]
    refine mul_mem ?_ hx
    have : φ (algebraMap R₁ S r) = r := congrArg (fun f : R₁ →+* ℂ => f r) hφ
    rw [this]
    exact (le_sup_left : _ ≤ k₁ ⊔ _) (hR r r.2)

theorem exists_field_of_isFinite (k₁ : IntermediateField ℚ ℂ) (hk : FiniteDimensional ℚ k₁) (R₁ : Subring ℂ)
    (hR : ∀ x ∈ R₁, x ∈ k₁) (X : Scheme.{0}) (f : X ⟶ Sp R₁) [IsFinite f] :
    ∃ k : IntermediateField ℚ ℂ, FiniteDimensional ℚ k ∧ k₁ ≤ k ∧
      ∀ x : Sp ℂ ⟶ X, x ≫ f = spMap R₁.subtype → ∃ y : Sp k ⟶ X, spMap (algebraMap k ℂ) ≫ y = x := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let a : CommRingCat.of R₁ ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ f)
  have ha : Spec.map a = X.isoSpec.inv ≫ f := Spec.map_preimage _
  have hfin : a.hom.Finite := by
    have : IsFinite (Spec.map a) := by rw [ha]; infer_instance
    exact (IsFinite.SpecMap_iff a).1 this
  obtain ⟨k, hk1, hk2, hk3⟩ := exists_field_of_finite k₁ hk R₁ hR Γ(X, ⊤) a.hom hfin
  refine ⟨k, hk1, hk2, fun x hx => ?_⟩
  let φ : Γ(X, ⊤) ⟶ CommRingCat.of ℂ := Spec.preimage (x ≫ X.isoSpec.hom)
  have hφ : Spec.map φ = x ≫ X.isoSpec.hom := Spec.map_preimage _
  have hcomp : φ.hom.comp a.hom = R₁.subtype := by
    have : a ≫ φ = CommRingCat.ofHom R₁.subtype := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ, ha, Category.assoc, Iso.hom_inv_id_assoc, hx]
    exact congrArg CommRingCat.Hom.hom this
  refine ⟨Spec.map (CommRingCat.ofHom (φ.hom.codRestrict k (hk3 φ.hom hcomp))) ≫ X.isoSpec.inv, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, Iso.comp_inv_eq, ← hφ]
  rfl

theorem epi_field (k K : Type) [Field k] [Field K] (t : Sp k ⟶ Sp K) : Epi t :=
  Flat.epi_of_flat_of_surjective t

theorem kill (A Y Y' : Over (Sp ℂ)) [GrpObj A] [GrpObj Y] [GrpObj Y'] (hA : IsAbelianScheme A)
    [IsSeparated Y'.hom] (u : A ⟶ Y) (f : A ⟶ Y') [IsFinite u.left] [Flat u.left] (N : ℕ) (hN : 1 ≤ N)
    (hu : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ u = 1 → x ^ N = 1)
    (h : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ u = 1 → x ≫ f = 1) :
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ u = 1 → x ≫ f = 1 := by
  let Z : Over (Sp ℂ) := pullback u η
  let i : Z ⟶ A := pullback.fst u η
  have hP : IsPullback i (toUnit Z) u η := by
    have := IsPullback.of_hasPullback u (η : 𝟙_ _ ⟶ Y)
    rwa [toUnit_unique (pullback.snd u η) (toUnit Z)] at this
  have hP' : IsPullback i.left Z.hom u.left (η : 𝟙_ _ ⟶ Y).left := by
    have := hP.map (Over.forget _)
    simpa using this
  haveI : IsFinite Z.hom := MorphismProperty.of_isPullback (P := @IsFinite) hP' inferInstance
  haveI : Flat Z.hom := MorphismProperty.of_isPullback (P := @Flat) hP' inferInstance
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have h1 : IsUnit ((N : ℕ) : ℂ) := (Nat.cast_ne_zero.2 (by omega) : ((N : ℕ) : ℂ) ≠ 0).isUnit
    simpa using h1.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  obtain ⟨-, -, het, -⟩ := abelianScheme_id_pow_finite_etale_surjective _ A N hA hunit
  have hi : i ≫ (𝟙 A ^ N) = toUnit Z ≫ η := by
    rw [comp_pow, Category.comp_id, hu Z i (by rw [hP.w, Hom.one_def]), Hom.one_def]
  have hi' : i.left ≫ (𝟙 A ^ N).left = Z.hom ≫ (η : 𝟙_ _ ⟶ A).left := by
    simpa using congrArg (fun z => z.left) hi
  let j := pullback.lift i.left Z.hom hi'
  haveI : Mono (η : 𝟙_ _ ⟶ Y) := ⟨fun a b _ => toUnit_unique a b⟩
  haveI : Mono i := inferInstanceAs (Mono (pullback.fst u η))
  haveI : Mono i.left := inferInstanceAs (Mono ((Over.forget _).map i))
  haveI : Mono (j ≫ pullback.fst _ _) := by rw [pullback.lift_fst]; infer_instance
  haveI : Mono j := mono_of_mono j (pullback.fst _ _)
  haveI : FormallyUnramified j := inferInstance
  haveI : FormallyUnramified Z.hom := by
    rw [← pullback.lift_snd i.left Z.hom hi']
    haveI : Etale (pullback.snd (𝟙 A ^ N).left (η : 𝟙_ _ ⟶ A).left) := inferInstance
    exact MorphismProperty.comp_mem @FormallyUnramified j _ inferInstance inferInstance
  haveI : Etale Z.hom := Etale.of_formallyUnramified_of_flat _
  haveI : AlgebraicGeometry.IsReduced Z.left := isReduced_of_smooth_of_isReduced Z.hom
  exact KernelKill.comp_eq_one_of_kill_closedPoints A Y Y' Z u f i hP h

theorem exists_iso (A Y Y' : Over (Sp ℂ)) [GrpObj A] [GrpObj Y] [GrpObj Y'] (hA : IsAbelianScheme A)
    [IsSeparated Y.hom] [IsSeparated Y'.hom] (u : A ⟶ Y) (f : A ⟶ Y') [IsMonHom u] [IsMonHom f]
    [IsFinite u.left] [Flat u.left] [Surjective u.left] [IsFinite f.left] [Flat f.left] [Surjective f.left]
    (N : ℕ) (hN : 1 ≤ N)
    (hu : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ u = 1 → x ^ N = 1)
    (hf : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ f = 1 → x ^ N = 1)
    (h : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ u = 1 ↔ x ≫ f = 1) :
    ∃ e : Y ≅ Y', IsMonHom e.hom ∧ u ≫ e.hom = f := by
  obtain ⟨⟨a, ha, hua⟩, eu⟩ := exists_monHom_factor_of_flat_surjective _ A Y Y' u f inferInstance inferInstance
    inferInstance inferInstance inferInstance (kill A Y Y' hA u f N hN hu fun x => (h x).1)
  obtain ⟨⟨b, hb, hfb⟩, ef⟩ := exists_monHom_factor_of_flat_surjective _ A Y' Y f u inferInstance inferInstance
    inferInstance inferInstance inferInstance (kill A Y' Y hA f u N hN hf fun x => (h x).2)
  refine ⟨⟨a, b, ?_, ?_⟩, ha, hua⟩
  · rw [← cancel_epi u, reassoc_of% hua, hfb, Category.comp_id]
  · rw [← cancel_epi f, reassoc_of% hfb, hua, Category.comp_id]

theorem exists_field_model (K : Type) [Field K] (t : Sp ℂ ⟶ Sp K) (P : Out.PolAV (Sp K))
    (A' : Over (Sp ℂ)) [GrpObj A'] (φ : A'.left ⟶ P.A.left) (hφ : IsGrpPullback A' P.A t φ)
    (B : Over (Sp ℂ)) [GrpObj B] (α : A' ⟶ B) (N : ℕ) (hB : IsAbelianScheme B) [IsMonHom α] [IsFinite α.left]
    [Flat α.left] [Surjective α.left] (hN : 1 ≤ N)
    (hα : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A'), x ≫ α = 1 → x ^ N = 1)
    (hrat : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A', x ^ N = 1 →
      ∃ c : 𝟙_ (Over (Sp K)) ⟶ P.A, x.left ≫ φ = t ≫ c.left) :
    ∃ (B₀ : Over (Sp K)) (_ : GrpObj B₀) (ψ : P.A ⟶ B₀) (q : B.left ⟶ B₀.left), IsAbelianScheme B₀ ∧
      IsMonHom ψ ∧ IsFinite ψ.left ∧ Flat ψ.left ∧ Surjective ψ.left ∧
      (∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ≫ ψ = 1 → x ^ N = 1) ∧
      IsGrpPullback B B₀ t q ∧ α.left ≫ q = φ ≫ ψ.left := by
  haveI := P.isAb.comm
  haveI := P.isAb.proper
  haveI := hB.proper
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback P.isAb hφ
  obtain ⟨e, he⟩ : ∃ e : (𝟙_ (Over (Sp ℂ)) ⟶ A') ≃* (Over.mk t ⟶ P.A), ∀ x, (e x).left = x.left ≫ φ :=
    exists_mulEquiv_of_isGrpPullback hφ (𝟙 _) t (Category.id_comp _).symm
  have hjinj : ∀ (k : Type) [Field k] (s : Sp k ⟶ Sp K) (c c' : 𝟙_ (Over (Sp K)) ⟶ P.A),
      toUnit (Over.mk s) ≫ c = toUnit (Over.mk s) ≫ c' → c = c' := by
    intro k _ s c c' h
    haveI := epi_field k K s
    ext1
    have := congrArg (fun z => z.left) h
    rw [← cancel_epi s]
    simpa using this
  let j : (𝟙_ (Over (Sp K)) ⟶ P.A) →* (Over.mk t ⟶ P.A) :=
    { toFun := fun c => toUnit _ ≫ c, map_one' := comp_one _, map_mul' := fun a b => comp_mul _ a b }
  let m : (𝟙_ (Over (Sp K)) ⟶ P.A) →* (𝟙_ (Over (Sp ℂ)) ⟶ B) :=
    (IsMonHom.monoidHom α _).comp (e.symm.toMonoidHom.comp j)
  let C := m.ker
  have hC : ∀ c, c ∈ C ↔ e.symm (toUnit _ ≫ c) ≫ α = 1 := fun c => Iff.rfl
  have hCN : ∀ c ∈ C, (toUnit (Over.mk t) ≫ c) ^ N = 1 := by
    intro c hc
    apply e.symm.injective
    rw [map_pow, map_one]
    exact hα _ _ ((hC c).1 hc)
  have hCN' : ∀ c ∈ C, c ^ N = 1 := by
    intro c hc
    apply hjinj ℂ t
    rw [comp_pow, hCN c hc, comp_one]
  haveI : Finite C := by
    have hcard := (firstFiveLaws.1.mulN (Sp K) P N hN).2.2.2.2 ℂ t (Nat.cast_ne_zero.2 (by omega))
    haveI : Finite {x : Over.mk t ⟶ P.A // x ^ N = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
    refine Finite.of_injective
      (fun c : C => (⟨toUnit _ ≫ c.1, hCN c.1 c.2⟩ : {x : Over.mk t ⟶ P.A // x ^ N = 1})) ?_
    intro c c' h
    exact Subtype.ext (hjinj ℂ t _ _ (congrArg Subtype.val h))
  letI : CommGroup C := { (inferInstance : Group C) with
    mul_comm := fun a b => Subtype.ext (Hom.commMonoid.mul_comm a.1 b.1) }
  obtain ⟨B₀, _, ψ, hB₀, hψ, hfin, het, hsurj, -, hker⟩ :=
    exists_quotient_by_finite_group_of_sections K P C C.subtype (fun k _ _ s c h =>
      Subtype.ext (hjinj k s _ _ (h.trans (comp_one _).symm)))
  haveI := hB₀.proper
  haveI : IsMonHom (𝟙 P.A ^ N) := by
    have hne : ((N : ℕ) : K) ≠ 0 := by
      intro h0
      have := congrArg (Spec.preimage t).hom h0
      rw [map_natCast, map_zero, Nat.cast_eq_zero] at this
      omega
    refine (abelianScheme_id_pow_finite_etale_surjective _ P.A N P.isAb ?_).1
    simpa using hne.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨g', hg', hψg, -⟩ := HkFactor.exists_unique_factor (Sp K) P.A B₀ P.A ψ (𝟙 P.A ^ N) P.isAb hB₀
    inferInstance hψ hfin het hsurj inferInstance (fun k _ _ s x hx => by
      obtain ⟨c, rfl⟩ := (hker k s x).1 hx
      rw [Category.assoc, comp_pow, Category.comp_id]
      exact (congrArg (toUnit _ ≫ ·) (hCN' c.1 c.2)).trans (comp_one _))
  have hψN : ∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ≫ ψ = 1 → x ^ N = 1 := by
    intro T x hx
    have : x ≫ ψ ≫ g' = 1 := by rw [reassoc_of% hx, one_comp]
    rwa [hψg, comp_pow, Category.comp_id] at this
  obtain ⟨B', _, q', hq'⟩ := FlagTan.exists_isGrpPullback B₀ t
  obtain ⟨π, hπ, hπw⟩ := HomDescent.exists_isMonHom_pull hφ hq' ψ
  have hsq : IsPullback φ π.left ψ.left q' := by
    refine IsPullback.of_bot ?_ hπw.symm hq'.1
    simpa using hφ.1
  haveI : IsFinite π.left := MorphismProperty.of_isPullback (P := @IsFinite) hsq hfin
  haveI : Flat π.left := MorphismProperty.of_isPullback (P := @Flat) hsq inferInstance
  haveI : Surjective π.left := MorphismProperty.of_isPullback (P := @Surjective) hsq hsurj
  haveI := (PolPull.isAbelianScheme_of_isGrpPullback hB₀ hq').proper
  have hπN : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A'), x ≫ π = 1 → x ^ N = 1 := by
    intro T x hx
    obtain ⟨eA, heA⟩ : ∃ e : (T ⟶ A') ≃* (Over.mk (T.hom ≫ t) ⟶ P.A), ∀ x, (e x).left = x.left ≫ φ :=
      exists_mulEquiv_of_isGrpPullback hφ T.hom _ rfl
    obtain ⟨eB, heB⟩ : ∃ e : (T ⟶ B') ≃* (Over.mk (T.hom ≫ t) ⟶ B₀), ∀ x, (e x).left = x.left ≫ q' :=
      exists_mulEquiv_of_isGrpPullback hq' T.hom _ rfl
    apply eA.injective
    rw [map_pow, map_one]
    apply hψN
    have : eA x ≫ ψ = eB (x ≫ π) := by
      ext1
      rw [heB, Over.comp_left, Over.comp_left, heA, Category.assoc, Category.assoc, hπw]
    rw [this, hx, map_one]
  obtain ⟨eB, heB⟩ : ∃ e : (𝟙_ (Over (Sp ℂ)) ⟶ B') ≃* (Over.mk t ⟶ B₀), ∀ x, (e x).left = x.left ≫ q' :=
    exists_mulEquiv_of_isGrpPullback hq' (𝟙 _) t (Category.id_comp _).symm
  obtain ⟨β, hβ, hαβ⟩ := exists_iso A' B B' hA' α π N hN hα hπN (fun x => by
    have h1 : e x ≫ ψ = eB (x ≫ π) := by
      ext1
      rw [heB, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, hπw]
    have h2 : x ≫ π = 1 ↔ e x ≫ ψ = 1 := by rw [h1, map_eq_one_iff _ eB.injective]
    rw [h2, hker ℂ t]
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := hrat x (hα _ x hx)
      have h3 : e x = toUnit _ ≫ c := by
        ext1
        rw [he, hc]
        simp
      refine ⟨⟨c, (hC c).2 ?_⟩, h3⟩
      rw [← h3, e.symm_apply_apply, hx]
    · rintro ⟨c, hc⟩
      have := (hC c.1).1 c.2
      change e x = toUnit _ ≫ c.1 at hc
      rwa [← hc, e.symm_apply_apply] at this)
  refine ⟨B₀, inferInstance, ψ, β.hom.left ≫ q', hB₀, hψ, hfin, inferInstance, hsurj, hψN,
    ((isGrpPullback_of_iso β).comp hq').congr (Category.id_comp _) rfl, ?_⟩
  rw [← Category.assoc, ← Over.comp_left, hαβ, hπw]

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem dualMapR_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : (Chart.dualMapR g).comp (Chart.dualMapR f) = Chart.dualMapR (g.comp f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem dualMapR_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_polPull {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (P' : Out.PolAV S') (g : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f g := by
  obtain ⟨P', g, hg, -, hmul, -⟩ := firstFiveLaws.1.polBaseChange S S' f P
  refine ⟨P', g, hg, fun T x y x₀ y₀ hx hy => ?_⟩
  have h1 : x₀ = Out.toBase hg.w x := by ext1; exact hx
  have h2 : y₀ = Out.toBase hg.w y := by ext1; exact hy
  rw [h1, h2, ← hmul]
  rfl

theorem exists_quotModel : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ),
    FiniteDimensional ℚ k₁ → IsPlaceOver l lam k₁ R₁ → (∀ x ∈ R₁, x ∈ k₁) →
    ∀ (P : Out.PolAV (Sp R₁)) (A' : Over (Sp ℂ)) [GrpObj A'] (φ' : A'.left ⟶ P.A.left),
    IsGrpPullback A' P.A (spMap R₁.subtype) φ' →
    ∀ (B : Over (Sp ℂ)) [GrpObj B] (α : A' ⟶ B) (N : ℕ), IsAbelianScheme B → IsMonHom α → IsFinite α.left →
    Flat α.left → Surjective α.left → 1 ≤ N → (∀ (T : Over (Sp ℂ)) (x : T ⟶ A'), x ≫ α = 1 → x ^ N = 1) →
    ∃ (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), FiniteDimensional ℚ k₀ ∧ IsPlaceOver l lam k₀ R₀ ∧
      (∀ x ∈ R₀, x ∈ k₀) ∧
      ∃ (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (p₀ : B.left ⟶ G₀.left) (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
        IsAbelianScheme G₀ ∧ IsGrpPullback B G₀ (spMap R₀.subtype) p₀ ∧ IsMonHom Ψ₀ ∧ IsFinite Ψ₀.left ∧
        Flat Ψ₀.left ∧ Surjective Ψ₀.left ∧
        ∀ (v : epsR R₁ ⟶ P.A) (v' : epsR ℂ ⟶ A'), IsTangent v →
          v'.left ≫ φ' = spMap (Chart.dualMapR R₁.subtype) ≫ v.left →
          ∃ v₀ : epsR R₀ ⟶ G₀, IsTangent v₀ ∧ (v' ≫ α).left ≫ p₀ = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left := by
  intro l _ lam k₁ R₁ hk₁ hR₁ hRk₁ P A' _ φ' hφ' B _ α N hB hα hfin hflat hsurj hN hker
  haveI := hR₁.1
  obtain ⟨hNfin, -⟩ := firstFiveLaws.1.mulN (Sp R₁) P N hN
  obtain ⟨K, hK, hk₁K, hdesc⟩ := exists_field_of_isFinite k₁ hk₁ R₁ hRk₁ _
    (pullback.snd (𝟙 P.A ^ N).left (η : 𝟙_ _ ⟶ P.A).left)
  obtain ⟨R₀, hR₀, hR₀K⟩ := exists_place l lam K hK
  haveI := hR₀.1
  have hle : R₁ ≤ R₀ := fun x hx => hR₀.2.2 x (hk₁K (hRk₁ x hx)) (hR₁.2.1 x hx)
  let inc : R₁ →+* R₀ := Subring.inclusion hle
  let a : R₀ →+* K := R₀.subtype.codRestrict K fun x => hR₀K x x.2
  letI : Algebra R₀ K := a.toAlgebra
  haveI : IsFractionRing R₀ K := by
    haveI : FaithfulSMul R₀ K := (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h =>
      Subtype.ext (congrArg (fun z : K => (z : ℂ)) h)
    refine IsFractionRing.of_field _ _ fun z => ?_
    rcases mem_or_inv_mem hK hR₀ z.2 with h | h
    · exact ⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩
    · refine ⟨1, ⟨(z : ℂ)⁻¹, h⟩, ?_⟩
      have : algebraMap R₀ K ⟨(z : ℂ)⁻¹, h⟩ = z⁻¹ := Subtype.ext rfl
      rw [this, map_one, one_div, inv_inv]
  let t : Sp ℂ ⟶ Sp K := spMap (algebraMap K ℂ)
  haveI := epi_field ℂ K t
  have hta : t ≫ spMap (algebraMap R₀ K) = spMap R₀.subtype := spMap_comp _ _
  have htai : t ≫ spMap (algebraMap R₀ K) ≫ spMap inc = spMap R₁.subtype := by
    rw [reassoc_of% hta, spMap_comp]; rfl
  obtain ⟨P₀, g₀, hg₀⟩ := exists_polPull (spMap inc) P
  obtain ⟨PK, gK, hgK⟩ := exists_polPull (spMap (algebraMap R₀ K)) P₀
  have hg := hgK.comp hg₀
  let φ : A'.left ⟶ PK.A.left := hg.1.lift φ' (A'.hom ≫ t) (by rw [hφ'.1.w, Category.assoc, htai])
  have hφ1 : φ ≫ gK ≫ g₀ = φ' := hg.1.lift_fst _ _ _
  have hφ2 : φ ≫ PK.A.hom = A'.hom ≫ t := hg.1.lift_snd _ _ _
  have hφ : IsGrpPullback A' PK.A t φ := hg.cancel (hφ'.congr htai.symm hφ1.symm) hφ2
  obtain ⟨BK, _, ψ, q, hBK, hψ, hψfin, hψflat, hψsurj, hψN, hq, hαq⟩ :=
    exists_field_model K t PK A' φ hφ B α N hB hN hker (fun x hx => by
      obtain ⟨e, he⟩ : ∃ e : (𝟙_ (Over (Sp ℂ)) ⟶ A') ≃* (Over.mk (spMap R₁.subtype) ⟶ P.A),
          ∀ x, (e x).left = x.left ≫ φ' :=
        exists_mulEquiv_of_isGrpPullback hφ' (𝟙 _) _ (Category.id_comp _).symm
      have h1 : e x ≫ (𝟙 P.A ^ N) = toUnit _ ≫ η := by
        rw [comp_pow, Category.comp_id, ← map_pow, hx, map_one, Hom.one_def]
      have h2 : (x.left ≫ φ') ≫ (𝟙 P.A ^ N).left = spMap R₁.subtype ≫ (η : 𝟙_ _ ⟶ P.A).left := by
        rw [← he]
        simpa using congrArg (fun z => z.left) h1
      obtain ⟨y, hy⟩ := hdesc (pullback.lift _ _ h2) (pullback.lift_snd _ _ _)
      have hy1 : t ≫ y ≫ pullback.fst _ _ = x.left ≫ φ' := by
        rw [← Category.assoc, hy, pullback.lift_fst]
      have hxw : x.left ≫ A'.hom = 𝟙 _ := Over.w x
      have hy2 : (y ≫ pullback.fst _ _) ≫ P.A.hom = 𝟙 _ ≫ spMap (algebraMap R₀ K) ≫ spMap inc := by
        rw [← cancel_epi t, ← Category.assoc, hy1, Category.assoc, hφ'.1.w, reassoc_of% hxw,
          Category.id_comp, htai]
      refine ⟨Over.homMk (hg.1.lift _ _ hy2) (hg.1.lift_snd _ _ _), ?_⟩
      change x.left ≫ φ = t ≫ hg.1.lift _ _ hy2
      refine hg.1.hom_ext ?_ ?_
      · rw [Category.assoc, hφ1, Category.assoc, hg.1.lift_fst, hy1]
      · rw [Category.assoc, hφ2, Category.assoc, hg.1.lift_snd, reassoc_of% hxw]
        exact (Category.comp_id _).symm)
  obtain ⟨G₀, _, φB, Ψ, hG₀, hφB, hΨ, hΨfin, hΨflat, hΨsurj, hΨw⟩ :=
    exists_abelianScheme_model_of_isogeny_dedekind firstFiveLaws.1 R₀ K P₀ PK.A BK gK ψ N hgK hBK hψ hψfin
      hψflat hψsurj hN hψN
  refine ⟨K, R₀, hK, hR₀, hR₀K, G₀, inferInstance, q ≫ φB, P₀, Ψ, hG₀, (hq.comp hφB).congr hta rfl, hΨ, hΨfin,
    hΨflat, hΨsurj, fun v v' hv hvv' => ?_⟩
  obtain ⟨w, hw, -⟩ := existsUnique_isVecOver hg₀.1 v
  refine ⟨w ≫ Ψ, HomLinear.isTangent_comp Ψ (hw.isTangent hg₀ hv), ?_⟩
  have hw' : w.left ≫ g₀ = spMap (Chart.dualMapR inc) ≫ v.left := hw
  have hww : w.left ≫ P₀.A.hom = spMap (algebraMap R₀ (DualNumber R₀)) := Over.w w
  have hv'w : v'.left ≫ A'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w v'
  have key : v'.left ≫ φ ≫ gK = spMap (Chart.dualMapR R₀.subtype) ≫ w.left := by
    refine hg₀.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hφ1, hvv', Category.assoc, hw', ← Category.assoc, spMap_comp,
        dualMapR_comp]
      rfl
    · rw [Category.assoc, Category.assoc, hgK.1.w, reassoc_of% hφ2, hta, reassoc_of% hv'w, Category.assoc, hww,
        spMap_comp, spMap_comp, dualMapR_algebraMap]
  rw [Over.comp_left, Over.comp_left, Category.assoc, reassoc_of% hαq, hΨw, ← Category.assoc φ,
    ← Category.assoc, key, Category.assoc]

end GlobalTheory.QuotModel
