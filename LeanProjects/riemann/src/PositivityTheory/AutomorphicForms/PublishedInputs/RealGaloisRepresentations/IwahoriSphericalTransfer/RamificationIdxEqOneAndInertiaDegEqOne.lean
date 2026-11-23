import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
import GroundTheory.GlobalFields.CompletionAtPlace.Galois
import ReciprocityTheory.GaloisValuations.Global
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceIsoDec

open scoped Pointwise

theorem exists_isPlaceOver_mid {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP⟩

theorem liesOver_of_isPlaceOver {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hv : IsPlaceOver A v) (hw : IsPlaceOver A w) : w.asIdeal.LiesOver v.asIdeal := by
  refine ⟨?_⟩
  ext x
  rw [← hv x, Ideal.under, Ideal.mem_comap, ← hw, IsScalarTower.algebraMap_apply K L Ω]
  rfl

theorem valuation_smul_lt_one_iff {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (σ : Ω ≃ₐ[F] Ω)
    (A : ValuationSubring Ω) (z : Ω) :
    (σ • A).valuation z < 1 ↔ A.valuation (σ.symm z) < 1 := by
  have hmem : ∀ y, y ∈ σ • A ↔ σ.symm y ∈ A := fun y => by
    conv_lhs => rw [show y = σ (σ.symm y) by simp]
    rw [← AlgEquiv.smul_def]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  rw [valuation_lt_one_iff', valuation_lt_one_iff', hmem, hmem, map_inv₀, map_eq_zero_iff _ σ.symm.injective]

end GlobalTheory.PlaceIsoDec

namespace GlobalTheory.PlaceIsoDec

open scoped Pointwise

variable {F K L Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra F K] [Algebra F L] [Algebra K L] [Algebra F Ω] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower F K L] [IsScalarTower F L Ω] [IsScalarTower K L Ω] [IsScalarTower F K Ω]

theorem fixes_of_mem_stabilizer [IsAlgClosure F Ω] [IsAlgClosure L Ω]
    {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 L)} (hP : IsPlaceOver A P)
    (hD : Dec (F := F) A ≤ (res F Ω K).range)
    (τ : L ≃ₐ[F] L) (hτ : τ • P.asIdeal = P.asIdeal) (x : K) :
    τ (algebraMap K L x) = algebraMap K L x := by
  haveI : Normal F Ω := IsAlgClosure.normal F Ω
  set σ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω with hσ
  have hσL : ∀ y : L, σ (algebraMap L Ω y) = algebraMap L Ω (τ y) := fun y =>
    AlgEquiv.liftNormal_commutes τ Ω y
  have hσL' : ∀ y : L, σ.symm (algebraMap L Ω y) = algebraMap L Ω (τ.symm y) := fun y => by
    rw [AlgEquiv.symm_apply_eq, hσL, AlgEquiv.apply_symm_apply]
  have hσA : IsPlaceOver (σ • A) P := fun y => by
    rw [valuation_smul_lt_one_iff, hσL', ← hτ, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact hP (τ⁻¹ • y)
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_isPlaceOver (F := L) hσA hP
  set g : Ω ≃ₐ[F] Ω := ρ.restrictScalars F * σ with hg
  have hgA : g ∈ Dec (F := F) A := by
    show g • A = A
    rw [hg, mul_smul]
    exact hρ
  obtain ⟨h, hh⟩ := hD hgA
  have e1 : g (algebraMap K Ω x) = algebraMap K Ω x := by
    rw [← hh]
    exact h.commutes x
  have e2 : g (algebraMap K Ω x) = algebraMap L Ω (τ (algebraMap K L x)) := by
    rw [IsScalarTower.algebraMap_apply K L Ω]
    show ρ (σ (algebraMap L Ω _)) = _
    rw [hσL]
    exact ρ.commutes _
  exact (algebraMap L Ω).injective (by rw [← e2, e1, IsScalarTower.algebraMap_apply K L Ω])

end GlobalTheory.PlaceIsoDec

namespace GlobalTheory.PlaceIsoDec

open scoped Pointwise

variable {F K L Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra F K] [Algebra F L] [Algebra K L] [Algebra F Ω] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower F K L] [IsScalarTower F L Ω] [IsScalarTower K L Ω] [IsScalarTower F K Ω]

theorem ramificationIdx_eq_one_and_inertiaDeg_eq_one [IsAlgClosure F Ω] [IsAlgClosure L Ω] [IsGalois F L]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 K)}
    {P : HeightOneSpectrum (𝓞 L)} (hv : IsPlaceOver A v) (hw : IsPlaceOver A w) (hP : IsPlaceOver A P)
    (hD : Dec (F := F) A ≤ (res F Ω K).range) :
    w.asIdeal.ramificationIdx (𝓞 F) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois F K L
  haveI : w.asIdeal.LiesOver v.asIdeal := liesOver_of_isPlaceOver hv hw
  haveI : P.asIdeal.LiesOver w.asIdeal := liesOver_of_isPlaceOver hw hP
  haveI : P.asIdeal.LiesOver v.asIdeal := liesOver_of_isPlaceOver hv hP
  have hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) P.asIdeal) =
      Nat.card (MulAction.stabilizer (L ≃ₐ[F] L) P.asIdeal) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun σ ↦ ⟨(σ : L ≃ₐ[K] L).restrictScalars F, σ.2⟩) ⟨?_, ?_⟩)
    · intro σ τ h
      exact Subtype.ext (AlgEquiv.restrictScalars_injective F (congrArg Subtype.val h))
    · rintro ⟨τ, hτ⟩
      have hfix := fixes_of_mem_stabilizer (K := K) hP hD τ hτ
      exact ⟨⟨{ τ.toRingEquiv with commutes' := hfix }, hτ⟩, Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)⟩
  have h1 := GroundTheory.Global.card_decompositionGroup v P
  have h2 := GroundTheory.Global.card_decompositionGroup w P
  rw [hcard] at h2
  rw [Ideal.ramificationIdx_tower (R := 𝓞 F) w.asIdeal P.asIdeal,
    Ideal.inertiaDeg_tower (R := 𝓞 F) w.asIdeal P.asIdeal, h2] at h1
  have hpos : 0 < P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) := by
    rw [← h2]
    exact Nat.card_pos
  have key : w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) *
      (P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K)) =
      1 * (P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K)) := by
    rw [one_mul]
    conv_rhs => rw [h1]
    ring
  exact mul_eq_one.1 (Nat.eq_of_mul_eq_mul_right hpos key)

end GlobalTheory.PlaceIsoDec

namespace GlobalTheory.PlaceIsoDec

open GroundTheory.Global.SemiLocal in

theorem exists_placeIso_of_dec_le_range : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → Dec (F := F) A ≤ (res F Ω K).range → ∃ (w : HeightOneSpectrum (𝓞 K)) (_ : IsPlaceOver A w) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ v A hv hD
  obtain ⟨w, hw⟩ := GlobalTheory.PlaceIsoDec.exists_isPlaceOver_mid (L := K) hv
  haveI : Module.Finite F K := Module.Finite.of_restrictScalars_finite ℚ F K
  haveI : NumberField (IntermediateField.normalClosure F K Ω) := NumberField.of_module_finite F (IntermediateField.normalClosure F K Ω)
  haveI : IsAlgClosure (IntermediateField.normalClosure F K Ω) Ω :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) (IntermediateField.normalClosure F K Ω)⟩
  obtain ⟨P, hP⟩ := GlobalTheory.PlaceIsoDec.exists_isPlaceOver_mid (L := IntermediateField.normalClosure F K Ω) hv
  obtain ⟨he, hf⟩ := GlobalTheory.PlaceIsoDec.ramificationIdx_eq_one_and_inertiaDeg_eq_one (K := K) hv hw hP hD
  haveI : w.asIdeal.LiesOver v.asIdeal := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hv hw
  have hrank : Module.finrank (v.adicCompletion F) (w.adicCompletion K) = 1 := by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg K v w, he, hf]
  have hsurj : Function.Surjective (completionMap v w) := by
    intro y
    have hy : y ∈ (⊥ : Subalgebra (v.adicCompletion F) (w.adicCompletion K)) := by
      rw [Subalgebra.bot_eq_top_of_finrank_eq_one hrank]
      trivial
    obtain ⟨x, hx⟩ := Algebra.mem_bot.1 hy
    exact ⟨x, hx⟩
  refine ⟨w, hw, RingEquiv.ofBijective (completionMap v w) ⟨(completionMap v w).injective, hsurj⟩,
    ⟨fun _ => Iff.rfl, fun x => IsScalarTower.algebraMap_apply F K Ω x, continuous_completionMap v w, fun x => ?_⟩⟩
  exact (completionMap_algebraMap v w x).trans (IsScalarTower.algebraMap_apply F K _ x)

end GlobalTheory.PlaceIsoDec
