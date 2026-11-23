import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeCupProps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerGeneratorOfChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitMulPowOfKummerVanishesOnInertiaCurve
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeEqZeroOfInert
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacter

open GlobalTheory.K4 GlobalTheory.KEdge GlobalTheory.NeedB Polynomial

namespace GlobalTheory.K4.TopSpec

variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]

open Polynomial in
variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω] in
theorem _root_.GlobalTheory.K4.TopSpec.res_mem_geo (g : Ω ≃ₐ[K] Ω) :
    AlgEquiv.restrictScalarsHom F g ∈ _root_.GlobalTheory.K4.geo F K Ω := by
  rw [_root_.GlobalTheory.K4.TopW.mem_geo]
  intro z
  exact g.commutes z

open Polynomial in
variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω] in
theorem _root_.GlobalTheory.K4.TopSpec.exists_res {g : Ω ≃ₐ[F] Ω}
    (hg : g ∈ _root_.GlobalTheory.K4.geo F K Ω) :
    ∃ g' : Ω ≃ₐ[K] Ω, AlgEquiv.restrictScalarsHom F g' = g := by
  rw [_root_.GlobalTheory.K4.TopW.mem_geo] at hg
  refine ⟨{ g.toRingEquiv with commutes' := hg }, ?_⟩
  ext y
  rfl

open Polynomial in
variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω] in
theorem _root_.GlobalTheory.K4.TopSpec.continuous_res [Algebra.IsAlgebraic K Ω] :
    Continuous (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[F] Ω)) := by
  classical
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro s hs
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hEs⟩ := hs
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  let b := Module.finBasis F E
  refine ⟨IntermediateField.adjoin K (Set.range fun i => (b i : Ω)), ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  · intro g hg
    apply hEs
    have hfix : ∀ i, g (b i : Ω) = b i := fun i =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _
        (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have key : ∀ z : E, AlgEquiv.restrictScalarsHom F g (z : Ω) = z := by
      intro z
      induction (b.mem_span z) using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨i, rfl⟩ := hu
        exact hfix i
      | zero => simp
      | add u v _ _ hu hv => rw [IntermediateField.coe_add, map_add, hu, hv]
      | smul a u _ hu => rw [IntermediateField.coe_smul, map_smul, hu]
    exact key ⟨y, hy⟩

end GlobalTheory.K4.TopSpec

open Polynomial in

theorem _root_.GlobalTheory.K4.isTopW_topW : ∀ (k K Ω F : Type) [Field k]
    [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] [Field F] [Algebra F K] [Algebra F Ω] [IsScalarTower F K Ω] [Normal F K]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[F] Ω, g ζ = ζ) →
    (∀ τ : K ≃ₐ[F] K, ∀ x ∈ FunctionField.ringOfIntegers k K,
      τ x ∈ FunctionField.ringOfIntegers k K) →
    ∀ (a b : F) (α β : Ω), a ≠ 0 → b ≠ 0 → algebraMap F K a ∈ FunctionField.ringOfIntegers k K →
      (algebraMap F K a)⁻¹ ∈ FunctionField.ringOfIntegers k K →
      algebraMap F K b ∈ FunctionField.ringOfIntegers k K →
      (algebraMap F K b)⁻¹ ∈ FunctionField.ringOfIntegers k K →
      α ^ N = algebraMap F Ω a → β ^ N = algebraMap F Ω b →
    ∀ (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)),
      (∀ g, (x g).toAdd = _root_.GlobalTheory.NeedB.kum (N := N) ζ α g) →
      (∀ g, (y g).toAdd = _root_.GlobalTheory.NeedB.kum (N := N) ζ β g) →
    ∀ η : (Ω ≃ₐ[F] Ω) → ZMod N,
      _root_.GlobalTheory.KEdge.CobOn (_root_.GlobalTheory.K4.geo F K Ω) x y η →
      IsLocallyConstant (fun g : _root_.GlobalTheory.K4.geo F K Ω => η g) →
      (∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω),
        _root_.GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
        (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) →
        g ∈ _root_.GlobalTheory.K4.geo F K Ω → η g = 0) →
    ∀ σ : Ω ≃ₐ[F] Ω, _root_.GlobalTheory.K4.IsTopW (K := K) ζ x y η σ
      (_root_.GlobalTheory.K4.topW (K := K) ζ x y η σ) := by
  intro k K Ω F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ hfix _ a b α β ha hb _ _ _ _ hα hβ
    x y hx hy η hcob hη _ σ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : CharZero (RatFunc k) :=
    charZero_of_injective_algebraMap (algebraMap k (RatFunc k)).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.trans F K Ω
  set H := _root_.GlobalTheory.K4.geo F K Ω with hH
  haveI : H.Normal := ⟨fun h hh g => _root_.GlobalTheory.K4.TopW.conj_mem_geo g hh⟩
  obtain ⟨hhom, -, -⟩ := _root_.GlobalTheory.KEdge.edge_cup_props _ N H x y η hcob
  have hres := _root_.GlobalTheory.K4.TopSpec.continuous_res (F := F) (K := K) (Ω := Ω)
  have hmem : ∀ g : Ω ≃ₐ[K] Ω, AlgEquiv.restrictScalarsHom F g ∈ H :=
    _root_.GlobalTheory.K4.TopSpec.res_mem_geo
  have hne : ∀ {γ : Ω} {c : F}, c ≠ 0 → γ ^ N = algebraMap F Ω c → γ ≠ 0 := by
    intro γ c hc hγ h0
    rw [h0, zero_pow hN.ne'] at hγ
    exact hc ((algebraMap F Ω).injective (hγ.symm.trans (map_zero _).symm))
  have hkum : ∀ {γ : Ω} {c : F}, c ≠ 0 → γ ^ N = algebraMap F Ω c →
      IsLocallyConstant (_root_.GlobalTheory.NeedB.kum (K := F) (N := N) ζ γ) :=
    fun hc hγ => (_root_.GlobalTheory.NeedB.KumLemma.kummer_character_main F Ω N ζ _ hN hζ hfix
      (hne hc hγ) ⟨_, hγ.symm⟩).1
  have hx_lc : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω =>
      Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g)) := by
    have hfun : (fun g : Ω ≃ₐ[K] Ω => Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g))) =
        _root_.GlobalTheory.NeedB.kum ζ α ∘ AlgEquiv.restrictScalarsHom F := funext fun g => hx _
    rw [hfun]
    exact (hkum ha hα).comp_continuous hres
  have hy_lc : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω =>
      Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g)) := by
    have hfun : (fun g : Ω ≃ₐ[K] Ω => Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g))) =
        _root_.GlobalTheory.NeedB.kum ζ β ∘ AlgEquiv.restrictScalarsHom F := funext fun g => hy _
    rw [hfun]
    exact (hkum hb hβ).comp_continuous hres
  have hη₁ : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => η (AlgEquiv.restrictScalarsHom F g) :=
    hη.comp_continuous (f := fun g : Ω ≃ₐ[K] Ω => (⟨AlgEquiv.restrictScalarsHom F g, hmem g⟩ : H))
      (hres.subtype_mk _)
  have hη₂ : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => η (σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹) :=
    hη.comp_continuous (f := fun g : Ω ≃ₐ[K] Ω =>
      (⟨σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹,
        _root_.GlobalTheory.K4.TopW.conj_mem_geo σ (hmem g)⟩ : H))
      (((continuous_const.mul hres).mul continuous_const).subtype_mk _)
  let χ : (Ω ≃ₐ[K] Ω) → ZMod N := fun g =>
    _root_.GlobalTheory.KEdge.edge x y η σ (AlgEquiv.restrictScalarsHom F g)
  have hlc : IsLocallyConstant χ := by
    have hfun : χ = fun g => η (σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹) -
        η (AlgEquiv.restrictScalarsHom F g) -
        Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g)) * Multiplicative.toAdd (y σ) +
        Multiplicative.toAdd (x σ) * Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g)) :=
      rfl
    rw [hfun]
    exact ((hη₂.comp₂ hη₁ (· - ·)).comp₂ (hx_lc.comp (· * Multiplicative.toAdd (y σ))) (· - ·)).comp₂
      (hy_lc.comp (Multiplicative.toAdd (x σ) * ·)) (· + ·)
  have hadd : ∀ g ∈ (⊥ : IntermediateField K Ω).fixingSubgroup,
      ∀ h ∈ (⊥ : IntermediateField K Ω).fixingSubgroup, χ (g * h) = χ g + χ h := by
    intro g _ h _
    simp only [χ, map_mul]
    exact hhom σ _ (hmem g) _ (hmem h)
  obtain ⟨θ, hθ0, hθN, hθ⟩ :=
    _root_.GlobalTheory.kummer_generator_of_char K Ω N ζ hN hζ (fun g => hfix (AlgEquiv.restrictScalarsHom F g)) ⊥ χ hlc hadd
  obtain ⟨w, hw⟩ := IntermediateField.mem_bot.mp hθN
  apply _root_.GlobalTheory.K4.TopW.isTopW_topW_of_exists
  refine ⟨w, ?_, θ, hw.symm, ?_⟩
  · rintro rfl
    rw [map_zero] at hw
    exact hθ0 ((pow_eq_zero_iff hN.ne').mp hw.symm)
  · intro g hg
    obtain ⟨g', rfl⟩ := _root_.GlobalTheory.K4.TopSpec.exists_res hg
    apply _root_.GlobalTheory.NeedB.kum_eq_of hζ hθ0
    exact hθ g' (by rw [IntermediateField.fixingSubgroup_bot]; exact Subgroup.mem_top _)
