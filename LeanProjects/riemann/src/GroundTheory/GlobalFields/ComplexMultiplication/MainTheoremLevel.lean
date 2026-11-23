import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremAssembly
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremModels
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremFields
import GroundTheory.GlobalFields.ComplexMultiplication.BadPrimesFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IsDedekindDomain WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian
  IntermediateField
open GroundTheory.LocalField (maximalAbelianExtension)
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

omit [NumberField K] [IsTotallyComplex K] in
theorem exists_isogeny_homConstSet_congr {L : Type} [Field L] [Algebra L ℂ]
    {A A' B B' : WeierstrassCurve L} [A.IsElliptic] [A'.IsElliptic] [B.IsElliptic] [B'.IsElliptic]
    (eA : A = A') (eB : B = B') {S : Set ℂ}
    (h : ∃ φ : Isogeny A B, (homConstSet (A.baseChange ℂ) (B.baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) '' S) :
    ∃ φ : Isogeny A' B', (homConstSet (A'.baseChange ℂ) (B'.baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) '' S := by
  subst eA eB
  exact h

omit [NumberField K] [IsTotallyComplex K] [Algebra K ℂ] in
theorem nonempty_isogEnd_congr {L : Type} [Field L] [Algebra L ℂ] {B B' : WeierstrassCurve L}
    [B.IsElliptic] [B'.IsElliptic] (e : B = B') (h : Nonempty (isogEnd (B.baseChange ℂ) ≃+* 𝓞 K)) :
    Nonempty (isogEnd (B'.baseChange ℂ) ≃+* 𝓞 K) := by
  subst e
  exact h

include hK in

theorem exists_uniformization_level (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {E : WeierstrassCurve ℂ} [E.IsElliptic]
    {f : ℂ →+ E.toAffine.Point} (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f)
    {m : ℕ} (hm : m ≠ 0) :
    ∃ f' : ℂ →+ (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticUniformization (idealLattice (algebraMap K ℂ) ↑(s⁻¹ • 𝔞)) f' ∧
      ∀ t y : K, (m : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) →
        IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk y →
          f' (algebraMap K ℂ y) = pointMapRing (σ : ℂ →+* ℂ) E (f (algebraMap K ℂ t)) := by
  classical

  have hL₁ := lattice_idealPeriodPair (algebraMap K ℂ) hK 𝔞
  have hL₁end := latticeEnd_idealPeriodPair (algebraMap K ℂ) hK 𝔞
  have hf₁ := hf
  rw [← hL₁] at hf₁
  obtain ⟨C₁, hC₁, -⟩ := exists_vcPoint_of_isAnalyticUniformization hf₁
  have hEend : Nonempty (isogEnd E ≃+* 𝓞 K) :=
    ⟨(vcEndEquiv C₁ hC₁).symm.trans (CMCurve.ofLattice (algebraMap K ℂ) _ hL₁end).endIso.some⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ELL K, x₀ = (⟨E, hEend⟩ : CMCurve K).toEll := ⟨_, rfl⟩
  have hx₀ell : x₀ = ellOf (algebraMap K ℂ) _ hL₁end := by
    rw [hx₀]
    exact (CMCurve.toEll_eq_iff _ _).2 ⟨C₁⁻¹, inv_smul_eq_of_smul_eq C₁ hC₁⟩
  have hjE : ELL.j x₀ = E.j := by
    rw [hx₀]
    exact ELL.j_toEll _

  have hJfin : FiniteDimensional K K⟮ELL.j x₀⟯ :=
    adjoin.finiteDimensional (ELL.isAlgebraic_j_over hK x₀).isIntegral
  set aJ : K⟮ELL.j x₀⟯ := ⟨ELL.j x₀, mem_adjoin_simple_self K _⟩
  obtain ⟨M₁, hM₁fin, -, htorsJ⟩ := exists_le_forall_torsion_mem K⟮ELL.j x₀⟯ (shortModel aJ) hm

  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (12 : ℕ))
  have hζ : IsPrimitiveRoot ζ 12 := Complex.isPrimitiveRoot_exp 12 (by norm_num)
  have hM₃fin : FiniteDimensional K K⟮ζ⟯ :=
    adjoin.finiteDimensional ((hζ.isIntegral (by norm_num)).tower_top)

  obtain ⟨L, hML, hLfin, hLgal, hL, hE, hiso⟩ := exists_shortModels_isogenous hK
    (M₁ ⊔ (Modulus.ofNat (K := K) m hm).rayClassField ℂ ⊔ K⟮ζ⟯)
  have : NumberField L := NumberField.of_module_finite K L
  have hM₁L : M₁ ≤ L := le_trans (le_trans le_sup_left le_sup_left) hML
  have hM₂L : (Modulus.ofNat (K := K) m hm).rayClassField ℂ ≤ L :=
    le_trans (le_trans le_sup_right le_sup_left) hML
  have hζL : ζ ∈ L := hML (le_sup_right (a := M₁ ⊔ _) (mem_adjoin_simple_self K ζ))
  have hζL' : IsPrimitiveRoot (⟨ζ, hζL⟩ : L) 12 :=
    (IsPrimitiveRoot.map_iff_of_injective (algebraMap L ℂ).injective).1 hζ

  obtain ⟨A, hAdef⟩ : ∃ A : WeierstrassCurve L, A = shortModel (⟨ELL.j x₀, hL x₀⟩ : L) := ⟨_, rfl⟩
  have : A.IsElliptic := by rw [hAdef]; infer_instance
  have : A.IsShortNF := by rw [hAdef]; infer_instance
  have hAℂ : A.baseChange ℂ = (shortModel aJ).baseChange ℂ := by
    rw [hAdef, WeierstrassCurve.baseChange, WeierstrassCurve.baseChange, shortModel_map, shortModel_map]
    rfl
  obtain ⟨V₀, hV₀⟩ := exists_variableChange_of_j_eq E (A.baseChange ℂ) (by
    rw [j_congr hAℂ]
    show E.j = ((shortModel aJ).map (algebraMap _ ℂ)).j
    rw [map_j, shortModel_j, ← hjE]
    rfl)
  have htors : ∀ (a b : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular a b),
      m • (Point.some a b h : (A.baseChange ℂ).toAffine.Point) = 0 →
        a ∈ (algebraMap L ℂ).range ∧ b ∈ (algebraMap L ℂ).range := by
    intro a b h hP
    have h' : ((shortModel aJ).baseChange ℂ).toAffine.Nonsingular a b := hAℂ ▸ h
    have hP' : m • (Point.some a b h' : ((shortModel aJ).baseChange ℂ).toAffine.Point) = 0 :=
      nsmul_some_congr hAℂ h h' hP
    obtain ⟨ha, hb⟩ := htorsJ a b h' hP'
    exact ⟨⟨⟨a, hM₁L ha⟩, rfl⟩, ⟨⟨b, hM₁L hb⟩, rfl⟩⟩

  have hτσ : ∀ a : L, σ (algebraMap L ℂ a) = algebraMap L ℂ (σ.restrictNormal L a) :=
    fun a ↦ (AlgEquiv.restrictNormal_commutes σ L a).symm

  obtain ⟨S₀, hS₀, hS₀p⟩ := frobenius_at_primes_of_degree_one hK hL
    (fun x ↦ shortModel (⟨ELL.j x, hL x⟩ : L)) hE hiso
  have hgood : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ W : WeierstrassCurve (localizationAt L w), W.IsElliptic ∧
        W.map (algebraMap (localizationAt L w) L) = A ∧ (W.a₄ = 0 ∨ IsUnit W.a₄) ∧
          (W.a₆ = 0 ∨ IsUnit W.a₆) := by
    have h4 : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
        A.a₄ = 0 ∨ ∃ h : A.a₄ ∈ localizationAt L w, IsUnit (⟨A.a₄, h⟩ : localizationAt L w) := by
      by_cases h0 : A.a₄ = 0
      · exact Filter.Eventually.of_forall fun _ ↦ Or.inl h0
      · exact (eventually_isUnit_localizationAt h0).mono fun _ h ↦ Or.inr h
    have h6 : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
        A.a₆ = 0 ∨ ∃ h : A.a₆ ∈ localizationAt L w, IsUnit (⟨A.a₆, h⟩ : localizationAt L w) := by
      by_cases h0 : A.a₆ = 0
      · exact Filter.Eventually.of_forall fun _ ↦ Or.inl h0
      · exact (eventually_isUnit_localizationAt h0).mono fun _ h ↦ Or.inr h
    filter_upwards [eventually_exists_model A, h4, h6] with w ⟨W, hW, hWA⟩ h4w h6w
    have e4 : algebraMap (localizationAt L w) L W.a₄ = A.a₄ := by rw [← hWA]; rfl
    have e6 : algebraMap (localizationAt L w) L W.a₆ = A.a₆ := by rw [← hWA]; rfl
    refine ⟨W, hW, hWA, ?_, ?_⟩
    · rcases h4w with h0 | ⟨h, hu⟩
      · left
        exact Subtype.ext (e4.trans h0)
      · right
        have : W.a₄ = ⟨A.a₄, h⟩ := Subtype.ext e4
        rwa [this]
    · rcases h6w with h0 | ⟨h, hu⟩
      · left
        exact Subtype.ext (e6.trans h0)
      · right
        have : W.a₆ = ⟨A.a₆, h⟩ := Subtype.ext e6
        rwa [this]
  obtain ⟨S₁, hS₁, hS₁p⟩ := exists_finite_forall_liesOver (K := K) hgood
  have h6m : ((6 * m : ℕ) : 𝓞 K) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero]
    omega
  have hS : (S₀ ∪ S₁ ∪ {v : HeightOneSpectrum (𝓞 K) | ((6 * m : ℕ) : 𝓞 K) ∈ v.asIdeal}).Finite :=
    (hS₀.union hS₁).union (finite_setOf_mem_asIdeal h6m)

  obtain ⟨𝔭, h𝔭S, h𝔭1, 𝔓, hlies, -, hfrob⟩ := exists_isArithFrobAt L (σ.restrictNormal L) hS
  have : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := hlies
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at h𝔭S
  obtain ⟨⟨h𝔭S₀, h𝔭S₁⟩, h𝔭6m⟩ := h𝔭S
  have hv := absNorm_prime_of_mem_degreeOnePrimes h𝔭1
  have hm𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal := fun h ↦ h𝔭6m (by
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ h)
  have hnorm : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal := Ideal.absNorm_mem _
  have h5 : 5 ≤ Ideal.absNorm 𝔭.asIdeal := by
    refine hv.five_le_of_ne_two_of_ne_three (fun h2 ↦ h𝔭6m ?_) (fun h3 ↦ h𝔭6m ?_)
    · rw [h2] at hnorm
      rw [show ((6 * m : ℕ) : 𝓞 K) = ((2 : ℕ) : 𝓞 K) * ((3 * m : ℕ) : 𝓞 K) by push_cast; ring]
      exact Ideal.mul_mem_right _ _ hnorm
    · rw [h3] at hnorm
      rw [show ((6 * m : ℕ) : 𝓞 K) = ((3 : ℕ) : 𝓞 K) * ((2 * m : ℕ) : 𝓞 K) by push_cast; ring]
      exact Ideal.mul_mem_right _ _ hnorm

  obtain ⟨-, hcls, -⟩ := hS₀p 𝔭 h𝔭S₀ h𝔭1 𝔓
  obtain ⟨-, hτj⟩ := hcls (σ.restrictNormal L) hfrob
  have hAτ : A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L) = shortModel (⟨ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀), hL _⟩ : L) := by
    rw [hAdef, shortModel_map]
    congr 1
    exact hτj x₀

  have hφex : ∃ φ : Isogeny A (A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L)),
      (homConstSet (A.baseChange ℂ) ((A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L)).baseChange ℂ) :
        Set ℂ) = (algebraMap L ℂ (invConst φ) * ·) ''
          idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    obtain ⟨φ, hφ, -⟩ := exists_isogeny_primeClass_smul hK (fun x ↦ shortModel (⟨ELL.j x, hL x⟩ : L))
      hE hiso 𝔭 x₀
    exact exists_isogeny_homConstSet_congr hAdef.symm hAτ.symm ⟨φ, hφ⟩
  obtain ⟨φ, hφ⟩ := hφex
  have hEA : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K) :=
    nonempty_isogEnd_congr hAdef.symm (hE x₀).1
  have hEA' : Nonempty (isogEnd ((A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L)).baseChange ℂ) ≃+*
      𝓞 K) :=
    nonempty_isogEnd_congr hAτ.symm (hE _).1

  obtain ⟨W, hW, hWA, ha₄, ha₆⟩ := hS₁p 𝔭 h𝔭S₁ 𝔓 hlies
  have : W.IsShortNF := by
    have hinj : Function.Injective (algebraMap (localizationAt L 𝔓) L) := Subtype.val_injective
    refine ⟨hinj ?_, hinj ?_, hinj ?_⟩ <;> rw [map_zero]
    · rw [← a₁_of_isShortNF A, ← hWA]; rfl
    · rw [← a₂_of_isShortNF A, ← hWA]; rfl
    · rw [← a₃_of_isShortNF A, ← hWA]; rfl

  obtain ⟨D, hD, hDφ⟩ := exists_vcPoint_pointHomOver_eq hK 𝔭 hv h5 𝔓 hfrob hEA hEA' φ hφ hWA ha₄ ha₆
    hζL' hm𝔭

  obtain ⟨x, hx⟩ := exists_diagonal_of_isArithFrobAt m hm σ s hs 𝔭 hm𝔭 L hM₂L 𝔓 hfrob

  have hL₂ := lattice_idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞)
  have hL₂end := latticeEnd_idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞)
  have hsmul := classGroup_smul_ellOf (algebraMap K ℂ) hK _ _ hL₁end hL₂end (primeIdealUnit 𝔭)
    (by rw [hL₂, hL₁, Units.val_mul, idealLattice_mul])
  have hcl : primeClass 𝔭 = ClassGroup.mk K (primeIdealUnit 𝔭) := by
    rw [primeClass, ← classGroup_mk_primeUnit]
    rfl
  have hyL₂ : (ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀ =
      ellOf (algebraMap K ℂ) _ hL₂end := by
    rw [hcl, hx₀ell, hsmul]
  have hjV' : (weierstrassCurve (idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞))).j =
      ((A.map ((σ.restrictNormal L : L ≃ₐ[K] L) : L →+* L)).baseChange ℂ).j := by
    rw [j_congr (congrArg (fun B : WeierstrassCurve L ↦ B.baseChange ℂ) hAτ)]
    show _ = ((shortModel (⟨ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀), hL _⟩ : L)).map (algebraMap L ℂ)).j
    rw [map_j, shortModel_j]
    show _ = ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (primeClass 𝔭) x₀)
    rw [hyL₂, ellOf, ELL.j_toEll]
    exact j_congr rfl
  obtain ⟨V', hV'⟩ := exists_variableChange_of_j_eq _ _ hjV'
  exact exists_uniformization_of_data hK σ s 𝔞 hf (σ.restrictNormal L) hτσ V₀ hV₀ htors 𝔭 x
    (hx 𝔞).1 (hx 𝔞).2 φ hφ D hD hDφ V' hV'

end

end Elliptic
end GroundTheory.Global
