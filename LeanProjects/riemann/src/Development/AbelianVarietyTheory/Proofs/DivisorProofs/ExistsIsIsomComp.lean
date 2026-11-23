import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonical
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.EmbConj

open GlobalTheory.PadicComplexHost

noncomputable def stdInt (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* 𝓞_ℂ_[p] :=
  ((algebraMap (PadicAlgCl p) ℂ_[p]).comp (algebraMap ℤ_[p] (PadicAlgCl p))).codRestrict
    (𝓞_ℂ_[p]).toSubring (fun x => by
      change _ ∈ 𝓞_ℂ_[p]
      rw [mem_iff_norm, RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends,
        IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), norm_algebraMap']
      exact x.norm_le_one)

theorem coe_stdInt (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) :
    ((stdInt p a : 𝓞_ℂ_[p]) : ℂ_[p]) =
      algebraMap (PadicAlgCl p) ℂ_[p] (algebraMap ℤ_[p] (PadicAlgCl p) a) :=
  rfl

variable {p : ℕ} [Fact p.Prime]

theorem apply_algebraMap {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (t : Λ →+* 𝓞_ℂ_[p])
    (a : ℤ_[p]) : ((t (algebraMap ℤ_[p] Λ a) : 𝓞_ℂ_[p]) : ℂ_[p]) =
      algebraMap (PadicAlgCl p) ℂ_[p] (algebraMap ℤ_[p] (PadicAlgCl p) a) := by
  haveI := isHausdorff p
  have h := GlobalTheory.padicInt_ringHom_ext p 𝓞_ℂ_[p] (t.comp (algebraMap ℤ_[p] Λ)) (stdInt p)
  rw [← coe_stdInt, ← h, RingHom.comp_apply]

theorem isAlgebraic_coe {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ]
    (t : Λ →+* 𝓞_ℂ_[p]) (x : Λ) : IsAlgebraic ℚ_[p] ((t x : 𝓞_ℂ_[p]) : ℂ_[p]) := by
  obtain ⟨f, hf, hfx⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[p]) x
  let g : Λ →+* ℂ_[p] := (𝓞_ℂ_[p]).subtype.comp t
  have hstd : g.comp (algebraMap ℤ_[p] Λ) =
      (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p]) := by
    ext a
    refine (apply_algebraMap t a).trans ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p),
      IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p]]
  refine ⟨f.map (algebraMap ℤ_[p] ℚ_[p]), (hf.map _).ne_zero, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hstd]
  change Polynomial.eval₂ (g.comp (algebraMap ℤ_[p] Λ)) (g x) f = 0
  rw [← Polynomial.hom_eval₂, hfx, map_zero]

theorem exists_lift {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ]
    (t : Λ →+* 𝓞_ℂ_[p]) : ∃ φ : Λ →+* PadicAlgCl p,
      (∀ x, algebraMap (PadicAlgCl p) ℂ_[p] (φ x) = ((t x : 𝓞_ℂ_[p]) : ℂ_[p])) ∧
      φ.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p) := by
  have hex : ∀ x : Λ, ∃ y : PadicAlgCl p,
      algebraMap (PadicAlgCl p) ℂ_[p] y = ((t x : 𝓞_ℂ_[p]) : ℂ_[p]) := fun x => by
    have h1 : IsIntegral (PadicAlgCl p) ((t x : 𝓞_ℂ_[p]) : ℂ_[p]) :=
      ((isAlgebraic_coe t x).tower_top (PadicAlgCl p)).isIntegral
    exact minpoly.mem_range_of_degree_eq_one _ _
      (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible h1))
  choose f hf using hex
  have hinj : Function.Injective (algebraMap (PadicAlgCl p) ℂ_[p]) :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf, ?_⟩
  · apply hinj; rw [hf]; simp
  · intro x y; apply hinj; rw [map_mul, hf, hf, hf]; simp
  · apply hinj; rw [hf]; simp
  · intro x y; apply hinj; rw [map_add, hf, hf, hf]; simp
  · ext a
    apply hinj
    exact (hf _).trans (apply_algebraMap t a)

theorem injective_of_comp {Λ : Type} [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ]
    [Module.Finite ℤ_[p] Λ] (φ : Λ →+* PadicAlgCl p)
    (h : φ.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p)) :
    Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
  rw [RingHom.comap_ker, h, ← RingHom.injective_iff_ker_eq_bot,
    IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p), RingHom.coe_comp]
  exact (algebraMap ℚ_[p] (PadicAlgCl p)).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

theorem exists_algEquiv {Λ : Type} [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ]
    [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (φ₀ φ₁ : Λ →+* PadicAlgCl p)
    (h₀ : φ₀.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p))
    (h₁ : φ₁.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p)) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ x, σ (φ₀ x) = φ₁ x := by
  have tf : ∀ φ : Λ →+* PadicAlgCl p, Function.Injective φ →
      letI := φ.toAlgebra
      Module.IsTorsionFree Λ (PadicAlgCl p) := fun φ hφ => by
    letI := φ.toAlgebra
    haveI : FaithfulSMul Λ (PadicAlgCl p) := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
    infer_instance
  have alg : letI := φ₀.toAlgebra
      Algebra.IsAlgebraic Λ (PadicAlgCl p) := by
    letI := φ₀.toAlgebra
    haveI : IsScalarTower ℤ_[p] Λ (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq' h₀.symm
    haveI : Algebra.IsAlgebraic ℤ_[p] (PadicAlgCl p) := ⟨fun x =>
      (IsFractionRing.isAlgebraic_iff ℤ_[p] ℚ_[p] (PadicAlgCl p)).2
        (Algebra.IsAlgebraic.isAlgebraic x)⟩
    exact Algebra.IsAlgebraic.extendScalars (R := ℤ_[p]) (FaithfulSMul.algebraMap_injective _ _)
  obtain ⟨g, hg⟩ : ∃ g : PadicAlgCl p →+* PadicAlgCl p, ∀ x, g (φ₀ x) = φ₁ x := by
    let f := @IsAlgClosed.lift (PadicAlgCl p) _ _ Λ _ _ (PadicAlgCl p) _ _ φ₀.toAlgebra
      φ₁.toAlgebra (tf φ₀ (injective_of_comp φ₀ h₀)) (tf φ₁ (injective_of_comp φ₁ h₁)) alg
    exact ⟨@AlgHom.toRingHom _ _ _ _ _ _ φ₀.toAlgebra φ₁.toAlgebra f,
      fun x => @AlgHom.commutes _ _ _ _ _ _ φ₀.toAlgebra φ₁.toAlgebra f x⟩
  have hq : g.comp (algebraMap ℚ_[p] (PadicAlgCl p)) = algebraMap ℚ_[p] (PadicAlgCl p) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p)]
    ext a
    exact (congrArg g (RingHom.congr_fun h₀ a).symm).trans
      ((hg _).trans (RingHom.congr_fun h₁ a))
  let g' : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p := { g with commutes' := RingHom.congr_fun hq }
  exact ⟨AlgEquiv.ofBijective g' (Algebra.IsAlgebraic.algHom_bijective g'), hg⟩

theorem exists_extension (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ γ : ℂ_[p] ≃+* ℂ_[p], (∀ y : PadicAlgCl p, γ (y : ℂ_[p]) = ((σ y : PadicAlgCl p) : ℂ_[p])) ∧
      ∀ z, ‖γ z‖ = ‖z‖ := by
  have hn : ∀ (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p), ‖g x‖ = ‖x‖ :=
    fun g x => (spectralNorm_eq_of_equiv g x).symm
  have hi : ∀ g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      Isometry (g : PadicAlgCl p → PadicAlgCl p) :=
    fun g => AddMonoidHomClass.isometry_of_norm g (hn g)
  let γ : ℂ_[p] ≃+* ℂ_[p] := UniformSpace.Completion.mapRingEquiv σ.toRingEquiv
    (hi σ).continuous (hi σ.symm).continuous
  have hc : ∀ y : PadicAlgCl p, γ (y : ℂ_[p]) = ((σ y : PadicAlgCl p) : ℂ_[p]) :=
    fun y => UniformSpace.Completion.map_coe (hi σ).uniformContinuous y
  have hcont : Continuous γ := UniformSpace.Completion.continuous_map
  refine ⟨γ, hc, fun z => ?_⟩
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hcont.norm continuous_norm
  | ih x => rw [hc, PadicComplex.norm_extends, PadicComplex.norm_extends, hn]

theorem exists_isIsom_comp : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ]
    [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (t₀ t : Λ →+* 𝓞_ℂ_[p]),
    ∃ γ : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p], IsIsom ℂ_[p] (Valued.v : Valuation ℂ_[p] NNReal) γ ∧
      t = (γ : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]).comp t₀ := by
  intro p _ Λ _ _ _ _ _ t₀ t
  obtain ⟨φ₀, e₀, h₀⟩ := exists_lift t₀
  obtain ⟨φ₁, e₁, h₁⟩ := exists_lift t
  obtain ⟨σ, hσ⟩ := exists_algEquiv φ₀ φ₁ h₀ h₁
  obtain ⟨γC, hc, hn⟩ := exists_extension σ
  have hn' : ∀ z, ‖γC.symm z‖ = ‖z‖ := fun z => by rw [← hn, γC.apply_symm_apply]
  let γ : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p] :=
    { toFun := fun x => ⟨γC x, (mem_iff_norm p _).2 ((hn _).trans_le ((mem_iff_norm p _).1 x.2))⟩
      invFun := fun x =>
        ⟨γC.symm x, (mem_iff_norm p _).2 ((hn' _).trans_le ((mem_iff_norm p _).1 x.2))⟩
      left_inv := fun x => Subtype.ext (γC.symm_apply_apply _)
      right_inv := fun x => Subtype.ext (γC.apply_symm_apply _)
      map_mul' := fun x y => Subtype.ext (map_mul γC _ _)
      map_add' := fun x y => Subtype.ext (map_add γC _ _) }
  refine ⟨γ, ⟨γC, fun x => rfl, fun z => ?_⟩, ?_⟩
  · apply NNReal.coe_injective
    rw [valuation_coe_eq_norm, valuation_coe_eq_norm, hn]
  · ext x
    change ((t x : 𝓞_ℂ_[p]) : ℂ_[p]) = γC ((t₀ x : 𝓞_ℂ_[p]) : ℂ_[p])
    rw [← e₀, ← e₁, ← PadicComplex.coe_eq, ← PadicComplex.coe_eq, hc, hσ]

end GlobalTheory.EmbConj
