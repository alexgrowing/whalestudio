import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenNormClosedBallQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralNormFormNonNormCancelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralQuadraticCharEventuallyConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompAddEquivRescaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenSubgroupExhaustionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualBicharacterPairingOfSymmBilinFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulLeftEqNormSmulStatement

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.GaussNorm

open GlobalTheory.SplitWeil (cball)

section Ball

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_cball_sup (a b : Fˣ) : ∃ s : Fˣ, cball a ⊆ cball s ∧ cball b ⊆ cball s := by
  rcases le_total (ValuativeRel.valuation F (a : F)) (ValuativeRel.valuation F (b : F)) with h | h
  · exact ⟨b, fun x (hx : ValuativeRel.valuation F x ≤ _) => (le_trans hx h : ValuativeRel.valuation F x ≤ _),
      Set.Subset.rfl⟩
  · exact ⟨a, Set.Subset.rfl,
      fun x (hx : ValuativeRel.valuation F x ≤ _) => (le_trans hx h : ValuativeRel.valuation F x ≤ _)⟩

theorem exists_cball_of_isCompact {K : Set F} (hK : IsCompact K) : ∃ s : Fˣ, K ⊆ cball s := by
  have hcov : K ⊆ ⋃ s : Fˣ, cball s := by
    intro x _
    by_cases hx : x = 0
    · exact Set.mem_iUnion.mpr ⟨1, by simp [cball, hx]⟩
    · exact Set.mem_iUnion.mpr ⟨Units.mk0 x hx, by simp [cball]⟩
  have hd : Directed (· ⊆ ·) (fun s : Fˣ => cball s) := by
    intro a b
    obtain ⟨s, h1, h2⟩ := exists_cball_sup a b
    exact ⟨s, h1, h2⟩
  exact hK.elim_directed_cover _ (fun s => GlobalTheory.SplitWeil.isOpen_cball s) hcov hd

theorem mul_mem_cball_iff (t s : Fˣ) (x : F) : (t : F) * x ∈ cball s ↔ x ∈ cball (t⁻¹ * s) := by
  simp only [cball, Set.mem_setOf_eq, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  rw [le_inv_mul_iff₀ (by simp [zero_lt_iff])]

end Ball

section Polar

variable {F : Type} [Field F] [CharZero F] {E : Type} [Field E] [Algebra F E] {c : E →ₐ[F] E} {δ : E}

theorem algebraMap_norm_add (hE : IsQuad c δ) (x y : E) :
    algebraMap F E (Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y) = x * c y + y * c x := by
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  rw [map_sub, map_sub, hE.algebraMap_norm, hE.algebraMap_norm, hE.algebraMap_norm, map_add]
  ring

def polar (hE : IsQuad c δ) : E →ₗ[F] E →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y)
    (fun x x' y => hE.algebraMap_injective (by
      simp only [map_add, algebraMap_norm_add hE]; ring))
    (fun a x y => hE.algebraMap_injective (by
      show algebraMap F E (Algebra.norm F (a • x + y) - Algebra.norm F (a • x) - Algebra.norm F y) =
        algebraMap F E (a • (Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y))
      rw [algebraMap_norm_add hE, smul_eq_mul, map_mul, algebraMap_norm_add hE, Algebra.smul_def, map_mul,
        AlgHom.commutes]; ring))
    (fun x y y' => hE.algebraMap_injective (by
      simp only [map_add, algebraMap_norm_add hE]; ring))
    (fun a x y => hE.algebraMap_injective (by
      show algebraMap F E (Algebra.norm F (x + a • y) - Algebra.norm F x - Algebra.norm F (a • y)) =
        algebraMap F E (a • (Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y))
      rw [algebraMap_norm_add hE, smul_eq_mul, map_mul, algebraMap_norm_add hE, Algebra.smul_def, map_mul,
        AlgHom.commutes]; ring))

theorem polar_apply (hE : IsQuad c δ) (x y : E) :
    polar hE x y = Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y := rfl

theorem algebraMap_polar (hE : IsQuad c δ) (x y : E) : algebraMap F E (polar hE x y) = x * c y + y * c x :=
  algebraMap_norm_add hE x y

theorem polar_symm (hE : IsQuad c δ) (x y : E) : polar hE x y = polar hE y x := by
  rw [polar_apply, polar_apply, add_comm x y]; ring

theorem polar_nondeg (hE : IsQuad c δ) (y : E) (hy : ∀ x, polar hE x y = 0) : y = 0 := by
  have h1 := congrArg (algebraMap F E) (hy y)
  rw [algebraMap_polar, map_zero] at h1
  have h2 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]; exact (map_ne_zero _).mpr two_ne_zero
  have h3 : (2 : E) * (y * c y) = 0 := by rw [two_mul]; exact h1
  rcases mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left h2) with h | h
  · exact h
  · rw [← hE.invol y, h, map_zero]

theorem polar_half (hE : IsQuad c δ) (z : E) : polar hE ((2 : F)⁻¹ • z) z = Algebra.norm F z := by
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  apply hE.algebraMap_injective
  rw [algebraMap_polar, hE.algebraMap_norm, Algebra.smul_def, map_mul, AlgHom.commutes]
  have h2 : algebraMap F E (2 : F)⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  linear_combination (z * c z) * h2

theorem norm_add_eq (hE : IsQuad c δ) (x y : E) :
    Algebra.norm F (x + y) = Algebra.norm F x + Algebra.norm F y + polar hE x y := by
  rw [polar_apply]; ring

end Polar

end GlobalTheory.KSp.GaussNorm

namespace GlobalTheory.KSp

open GlobalTheory.KSp.GaussNorm GlobalTheory.SplitWeil

theorem hasGauss_norm_mul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], ∃ g : ℂ, ∀ t : Fˣ, HasGauss μ (fun z => ψ ((t : F) * Algebra.norm F z)) (g * (sgn E t * ((nabs F t)⁻¹ : ℝ))) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE ψ hψ hψ1 hψ0 _ _ μ _
  obtain ⟨hfin, htr, -, -, -, hNc, -, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := hfin
  haveI := htr
  have hgood : Good E := GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional F E
  have hpair : IsPair fun x y => ψ (polar hE x y) :=
    GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F E ψ hψ hψ1 hψ0 (polar hE) (polar_symm hE) (polar_nondeg hE)
  set f : E → ℂ := fun z => ψ (Algebra.norm F z) with hf
  have hlc : IsLocallyConstant f := by
    have h := hpair.lc.comp_continuous (show Continuous fun z : E => ((2 : F)⁻¹ • z, z) by fun_prop)
    have heq : ((fun p : E × E => ψ (polar hE p.1 p.2)) ∘ fun z : E => ((2 : F)⁻¹ • z, z)) = f := by
      funext z; simp only [Function.comp_apply, f, polar_half]
    rwa [heq] at h
  have hf0 : f 0 = 1 := by simp [f]
  have hfadd : ∀ x y, f (x + y) = f x * f y * ψ (polar hE x y) := by
    intro x y
    simp only [f]
    rw [norm_add_eq hE, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  obtain ⟨γ, K₁, hK₁, hγ⟩ := GlobalTheory.T.gaussIntegral_quadraticChar_eventually_const E hgood μ _ hpair f hlc hf0 hfadd
  have hG : HasGauss μ f γ := by
    intro K hK
    obtain ⟨L, hLc, hLo, hL⟩ := hgood.large (K ∪ K₁) (hK.union hK₁)
    exact ⟨L, hLc, hLo, Set.subset_union_left.trans hL, hγ L hLc hLo (Set.subset_union_right.trans hL)⟩
  refine ⟨γ, fun t => ?_⟩
  by_cases ht : t ∈ (Units.map (Algebra.norm F : E →* F)).range
  · obtain ⟨w, hw⟩ := ht
    let T : E ≃ₜ+ E :=
      { toFun := fun z => (w : E) * z
        invFun := fun z => ((w⁻¹ : Eˣ) : E) * z
        left_inv := fun z => by simp
        right_inv := fun z => by simp
        map_add' := fun x y => mul_add _ _ _
        continuous_toFun := continuous_const.mul continuous_id
        continuous_invFun := continuous_const.mul continuous_id }
    have hT : μ.map T = (distribHaarChar F t)⁻¹ • μ := by
      have h := GlobalTheory.T.map_mul_left_eq_inv_norm_haarChar_smul F E c δ hE μ w
      rw [hw] at h
      exact h
    have h := GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale E E μ μ T _ f γ hT hG
    have e1 : (fun z : E => ψ ((t : F) * Algebra.norm F z)) = fun x => f (T x) := by
      funext z
      show ψ ((t : F) * Algebra.norm F z) = ψ (Algebra.norm F ((w : E) * z))
      rw [MonoidHom.map_mul (Algebra.norm F) (w : E) z, ← hw, Units.coe_map]
    have hs : sgn E t = 1 := by rw [sgn, if_pos ⟨w, hw⟩]
    have e2 : γ * (sgn E t * (((nabs F t)⁻¹ : ℝ) : ℂ)) = (((((distribHaarChar F t)⁻¹ : NNReal) : ℝ)) : ℂ) * γ := by
      rw [hs, one_mul, mul_comm]
      simp [nabs]
    rw [e1, e2]
    exact h
  · obtain ⟨s₀, hcan⟩ := GlobalTheory.T.gaussIntegral_normForm_nonNorm_cancel F E c δ hE ψ hψ hψ1 hψ0 μ t ht
    have hs : sgn E t = -1 := by rw [sgn, if_neg ht]
    intro K hK
    obtain ⟨a₁, ha₁⟩ := exists_cball_of_isCompact (hK.image hNc)
    obtain ⟨a₂, ha₂⟩ := exists_cball_of_isCompact (hK₁.image hNc)
    obtain ⟨s', hs'1, hs'2⟩ := exists_cball_sup (t * a₁) a₂
    obtain ⟨s, hs1, hs2⟩ := exists_cball_sup s' s₀
    obtain ⟨L, hLeq, hLc, hLo⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE (t⁻¹ * s)
    obtain ⟨L₁, hL₁eq, hL₁c, hL₁o⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE s
    have hset : {z : E | (t : F) * Algebra.norm F z ∈ cball s} = (L : Set E) := by
      rw [hLeq]; ext z; exact mul_mem_cball_iff t s _
    have hK₁L₁ : K₁ ⊆ L₁ := by
      intro z hz
      rw [hL₁eq]
      exact hs1 (hs'2 (ha₂ ⟨z, hz, rfl⟩))
    have hKL : K ⊆ L := by
      intro z hz
      rw [← hset]
      have h1 : Algebra.norm F z ∈ cball a₁ := ha₁ ⟨z, hz, rfl⟩
      have h2 : (t : F) * Algebra.norm F z ∈ cball (t * a₁) := by
        rw [mul_mem_cball_iff, inv_mul_cancel_left]; exact h1
      exact hs1 (hs'1 h2)
    have hs₀ : (s₀ : F) ∈ cball s := hs2 (show ValuativeRel.valuation F (s₀ : F) ≤ ValuativeRel.valuation F (s₀ : F) from le_refl _)
    have h1 := hcan s hs₀
    rw [← hL₁eq, hγ L₁ hL₁c hL₁o hK₁L₁, hset] at h1
    refine ⟨L, hLc, hLo, hKL, ?_⟩
    have hn : (nabs F t : ℂ) ≠ 0 := by exact_mod_cast (nabs_pos F t).ne'
    rw [hs, Complex.ofReal_inv]
    field_simp
    linear_combination h1
end GlobalTheory.KSp
