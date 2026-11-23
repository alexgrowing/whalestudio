import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FockZeroRight
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FactorsOfPerturb

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

section FG

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vK_wpow {p : ℕ} {w : O} (hw : Irreducible w) (h2 : w ^ 2 = (p : O)) (n : ℕ) :
    vK p (algebraMap O (KK O) (w ^ n)) = ((((n : ℚ) / 2 : ℚ)) : WithTop ℚ) := by
  rw [valuation_algebraMap_eq_alt p _ (pow_ne_zero _ hw.ne_zero), dvr_order_pow hw.ne_zero, nv_irr hw, ramE_two hw h2]
  push_cast
  ring_nf

theorem bb_coeff {p : ℕ} (S : UniformizedDVR p O) (h2 : S.w ^ 2 = (p : O)) {σ : Type} (sp : ℕ)
    (F : MvPolynomial σ (KK O)) (hF : F ∈ bbSpec O p σ sp) (μ : σ →₀ ℕ) :
    ∃ a : O, algebraMap O (KK O) (S.w ^ (padicValNat p (expFact μ) + padicValNat p sp)) * F.coeff μ =
      algebraMap O (KK O) a := by
  classical
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ', c, hc, rfl⟩ := hx
    rw [coeff_monomial]
    split_ifs with h
    · subst h
      apply (valuation_nonneg_iff_integral S _).1
      rw [valuation_mul_alt, vK_wpow S.w_irr h2]
      have e : (((padicValNat p (expFact μ') + padicValNat p sp : ℕ) : ℚ) / 2 : ℚ) =
          (padicValNat p (expFact μ') : ℚ) / 2 + (padicValNat p sp : ℚ) / 2 := by push_cast; ring
      rw [e, add_comm]
      exact hc
    · exact ⟨0, by simp⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [coeff_add, mul_add, ha, hb, map_add]⟩
  | smul o x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨o * a, ?_⟩
    rw [coeff_smul, Algebra.smul_def, map_mul, ← ha]
    ring

theorem fg_inter {p : ℕ} (S : UniformizedDVR p O) (h2 : S.w ^ 2 = (p : O)) {σ : Type} (sp : ℕ)
    (V : Submodule (KK O) (MvPolynomial σ (KK O))) (hV : FiniteDimensional (KK O) V) :
    Module.Finite O (V.restrictScalars O ⊓ bbSpec O p σ sp : Submodule O (MvPolynomial σ (KK O))) := by
  classical
  haveI := hV
  let bV := Module.finBasis (KK O) V
  let Sμ : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun k => ((bV k : V) : MvPolynomial σ (KK O)).support
  have hsupp : ∀ F ∈ V, ∀ μ, μ ∉ Sμ → F.coeff μ = 0 := by
    intro F hF μ hμ
    have hF' : (⟨F, hF⟩ : V) = ∑ k, (bV.repr ⟨F, hF⟩ k) • bV k := (bV.sum_repr _).symm
    have : F = ∑ k, (bV.repr ⟨F, hF⟩ k) • ((bV k : V) : MvPolynomial σ (KK O)) := by
      have h := congrArg (fun v : V => (v : MvPolynomial σ (KK O))) hF'
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      exact h
    rw [this, coeff_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [coeff_smul]
    have : μ ∉ ((bV k : V) : MvPolynomial σ (KK O)).support := fun h =>
      hμ (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, h⟩)
    rw [MvPolynomial.notMem_support_iff.1 this, smul_zero]
  set Λ := (V.restrictScalars O ⊓ bbSpec O p σ sp : Submodule O (MvPolynomial σ (KK O)))
  let nμ : (σ →₀ ℕ) → ℕ := fun μ => padicValNat p (expFact μ) + padicValNat p sp
  let gen : Sμ → (Sμ → KK O) := fun μ => Pi.single μ (algebraMap O (KK O) (S.w ^ nμ μ))⁻¹
  let N : Submodule O (Sμ → KK O) := Submodule.span O (Set.range gen)
  let Φ : MvPolynomial σ (KK O) →ₗ[O] (Sμ → KK O) :=
    { toFun := fun F μ => F.coeff μ
      map_add' := fun F G => by funext μ; simp
      map_smul' := fun o F => by funext μ; simp }
  have hΦN : ∀ F ∈ Λ, Φ F ∈ N := by
    intro F hF
    have hw0 : algebraMap O (KK O) (S.w ^ 1) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective O (KK O))]; exact pow_ne_zero _ S.w_irr.ne_zero
    choose a ha using fun μ => bb_coeff S h2 sp F hF.2 μ
    have : Φ F = ∑ μ : Sμ, a μ • gen μ := by
      funext μ
      simp only [Finset.sum_apply, Pi.smul_apply, gen]
      rw [Finset.sum_eq_single μ (fun b _ hb => by rw [Pi.single_eq_of_ne (Ne.symm hb), smul_zero]) (by simp),
        Pi.single_eq_same]
      show F.coeff μ = a μ • (algebraMap O (KK O) (S.w ^ nμ μ))⁻¹
      have hne : algebraMap O (KK O) (S.w ^ nμ μ) ≠ 0 := by
        rw [map_ne_zero_iff _ (IsFractionRing.injective O (KK O))]; exact pow_ne_zero _ S.w_irr.ne_zero
      rw [Algebra.smul_def, ← ha μ]
      field_simp
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun μ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, rfl⟩)
  have hinj : ∀ F ∈ Λ, Φ F = 0 → F = 0 := by
    intro F hF h0
    ext μ
    by_cases hμ : μ ∈ Sμ
    · exact congrFun h0 ⟨μ, hμ⟩
    · simpa using hsupp F hF.1 μ hμ
  haveI : Module.Finite O N := Module.Finite.span_of_finite O (Set.finite_range gen)
  haveI : IsNoetherian O N := isNoetherian_of_isNoetherianRing_of_finite O N
  let f : Λ →ₗ[O] N := (Φ.comp Λ.subtype).codRestrict N fun F => hΦN F.1 F.2
  refine Module.Finite.of_injective f ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hF
  apply Subtype.ext
  exact hinj F.1 F.2 (congrArg Subtype.val hF)

end FG

theorem blockFG_all (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r] (s : ℕ)
    (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r) (Sd : UniformizedDVR p O)
    (h2 : Sd.w ^ 2 = (p : O)) : Module.Finite O (blockLat O p r S aTop aPlus m b) := by
  exact fg_inter Sd h2 _ _ (spanSSZ_finite (O := O) (N := 2 * s + 1) (r := r) (blockData p S aTop aPlus m b))

theorem smithAt_all (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : SmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS _ _ j
  exact smithData_seg X.p X.m _ _ _ _ fun b => blockFG_all O X.p X.m _ _ _ _ _ b (dvrOfStd hS) (dvrOfStd_sq hS)

theorem restSmith : RestSmith := TransportedAlt.of_all fun _ _ _ _ _ _ _ _ _ _ => smithAt_all _ _ _ _ _ _ _ _ _ _

theorem partners_to_factors_holds : PartnersToFactors := partners_factors_of_smith_bases restSmith

end Formalism.MainNotions.ColumnSystems.Pf
