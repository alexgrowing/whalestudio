import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateAbsSumWeilTranslateModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNormStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRational
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.FlatSup

theorem lintegral_le_of_tsum {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] (ν : Measure G) [ν.IsMulLeftInvariant] {𝓤 : Set G} (h : IsFundamentalDomain Γ 𝓤 ν)
    (h1 : ν 𝓤 = 1) (f : G → ENNReal) (hf : Measurable f) (B : ENNReal) (hB : ∀ u, ∑' γ : Γ, f (γ.1 * u) ≤ B) :
    ∫⁻ u, f u ∂ν ≤ B := by
  rw [h.lintegral_eq_tsum'' f, ← lintegral_tsum]
  · calc _ ≤ ∫⁻ _ in 𝓤, B ∂ν := lintegral_mono fun u => hB u
      _ = B := by rw [setLIntegral_const, h1, mul_one]
  · exact fun γ => (hf.comp (measurable_const_mul γ.1)).aemeasurable

theorem rat_cancel {D : D7} {m ρ : ℕ} {x : Matrix (Fin m) (Fin ρ) D.host.E} (hx : LinearIndependent D.host.E x.transpose)
    {a b : Mx D ρ ρ} (ha : a ∈ ratMx D ρ ρ) (hb : b ∈ ratMx D ρ ρ)
    (h : (rat x : Mx D m ρ) ⬝ a = (rat x : Mx D m ρ) ⬝ b) : a = b := by
  obtain ⟨a, rfl⟩ := mem_ratMx.1 ha
  obtain ⟨b, rfl⟩ := mem_ratMx.1 hb
  rw [← rat_mul, ← rat_mul] at h
  have h2 := rat_injective h
  have hi : Function.Injective x.mulVec := Matrix.mulVec_injective_iff.2 hx
  refine congrArg rat (Matrix.ext fun i j => ?_)
  have h3 : x *ᵥ (fun k => a k j) = x *ᵥ (fun k => b k j) := by
    funext l
    exact congrFun (congrFun h2 l) j
  exact congrFun (hi h3) i

theorem uni_bound (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    (s : Step ψ V V₀ W W₀ ρ σ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx : LinearIndependent D.host.E x.transpose)
    (Φ : WO V W → ℂ) (hΦ : IsThetaFunO ψ V W Φ) : ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ g h (w : WO V₀ W),
      ∫⁻ u : UX D ρ, ‖dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (g, h) Φ) ((rat x : Mx D W.rank ρ) ⬝ u.1.1) w‖ₑ ∂s.vU.ν ≤
        ENNReal.ofReal (C * (height V g * height W h) ^ A) := by
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.mixedCoordinate_absSum_weilTranslate_moderateGrowth D ψ V W s.χV s.χW s.om s.weil V₀ ρ dV s.vS Φ hΦ
  obtain ⟨om', hW'⟩ := (GlobalTheory.T.weilDatum_descends_to_wittCore D ψ V W s.χV s.χW s.om s.weil).1 V₀ ρ dV
  have hMS := GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ V V₀ W ρ dV s.χV s.χW s.om om' s.weil hW' s.vS.μ s.vS.𝓕 s.vS.covol
  have hmix := (GlobalTheory.T.weilMixedCoordinates_continuous_bounded_supNorm D ψ V V₀ W W₀ ρ σ dV dW s.vS s.vT s.χV s.χW s.om s.weil Φ hΦ).1
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.UnitU.cocompact D ρ
  obtain ⟨c, hc⟩ := exists_height_le_of_isCompact V (hK.image (dV.continuous_levi.comp continuous_subtype_val))
  have hc'1 : 1 ≤ max c 1 := le_max_right _ _
  have hC₀0 : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨max C 0 * max c 1 ^ A, A, mul_nonneg hC₀0 (pow_nonneg (zero_le_one.trans hc'1) _), fun g h w => ?_⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : Countable (UXQ D ρ) := (GlobalTheory.UnitU.rational D ρ).1
  obtain ⟨hH, 𝓤, h𝓤, h1⟩ := s.vU.unit
  have hval : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) := Units.continuous_val.comp continuous_subtype_val
  have hxu : Continuous fun u : UX D ρ => (rat x : Mx D W.rank ρ) ⬝ u.1.1 := continuous_const.matrix_mul hval
  refine lintegral_le_of_tsum (UXQ D ρ) s.vU.ν h𝓤 h1 _ ?_ _ fun u => ?_
  · have hf : Continuous fun u : UX D ρ => (((g, h), ((rat x : Mx D W.rank ρ) ⬝ u.1.1, w)) :
        (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W) := continuous_const.prodMk (hxu.prodMk continuous_const)
    have h2 := hmix.comp hf
    simp only [Function.comp_def] at h2
    exact h2.enorm.measurable
  · obtain ⟨γ₀, hγ₀, k, hk, rfl⟩ := hcov u
    have hp : ((dV.levi k.1 * g, h) : GA D V × GA D W) = (dV.levi k.1, 1) * (g, h) := by simp
    have hom : s.om (dV.levi k.1 * g, h) Φ = s.om (dV.levi k.1, 1) (s.om (g, h) Φ) := by
      rw [hp, map_mul, Module.End.mul_apply]
    let φ : UXQ D ρ → ratMx D W.rank ρ := fun γ =>
      ⟨(rat x : Mx D W.rank ρ) ⬝ (γ.1 * γ₀).1.1, ratMx_mul (rat_mem x) (mul_mem γ.2 hγ₀).1⟩
    have hφ : Function.Injective φ := fun a b hab => by
      have h3 := rat_cancel hx (mul_mem a.2 hγ₀).1 (mul_mem b.2 hγ₀).1 (congrArg Subtype.val hab)
      exact Subtype.ext (mul_right_cancel (Subtype.ext (Units.ext h3)))
    have key : ∀ γ : UXQ D ρ, dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (g, h) Φ) ((rat x : Mx D W.rank ρ) ⬝ (γ.1 * (γ₀ * k)).1.1) =
        dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (dV.levi k.1 * g, h) Φ) (φ γ) := by
      intro γ
      rw [hom, GlobalTheory.Unf.TermLaw.mixS_levi_uni dV (hMS _ (s.weil.om_pres _ _ hΦ)) k.2, ← mul_assoc]
      congr 1
      exact (Matrix.mul_assoc _ _ _).symm
    simp only [key]
    refine (ENNReal.tsum_comp_le_tsum_of_injective hφ
      (fun y : ratMx D W.rank ρ => ‖dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (dV.levi k.1 * g, h) Φ) y w‖ₑ)).trans
      ((hC _ h w).trans (ENNReal.ofReal_le_ofReal ?_))
    have hk' : height V (dV.levi k.1) ≤ max c 1 := (hc _ ⟨k, hk, rfl⟩).trans (le_max_left _ _)
    have hkg : height V (dV.levi k.1 * g) ≤ max c 1 * height V g :=
      (height_mul_le V _ _).trans (mul_le_mul_of_nonneg_right hk' (height_pos V g).le)
    have hx0 : 0 ≤ height V (dV.levi k.1 * g) * height W h := mul_nonneg (height_pos V _).le (height_pos W h).le
    have hx1 : height V (dV.levi k.1 * g) * height W h ≤ max c 1 * (height V g * height W h) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hkg (height_pos W h).le
    calc C * (height V (dV.levi k.1 * g) * height W h) ^ A ≤ max C 0 * (height V (dV.levi k.1 * g) * height W h) ^ A :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx0 _)
      _ ≤ max C 0 * (max c 1 * (height V g * height W h)) ^ A :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx1 _) hC₀0
      _ = _ := by rw [mul_pow, mul_assoc]

theorem sfinite_haar {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (ν : Measure G) [ν.IsHaarMeasure] : SFinite ν := inferInstance

theorem sfinite_fin {G : Type} [MeasurableSpace G] (ν : Measure G) [IsFiniteMeasure ν] : SFinite ν := inferInstance

theorem flat_sup_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ Φ, IsThetaFunO ψ V W Φ → ∃ (C : ℝ) (A : ℕ), ∀ g h y w, ‖flatS dV dW s (rat x) y (s.om (g, h) Φ) w‖ ≤ C * (height V g * height W h) ^ A := by
  intro D ψ V V₀ W W₀ ρ σ dV dW s x hx Φ hΦ
  obtain ⟨C, A, hC0, hC⟩ := uni_bound D ψ V V₀ W W₀ ρ σ dV dW s x hx Φ hΦ
  refine ⟨C, A, fun g h y w => ?_⟩
  have hn : ∀ a, ‖ψ a‖ = 1 := s.weil.std.1.2.1
  have hne : ∀ a, ‖ψ a‖ₑ = 1 := fun a => by rw [← ofReal_norm, hn, ENNReal.ofReal_one]
  have hmix := (GlobalTheory.T.weilMixedCoordinates_continuous_bounded_supNorm D ψ V V₀ W W₀ ρ σ dV dW s.vS s.vT s.χV s.χW s.om s.weil Φ hΦ).1
  have hT := s.vT.covol
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.UnitU.topology D ρ
  obtain ⟨j1, j2, j3, j4, -⟩ := lattice_Mx D σ V₀.rank
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D σ V₀.rank) := ⟨rfl⟩
  haveI := s.vU.unit.1
  haveI : IsFiniteMeasure (s.vT.μ.restrict s.vT.𝓕) := ⟨by rw [Measure.restrict_apply_univ, hT.2.2]; exact ENNReal.one_lt_top⟩
  haveI := sfinite_haar s.vU.ν
  haveI := sfinite_fin (s.vT.μ.restrict s.vT.𝓕)
  let F : UX D ρ → Mx D σ V₀.rank → ENNReal := fun u ξ =>
    ‖dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (g, h) Φ) ((rat x : Mx D W.rank ρ) ⬝ u.1.1) (dW.incX V₀ ξ + dW.incAdj V₀ y + dW.inc0 V₀ w)‖ₑ
  have hval : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) := Units.continuous_val.comp continuous_subtype_val
  have hxu : Continuous fun u : UX D ρ => (rat x : Mx D W.rank ρ) ⬝ u.1.1 := continuous_const.matrix_mul hval
  have hX : Continuous (dW.incX V₀) := continuous_const.matrix_mul continuous_id
  have hFm : Measurable (Function.uncurry F) := by
    have hf : Continuous fun p : UX D ρ × Mx D σ V₀.rank => (((g, h), ((rat x : Mx D W.rank ρ) ⬝ p.1.1.1,
        dW.incX V₀ p.2 + dW.incAdj V₀ y + dW.inc0 V₀ w)) : (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W) :=
      continuous_const.prodMk ((hxu.comp continuous_fst).prodMk
        (((hX.comp continuous_snd).add continuous_const).add continuous_const))
    have h2 := hmix.comp hf
    simp only [Function.comp_def] at h2
    exact h2.enorm.measurable
  have h1 : ∀ u : UX D ρ, ‖flatFun ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (rat x) y (s.om (g, h) Φ) w u‖ₑ ≤
      ∫⁻ ξ in s.vT.𝓕, F u ξ ∂s.vT.μ := by
    intro u
    unfold flatFun evalAt
    have e1 : ‖star (psiUni ψ u.1)‖ₑ = 1 := by
      rw [← ofReal_norm, norm_star, show ‖psiUni ψ u.1‖ = 1 from hn _, ENNReal.ofReal_one]
    rw [enorm_mul, e1, one_mul]
    unfold GlobalTheory.MixModel.HypDec.mixT
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun ξ => le_of_eq ?_)
    simp only [F]
    rw [dW.integrandT_eq, enorm_mul, hne, one_mul]
  have h2 : ‖flatS dV dW s (rat x) y (s.om (g, h) Φ) w‖ₑ ≤ ENNReal.ofReal (C * (height V g * height W h) ^ A) := by
    unfold flatS flatAt
    refine (enorm_integral_le_lintegral_enorm _).trans ((lintegral_mono h1).trans ?_)
    rw [lintegral_lintegral_swap hFm.aemeasurable]
    calc _ ≤ ∫⁻ _ in s.vT.𝓕, ENNReal.ofReal (C * (height V g * height W h) ^ A) ∂s.vT.μ :=
          lintegral_mono fun ξ => hC g h _
      _ = _ := by rw [setLIntegral_const, hT.2.2, mul_one]
  rw [← ofReal_norm] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0 (pow_nonneg
    (mul_nonneg (height_pos V g).le (height_pos W h).le) _))).1 h2

end GlobalTheory.FlatSup
