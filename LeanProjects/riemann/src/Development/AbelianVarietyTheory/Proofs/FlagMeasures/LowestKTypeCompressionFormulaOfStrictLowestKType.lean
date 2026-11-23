import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightDerivativeSumZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightGapBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightEventuallyZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeAnalytic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneLargeGaps
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.FormGapFree

open GlobalTheory.Jet.FormGap GlobalTheory.Dec.FormF GlobalTheory.Dec.PsiEig Filter Topology

theorem formulaGap : FormulaGap := by
  intro n ε lam H _ _ σ hlam hσ h hgap hh w hw X hX u hu v hv
  haveI := hσ.1
  have hU := hσ.2.2.1
  obtain ⟨g₀, hg1, hg2⟩ := exists_gap hlam hgap hh
  have hS := GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub n ε lam H σ hlam hσ fun a b hab => by
    rcases lt_trichotomy a b with hlt | heq | hlt
    · exact (hg2.trans_le (hg1 a b hlt hab)).trans_le (le_abs_self _)
    · exact absurd (congrArg ε heq) hab
    · rw [abs_sub_comm]
      exact (hg2.trans_le (hg1 b a hlt hab.symm)).trans_le (le_abs_self _)
  obtain ⟨V, E, hD, hSV⟩ := GlobalTheory.DerEx.exists_isDer_lowKSub n ε lam H σ hU hS
  have han := GlobalTheory.Jet.Anal.lowK_analytic n ε H σ V E lam hU hD hS hSV u hu X hX.1
  obtain ⟨hw1, hwS, hwt⟩ := hw
  generalize lowKSub ε lam σ = S at *
  haveI := hS.1
  haveI := FiniteDimensional.complete ℂ S
  obtain ⟨τ, hτ, hτσ⟩ := TauExt.tauExists n ε _ H σ S ⟨w, hwS⟩ (URep_K hU) hS hw1 hwt
  have hw0 : (⟨w, hSV hwS⟩ : V) ≠ 0 := fun h0 => by
    have : w = 0 := congrArg Subtype.val h0
    simp [this] at hw1
  obtain ⟨hK, hsp, hfd⟩ := (KType.kType_iff n ε H σ V E hU hD).2 _ S ⟨w, hSV hwS⟩ hS hSV hwS hw0 hwt
  have hA : ∀ x y : S, LocAn ε (fun z => ⟪y, Psi ε lam τ ⟨w, hwS⟩ (z.map star) x⟫_ℂ) := fun x y =>
    locAn_conj (f := fun z => ⟪y, Psi ε lam τ ⟨w, hwS⟩ z x⟫_ℂ) fun g hg => psiAnalytic n ε lam S τ _ hlam hτ y x g hg
  have hsm : ∀ (x : V) (y : H), SmoothOnG ε (fun z => ⟪y, diffOp ε lam σ τ ⟨w, hwS⟩ z x⟫_ℂ) := fun x y => by
    rw [inner_diffOp]
    exact Line.smooth_comb _ (hD.2.2.2 x _) (hA _ _).smooth
  have hjet := GlobalTheory.Jet.Germ.germ_jet_zero n ε H σ V E lam g₀ ⟨w, hSV hwS⟩ hU hD hK hfd hg1 hg2
    (fun z => (diffOp ε lam σ τ ⟨w, hwS⟩ z : H →ₗ[ℂ] H)) ?_ ?_ ?_ ?_
  · rw [hsp] at hjet
    have h0 := Line.vanish_of_zero_jet n ε _ X (hsm ⟨u, hSV hu⟩ v) hX.1 (fun l => hjet l u hu v) (by
      intro t ht
      have e := inner_diffOp (ε := ε) (σ := σ) lam τ ⟨w, hwS⟩ u v
      simp only [congrFun e]
      exact (((innerSL ℂ (S.starProjection v)).restrictScalars ℝ).analyticAt _ |>.comp (han t ht)).add
        (analyticAt_const.mul (locAn_line (hA _ _) hX.1 t ht)))
    have hp := exp_posDef (P_star hX)
    have h1 := (psiPolar n ε lam S τ _ hlam hτ).1 1 (one_K ε) _ (P_star hX)
    rw [one_mul, hτ.2.1.1, ← exp_star] at h1
    rw [← exp_star] at hp
    have h2 := ps_entry (lam := lam) hτ hτσ (z := NormedSpace.exp X) (fun k hk => (phiPos n lam _ (by
      rw [K_inv hk]
      exact hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC hk).1))).1) u v
    rw [congrFun (inner_diffOp lam τ ⟨w, hwS⟩ u v), h1, Submodule.starProjection_eq_self_iff.2 hv, neg_one_mul,
      add_neg_eq_zero] at h0
    refine h0.trans (h2.trans ?_)
    congr 2
    funext k
    have hk : toMK k ∈ Kset ε := k.2
    have hpos : ((toMK k)⁻¹ * NormedSpace.exp X * toMK k).PosDef := by
      rw [K_inv hk]
      exact (exp_posDef hX).conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC hk).1)
    rw [Phi_star, (phiPos n lam _ hpos).2.1.le.isSelfAdjoint.star_eq]
  · rw [hsp]
    exact fun g hg x _ => ⟨S.sub_mem (S.starProjection_apply_mem _) (Subtype.prop _),
      fun k₁ h₁ k₂ h₂ => diffOp_equiv hlam hU hS.2.1 hτ hτσ hg h₁ h₂ x⟩
  · rw [hsp]
    exact fun x hx y => hsm ⟨x, hSV hx⟩ y
  · intro G hG y
    filter_upwards [psi_near_one hlam hτ hτσ, GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero n ε H σ V E lam _ hU hD hK hfd G hG y] with g h1 h2
    have h3 : ∀ a b, Eab ε a b (fun z => ⟪y, diffOp ε lam σ τ ⟨w, hwS⟩ z (at1 G a b : V)⟫_ℂ) (umat g) =
        ⟪S.starProjection y, σ (umat g) (E a b (at1 G a b) : V)⟫_ℂ + (-1) * ((Module.finrank ℂ S : ℂ) *
          Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) *
            (⟪y, σ (toMK k) w⟫_ℂ * ⟪σ (toMK k) w, (at1 G a b : V)⟫_ℂ) ∂(muK ε)) (umat g)) := fun a b => by
      rw [inner_diffOp, ← h1 a b (at1 G a b : V) y]
      refine (Line.word_comb (-1) (hD.2.2.2 _ _) (hA _ _).smooth [(a, b)] _ g.2).trans ?_
      rw [(Coef.coef_flow n ε H σ V E hU hD).1 _ _ _ _ g.2]
      rfl
    have h4 := congrArg (fun x : V => ⟪S.starProjection y, σ (umat g) x⟫_ℂ)
      (GlobalTheory.Jet.Schmid.mul_vminus_eq_zero n ε H σ V E lam _ hlam hσ hD hK hfd G hG)
    simp only [Submodule.coe_sum, map_sum, inner_sum, Submodule.coe_zero, map_zero, inner_zero_right] at h4
    simp only [ContinuousLinearMap.coe_coe, h3, Finset.sum_add_distrib, ← Finset.mul_sum, h2, h4]
    simp
  · rw [hsp]
    intro x hx
    change diffOp ε lam σ τ ⟨w, hwS⟩ 1 x = 0
    rw [diffOp_apply, map_star_one, (psiPolar n ε lam S τ _ hlam hτ).2.1, hU.1.1]
    exact sub_self _

end GlobalTheory.Jet.FormGapFree
