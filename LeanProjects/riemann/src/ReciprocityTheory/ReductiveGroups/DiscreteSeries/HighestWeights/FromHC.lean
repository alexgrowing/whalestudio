import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.FromHCB

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem derivExists_allPos : DerivExistsAllPosStatement := by
  intro k V _ _ _ τ hτ
  let b := stdOrthonormalBasis ℂ V
  choose L hL using fun i j => fh_coef τ hτ (b j) (b i)
  refine ⟨∑ i, ∑ j, (L i j).smulRight ((innerSL ℂ (b j)).smulRight (b i)), ?_⟩
  intro X hX γ hγ
  have key : (∑ i, ∑ j, (L i j).smulRight ((innerSL ℂ (b j)).smulRight (b i))) X =
      derOp (fun _ : Fin k => true) τ X := by
    ext v
    have hv : derOp (fun _ : Fin k => true) τ X v = ∑ i, ∑ j, (L i j X * inner ℂ (b j) v) • b i := by
      conv_lhs => rw [← b.sum_repr' (derOp (fun _ : Fin k => true) τ X v)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      conv_lhs => rw [← b.sum_repr' v]
      rw [map_sum, inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, inner_smul_right, hL i j X hX, mul_comm]
    rw [hv]
    simp [LinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply, smul_smul,
      ContinuousLinearMap.sum_apply]
  rw [key]
  exact derOp_hasDeriv _ τ hτ X hX γ hγ

theorem kType_of_hcTypeU {k : ℕ} {u : Fin k → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (hπ : Formalism.MainNotions.S.IsHCTypeU k u π) :
    ∃ T : KType (fun _ : Fin k => true) (lowK (fun _ : Fin k => true) u), ∃ U : H ≃ₗᵢ[ℂ] T.V,
      ∀ (g : KG (fun _ : Fin k => true)) (v : H), U (π (toMK g) v) = T.op g (U v) := by
  obtain ⟨hnt, hfd, hU, hK⟩ := hπ
  haveI := hfd
  haveI : CompleteSpace H := FiniteDimensional.complete ℂ H
  obtain ⟨dτ, hd⟩ := derivExists_allPos k H (fhTau π hU) (fhTau_cont π hU)
  have hσ : ∀ g, π (toMK g) = ((fhTau π hU g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) :=
    fun g => (fhTau_coe π hU g).symm
  obtain ⟨_, _, hirr, ⟨v, -, hv0, hvw⟩, hdom⟩ := hK
  have hwt := fun a => fh_dτ_of_wt (fhTau π hU) dτ hd π hσ hvw a
  have hhw := fun a b hab => fh_hw (fhTau π hU) dτ hd π hσ hdom hvw a b hab
  let T : KType (fun _ : Fin k => true) (lowK (fun _ : Fin k => true) u) :=
    { V := H
      τ := fhTau π hU
      cont := fhTau_cont π hU
      irred := ?irr
      dτ := dτ
      hasDeriv := hd
      w := ((‖v‖⁻¹ : ℝ) : ℂ) • v
      w_norm := ?nrm
      w_wt := ?wt
      w_hw := ?hw }
  refine ⟨T, LinearIsometryEquiv.refl ℂ H, ?_⟩
  case irr =>
    intro W hW
    apply hirr W le_top
    intro g hg x hx
    have := hW (torepK _ hg) x hx
    rw [← hσ] at this
    first
    | (rwa [toMK_torepK (fun _ : Fin k => true) hg] at this)
    | (convert this using 2; exact (toMK_torepK (fun _ : Fin k => true) hg).symm)
  case nrm =>
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)
  case wt =>
    intro a
    rw [map_smul, hwt a]
    exact smul_comm _ _ _
  case hw =>
    intro a b hab _
    rw [map_smul, hhw a b hab, smul_zero]
  intro g x
  first
  | (simp only [LinearIsometryEquiv.refl_apply, KType.op, hσ])
  | (show π (toMK g) x = ((fhTau π hU g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x; rw [hσ])

end ReciprocityTheory.ChartRestriction.DS.HW
