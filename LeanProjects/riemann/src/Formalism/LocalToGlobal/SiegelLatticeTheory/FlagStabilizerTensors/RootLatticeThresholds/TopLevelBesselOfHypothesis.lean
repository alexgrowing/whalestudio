import Formalism.SharpRestriction.CuspSpanNormBounds.BigCellDensity

noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.BigCellDensity
open scoped InnerProductSpace

def TopLevelBesselHypothesis : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq)
    (ν' : Fin (2 * r + (k0 + 1) + 1) → ℂ) (m₀ : Formalism.FourierDecayAlt.B.Mat (k0 + 1) r),
    L.c = cStd → 0 < L.κN → L.κN ≠ ⊤ → Ds.z = L.z → Ds.z' = L.z' → Ds.π = L.π → Ds.π' = L.π' →
    Ds.μW = L.μW → Ds.μN = L.μN → Ds.μW' = L.μW' → Formalism.FourierDecayAlt.D.IsBaseFrame Ds ν' m₀ →
      ∀ (F : ThB.Mx (k0 + 1) r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)), IsKFinCoefH L.σ F →
        Formalism.FourierDecayAlt.B.InCC (A0 (k0 + 1) r) 1 F →
        0 < ThB.Gpt (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') γ → (∃ g, IsPtRep L γ g ∧ IsRelStab L g) →
        ThB.orbSq L F γ = ENNReal.ofReal (Real.pi ^ (2 * pc r (γ.1.map Prod.snd)) *
          (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))
            (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))).re)

theorem topLevelBesselHypothesis : TopLevelBesselHypothesis := by
  have hDF := Formalism.FourierDecayAlt.P.exists_isotropic_frame
  have hVI := Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep
  have hPR := Formalism.FourierDecayAlt.P.relevant_points_holds
  have hRM := root_measure_of_mu_R
  have hQE := quotient_exists
  have hCut := K_finite_decay
  have hRI := repIndep_of K_finite_decay orbital_norm_independence
  intro k0 r L Ds ν' m₀ hc hκ0' hκ1 hz hz' hπ hπ' hW hN hW' hBF
  have hκ0 : L.κN ≠ 0 := hκ0'.ne'
  intro F γ hK hdec hpos _
  have hp : Formalism.FourierDecayAlt.D.IsLocPt (γ.1.map Prod.swap) (r + 1) := isLocPt_swap γ
  have hG : 0 < Formalism.FourierDecayAlt.D.ptG (Tz (k0 + 1) r Ds.z * Tz (k0 + 1) r Ds.z') r (γ.1.map Prod.swap) := by
    rw [ptG_eq_GPoint, hz, hz']
    exact hpos
  obtain ⟨g, hgG, hgZ, hgF⟩ := hDF (k0 + 1) r L.Wp L.Wq Ds ν' m₀ _ hBF hp hG
  have hvec := hVI (k0 + 1) r L.Wp L.Wq Ds ν' m₀ F _ hp g hBF hG hgG hgZ hgF
  have hrep : IsPtRep L γ g := ⟨hgG, by rw [← hz, ← hz', hgZ, ptMatN_swap]⟩
  have hrelD := hPR (k0 + 1) r L.Wp L.Wq Ds _ g hp hgG hgZ
  have hrel : IsRelStab L g := fun a ha => by
    have h1 := hrelD.2 a ha
    rw [hz, hz'] at h1
    rw [hc]
    exact h1
  have hroot := hRM k0 r L Ds γ g hp hc hz hz' hgG hgZ
  obtain ⟨ν, hq⟩ := hQE k0 r L γ g _ hc hκ0 hκ1 hrep hrel hroot
  have hcard_pos : (0 : ℝ) < Real.pi⁻¹ ^ (rootPat γ).card := by positivity
  have hl0 : ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hcard_pos
  have hq' := isOrbQuot_rescale L _ ENNReal.ofReal_ne_top hq
  have hconc : Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap))
      {x | Matrix.of x ∉ RStab (k0 + 1) r g} = 0 := by
    have h1 := hroot.1
    rw [Measure.smul_apply, smul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hl0
    · exact h
  have hne : Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap)) ≠ 0 := by
    intro h0
    apply muR_ne_zero L hc γ g _ hroot
    rw [h0, smul_zero]
  have : SFinite (Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap))) := by
    unfold Formalism.FourierDecayAlt.D.muR
    infer_instance
  have hcut := hCut k0 r L Ds γ g hp F hc hz hz' hπ hπ' hW hN hW' hK hdec hpos hgG hgZ
  have hJ := orbJ_eq L Ds hc hκ0 hκ1 hz hz' hπ hπ' hW hN hW' hgG hrel hconc hne hq' F hcut
  have hsm : OrbInt L F g (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • ν) =
      (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal • OrbInt L F g ν := by
    unfold OrbInt
    rw [integral_smul_measure]
  rw [hvec, hJ, hsm,
    orbSq_eq_of L F γ (hsNormSq (OrbInt L F g ν))
      (fun g' μ' ν' h' => hRI k0 r L Ds F γ hc hκ0 hκ1 hz hz' hπ hπ' hW hN hW' hK hdec hpos g' μ' ν' g _ ν h' ⟨hrep, hrel, hroot, hq⟩)
      ⟨g, _, ν, hrep, hrel, hroot, hq⟩]
  congr 1
  rw [show (Formalism.FourierDecayAlt.B.hsInner ((ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal • OrbInt L F g ν)
      ((ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal • OrbInt L F g ν)).re =
      hsNormSq ((ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal • OrbInt L F g ν) by rw [hsNormSq, hsInner_eq],
    Formalism.MainNotions.BigCellDensity.hsNormSq_smul, ENNReal.toReal_ofReal hcard_pos.le]
  rw [← card_rootPat γ]
  have h1 : Real.pi ^ (2 * (rootPat γ).card) * (Real.pi⁻¹ ^ (rootPat γ).card) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm (rootPat γ).card 2, ← mul_pow, mul_inv_cancel₀ Real.pi_ne_zero, one_pow]
  rw [← mul_assoc, h1, one_mul]

end Formalism.L2.SG.Pf.BesselExpansion
