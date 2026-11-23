import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalMeasurabilityWeakThreshold
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiNormalization
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem thrW_of (k r o : ℕ) (A : ℝ)
    (h : 12 * ((r : ℝ) + 1) ^ 2 * ((o : ℝ) + r * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A o := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ho : (0 : ℝ) ≤ o := Nat.cast_nonneg o
  push_cast at h
  constructor <;>
    nlinarith [mul_nonneg (mul_nonneg hr hr) (mul_nonneg hr hr), mul_nonneg (mul_nonneg hr hr) (mul_nonneg hr hk),
      mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg hr hr, mul_nonneg (mul_nonneg hr hr) hk, mul_nonneg hr hk,
      mul_nonneg (mul_nonneg hr hr) ho, mul_nonneg hr ho]

theorem inCC_pred {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {o : ℕ}
    {F : Mat k r → E} (h : InCC A (o + 1) F) : InCC A o F := by
  obtain ⟨c, hck, hb⟩ := h
  refine ⟨c, ?_, fun u v hu hv hl g hg => hb u v hu hv (by omega) g hg⟩
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hck g₀ hg₀
  exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast Nat.le_succ o), hfe⟩

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem bigPos_sub (D : RealPlaceData k r Wp Wq) : Formalism.FourierDecayAlt.C6.bigPos D ⊆ Om k r D.z D.z' := by
  intro g hg
  simp only [Formalism.FourierDecayAlt.C6.bigPos, Formalism.FourierDecayAlt.C6.domL, Set.mem_ofPred_eq] at hg
  obtain ⟨hgv, hgf, hd⟩ := hg
  show g ∈ GV k r ∩ Q.OmPlus k r D.z D.z'
  exact ⟨hgv, fun l _ => hd l (Finset.mem_univ l), hgf⟩

theorem glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Q.Glev k r 0 := by
  refine ⟨hg, fun a ha => ?_⟩
  simp at ha

theorem psi_inv {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n : Mat k r} (hn : n ∈ Nset k r) :
    psi k r z cStd n⁻¹ = (psi k r z cStd n)⁻¹ := by
  have h := Formalism.QuantumDeterminants.BesselUnipotentEquiv.star_psi_inv z cStd hz n hn
  rw [← h]
  unfold psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.conj_ofReal]

theorem xiTau_eq (D : RealPlaceData k r Wp Wq) (p : SS k r) :
    xiTau D (1, 1) p = psi k r D.z cStd (Matrix.of p.1.2) * (psi k r D.z' cStd (Matrix.of p.2.2))⁻¹ := by
  unfold xiTau lam psi
  push_cast
  rw [← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  ring

variable [FiniteDimensional ℂ Wp]

theorem jf_equiv (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) (hp : D.inSS p)
    (g : Mat k r) : rho D p (JF D F) g = (xiTau D (1, 1) p)⁻¹ • JF D F g := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r D.z
  have hW' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r D.z'
  have hU := Formalism.QuantumDeterminants.bessel_unitary_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F
    D.z_mem D.z'_mem D.haarN.conc D.haarW.conc D.haarW'.conc D.haarW.left D.haarW'.left
    (Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D) D.π_rep D.π'_rep
  have hNe := Formalism.QuantumDeterminants.bessel_unipotent_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F
    D.z_mem D.z'_mem D.haarN.conc D.haarN.left
  have key : JF D F (sgs p g) =
      (psi k r D.z cStd (Matrix.of p.1.2)⁻¹ * psi k r D.z' cStd (Matrix.of p.2.2)) •
        (D.π (Matrix.of p.1.1)⁻¹).comp ((JF D F g).comp (D.π' (Matrix.of p.2.1))) := by
    unfold Formalism.FourierDecayAlt.B.JF Formalism.FourierDecayAlt.B.sgs
    rw [show (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1 =
        (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 by
      simp only [Matrix.mul_assoc]]
    rw [hU _ _ (hW.inv_mem _ h1) _ h3, hNe _ _ (hN.inv_mem _ h2) _ h4,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  ext x
  simp only [rho, key, ContinuousLinearMap.comp_apply, _root_.smul_apply, map_smul]
  rw [Formalism.QuantumDeterminants.BesselUnitaryEquiv.rep_inv D.π'_rep h3 (hW'.inv_mem _ h3) (Matrix.mul_nonsing_inv _ (hW'.unit _ h3)) x,
    Formalism.QuantumDeterminants.BesselUnitaryEquiv.rep_inv D.π_rep h1 (hW.inv_mem _ h1) (Matrix.mul_nonsing_inv _ (hW.unit _ h1))]
  congr 1
  rw [xiTau_eq, psi_inv D.z_mem h2, mul_inv, inv_inv]

end

end Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem orbital_integral_commutes_large : Formalism.FourierDecayAlt.C6.JCommuteBig := by
  refine ⟨12, by norm_num, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ D Θ A F _ hcomm hA hF
  have hthr := Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.thrW_of k r (opOrder Θ) A hA
  have hF' := Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.inCC_pred hF
  obtain ⟨hck, -⟩ := Formalism.FourierDecayAlt.P.WeakDominationWordBounds.orbital_derivative_words_weak k r Wp Wq D A (opOrder Θ) F hthr hF'
  refine ⟨?_, ?_, ?_⟩
  · intro g₀ hg₀
    have hO := Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.bigPos_sub D hg₀
    obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hck g₀ ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hO.1, hO.2⟩
    exact ⟨U, f', hU, hgU, by exact_mod_cast hf', fun g hg hgv => hfe g hg (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgv)⟩
  · intro p hp g _
    exact Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.jf_equiv D F p hp g
  · intro g hg
    exact (Formalism.FourierDecayAlt.P.orbital_commutes_on_open_set k r Wp Wq D A (opOrder Θ) F Θ _ (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.bigPos_sub D) le_rfl
      hthr hF' hcomm g hg).symm

end Formalism.FourierDecayAlt.P
