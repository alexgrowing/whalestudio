import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiRegOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem gN_cont : Continuous (fun g : Mx k r => B.gN g) := by
  unfold B.gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp (continuous_apply_apply i j))

theorem gNpow_inCC (hNI : NormInv) (b : ℝ) (hb : b ≠ 0) :
    B.InCC b 0 (fun g : B.Mat k r => ((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
  have hpos : ∀ g ∈ B.GV k r, 0 < B.gN g := fun g hg => lt_of_lt_of_le one_pos ((hNI k r).2 g hg).2
  have hf : ContinuousOn (fun g : Mx k r => ((B.gN g ^ (-b) : ℝ) : ℂ)) (B.GV k r) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact gN_cont.continuousOn.rpow_const (fun g hg => Or.inl (hpos g hg).ne')
  refine ⟨1, ckOn_zero_of_contOn _ hf, ?_⟩
  intro uu vv _ _ hlen g hg
  have hu : uu = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hv : vv = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hu; subst hv
  show B.gN g ^ b * ‖((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)‖ ≤ 1
  have hgN : 0 ≤ B.gN g := Real.sqrt_nonneg _
  rw [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hgN _)]
  have := rpow_bound (B.gN g) 1 b hgN hb
  simpa using this

def invP (p : B.SS k r) : B.SS k r :=
  ((B2.invM p.1.1, B2.invM p.1.2), (B2.invM p.2.1, B2.invM p.2.2))

theorem measurable_componentwiseInv : Measurable (invP (k := k) (r := r)) := by
  have h := B2x1.invM_meas (k := k) (r := r)
  exact (h.prodMap h).prodMap (h.prodMap h)

theorem map_invM_eq {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U) {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : B.IsHaarOn U μ) : μ.map B2.invM = μ := Formalism.FourierDecayAlt.P.haar_measure_inversion k r U μ hU hμ

theorem ae_of_haarB {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : B.IsHaarOn U μ) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ U := by
  rw [ae_iff]; exact hμ.conc

theorem ae_SS {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] [SigmaFinite D.μW'] :
    ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z ∧ Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r ∧
      Matrix.of p.2.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z' ∧ Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hW := ae_of_haarB D.haarW
  have hN := ae_of_haarB D.haarN
  have hW' := ae_of_haarB D.haarW'
  have e1 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hW)
  have e2 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  have e3 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z' :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae hW')
  have e4 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  filter_upwards [e1, e2, e3, e4] with p h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

theorem map_invP {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] [SigmaFinite D.μW'] :
    D.μSS.map invP = D.μSS := by
  have hm := B2x1.invM_meas (k := k) (r := r)
  have hW := map_invM_eq (weyl_subgroup_closed k r D.z) D.haarW
  have hN := map_invM_eq (unipotent_radical_closed k r) D.haarN
  have hW' := map_invM_eq (weyl_subgroup_closed k r D.z') D.haarW'
  show ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)).map
      (Prod.map (Prod.map B2.invM B2.invM) (Prod.map B2.invM B2.invM)) = (D.μW.prod D.μN).prod (D.μW'.prod D.μN)
  rw [← Measure.map_prod_map _ _ (hm.prodMap hm) (hm.prodMap hm), ← Measure.map_prod_map _ _ hm hm,
    ← Measure.map_prod_map _ _ hm hm, hW, hN, hW']

theorem la_fin (hNI : NormInv) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] [SigmaFinite D.μW'] {b : ℝ} (hb : JF.TransportedAlt k r b 0) (hb0 : b ≠ 0)
    {γ : B.Mat k r} (hγ : γ ∈ JF.Om k r D.z D.z') :
    ∫⁻ p, ‖B.gN (Matrix.of p.1.1 * Matrix.of p.1.2 * γ * (Matrix.of p.2.2)⁻¹ * (Matrix.of p.2.1)⁻¹) ^ (-b)‖ₑ
      ∂D.μSS < ⊤ := by
  set F : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun g => ((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ) with hF
  have hJC := Formalism.FourierDecayAlt.P.bessel_integral_converges k r ℂ ℂ (triv D) b F hb (gNpow_inCC hNI b hb0)
  obtain ⟨bb, hbb, hbd⟩ := hJC.2 {γ} isCompact_singleton (Set.singleton_subset_iff.mpr hγ)
  set G : B.SS k r → ℝ≥0∞ := fun p => ‖B.gN (B.sgs p γ) ^ (-b)‖ₑ with hG
  have h1 : ∫⁻ p, G p ∂D.μSS < ⊤ := by
    calc ∫⁻ p, G p ∂D.μSS ≤ ∫⁻ p, ‖bb p‖ₑ ∂D.μSS := by
          apply lintegral_mono_ae
          filter_upwards [hbd γ rfl] with p hp
          have e : ‖B.gN (B.sgs p γ) ^ (-b)‖ = ‖B.rho (triv D) p F γ‖ := by
            rw [rho_triv]; simp [hF]
          simp only [hG]
          rw [← ofReal_norm, ← ofReal_norm, e]
          exact ENNReal.ofReal_le_ofReal (hp.trans (Real.le_norm_self _))
      _ < ⊤ := hbb.hasFiniteIntegral
  have hinv : ∀ᵐ p ∂D.μSS, invP (invP p) = p ∧
      G (invP p) = ‖B.gN (Matrix.of p.1.1 * Matrix.of p.1.2 * γ * (Matrix.of p.2.2)⁻¹ *
        (Matrix.of p.2.1)⁻¹) ^ (-b)‖ₑ := by
    filter_upwards [ae_SS D] with p hp
    have u1 := (weyl_subgroup_closed k r D.z).unit _ hp.1
    have u2 := (unipotent_radical_closed k r).unit _ hp.2.1
    have u3 := (weyl_subgroup_closed k r D.z').unit _ hp.2.2.1
    have u4 := (unipotent_radical_closed k r).unit _ hp.2.2.2
    have ii : ∀ x : Formalism.QuantumDeterminants.Mt k r, IsUnit (Matrix.of x).det → B2.invM (B2.invM x) = x := by
      intro x hx
      show (((Matrix.of x)⁻¹)⁻¹ : B.Mat k r) = Matrix.of x
      exact Matrix.nonsing_inv_nonsing_inv _ hx
    refine ⟨?_, ?_⟩
    · simp only [invP]
      rw [ii _ u1, ii _ u2, ii _ u3, ii _ u4]
    · simp only [hG, invP, B.sgs]
      have j1 : (Matrix.of (B2.invM p.1.1))⁻¹ = Matrix.of p.1.1 := ii _ u1
      have j2 : (Matrix.of (B2.invM p.1.2))⁻¹ = Matrix.of p.1.2 := ii _ u2
      rw [j1, j2]
      rfl
  calc ∫⁻ p, ‖B.gN (Matrix.of p.1.1 * Matrix.of p.1.2 * γ * (Matrix.of p.2.2)⁻¹ * (Matrix.of p.2.1)⁻¹) ^ (-b)‖ₑ
        ∂D.μSS = ∫⁻ p, G (invP p) ∂D.μSS := lintegral_congr_ae (hinv.mono fun p hp => hp.2.symm)
    _ = ∫⁻ p, G (invP p) ∂(D.μSS.map invP) := by rw [map_invP D]
    _ ≤ ∫⁻ p, G (invP (invP p)) ∂D.μSS := lintegral_map_le (fun p => G (invP p)) invP
    _ = ∫⁻ p, G p ∂D.μSS := lintegral_congr_ae (hinv.mono fun p hp => by show G (invP (invP p)) = G p; rw [hp.1])
    _ < ⊤ := h1

end Formalism.FourierDecayAlt.P.S3dx4
