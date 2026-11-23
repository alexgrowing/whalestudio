import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIntertwinerUniqueScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenExtendsContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenContinuousInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerL2ConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInfiniteScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThKTorus.ScaleBound

theorem exists_l2_const (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ) (hPair : IsPair B M χX χW om r s r' s') (M₁ : Model σ X W) (hM₁ : M₁.IsGood B.ψ)
    (e : Fn F n d →ₗ[ℂ] Fn F n d) (hE : IsEv B M M₁ 1 1 ∅ e)
    (μ : @Measure (Fin n × Fin d → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖e Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  obtain ⟨ei, ev, hei, hev, hpure⟩ := hE.loc
  have hSB : ∀ v : Pl F, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v φ ∈ SB (Fin n × Fin d → Fv F v) := by
    intro v φ hφ
    rw [← (hev v).2]
    exact Submodule.mem_map_of_mem hφ
  refine GlobalTheory.T.restricted_tensor_schwartz F (Fin n × Fin d) e M.vac M₁.vac ei ev (fun v => (hPair.good.vac v).1) hPair.good.std hM₁.std
    (fun v => (hev v).1) hSB hpure ?_ (fun v => ?_) μ hμ
  · letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
    letI : Invertible (2 : mixedEmbedding.mixedSpace F) :=
      (Invertible.map (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2).copy 2 (map_ofNat _ 2).symm
    obtain ⟨ψ, hψ, A, hA⟩ := GlobalTheory.T.weil_eigen_continuous_inverse F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure
    exact GlobalTheory.T.schrodinger_intertwiner_l2_constant F (Fin n × Fin d) ψ hψ ei A hA
  · have h2 : (2 : Fv F v) ≠ 0 := by
      intro h
      apply two_ne_zero (α := F)
      apply (algebraMap F (Fv F v)).injective
      rw [map_ofNat, h, map_zero]
    letI : Invertible (2 : Fv F v) := invertibleOfNonzero h2
    obtain ⟨ψv, hc, hne, A, hA⟩ :=
      GlobalTheory.T.exists_addChar_normalizing_schrodinger_action F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure v
    exact GlobalTheory.T.local_intertwiner_unique_scalar F v (Fin n × Fin d) ψv hc hne (ev v) A (hSB v) hA

variable {F : Type} [Field F] [NumberField F]

theorem tAd_eq_infScale (s : ℝ) : tAd F s = GlobalTheory.TorusTheta.infScale F s := by
  unfold tAd GlobalTheory.TorusTheta.infScale realAd
  refine Prod.ext ?_ ?_
  · show (1 : InfiniteAdeleRing F) + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ (s - 1)) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ s)
    rw [map_sub, map_sub, map_one, map_one, add_sub_cancel]
  · show (1 : FiniteAdeleRing (𝓞 F) F) + 0 = 1
    exact add_zero 1

variable (F) in

def scaleHom : ℝ →* AF F where
  toFun := GlobalTheory.TorusTheta.infScale F
  map_one' := by
    unfold GlobalTheory.TorusTheta.infScale
    rw [map_one, map_one]
    rfl
  map_mul' u v := by
    unfold GlobalTheory.TorusTheta.infScale
    rw [map_mul, map_mul]
    exact Prod.ext rfl (one_mul (1 : FiniteAdeleRing (𝓞 F) F)).symm

theorem blkScale_eq {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (t : Fin q → ℝ)
    (z : κ → AF F) :
    blkScale blk t z = fun j => GlobalTheory.TorusTheta.infScale F (∏ i, if j ∈ blk i then t i else 1) * z j := by
  funext j
  unfold blkScale
  congr 1
  show _ = scaleHom F _
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · exact tAd_eq_infScale _
  · exact (map_one _).symm

theorem prod_scale_pow {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (t : Fin q → ℝ)
    (ht : ∀ i, 0 < t i) (f : ℕ) :
    ∏ j, (∏ i, if j ∈ blk i then t i else 1) ^ f = (∏ i, t i ^ (((f * (blk i).card : ℕ) : ℝ) / 2)) ^ 2 := by
  rw [Finset.prod_pow, Finset.prod_comm, ← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, ← Real.rpow_natCast (t i ^ _) 2,
    ← Real.rpow_mul (ht i).le, Nat.cast_ofNat, div_mul_cancel₀ _ two_ne_zero, Real.rpow_natCast, mul_comm, pow_mul]

theorem norm_scalar_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∃ ex : Fin q → ℝ, ∀ (t : Fin q → ℝ) (a : UA σ X.J) (c : ℂ), (∀ i, 0 < t i) → IsTorusU x y t a →
      (∀ Ψ ∈ schA F (Fin n × Fin d), ∀ z, e (om (a, 1) Ψ) z = c * e Ψ (blkScale blk t z)) →
      ‖c‖ ≤ ∏ i, t i ^ ex i := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP q x y _ M₁ blk e hM₁ _ hE
  refine ⟨fun i => (((Module.finrank ℚ F * (blk i).card : ℕ) : ℝ) / 2), fun t a c ht _ hc => ?_⟩
  have hS := IsUWeilPair.isUSplitting hP.weil
  letI mA : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero F E σ B n d n d X W X W M M₁ 1 1 ∅ e hP.good hM₁ hE
  have heΦ := hE.maps Φ hΦ
  have hcont : Continuous (e Φ) := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA (F := F) heΦ
  have hI0 : ∫⁻ z, ‖e Φ z‖ₑ ^ 2 ∂μ ≠ 0 := by
    intro h
    have hm : AEMeasurable (fun z => ‖e Φ z‖ₑ ^ 2) μ := (hcont.measurable.enorm.pow_const 2).aemeasurable
    rw [lintegral_eq_zero_iff' hm] at h
    have h' : e Φ =ᵐ[μ] 0 := h.mono fun z hz => by simpa using hz
    exact h0 ((hcont.ae_eq_iff_eq μ continuous_const).1 h')
  have hIt : ∫⁻ z, ‖e Φ z‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have h2 := (GlobalTheory.WeilM.schA_memLp_two F _ μ hμ _ heΦ).eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at h2
    simpa using h2.ne
  obtain ⟨l, hl⟩ := exists_l2_const F E σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE μ hμ
  have hU : ∫⁻ z, ‖e (om (a, 1) Φ) z‖ₑ ^ 2 ∂μ = ∫⁻ z, ‖e Φ z‖ₑ ^ 2 ∂μ := by
    rw [hl _ (hS.pres (a, 1) Φ hΦ), hl Φ hΦ, hS.unit μ hμ (a, 1) Φ hΦ]
  set u : Fin n × Fin d → ℝ := fun j => ∏ i, if j ∈ blk i then t i else 1 with hu
  have hupos : ∀ j, 0 < u j := fun j => Finset.prod_pos fun i _ => by
    split_ifs
    · exact ht i
    · exact one_pos
  have hsc := GlobalTheory.T.lintegral_infinite_scaling F (Fin n × Fin d) u hupos μ hμ (fun z => ‖e Φ z‖ₑ ^ 2)
  simp only [hc Φ hΦ, enorm_mul, mul_pow, blkScale_eq] at hU
  rw [lintegral_const_mul' _ _ (by simp), hsc] at hU
  set P := ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F) with hPdef
  have hPpos : 0 < ∏ j, u j ^ Module.finrank ℚ F := Finset.prod_pos fun j _ => pow_pos (hupos j) _
  have hP0 : P ≠ 0 := by rw [hPdef]; exact (ENNReal.ofReal_pos.2 hPpos).ne'
  have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hk : ‖c‖ₑ ^ 2 * P⁻¹ = 1 := by
    rw [← mul_assoc] at hU
    exact (ENNReal.mul_eq_right hI0 hIt).1 hU
  have hk' : ‖c‖ₑ ^ 2 = P := by
    have := congrArg (· * P) hk
    simpa [mul_assoc, ENNReal.inv_mul_cancel hP0 hPt] using this
  have hk'' : ENNReal.ofReal (‖c‖ ^ 2) = ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F) := by
    rw [← hPdef, ← hk', ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hsq := (ENNReal.ofReal_eq_ofReal_iff (by positivity) hPpos.le).1 hk''
  rw [hu, prod_scale_pow blk t ht] at hsq
  exact ((pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (ht i).le _) two_ne_zero).1 hsq).le

end GlobalTheory.ThKTorus.ScaleBound

end
