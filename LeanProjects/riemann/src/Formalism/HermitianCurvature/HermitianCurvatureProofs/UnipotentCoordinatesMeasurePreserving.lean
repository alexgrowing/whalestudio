import Formalism.HermitianCurvature.StatementD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSizesJointMean
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualCovolumeChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonJointFirstReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwistedIsRealOrderLattice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalConditionsAndQuotientSplitting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PeriodLatticeFactsSplitOfGeneral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerPairs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShearMeasurability
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFourthCondition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WittOrthonormalBasis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks

noncomputable section

section

open MeasureTheory Filter

namespace Formalism.FourierDecayAlt.P.Dx2.OrbJ

open Formalism.QuantumDeterminants

instance instBorelSS {k r : ℕ} : BorelSpace (Formalism.FourierDecayAlt.B.SS k r) := Prod.borelSpace

instance instBorelSSM {k r : ℕ} : BorelSpace (Formalism.FourierDecayAlt.B.SS k r × Mt k r) := Prod.borelSpace

section

variable {k r : ℕ}

theorem isUnit_of_N {g : Formalism.FourierDecayAlt.B.Mat k r} (hg : g ∈ Nset k r) : IsUnit g.det :=
  (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).unit g hg

theorem isUnit_of_G {g : Formalism.FourierDecayAlt.B.Mat k r} (hg : g ∈ Formalism.FourierDecayAlt.B.GV k r) : IsUnit g.det :=
  (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit g hg

theorem closedR {γ : Formalism.FourierDecayAlt.B.Mat k r} (hγ : IsUnit γ.det) :
    Formalism.FourierDecayAlt.B2.IsClosedSubgroup (Formalism.FourierDecayAlt.C6.Rset γ) := by
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  refine ⟨⟨hN.one_mem, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hγ]; exact hN.one_mem
  · rintro a ⟨ha, ha'⟩ b ⟨hb, hb'⟩
    refine ⟨hN.mul_mem a ha b hb, ?_⟩
    have e : γ⁻¹ * (a * b) * γ = (γ⁻¹ * a * γ) * (γ⁻¹ * b * γ) := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hγ]
    rw [e]; exact hN.mul_mem _ ha' _ hb'
  · rintro a ⟨ha, ha'⟩
    refine ⟨hN.inv_mem a ha, ?_⟩
    have e : γ⁻¹ * a⁻¹ * γ = (γ⁻¹ * a * γ)⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hγ, Matrix.mul_assoc]
    rw [e]; exact hN.inv_mem _ ha'
  · rintro a ⟨ha, -⟩; exact hN.unit a ha
  · have hc : Continuous fun ρ : Formalism.FourierDecayAlt.B.Mat k r => γ⁻¹ * ρ * γ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact hN.closed.inter (hN.closed.preimage hc)

theorem fmoc {U : Set (Formalism.FourierDecayAlt.B.Mat k r)} {μ : Measure (Mt k r)} (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) :
    IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩

theorem sigmaF {U : Set (Formalism.FourierDecayAlt.B.Mat k r)} {μ : Measure (Mt k r)} (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) :
    SigmaFinite μ := by
  have := fmoc h; infer_instance

theorem ae_mem {U : Set (Formalism.FourierDecayAlt.B.Mat k r)} {μ : Measure (Mt k r)} (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ U := by
  rw [ae_iff]; exact h.conc

theorem contL (a : Formalism.FourierDecayAlt.B.Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by
  unfold lmulM
  exact continuous_const.matrix_mul continuous_id

theorem contT (γ : Formalism.FourierDecayAlt.B.Mat k r) :
    Continuous fun z : Formalism.FourierDecayAlt.B.SS k r × Mt k r => Formalism.FourierDecayAlt.C6.actR γ (Matrix.of z.2) z.1 := by
  have hs : Continuous fun z : Formalism.FourierDecayAlt.B.SS k r × Mt k r => (Matrix.of z.2 : Formalism.FourierDecayAlt.B.Mat k r) :=
    continuous_snd
  have ha : Continuous fun z : Formalism.FourierDecayAlt.B.SS k r × Mt k r => (Matrix.of z.1.1.2 : Formalism.FourierDecayAlt.B.Mat k r) :=
    continuous_fst.fst.snd
  have hb : Continuous fun z : Formalism.FourierDecayAlt.B.SS k r × Mt k r => (Matrix.of z.1.2.2 : Formalism.FourierDecayAlt.B.Mat k r) :=
    continuous_fst.snd.snd
  have h1 : Continuous fun z : Formalism.FourierDecayAlt.B.SS k r × Mt k r =>
      (Matrix.of.symm ((Matrix.of z.2 : Formalism.FourierDecayAlt.B.Mat k r) * Matrix.of z.1.1.2) : Mt k r) :=
    hs.matrix_mul ha
  have h2 : Continuous fun z : Formalism.FourierDecayAlt.B.SS k r × Mt k r =>
      (Matrix.of.symm (γ⁻¹ * (Matrix.of z.2 : Formalism.FourierDecayAlt.B.Mat k r) * γ * Matrix.of z.1.2.2) : Mt k r) :=
    ((continuous_const.matrix_mul hs).matrix_mul continuous_const).matrix_mul hb
  exact ((continuous_fst.fst.fst).prodMk h1).prodMk ((continuous_fst.snd.fst).prodMk h2)

end

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem sfSS (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) : SigmaFinite D.μSS := by
  have := sigmaF D.haarW; have := sigmaF D.haarN; have := sigmaF D.haarW'
  unfold Formalism.FourierDecayAlt.B.RealPlaceData.μSS; infer_instance

theorem ae_inSS (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  have := sigmaF D.haarW; have := sigmaF D.haarN; have := sigmaF D.haarW'
  have b1 : ∀ᵐ q ∂(D.μW.prod D.μN), Matrix.of q.1 ∈ UWset k r D.z :=
    (Measure.quasiMeasurePreserving_fst (μ := D.μW) (ν := D.μN)).ae (ae_mem D.haarW)
  have b2 : ∀ᵐ q ∂(D.μW.prod D.μN), Matrix.of q.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd (μ := D.μW) (ν := D.μN)).ae (ae_mem D.haarN)
  have c1 : ∀ᵐ q ∂(D.μW'.prod D.μN), Matrix.of q.1 ∈ UWset k r D.z' :=
    (Measure.quasiMeasurePreserving_fst (μ := D.μW') (ν := D.μN)).ae (ae_mem D.haarW')
  have c2 : ∀ᵐ q ∂(D.μW'.prod D.μN), Matrix.of q.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd (μ := D.μW') (ν := D.μN)).ae (ae_mem D.haarN)
  have d1 : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)),
      Matrix.of p.1.1 ∈ UWset k r D.z ∧ Matrix.of p.1.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae (b1.and b2)
  have d2 : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)),
      Matrix.of p.2.1 ∈ UWset k r D.z' ∧ Matrix.of p.2.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae (c1.and c2)
  unfold Formalism.FourierDecayAlt.B.RealPlaceData.μSS
  filter_upwards [d1, d2] with p h1 h2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

theorem mp_act (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) {ρ : Formalism.FourierDecayAlt.B.Mat k r}
    (hρ : ρ ∈ Formalism.FourierDecayAlt.C6.Rset γ) : MeasurePreserving (Formalism.FourierDecayAlt.C6.actR γ ρ) D.μSS D.μSS := by
  have := sigmaF D.haarW; have := sigmaF D.haarN; have := sigmaF D.haarW'
  have hl : ∀ a ∈ Nset k r, MeasurePreserving (lmulM (k := k) (r := r) a) D.μN D.μN := fun a ha =>
    ⟨(contL a).measurable, D.haarN.left a ha⟩
  have e : Formalism.FourierDecayAlt.C6.actR γ ρ =
      Prod.map (Prod.map id (lmulM (k := k) (r := r) ρ)) (Prod.map id (lmulM (k := k) (r := r) (γ⁻¹ * ρ * γ))) := by
    funext p; rfl
  rw [e]
  unfold Formalism.FourierDecayAlt.B.RealPlaceData.μSS
  exact ((MeasurePreserving.id _).prod (hl ρ hρ.1)).prod ((MeasurePreserving.id _).prod (hl _ hρ.2))

theorem act_act (γ : Formalism.FourierDecayAlt.B.Mat k r) (hγ : IsUnit γ.det) {ρ : Formalism.FourierDecayAlt.B.Mat k r} (hρ : IsUnit ρ.det)
    (p : Formalism.FourierDecayAlt.B.SS k r) : Formalism.FourierDecayAlt.C6.actR γ ρ⁻¹ (Formalism.FourierDecayAlt.C6.actR γ ρ p) = p := by
  unfold Formalism.FourierDecayAlt.C6.actR
  have h1 : (Matrix.of.symm (ρ⁻¹ * Matrix.of (Matrix.of.symm (ρ * Matrix.of p.1.2))) : Mt k r) = p.1.2 := by
    simp only [Equiv.apply_symm_apply]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hρ]; rfl
  have h2 : (Matrix.of.symm (γ⁻¹ * ρ⁻¹ * γ * Matrix.of (Matrix.of.symm (γ⁻¹ * ρ * γ * Matrix.of p.2.2))) : Mt k r)
      = p.2.2 := by
    simp only [Equiv.apply_symm_apply, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hγ, Matrix.nonsing_inv_mul_cancel_left _ _ hρ,
      Matrix.nonsing_inv_mul_cancel_left _ _ hγ]; rfl
  rw [h1, h2]

theorem lam_mul (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) {g h : Formalism.FourierDecayAlt.B.Mat k r}
    (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) :
    Formalism.FourierDecayAlt.B.lam k r z (g * h) = Formalism.FourierDecayAlt.B.lam k r z g + Formalism.FourierDecayAlt.B.lam k r z h := by
  unfold Formalism.FourierDecayAlt.B.lam
  rw [Formalism.QuantumDeterminants.length_additive_holds k r z hz g hg h hh, mul_add, Complex.add_re]

theorem sgs_act (γ : Formalism.FourierDecayAlt.B.Mat k r) (hγ : IsUnit γ.det) {ρ : Formalism.FourierDecayAlt.B.Mat k r}
    (hρu : IsUnit ρ.det) (p : Formalism.FourierDecayAlt.B.SS k r) :
    Formalism.FourierDecayAlt.B.sgs (Formalism.FourierDecayAlt.C6.actR γ ρ p) γ = Formalism.FourierDecayAlt.B.sgs p γ := by
  unfold Formalism.FourierDecayAlt.B.sgs Formalism.FourierDecayAlt.C6.actR
  simp only [Equiv.apply_symm_apply]
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hγ, Matrix.nonsing_inv_mul_cancel_left _ _ hρu]

theorem xiTau_act (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r)
    (hrel : Formalism.FourierDecayAlt.C6.IsRelevant D γ)
    {ρ : Formalism.FourierDecayAlt.B.Mat k r} (hρ : ρ ∈ Formalism.FourierDecayAlt.C6.Rset γ) (p : Formalism.FourierDecayAlt.B.SS k r)
    (hn : Matrix.of p.1.2 ∈ Nset k r) (hn' : Matrix.of p.2.2 ∈ Nset k r) :
    Formalism.FourierDecayAlt.B.xiTau D (1, 1) (Formalism.FourierDecayAlt.C6.actR γ ρ p) = Formalism.FourierDecayAlt.B.xiTau D (1, 1) p := by
  have hpsi : Complex.exp (Complex.I * (Formalism.FourierDecayAlt.B.lam k r D.z ρ : ℂ)) =
      Complex.exp (Complex.I * (Formalism.FourierDecayAlt.B.lam k r D.z' (γ⁻¹ * ρ * γ) : ℂ)) := hrel.2 ρ hρ
  have e1 : Formalism.FourierDecayAlt.B.lam k r D.z (Matrix.of (Formalism.FourierDecayAlt.C6.actR γ ρ p).1.2) =
      Formalism.FourierDecayAlt.B.lam k r D.z ρ + Formalism.FourierDecayAlt.B.lam k r D.z (Matrix.of p.1.2) :=
    lam_mul D.z D.z_mem hρ.1 hn
  have e2 : Formalism.FourierDecayAlt.B.lam k r D.z' (Matrix.of (Formalism.FourierDecayAlt.C6.actR γ ρ p).2.2) =
      Formalism.FourierDecayAlt.B.lam k r D.z' (γ⁻¹ * ρ * γ) + Formalism.FourierDecayAlt.B.lam k r D.z' (Matrix.of p.2.2) :=
    lam_mul D.z' D.z'_mem hρ.2 hn'
  unfold Formalism.FourierDecayAlt.B.xiTau
  rw [e1, e2]
  generalize Formalism.FourierDecayAlt.B.lam k r D.z ρ = a at *
  generalize Formalism.FourierDecayAlt.B.lam k r D.z' (γ⁻¹ * ρ * γ) = c at *
  generalize Formalism.FourierDecayAlt.B.lam k r D.z (Matrix.of p.1.2) = b
  generalize Formalism.FourierDecayAlt.B.lam k r D.z' (Matrix.of p.2.2) = d
  have e : Complex.I * ((((1, 1) : ℝ × ℝ).1 * (a + b) - ((1, 1) : ℝ × ℝ).2 * (c + d) : ℝ) : ℂ) =
      (Complex.I * (a : ℂ) - Complex.I * (c : ℂ)) +
        Complex.I * ((((1, 1) : ℝ × ℝ).1 * b - ((1, 1) : ℝ × ℝ).2 * d : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_sub, hpsi, div_self (Complex.exp_ne_zero _), one_mul]

theorem integrand_act (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r)
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (hrel : Formalism.FourierDecayAlt.C6.IsRelevant D γ)
    {ρ : Formalism.FourierDecayAlt.B.Mat k r} (hρ : ρ ∈ Formalism.FourierDecayAlt.C6.Rset γ) (p : Formalism.FourierDecayAlt.B.SS k r)
    (hn : Matrix.of p.1.2 ∈ Nset k r) (hn' : Matrix.of p.2.2 ∈ Nset k r) :
    Formalism.FourierDecayAlt.D.orbIntegrand D γ F (Formalism.FourierDecayAlt.C6.actR γ ρ p) = Formalism.FourierDecayAlt.D.orbIntegrand D γ F p := by
  have hγ := isUnit_of_G hrel.1
  have hρu := isUnit_of_N hρ.1
  unfold Formalism.FourierDecayAlt.D.orbIntegrand Formalism.FourierDecayAlt.B.rho
  rw [xiTau_act D γ hrel hρ p hn hn', sgs_act γ hγ hρu p]
  rfl

theorem fub (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (μR : Measure (Mt k r))
    [SigmaFinite μR] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (G : Formalism.FourierDecayAlt.B.SS k r → E) (hG : Integrable G D.μSS)
    (θ' : Formalism.FourierDecayAlt.B.SS k r → ℝ) (hθ' : Formalism.FourierDecayAlt.D.IsNormCut D γ μR θ') :
    Integrable (fun z : Formalism.FourierDecayAlt.B.SS k r × Mt k r => θ' (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of z.2) z.1) • G z.1)
        (D.μSS.prod μR) ∧
      ∫ p, G p ∂D.μSS = ∫ x, ∫ p, θ' (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of x) p) • G p ∂D.μSS ∂μR := by
  have := sfSS D
  have hm : Measurable fun z : Formalism.FourierDecayAlt.B.SS k r × Mt k r => θ' (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of z.2) z.1) :=
    hθ'.1.comp (contT γ).measurable
  have hAE : AEStronglyMeasurable
      (fun z : Formalism.FourierDecayAlt.B.SS k r × Mt k r => θ' (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of z.2) z.1) • G z.1)
      (D.μSS.prod μR) :=
    hm.aestronglyMeasurable.smul hG.aestronglyMeasurable.comp_fst
  have hint : ∀ p, D.inSS p → Integrable (fun x : Mt k r => θ' (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of x) p)) μR := by
    intro p hp
    by_contra h
    have h1 := hθ'.2.2 p hp
    rw [integral_undef h] at h1
    exact zero_ne_one h1
  have hn : ∀ q, ‖θ' q‖ = θ' q := fun q => Real.norm_of_nonneg (hθ'.2.1 q)
  have hI : Integrable
      (fun z : Formalism.FourierDecayAlt.B.SS k r × Mt k r => θ' (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of z.2) z.1) • G z.1)
      (D.μSS.prod μR) := by
    rw [integrable_prod_iff hAE]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_inSS D] with p hp
      exact (hint p hp).smul_const (G p)
    · refine hG.norm.congr ?_
      filter_upwards [ae_inSS D] with p hp
      simp only [norm_smul, hn]
      rw [integral_mul_const, hθ'.2.2 p hp, one_mul]
  refine ⟨hI, ?_⟩
  calc ∫ p, G p ∂D.μSS
      = ∫ p, ∫ x, θ' (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of x) p) • G p ∂μR ∂D.μSS := by
        apply integral_congr_ae
        filter_upwards [ae_inSS D] with p hp
        rw [integral_smul_const, hθ'.2.2 p hp, one_smul]
    _ = ∫ z, θ' (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of z.2) z.1) • G z.1 ∂(D.μSS.prod μR) :=
        (integral_prod _ hI).symm
    _ = ∫ x, ∫ p, θ' (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of x) p) • G p ∂D.μSS ∂μR := integral_prod_symm _ hI

end

end Formalism.FourierDecayAlt.P.Dx2.OrbJ

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Filter Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Dx2.OrbJ

theorem orbital_integral_indep_choice : Formalism.FourierDecayAlt.D.OrbJIndep := by
  intro k r Wp Wq _ _ _ _ D γ μR hrel hR F θ θ' hθ hθ' hi hi'
  by_cases hE : CompleteSpace (Wq →L[ℂ] Wp)
  swap
  · simp only [integral, dif_neg hE]
  have : SigmaFinite μR := sigmaF hR
  have := sfSS D
  have hγ := isUnit_of_G hrel.1
  obtain ⟨-, E1⟩ := fub D γ μR (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) hi θ' hθ'
  obtain ⟨I2, E2⟩ := fub D γ μR (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) hi' θ hθ
  rw [E1, E2]
  have hinv : μR.map Formalism.FourierDecayAlt.B2.invM = μR :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μR (closedR hγ) hR
  have haem : AEMeasurable Formalism.FourierDecayAlt.B2.invM μR := by
    by_contra h
    have h0 := Measure.map_of_not_aemeasurable h
    rw [hinv] at h0
    exact hR.ne_zero h0
  have H'm : AEStronglyMeasurable (fun x : Mt k r => ∫ q, θ (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of x) q) •
      (θ' q • Formalism.FourierDecayAlt.D.orbIntegrand D γ F q) ∂D.μSS) μR :=
    I2.integral_prod_right.aestronglyMeasurable
  have hpt : ∀ᵐ x ∂μR, (∫ p, θ' (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of x) p) •
      (θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) ∂D.μSS) =
      ∫ q, θ (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of (Formalism.FourierDecayAlt.B2.invM x)) q) •
        (θ' q • Formalism.FourierDecayAlt.D.orbIntegrand D γ F q) ∂D.μSS := by
    filter_upwards [ae_mem hR] with x hx
    have hmp := mp_act D γ hx
    have hρu : IsUnit (Matrix.of x : Formalism.FourierDecayAlt.B.Mat k r).det := isUnit_of_N hx.1
    have hKm : AEStronglyMeasurable (fun q => θ (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of (Formalism.FourierDecayAlt.B2.invM x)) q) •
        (θ' q • Formalism.FourierDecayAlt.D.orbIntegrand D γ F q)) (Measure.map (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of x)) D.μSS) := by
      rw [hmp.map_eq]
      exact (hθ.1.comp (((contT γ).comp (continuous_id.prodMk continuous_const)).measurable)).aestronglyMeasurable.smul
        hi'.aestronglyMeasurable
    have hmap := integral_map hmp.measurable.aemeasurable hKm
    rw [hmp.map_eq] at hmap
    rw [hmap]
    apply integral_congr_ae
    filter_upwards [ae_inSS D] with p hp
    have hc : Formalism.FourierDecayAlt.C6.actR γ (Matrix.of (Formalism.FourierDecayAlt.B2.invM x)) (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of x) p) = p :=
      act_act γ hγ hρu p
    rw [hc, integrand_act D γ F hrel hx p hp.2.1 hp.2.2.2]
    exact smul_comm _ _ _
  calc ∫ x, ∫ p, θ' (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of x) p) • (θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) ∂D.μSS ∂μR
      = ∫ x, (fun y : Mt k r => ∫ q, θ (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of y) q) •
          (θ' q • Formalism.FourierDecayAlt.D.orbIntegrand D γ F q) ∂D.μSS) (Formalism.FourierDecayAlt.B2.invM x) ∂μR := integral_congr_ae hpt
    _ = ∫ y, ∫ q, θ (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of y) q) •
          (θ' q • Formalism.FourierDecayAlt.D.orbIntegrand D γ F q) ∂D.μSS ∂(μR.map Formalism.FourierDecayAlt.B2.invM) :=
        (integral_map haem (by rw [hinv]; exact H'm)).symm
    _ = _ := by rw [hinv]

end Formalism.FourierDecayAlt.P

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.Dx2.MN

variable {k ρ : ℕ}

theorem eB_mid (i : Fin (2 * ρ + k + 1)) : U.eB k 1 ρ (Sum.inl (Sum.inr i)) = levPos k 1 ρ i := by
  ext; rw [Ux3.block_index_middle_val]; simp [levPos]; omega

theorem eB_first_val : (U.eB k 1 ρ (Sum.inl (Sum.inl 0))).val = 0 := by rw [Ux3.block_index_first_val]; rfl

theorem eB_last_eq : U.eB k 1 ρ (Sum.inr 0) = B2x4.lastI k ρ := by
  ext; rw [Ux3.block_index_last_val]; simp [B2x4.lastI]; omega

theorem herm_bvec_lift (y : Fin (2 * ρ + k + 1) → ℂ) (q : Fin (2 * (1 + ρ) + k + 1)) :
    herm (Hpk k (1 + ρ)) (bvec q) (liftVec k 1 ρ y) = ∑ j, star (y j) * Hpk k (1 + ρ) (levPos k 1 ρ j) q := by
  have h : herm (Hpk k (1 + ρ)) (bvec q) (liftVec k 1 ρ y) = ∑ p, star (liftVec k 1 ρ y p) * Hpk k (1 + ρ) p q := by
    simp [herm, dotProduct, mulVec, bvec, Pi.single_apply]
  rw [h, B2x4.sum_lift]
  · simp only [B2x4.liftVec_levPos]
  · intro p hp; rw [B2x4.liftVec_out k ρ y p hp]; simp

theorem hpk_lev_first (j : Fin (2 * ρ + k + 1)) (q : Fin (2 * (1 + ρ) + k + 1)) (hq : q.val = 0) :
    Hpk k (1 + ρ) (levPos k 1 ρ j) q = 0 := by
  have := j.isLt
  unfold Hpk levPos
  split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; simp only [Fin.ext_iff] at *; omega)

theorem hpk_lev_last (j : Fin (2 * ρ + k + 1)) :
    Hpk k (1 + ρ) (levPos k 1 ρ j) (B2x4.lastI k ρ) = 0 := by
  have := j.isLt
  unfold Hpk levPos B2x4.lastI
  split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; simp only [Fin.ext_iff] at *; omega)

theorem herm_self_real (y : Fin (2 * ρ + k + 1) → ℂ) :
    (((herm (Hpk k ρ) y y).re : ℝ) : ℂ) = herm (Hpk k ρ) y y := by
  have h := B2x4.herm_symm _ (B2x4.Hpk_herm k ρ) y y
  apply Complex.ext
  · simp
  · have : (herm (Hpk k ρ) y y).im = 0 := by
      have h2 := congrArg Complex.im h
      simp at h2; linarith
    simp [this]

theorem cHc (c : Matrix (Fin (2 * ρ + k + 1)) (Fin 1) ℂ) :
    (cᴴ * Hpk k ρ * c) 0 0 = herm (Hpk k ρ) (fun i => c i 0) (fun i => c i 0) := by
  simp only [herm, dotProduct, mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

theorem rn_heis (x : U.RC k 1 ρ) : U.Rn k 1 ρ x = B2.heis0 k ρ (fun i => x.1 i 0, x.2.2 0) := by
  obtain ⟨c, q1, q2⟩ := x
  ext p q
  rw [← (U.eB k 1 ρ).apply_symm_apply p, ← (U.eB k 1 ρ).apply_symm_apply q]
  generalize (U.eB k 1 ρ).symm p = a
  generalize (U.eB k 1 ρ).symm q = b
  rw [Ux3.rn_eq, Ux3.block3_apply]
  simp only [B2.heis0, B2x4.heisG_apply, B2x4.goodRowsProjector_apply_eq_sum]
  have hlast : (B2x4.lastI k ρ).val = 2 * (1 + ρ) + k := rfl
  rcases a with ((a | a) | a) <;> rcases b with ((b | b) | b)
  ·
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    rw [herm_bvec_lift]
    simp [eB_first_val, hpk_lev_first _ _ eB_first_val, B2x4.liftVec_out k ρ _ _ (by rw [eB_first_val]; omega)]
    omega
  ·
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    rw [herm_bvec_lift, eB_mid]
    have h1 : U.eB k 1 ρ (Sum.inl (Sum.inl 0)) ≠ levPos k 1 ρ b := by
      intro h; have := congrArg Fin.val h; rw [eB_first_val] at this; simp [levPos] at this
    have h2 : ¬ ((levPos k 1 ρ b).val = 2 * (1 + ρ) + k) := by have := b.isLt; simp [levPos]; omega
    have hw : G.wMat 1 0 0 = 1 := by simp [G.wMat]
    simp only [B2x4.Hpk_levPos, if_neg h1, if_neg h2, eB_first_val, B2x4.liftVec_out k ρ _ _ (by rw [eB_first_val]; omega)]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hw]
  ·
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    rw [herm_bvec_lift, eB_last_eq]
    have h1 : U.eB k 1 ρ (Sum.inl (Sum.inl 0)) ≠ B2x4.lastI k ρ := by
      intro h; have := congrArg Fin.val h; rw [eB_first_val, hlast] at this; omega
    have hw : G.wMat 1 0 0 = 1 := by simp [G.wMat]
    have hs : G.strictUpper q1 0 0 = 0 := by simp [G.strictUpper]
    simp only [hpk_lev_last, if_neg h1, eB_first_val, B2x4.liftVec_out k ρ _ _ (by rw [eB_first_val]; omega), hlast]
    simp [Ux3.wMat_mul_apply, U.skewOf, B2.hb, hs, cHc, herm_self_real]
    ring
  ·
    have hb : b = 0 := Subsingleton.elim _ _
    subst hb
    rw [eB_mid]
    simp only [B2x4.liftVec_levPos]
    have h1 : levPos k 1 ρ a ≠ U.eB k 1 ρ (Sum.inl (Sum.inl 0)) := by
      intro h; have := congrArg Fin.val h; rw [eB_first_val] at this; simp [levPos] at this
    have h2 : ¬ (levPos k 1 ρ a).val = 0 := by simp [levPos]
    have h3 : ¬ (U.eB k 1 ρ (Sum.inl (Sum.inl 0))).val = 2 * (1 + ρ) + k := by rw [eB_first_val]; omega
    rw [if_neg h1, if_neg h2, if_neg h3]
    simp
  ·
    rw [eB_mid, eB_mid]
    simp only [B2x4.liftVec_levPos]
    have h2 : ¬ (levPos k 1 ρ a).val = 0 := by simp [levPos]
    have h3 : ¬ (levPos k 1 ρ b).val = 2 * (1 + ρ) + k := by have := b.isLt; simp [levPos]; omega
    have h4 : (levPos k 1 ρ a = levPos k 1 ρ b) ↔ a = b := by
      constructor
      · intro h; have := congrArg Fin.val h; simp [levPos] at this; exact Fin.ext this
      · intro h; rw [h]
    rw [if_neg h2, if_neg h3]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (fun h => hab (h4.1 h))]; simp [Matrix.one_apply, hab]
  ·
    have hb : b = 0 := Subsingleton.elim _ _
    subst hb
    rw [eB_mid, eB_last_eq]
    simp only [B2x4.liftVec_levPos]
    have h1 : levPos k 1 ρ a ≠ B2x4.lastI k ρ := by
      intro h; have e := congrArg Fin.val h; rw [hlast] at e; have := a.isLt; simp [levPos] at e; omega
    have h2 : ¬ (levPos k 1 ρ a).val = 0 := by simp [levPos]
    rw [if_neg h1, if_neg h2, if_pos hlast]
    simp
  ·
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    rw [eB_last_eq]
    simp only [B2x4.liftVec_last]
    have h1 : B2x4.lastI k ρ ≠ U.eB k 1 ρ (Sum.inl (Sum.inl 0)) := by
      intro h; have := congrArg Fin.val h; rw [eB_first_val, hlast] at this; omega
    have h2 : ¬ (B2x4.lastI k ρ).val = 0 := by rw [hlast]; omega
    have h3 : ¬ (U.eB k 1 ρ (Sum.inl (Sum.inl 0))).val = 2 * (1 + ρ) + k := by rw [eB_first_val]; omega
    rw [if_neg h1, if_neg h2, if_neg h3]
    simp
  ·
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    rw [eB_last_eq, eB_mid]
    simp only [B2x4.liftVec_last]
    have h1 : B2x4.lastI k ρ ≠ levPos k 1 ρ b := by
      intro h; have e := congrArg Fin.val h; rw [hlast] at e; have := b.isLt; simp [levPos] at e; omega
    have h2 : ¬ (B2x4.lastI k ρ).val = 0 := by rw [hlast]; omega
    have h3 : ¬ (levPos k 1 ρ b).val = 2 * (1 + ρ) + k := by have := b.isLt; simp [levPos]; omega
    rw [if_neg h1, if_neg h2, if_neg h3]
    simp
  ·
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    rw [eB_last_eq]
    simp only [B2x4.liftVec_last]
    have h2 : ¬ (B2x4.lastI k ρ).val = 0 := by rw [hlast]; omega
    simp [hlast]

theorem embG_eq (y : B.Mat k ρ) : U.embG k 1 ρ y = ιLev k 1 ρ y := by
  ext p q
  rw [← (U.eB k 1 ρ).apply_symm_apply p, ← (U.eB k 1 ρ).apply_symm_apply q]
  generalize (U.eB k 1 ρ).symm p = a
  generalize (U.eB k 1 ρ).symm q = b
  rw [U.embG, Ux3.block3_apply]
  rcases a with ((a | a) | a) <;> rcases b with ((b | b) | b) <;>
    simp [ιLev, Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val, Matrix.one_apply]
  all_goals (have := a.isLt; have := b.isLt; rw [if_pos (by omega), if_pos (by omega)])

def heisM (x : B2.HPar k ρ) : Mt k (1 + ρ) := B2.heis0 k ρ x

def castMt {a b : ℕ} (h : a = b) (x : Mt k a) : Mt k b := Matrix.of.symm (D.castM h (Matrix.of x))

theorem castM_rfl {a : ℕ} (g : B.Mat k a) : D.castM rfl g = g := by
  ext i j; simp [D.castM]

theorem haar_cast {a b : ℕ} (h : a = b) (μ : Measure (Mt k a)) (hμ : B.IsHaarOn (Nset k a) μ) :
    B.IsHaarOn (Nset k b) (μ.map (castMt h)) := by
  subst h
  have : (castMt (k := k) (rfl : a = a)) = id := by
    funext x; simp [castMt, castM_rfl]
  rw [this, Measure.map_id]; exact hμ

instance isEmpty_upperTriangular_one : IsEmpty (G.UT 1) := ⟨fun ⟨⟨a, b⟩, h⟩ => by
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst ha hb; exact lt_irrefl _ h⟩

def phi (x : U.RC k 1 ρ) : B2.HPar k ρ := (fun i => x.1 i 0, x.2.2 0)

theorem phi_mp : MeasurePreserving (phi (k := k) (ρ := ρ)) volume volume := by
  have h1 : MeasurePreserving (fun (c : Fin (2 * ρ + k + 1) → Fin 1 → ℂ) (i : Fin (2 * ρ + k + 1)) => c i 0)
      volume volume := by
    have := measurePreserving_pi (fun _ : Fin (2 * ρ + k + 1) => (volume : Measure (Fin 1 → ℂ)))
      (fun _ => (volume : Measure ℂ)) (f := fun _ => MeasurableEquiv.funUnique (Fin 1) ℂ)
      (fun _ => measurePreserving_funUnique volume (Fin 1))
    exact this
  have hP : IsProbabilityMeasure (volume : Measure (G.UT 1 → ℂ)) := by
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]; infer_instance
  have h2 : MeasurePreserving (fun (q : (G.UT 1 → ℂ) × (Fin 1 → ℝ)) => q.2 0) volume volume := by
    have a := (measurePreserving_funUnique (volume : Measure ℝ) (Fin 1))
    have b : MeasurePreserving (Prod.snd : (G.UT 1 → ℂ) × (Fin 1 → ℝ) → (Fin 1 → ℝ)) volume volume :=
      measurePreserving_snd
    exact a.comp b
  exact h1.prod h2

theorem castMt_cont {a b : ℕ} (h : a = b) : Continuous (castMt (k := k) h) := by
  subst h
  have : (castMt (k := k) (rfl : a = a)) = id := by
    funext x; simp [castMt, castM_rfl]
  rw [this]; exact continuous_id

theorem muN_succ (ρ : ℕ) [SigmaFinite (D.muN k ρ)] :
    D.muN k (ρ + 1) =
      (((B2.μHeis k ρ).prod ((D.muN k ρ).map (B2.levM k ρ))).map B2.mulM).map (castMt (Nat.add_comm 1 ρ)) := by
  have hfun : (fun x : U.RC k 1 ρ × Mt k ρ =>
      Matrix.of.symm (D.castM (Nat.add_comm 1 ρ) (U.Rn k 1 ρ x.1 * U.embG k 1 ρ (Matrix.of x.2)))) =
      castMt (Nat.add_comm 1 ρ) ∘ B2.mulM ∘
        Prod.map (heisM ∘ phi) (B2.levM k ρ) := by
    funext x
    simp only [Function.comp, castMt, B2.mulM, B2.levM, Prod.map, rn_heis, embG_eq, phi, heisM]
    rfl
  have hh0 : Measurable (heisM (k := k) (ρ := ρ)) := (show Continuous (heisM (k := k) (ρ := ρ)) from B2x5.continuous_heis0 k ρ).measurable
  have hh : Measurable (heisM (k := k) (ρ := ρ) ∘ phi) := hh0.comp phi_mp.measurable
  have hl : Measurable (B2.levM k ρ) := (B2x2.levM_cont k ρ).measurable
  have hm : Measurable (B2.mulM : Mt k (1 + ρ) × Mt k (1 + ρ) → Mt k (1 + ρ)) := B2x2.mulM_cont.measurable
  have hc : Measurable (castMt (k := k) (Nat.add_comm 1 ρ)) := (castMt_cont _).measurable
  have : SFinite (U.muRC k 1 ρ) := by unfold U.muRC; infer_instance
  show ((U.muRC k 1 ρ).prod (D.muN k ρ)).map _ = _
  rw [hfun, ← Measure.map_map hc (hm.comp (hh.prodMap hl)), ← Measure.map_map hm (hh.prodMap hl),
    ← Measure.map_prod_map _ _ hh hl]
  congr 3
  have : (U.muRC k 1 ρ).map (heisM ∘ phi) = ((U.muRC k 1 ρ).map phi).map heisM :=
    (Measure.map_map hh0 phi_mp.measurable).symm
  rw [this, U.muRC, phi_mp.map_eq]; rfl

theorem sigma_of_haar {a : ℕ} {S : Set (B.Mat k a)} {μ : Measure (Mt k a)} (h : B.IsHaarOn S μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem haar_zero : B.IsHaarOn (Nset k 0) (D.muN k 0) := by
  rw [Formalism.FourierDecayAlt.P.unipotent_haar_base_case k]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show Measure.dirac _ _ = 0
    rw [Measure.dirac_apply]; simp only [Set.indicator_apply_eq_zero]; intro h; exact absurd rfl h
  · intro a ha
    rw [Set.mem_singleton_iff] at ha; subst ha
    show Measure.map _ (Measure.dirac _) = Measure.dirac _
    rw [Measure.map_dirac' (B2x5.measurable_lmulM 1)]
    congr 1; simp [lmulM]; rfl
  · intro a ha
    rw [Set.mem_singleton_iff] at ha; subst ha
    show Measure.map _ (Measure.dirac _) = Measure.dirac _
    rw [Measure.map_dirac' (B2x5.measurable_rmulF 1)]
    congr 1; simp [B.rmulF]; rfl
  · intro K _; show Measure.dirac _ K < ⊤; exact measure_lt_top _ _
  · show Measure.dirac _ ≠ 0; exact Measure.dirac_ne_zero

theorem haar : ∀ r : ℕ, B.IsHaarOn (Nset k r) (D.muN k r)
  | 0 => haar_zero
  | ρ + 1 => by
    have ih := haar ρ
    have := sigma_of_haar ih
    rw [muN_succ]
    exact haar_cast _ _ (Formalism.FourierDecayAlt.P.unipotent_haar_recursion k ρ _ ih)

end Formalism.FourierDecayAlt.P.Dx2.MN

end

section

open MeasureTheory Module Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.Dx2.NH

theorem finrank_CV (E : Type) [Field E] [NumberField E] [IsCMField E] :
    finrank ℝ (J.CV E) = 2 * S6.deg E := by
  have h1 := Module.finrank_mul_finrank ℝ ℂ (J.CV E)
  rw [Complex.finrank_real_complex, finrank_euclideanSpace] at h1
  rw [← h1, (Formalism.FourierDecayAlt.P.degreeFacts_statement E).2.1]

theorem nhat : D.NhatCovol := by
  intro E _ _ _ hU g ν s hg
  obtain ⟨hd, hs, hc⟩ := Formalism.FourierDecayAlt.P.block_frame Formalism.FourierDecayAlt.P.lattice_facts_general
    Formalism.FourierDecayAlt.P.euclidean_frame E hU g ν s hg
  have hrd : 0 < S6.rd E := Formalism.FourierDecayAlt.P.Jx4.rd_pos E
  set c : ℝ := S6.rd E ^ (-ν) with hcdef
  have hc0 : c ≠ 0 := (zpow_pos hrd _).ne'
  have hci : c⁻¹ ≠ 0 := inv_ne_zero hc0
  set L := J.eLat E (S6.perLat E g ν s) c
  have : DiscreteTopology L := hd
  have : IsZLattice ℝ L := ⟨hs⟩
  have key : J.eLat E (S6.perLat E g ν s) 1 =
      ZLattice.comap ℝ L (Formalism.FourierDecayAlt.P.S6x5.scalInv (J.CV E) c⁻¹ hci).toLinearMap := by
    ext x
    simp only [J.eLat, ZLattice.comap, Submodule.mem_map, Submodule.mem_comap, L]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t, ht, ?_⟩
      show J.semb E c t = (Formalism.FourierDecayAlt.P.S6x5.scalInv (J.CV E) c⁻¹ hci) (J.semb E 1 t)
      rw [Formalism.FourierDecayAlt.P.S6x5.scalInv_apply, Formalism.FourierDecayAlt.P.Jx3.semb_apply, Formalism.FourierDecayAlt.P.Jx3.semb_apply, inv_inv, one_smul]
    · rintro ⟨t, ht, hx⟩
      refine ⟨t, ht, ?_⟩
      show J.semb E 1 t = x
      have hx' : J.semb E c t = c • x := by
        change J.semb E c t = (Formalism.FourierDecayAlt.P.S6x5.scalInv (J.CV E) c⁻¹ hci) x at hx
        rw [hx, Formalism.FourierDecayAlt.P.S6x5.scalInv_apply, inv_inv]
      rw [Formalism.FourierDecayAlt.P.Jx3.semb_apply] at hx'
      rw [Formalism.FourierDecayAlt.P.Jx3.semb_apply, one_smul]
      exact smul_right_injective _ hc0 hx'
  rw [key, Formalism.FourierDecayAlt.P.S6x5.covolume_scal volume L c⁻¹ hci, hc, finrank_CV]
  rw [hcdef, ← zpow_neg, neg_neg, abs_of_pos (zpow_pos hrd _), ← zpow_natCast, ← zpow_mul]
  push_cast
  ring_nf

end Formalism.FourierDecayAlt.P.Dx2.NH

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Formalism.FourierDecayAlt.P.Dx2.Tower

variable {k : ℕ}

theorem lev_eq_embG (o ρ : ℕ) (y : B.Mat k ρ) : ιLev k o ρ y = U.embG k o ρ y := by
  ext p q
  rw [← (U.eB k o ρ).apply_symm_apply p, ← (U.eB k o ρ).apply_symm_apply q]
  generalize (U.eB k o ρ).symm p = a
  generalize (U.eB k o ρ).symm q = b
  rw [U.embG, Ux3.block3_apply]
  rcases a with ((a | a) | a) <;> rcases b with ((b | b) | b) <;>
    simp [ιLev, Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val, Matrix.one_apply]
  all_goals (first | (have := a.isLt; have := b.isLt; rw [if_pos (by omega), if_pos (by omega)]) | (intros; exfalso; omega))

theorem lev_one (o ρ : ℕ) : ιLev k o ρ (1 : B.Mat k ρ) = 1 := by
  rw [lev_eq_embG, U.embG, Ux3.block3_one]

theorem lev_mul (o ρ : ℕ) (a b : B.Mat k ρ) : ιLev k o ρ (a * b) = ιLev k o ρ a * ιLev k o ρ b := by
  rw [lev_eq_embG, lev_eq_embG, lev_eq_embG, U.embG, U.embG, U.embG, Ux3.block3_mul]
  congr 1 <;> simp

theorem lev_GV (o ρ : ℕ) (y : B.Mat k ρ) (hy : y ∈ B.GV k ρ) : ιLev k o ρ y ∈ B.GV k (o + ρ) := by
  rw [lev_eq_embG]; exact (Formalism.FourierDecayAlt.P.slice_membership k o ρ).2.2 y hy

theorem lev_cont (o ρ : ℕ) : Continuous (ιLev k o ρ) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [ιLev]
  split_ifs
  all_goals first | exact (continuous_apply _).comp (continuous_apply _) | exact continuous_const

theorem sum_lift_gen (o ρ : ℕ) (F : Fin (2 * (o + ρ) + k + 1) → ℂ)
    (h : ∀ p : Fin (2 * (o + ρ) + k + 1), ¬ (o ≤ p.val ∧ p.val < 2 * ρ + k + 1 + o) → F p = 0) :
    ∑ p, F p = ∑ j : Fin (2 * ρ + k + 1), F (levPos k o ρ j) := by
  symm
  apply Finset.sum_bij_ne_zero (fun j _ _ => levPos k o ρ j)
  · intro _ _ _; exact Finset.mem_univ _
  · intro a _ _ b _ _ hab
    have := congrArg Fin.val hab; simp [levPos] at this; exact Fin.ext this
  · intro p _ hp
    have hr : o ≤ p.val ∧ p.val < 2 * ρ + k + 1 + o := by
      by_contra hc; exact hp (h p hc)
    refine ⟨⟨p.val - o, by omega⟩, Finset.mem_univ _, ?_, ?_⟩
    · have e : levPos k o ρ ⟨p.val - o, by omega⟩ = p := by ext; simp [levPos]; omega
      rw [e]; exact hp
    · ext; simp [levPos]; omega
  · intro _ _ _; rfl

theorem liftVec_levPos_gen (o ρ : ℕ) (v : Fin (2 * ρ + k + 1) → ℂ) (j : Fin (2 * ρ + k + 1)) :
    liftVec k o ρ v (levPos k o ρ j) = v j := by
  have := j.isLt
  unfold liftVec levPos
  rw [dif_pos (by simp; omega)]
  congr 1; ext; simp

theorem liftVec_out_gen (o ρ : ℕ) (v : Fin (2 * ρ + k + 1) → ℂ) (p : Fin (2 * (o + ρ) + k + 1))
    (hp : ¬ (o ≤ p.val ∧ p.val < 2 * ρ + k + 1 + o)) : liftVec k o ρ v p = 0 := by
  unfold liftVec; rw [dif_neg hp]

theorem lev_levPos (o ρ : ℕ) (y : B.Mat k ρ) (i j : Fin (2 * ρ + k + 1)) :
    ιLev k o ρ y (levPos k o ρ i) (levPos k o ρ j) = y i j := by
  have := i.isLt; have := j.isLt
  unfold ιLev levPos
  rw [dif_pos (by simp; omega), dif_pos (by simp; omega)]
  congr 1 <;> ext <;> simp

theorem lev_out_row (o ρ : ℕ) (y : B.Mat k ρ) (p q : Fin (2 * (o + ρ) + k + 1))
    (hp : ¬ (o ≤ p.val ∧ p.val < 2 * ρ + k + 1 + o)) : ιLev k o ρ y p q = if p = q then 1 else 0 := by
  unfold ιLev; rw [dif_neg hp]

theorem lev_out_col (o ρ : ℕ) (y : B.Mat k ρ) (p q : Fin (2 * (o + ρ) + k + 1))
    (hq : ¬ (o ≤ q.val ∧ q.val < 2 * ρ + k + 1 + o)) : ιLev k o ρ y p q = if p = q then 1 else 0 := by
  unfold ιLev
  by_cases hp : o ≤ p.val ∧ p.val < 2 * ρ + k + 1 + o
  · rw [dif_pos hp, dif_neg hq, if_neg]; intro h; rw [h] at hp; exact hq hp
  · rw [dif_neg hp]

theorem lev_mulVec_lift (o ρ : ℕ) (y : B.Mat k ρ) (v : Fin (2 * ρ + k + 1) → ℂ) :
    ιLev k o ρ y *ᵥ liftVec k o ρ v = liftVec k o ρ (y *ᵥ v) := by
  funext p
  show ∑ q, ιLev k o ρ y p q * liftVec k o ρ v q = _
  rw [sum_lift_gen o ρ _ (fun q hq => by rw [liftVec_out_gen o ρ v q hq, mul_zero])]
  by_cases hp : o ≤ p.val ∧ p.val < 2 * ρ + k + 1 + o
  · have e : p = levPos k o ρ ⟨p.val - o, by omega⟩ := by ext; simp [levPos]; omega
    rw [e, liftVec_levPos_gen]
    simp only [lev_levPos, liftVec_levPos_gen]
    rfl
  · rw [liftVec_out_gen o ρ _ p hp]
    apply Finset.sum_eq_zero
    intro j _
    rw [lev_out_row o ρ y p _ hp, if_neg]
    · simp
    · intro h; apply hp; rw [h]; have := j.isLt; simp [levPos]; omega

theorem lev_mulVec_out (o ρ : ℕ) (y : B.Mat k ρ) (p : Fin (2 * (o + ρ) + k + 1))
    (hp : ¬ (o ≤ p.val ∧ p.val < 2 * ρ + k + 1 + o)) : ιLev k o ρ y *ᵥ bvec p = bvec p := by
  funext i
  simp only [mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [lev_out_col o ρ y i p hp]

theorem bvec_levPos (o ρ : ℕ) (j : Fin (2 * ρ + k + 1)) : bvec (levPos k o ρ j) = liftVec k o ρ (bvec j) := by
  funext p
  by_cases hp : o ≤ p.val ∧ p.val < 2 * ρ + k + 1 + o
  · have e : p = levPos k o ρ ⟨p.val - o, by omega⟩ := by ext; simp [levPos]; omega
    rw [e, liftVec_levPos_gen]
    simp only [bvec, Pi.single_apply]
    congr 1
    apply propext; constructor
    · intro h; have := congrArg Fin.val h; simp [levPos] at this; exact Fin.ext this
    · intro h; rw [h]
  · rw [liftVec_out_gen o ρ _ p hp]
    simp only [bvec, Pi.single_apply]
    rw [if_neg]; intro h; apply hp; rw [h]; have := j.isLt; simp [levPos]; omega

theorem lev_UW (o ρ : ℕ) (z : Fin (2 * ρ + k + 1) → ℂ) (g : B.Mat k ρ) (hg : g ∈ UWset k ρ z) :
    ιLev k o ρ g ∈ UWset k (o + ρ) (liftVec k o ρ z) := by
  refine ⟨lev_GV o ρ g hg.1, fun a => ⟨?_, ?_⟩, ?_⟩
  · by_cases ha : a.val < o
    · exact lev_mulVec_out o ρ g _ (by simp [eI]; omega)
    · have e : eI k (o + ρ) a = levPos k o ρ (eI k ρ ⟨a.val - o, by omega⟩) := by
        ext; simp [eI, levPos]; omega
      rw [e, bvec_levPos, lev_mulVec_lift, (hg.2.1 ⟨a.val - o, by omega⟩).1]
  · by_cases ha : a.val < o
    · exact lev_mulVec_out o ρ g _ (by simp [esI]; omega)
    · have e : esI k (o + ρ) a = levPos k o ρ (esI k ρ ⟨a.val - o, by omega⟩) := by
        ext; simp [esI, levPos]; omega
      rw [e, bvec_levPos, lev_mulVec_lift, (hg.2.1 ⟨a.val - o, by omega⟩).2]
  · rw [lev_mulVec_lift, hg.2.2]

theorem castM_one {a b : ℕ} (h : a = b) : D.castM (k := k) h 1 = 1 := by
  subst h; exact MN.castM_rfl 1

theorem castM_mul {a b : ℕ} (h : a = b) (x y : B.Mat k a) : D.castM h (x * y) = D.castM h x * D.castM h y := by
  subst h; simp only [MN.castM_rfl]

theorem castV_rfl {a : ℕ} (v : Fin (2 * a + k + 1) → ℂ) : D.castV (rfl : a = a) v = v := by
  funext i; simp [D.castV]

theorem castM_UW {a b : ℕ} (h : a = b) (v : Fin (2 * a + k + 1) → ℂ) (g : B.Mat k a) (hg : g ∈ UWset k a v) :
    D.castM h g ∈ UWset k b (D.castV h v) := by
  subst h; rw [MN.castM_rfl, castV_rfl]; exact hg

theorem castM_cont {a b : ℕ} (h : a = b) : Continuous (D.castM (k := k) h) := by
  subst h
  have : D.castM (k := k) (rfl : a = a) = id := funext MN.castM_rfl
  rw [this]; exact continuous_id

theorem herm_wb {m : ℕ} (v : Fin (2 * m + k + 1) → ℂ) (hv : inWb k m v) :
    herm (Hpk k m) v v = herm (Hb k) (wbPart k m v) (wbPart k m v) := by
  have := TwoByOneBlock.herm_jV (k := k) (r := m) (wbPart k m v) (wbPart k m v)
  rwa [TwoByOneBlock.jV_wbPart hv] at this

theorem Tz_eq {m m' : ℕ} (v : Fin (2 * m + k + 1) → ℂ) (v' : Fin (2 * m' + k + 1) → ℂ) (hv : inWb k m v)
    (hv' : inWb k m' v') (h : wbPart k m v = wbPart k m' v') : Tz k m v = Tz k m' v' := by
  unfold Tz; rw [herm_wb v hv, herm_wb v' hv', h]

def zL {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * r + k + 1) → ℂ) : Fin (2 * ρ + k + 1) → ℂ :=
  fun i => z ⟨i.val + o, by omega⟩

theorem zL_wb {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    inWb k ρ (zL o ρ h z) := by
  intro i hi; apply hz; simp only []; omega

theorem zL_wbPart {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * r + k + 1) → ℂ) :
    wbPart k ρ (zL o ρ h z) = wbPart k r z := by
  funext t; simp only [wbPart, zL, wI]; congr 1; ext; simp only []; omega

theorem zL_Tz {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    Tz k ρ (zL o ρ h z) = Tz k r z :=
  Tz_eq _ _ (zL_wb o ρ h z hz) hz (zL_wbPart o ρ h z)

theorem lift_zL {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    D.castV h (liftVec k o ρ (zL o ρ h z)) = z := by
  subst h
  rw [castV_rfl]
  funext p
  by_cases hp : o ≤ p.val ∧ p.val < 2 * ρ + k + 1 + o
  · unfold liftVec; rw [dif_pos hp]; simp only [zL]; congr 1; ext; simp only []; omega
  · rw [liftVec_out_gen o ρ _ p hp, hz p (by omega)]

theorem haar_norm {a : ℕ} {U : Set (B.Mat k a)} {μ : Measure (Mt k a)} (hμ : B.IsHaarOn U μ)
    (hU : IsCompact U) : B.IsHaarOn U ((μ Set.univ)⁻¹ • μ) ∧ ((μ Set.univ)⁻¹ • μ) Set.univ = 1 := by
  have hfin : μ Set.univ < ⊤ := by
    have h1 : μ Set.univ ≤ μ U + μ Uᶜ := measure_univ_le_add_compl _
    rw [hμ.conc, add_zero] at h1
    exact lt_of_le_of_lt h1 (hμ.finite_compact U hU)
  have h0 : μ Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hμ.ne_zero
  have hc0 : (μ Set.univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hfin.ne
  have hct : (μ Set.univ)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr h0
  have hn : ((μ Set.univ)⁻¹ • μ) Set.univ = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hfin.ne]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hn⟩
  · simp [hμ.conc]
  · intro a ha; rw [Measure.map_smul, hμ.left a ha]
  · intro a ha; rw [Measure.map_smul, hμ.right a ha]
  · intro K hK
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hct.lt_top (hμ.finite_compact K hK)
  · intro h; rw [h] at hn; simp at hn

theorem mem_lev {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (a : B.Mat k ρ) (ha : a ∈ UWset k ρ (zL o ρ h z)) : D.castM h (ιLev k o ρ a) ∈ UWset k r z := by
  have := castM_UW h _ _ (lev_UW o ρ _ a ha)
  rwa [lift_zL o ρ h z hz] at this

theorem rep_lev {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (π : B.Mat k r → (E →L[ℂ] E))
    (hπ : IsCRepOn (UWset k r z) π) :
    IsCRepOn (UWset k ρ (zL o ρ h z)) (fun y => π (D.castM h (ιLev k o ρ y))) := by
  refine ⟨?_, fun a ha b hb => ?_⟩
  · simp only [lev_one, castM_one, hπ.1]
  · simp only [lev_mul, castM_mul]
    exact hπ.2 _ (mem_lev o ρ h z hz a ha) _ (mem_lev o ρ h z hz b hb)

theorem sec_lev {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (hz' : inWb k r z') (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hs : IsSection k r z z' μsec) :
    IsSection k ρ (zL o ρ h z) (zL o ρ h z') μsec := by
  unfold IsSection
  rw [zL_Tz o ρ h z hz, zL_Tz o ρ h z' hz', zL_wbPart, zL_wbPart]
  exact hs

def wMeas {m : ℕ} (z : Fin (2 * m + k + 1) → ℂ) (hz : inWb k m z) (hT : 0 < Tz k m z) : Measure (Mt k m) :=
  ((Classical.choose (B2x3.haarW k m z hz hT)) Set.univ)⁻¹ • Classical.choose (B2x3.haarW k m z hz hT)

theorem wMeas_spec {m : ℕ} (z : Fin (2 * m + k + 1) → ℂ) (hz : inWb k m z) (hT : 0 < Tz k m z) :
    B.IsHaarOn (UWset k m z) (wMeas z hz hT) ∧ wMeas z hz hT Set.univ = 1 :=
  haar_norm (Classical.choose_spec (B2x3.haarW k m z hz hT)) (B2x3.compactW k m z hz hT)

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def lvl {r : ℕ} (S : B.RealPlaceData k r Wp Wq) (o ρ : ℕ) (h : o + ρ = r) : B.RealPlaceData k ρ Wp Wq where
  z := zL o ρ h S.z
  z' := zL o ρ h S.z'
  π y := S.π (D.castM h (ιLev k o ρ y))
  π' y := S.π' (D.castM h (ιLev k o ρ y))
  μG := Classical.choose (B2x3.haarG k ρ)
  μW := wMeas (zL o ρ h S.z) (zL_wb o ρ h S.z S.z_mem) (by rw [zL_Tz o ρ h S.z S.z_mem]; exact S.T_pos)
  μN := D.muN k ρ
  μW' := wMeas (zL o ρ h S.z') (zL_wb o ρ h S.z' S.z'_mem) (by rw [zL_Tz o ρ h S.z' S.z'_mem]; exact S.T'_pos)
  μsec := S.μsec
  χ := S.χ
  k_pos := S.k_pos
  z_mem := zL_wb o ρ h S.z S.z_mem
  z'_mem := zL_wb o ρ h S.z' S.z'_mem
  T_pos := by rw [zL_Tz o ρ h S.z S.z_mem]; exact S.T_pos
  T'_pos := by rw [zL_Tz o ρ h S.z' S.z'_mem]; exact S.T'_pos
  π_rep := rep_lev o ρ h S.z S.z_mem S.π S.π_rep
  π'_rep := rep_lev o ρ h S.z' S.z'_mem S.π' S.π'_rep
  π_unitary := fun a ha v => S.π_unitary _ (mem_lev o ρ h S.z S.z_mem a ha) v
  π'_unitary := fun a ha v => S.π'_unitary _ (mem_lev o ρ h S.z' S.z'_mem a ha) v
  π_cont := S.π_cont.comp ((castM_cont h).comp (lev_cont o ρ)).continuousOn
    (fun a ha => mem_lev o ρ h S.z S.z_mem a ha)
  π'_cont := S.π'_cont.comp ((castM_cont h).comp (lev_cont o ρ)).continuousOn
    (fun a ha => mem_lev o ρ h S.z' S.z'_mem a ha)
  haarG := Classical.choose_spec (B2x3.haarG k ρ)
  haarW := (wMeas_spec _ _ _).1
  haarN := MN.haar ρ
  haarW' := (wMeas_spec _ _ _).1
  sec := sec_lev o ρ h S.z S.z' S.z_mem S.z'_mem S.μsec S.sec
  χ_smooth := S.χ_smooth
  χ_supp := S.χ_supp
  χ_int := S.χ_int

def tower {r : ℕ} (S : B.RealPlaceData k r Wp Wq) : ∀ j : ℕ, B.RealPlaceData k (r - j) Wp Wq
  | 0 => S
  | j + 1 => lvl S (min (j + 1) r) (r - (j + 1)) (by omega)

theorem lift_zL' {r : ℕ} (o o' ρ : ℕ) (e : o = o') (h : o + ρ = r) (h' : o' + ρ = r)
    (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    D.castV h' (liftVec k o' ρ (zL o ρ h z)) = z := by
  subst e; exact lift_zL o ρ h z hz

theorem castM_lev_congr {r : ℕ} (o o' ρ : ℕ) (e : o = o') (h : o + ρ = r) (h' : o' + ρ = r) (y : B.Mat k ρ) :
    D.castM h (ιLev k o ρ y) = D.castM h' (ιLev k o' ρ y) := by
  subst e; rfl

theorem castVec_liftVec_zero_level {r : ℕ} (h : 0 + r = r) (z : Fin (2 * r + k + 1) → ℂ) : D.castV h (liftVec k 0 r z) = z := by
  funext p
  simp only [D.castV, liftVec]
  rw [dif_pos (by simp; omega)]
  exact congrArg z (Fin.ext (by simp))

theorem castMat_levelEmbed_zero {r : ℕ} (h : 0 + r = r) (y : B.Mat k r) : D.castM h (ιLev k 0 r y) = y := by
  ext p q
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev]
  rw [dif_pos (by simp; omega), dif_pos (by simp; omega)]
  exact congrArg₂ y (Fin.ext (by simp)) (Fin.ext (by simp))

theorem towerExists : Formalism.FourierDecayAlt.D.TowerExists := by
  intro k r Wp Wq _ _ _ _ S hW hW' hN
  refine ⟨⟨tower S, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · intro j hj
    cases j with
    | zero => exact castVec_liftVec_zero_level _ _
    | succ j => exact lift_zL' (min (j + 1) r) (j + 1) (r - (j + 1)) (by omega) (by omega) (by omega) S.z S.z_mem
  · intro j hj
    cases j with
    | zero => exact castVec_liftVec_zero_level _ _
    | succ j => exact lift_zL' (min (j + 1) r) (j + 1) (r - (j + 1)) (by omega) (by omega) (by omega) S.z' S.z'_mem
  · intro j hj y
    cases j with
    | zero => show S.π y = S.π _; rw [castMat_levelEmbed_zero]
    | succ j =>
      show S.π _ = S.π _
      rw [castM_lev_congr (min (j + 1) r) (j + 1) (r - (j + 1)) (by omega)]
  · intro j hj y
    cases j with
    | zero => show S.π' y = S.π' _; rw [castMat_levelEmbed_zero]
    | succ j =>
      show S.π' _ = S.π' _
      rw [castM_lev_congr (min (j + 1) r) (j + 1) (r - (j + 1)) (by omega)]
  · intro j hj
    cases j with
    | zero => exact ⟨hW, hW', hN⟩
    | succ j =>
      exact ⟨(wMeas_spec _ (zL_wb _ _ _ _ S.z_mem) (by rw [zL_Tz _ _ _ _ S.z_mem]; exact S.T_pos)).2,
        (wMeas_spec _ (zL_wb _ _ _ _ S.z'_mem) (by rw [zL_Tz _ _ _ _ S.z'_mem]; exact S.T'_pos)).2, rfl⟩

end Formalism.FourierDecayAlt.P.Dx2.Tower

end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace Formalism.FourierDecayAlt.P.Dx2.DF

variable {k r : ℕ}

abbrev ee (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) → ℂ := bvec (eI k r a)

abbrev es (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) → ℂ := bvec (esI k r a)

theorem herm_bvec_right (x : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    herm (Hpk k r) x (bvec p) = ∑ j, Hpk k r p j * x j := by
  simp [herm, dotProduct, mulVec, bvec, Pi.single_apply]

theorem hpk_eI (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
  have ha := a.isLt
  unfold Hpk eI esI
  split_ifs with h1 h2 h3 h4 h5 h6 <;> first | rfl | (exfalso; simp only [Fin.ext_iff] at *; omega)

theorem hpk_esI (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  have ha := a.isLt
  unfold Hpk eI esI
  split_ifs with h1 h2 h3 h4 h5 h6 <;> first | rfl | (exfalso; simp only [Fin.ext_iff] at *; omega)

theorem herm_ee (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : herm (Hpk k r) x (ee k r a) = x (esI k r a) := by
  rw [herm_bvec_right]; simp [hpk_eI]

theorem herm_es (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : herm (Hpk k r) x (es k r a) = x (eI k r a) := by
  rw [herm_bvec_right]; simp [hpk_esI]

theorem eI_ne_esI (a b : Fin r) : eI k r a ≠ esI k r b := by
  have := a.isLt; have := b.isLt
  intro h; have h' := congrArg Fin.val h; simp [eI, esI] at h'; omega

theorem eI_inj {a b : Fin r} : eI k r a = eI k r b ↔ a = b := by
  constructor
  · intro h; have h' := congrArg Fin.val h; simp [eI] at h'; exact Fin.ext h'
  · rintro rfl; rfl

theorem esI_inj {a b : Fin r} : esI k r a = esI k r b ↔ a = b := by
  have := a.isLt; have := b.isLt
  constructor
  · intro h; have h' := congrArg Fin.val h; simp [esI] at h'; exact Fin.ext (by omega)
  · rintro rfl; rfl

@[simp] theorem h_ee_ee (a b : Fin r) : herm (Hpk k r) (ee k r a) (ee k r b) = 0 := by
  rw [herm_ee]; simp [bvec, Pi.single_apply, eI_ne_esI]

@[simp] theorem h_ee_es (a b : Fin r) : herm (Hpk k r) (ee k r a) (es k r b) = if a = b then 1 else 0 := by
  rw [herm_es]; simp [bvec, Pi.single_apply, eI_inj, eq_comm]

@[simp] theorem h_es_ee (a b : Fin r) : herm (Hpk k r) (es k r a) (ee k r b) = if a = b then 1 else 0 := by
  rw [herm_ee]; simp [bvec, Pi.single_apply, esI_inj, eq_comm]

@[simp] theorem h_es_es (a b : Fin r) : herm (Hpk k r) (es k r a) (es k r b) = 0 := by
  rw [herm_es]; simp [bvec, Pi.single_apply, (eI_ne_esI b a).symm]

theorem wb_eI {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (a : Fin r) : w (eI k r a) = 0 :=
  hw _ (Or.inl (by simp [eI]))

theorem wb_esI {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (a : Fin r) : w (esI k r a) = 0 :=
  hw _ (Or.inr (by have := a.isLt; simp [esI]; omega))

theorem herm_symm' (u w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) w u = star (herm (Hpk k r) u w) :=
  (B2x4.herm_symm _ (B2x4.Hpk_herm k r) u w).symm

@[simp] theorem h_w_ee {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (a : Fin r) :
    herm (Hpk k r) w (ee k r a) = 0 := by rw [herm_ee, wb_esI hw]

@[simp] theorem h_w_es {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (a : Fin r) :
    herm (Hpk k r) w (es k r a) = 0 := by rw [herm_es, wb_eI hw]

@[simp] theorem h_ee_w {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (a : Fin r) :
    herm (Hpk k r) (ee k r a) w = 0 := by rw [herm_symm', h_w_ee hw]; simp

@[simp] theorem h_es_w {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (a : Fin r) :
    herm (Hpk k r) (es k r a) w = 0 := by rw [herm_symm', h_w_es hw]; simp

theorem herm_self_alt {z : Fin (2 * r + k + 1) → ℂ} : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have h := B2x4.herm_symm _ (B2x4.Hpk_herm k r) z z
  have him : (herm (Hpk k r) z z).im = 0 := by
    have h2 := congrArg Complex.im h; simp at h2; linarith
  apply Complex.ext <;> simp [Tz, him]

section iso

variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

theorem herm_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin m → ℂ) (w : Fin m → ℂ) :
    herm H (∑ i ∈ s, f i) w = ∑ i ∈ s, herm H (f i) w := by
  simp [herm, Matrix.mulVec_sum, dotProduct_sum]

theorem herm_sum_right {ι : Type*} (s : Finset ι) (f : ι → Fin m → ℂ) (v : Fin m → ℂ) :
    herm H v (∑ i ∈ s, f i) = ∑ i ∈ s, herm H v (f i) := by
  simp [herm, star_sum, sum_dotProduct]

variable {ι : Type*} [Fintype ι]

def smap (u w Y : ι → Fin m → ℂ) (x : Fin m → ℂ) : Fin m → ℂ := x + ∑ i, herm H x (w i) • (Y i - u i)

theorem smap_iso (hH : Hᴴ = H) (u w Y : ι → Fin m → ℂ)
    (h2 : ∀ x j, herm H x (u j) = ∑ i, herm H x (w i) * herm H (u i) (u j))
    (h3 : ∀ i j, herm H (Y i) (Y j) = herm H (u i) (u j))
    (h4 : ∀ x, (∀ j, herm H x (u j) = 0) → ∀ i, herm H x (Y i) = 0)
    (x y : Fin m → ℂ) : herm H (smap H u w Y x) (smap H u w Y y) = herm H x y := by
  set cx := fun i => herm H x (w i)
  set cy := fun i => herm H y (w i)
  set x2 := x - ∑ i, cx i • u i
  set y2 := y - ∑ i, cy i • u i
  have ex : smap H u w Y x = (∑ i, cx i • Y i) + x2 := by
    simp only [smap, x2, cx, smul_sub, Finset.sum_sub_distrib]; abel
  have ey : smap H u w Y y = (∑ i, cy i • Y i) + y2 := by
    simp only [smap, y2, cy, smul_sub, Finset.sum_sub_distrib]; abel
  have ex' : x = (∑ i, cx i • u i) + x2 := by simp [x2]
  have ey' : y = (∑ i, cy i • u i) + y2 := by simp [y2]
  have perp : ∀ v : Fin m → ℂ, ∀ j, herm H (v - ∑ i, herm H v (w i) • u i) (u j) = 0 := by
    intro v j
    rw [B2x4.herm_sub_left, herm_sum_left, h2 v j]
    simp [B2x4.herm_smul_left]
  have px : ∀ j, herm H x2 (u j) = 0 := perp x
  have py : ∀ j, herm H y2 (u j) = 0 := perp y
  have symm : ∀ a b : Fin m → ℂ, herm H a b = star (herm H b a) := fun a b =>
    (B2x4.herm_symm H hH b a).symm
  have t1 : ∀ i, herm H (Y i) y2 = 0 := fun i => by rw [symm, h4 y2 py i]; simp
  have t2 : ∀ j, herm H x2 (Y j) = 0 := fun j => h4 x2 px j
  have t3 : ∀ i, herm H (u i) y2 = 0 := fun i => by rw [symm, py i]; simp
  have expand : ∀ (Z : ι → Fin m → ℂ), (∀ i, herm H (Z i) y2 = 0) → (∀ j, herm H x2 (Z j) = 0) →
      herm H ((∑ i, cx i • Z i) + x2) ((∑ i, cy i • Z i) + y2) =
        (∑ i, ∑ j, cx i * star (cy j) * herm H (Z i) (Z j)) + herm H x2 y2 := by
    intro Z hZ1 hZ2
    rw [B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_add_right, herm_sum_left, herm_sum_left,
      herm_sum_right]
    simp only [B2x4.herm_smul_left, herm_sum_right, B2x4.herm_smul_right, hZ1, hZ2, mul_zero, smul_zero,
      Finset.sum_const_zero, add_zero, zero_add]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [ex, ey, expand Y t1 t2]
  conv_rhs => rw [ex', ey', expand u t3 px]
  simp only [h3]

theorem smap_apply_u (u w Y : ι → Fin m → ℂ) [DecidableEq ι]
    (h1 : ∀ i j, herm H (u i) (w j) = if i = j then 1 else 0) (i : ι) : smap H u w Y (u i) = Y i := by
  simp only [smap, h1, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  abel

theorem smap_fix (u w Y : ι → Fin m → ℂ) (x : Fin m → ℂ) (hx : ∀ i, herm H x (w i) = 0) :
    smap H u w Y x = x := by
  simp [smap, hx]

def smat (u w Y : ι → Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun a b => smap H u w Y (bvec b) a

theorem smat_mulVec (u w Y : ι → Fin m → ℂ) (x : Fin m → ℂ) : smat H u w Y *ᵥ x = smap H u w Y x := by
  ext a
  simp only [smat, mulVec, dotProduct, Matrix.of_apply, smap, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp [bvec, Pi.single_apply]
  · simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [← B2x4.herm_sum H x (w i), Finset.sum_mul]
    apply Finset.sum_congr rfl; intro b _; ring

end iso

theorem smat_UH {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (hH : Hᴴ = H) {ι : Type*} [Fintype ι] (u w Y : ι → Fin m → ℂ)
    (h2 : ∀ x j, herm H x (u j) = ∑ i, herm H x (w i) * herm H (u i) (u j))
    (h3 : ∀ i j, herm H (Y i) (Y j) = herm H (u i) (u j))
    (h4 : ∀ x, (∀ j, herm H x (u j) = 0) → ∀ i, herm H x (Y i) = 0) : smat H u w Y ∈ UH H := by
  apply B2x4.mem_UH_of_herm
  intro x y
  rw [smat_mulVec, smat_mulVec]
  exact smap_iso H hH u w Y h2 h3 h4 x y

section weyl

variable {k r : ℕ} (π : Equiv.Perm (Fin (r + 1)))

def piX (b : Fin r) : Fin r := if h : π b.castSucc = Fin.last r then b else (π b.castSucc).castPred h

theorem piX_spec (b : Fin r) (h : π b.castSucc ≠ Fin.last r) : (piX π b).castSucc = π b.castSucc := by
  simp [piX, h]

theorem piX_inj {b c : Fin r} (hb : π b.castSucc ≠ Fin.last r) (hc : π c.castSucc ≠ Fin.last r) :
    piX π b = piX π c ↔ b = c := by
  constructor
  · intro h
    have h' := congrArg Fin.castSucc h
    rw [piX_spec π b hb, piX_spec π c hc] at h'
    exact Fin.castSucc_injective _ (π.injective h')
  · rintro rfl; rfl

theorem piX_ne {b a : Fin r} (hb : π b.castSucc ≠ Fin.last r) (ha : π (Fin.last r) = a.castSucc) : piX π b ≠ a := by
  intro h
  have h' := congrArg Fin.castSucc h
  rw [piX_spec π b hb, ← ha] at h'
  exact Fin.castSucc_ne_last b (π.injective h')

end weyl

section caseA

variable {k r : ℕ}

def uB (z' ν' : Fin (2 * r + k + 1) → ℂ) : (Fin r ⊕ Fin r) ⊕ Fin 2 → Fin (2 * r + k + 1) → ℂ
  | Sum.inl (Sum.inl b) => ee k r b
  | Sum.inl (Sum.inr b) => es k r b
  | Sum.inr j => ![z', ν'] j

def wB (z' ν' : Fin (2 * r + k + 1) → ℂ) (s : ℝ) : (Fin r ⊕ Fin r) ⊕ Fin 2 → Fin (2 * r + k + 1) → ℂ
  | Sum.inl (Sum.inl b) => es k r b
  | Sum.inl (Sum.inr b) => ee k r b
  | Sum.inr j => ![(-(1 / (s : ℂ) ^ 2)) • z', ν'] j

variable {z' ν' : Fin (2 * r + k + 1) → ℂ} {s : ℝ}

theorem herm_neg_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u w : Fin m → ℂ) : herm H u (-w) = -herm H u w := by
  simp [herm]

theorem herm_neg_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u w : Fin m → ℂ) : herm H (-u) w = -herm H u w := by
  simp [herm, Matrix.mulVec_neg]

theorem herm_rsmul_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (a : ℝ) (u w : Fin m → ℂ) :
    herm H (a • u) w = (a : ℂ) * herm H u w := by
  rw [← B2x4.herm_smul_left]; congr 1
  all_goals (ext i; simp [Complex.real_smul])

theorem herm_rsmul_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (a : ℝ) (u w : Fin m → ℂ) :
    herm H u (a • w) = (a : ℂ) * herm H u w := by
  have : herm H u ((a : ℂ) • w) = star (a : ℂ) * herm H u w := B2x4.herm_smul_right H _ u w
  rw [show (a • w) = ((a : ℂ) • w) by ext i; simp [Complex.real_smul], this]
  all_goals simp only [Complex.star_def, Complex.conj_ofReal]

theorem inWb_smul {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (c : ℂ) : inWb k r (c • w) := by
  intro i hi; simp [hw i hi]

theorem herm_zν (hνz : herm (Hpk k r) ν' z' = 0) : herm (Hpk k r) z' ν' = 0 := by
  rw [herm_symm', hνz]; simp

theorem uw_dual (hz : inWb k r z') (hν : inWb k r ν') (hs : 0 < s)
    (hzz : herm (Hpk k r) z' z' = -((s : ℂ) ^ 2)) (hνz : herm (Hpk k r) ν' z' = 0)
    (hνν : herm (Hpk k r) ν' ν' = 1) (i j : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    herm (Hpk k r) (uB z' ν' i) (wB z' ν' s j) = if i = j then 1 else 0 := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rcases i with ((b | b) | i) <;> rcases j with ((c | c) | j)
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [uB, wB, B2x4.herm_smul_right, herm_neg_right, hz, hν, herm_zν hνz, hzz, hνz, hνν, eq_comm]
  all_goals field_simp

theorem uw_complete (hz : inWb k r z') (hν : inWb k r ν') (hs : 0 < s)
    (hzz : herm (Hpk k r) z' z' = -((s : ℂ) ^ 2)) (hνz : herm (Hpk k r) ν' z' = 0)
    (hνν : herm (Hpk k r) ν' ν' = 1) (x : Fin (2 * r + k + 1) → ℂ) (j : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    herm (Hpk k r) x (uB z' ν' j) =
      ∑ i, herm (Hpk k r) x (wB z' ν' s i) * herm (Hpk k r) (uB z' ν' i) (uB z' ν' j) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two]
  rcases j with ((c | c) | j)
  all_goals try fin_cases j
  all_goals simp [uB, wB, B2x4.herm_smul_right, herm_neg_right, hz, hν, herm_zν hνz, hzz, hνz, hνν]
  field_simp

variable (π : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ)

def YA (z' ν' : Fin (2 * r + k + 1) → ℂ) (s : ℝ) (a0 b0 : Fin r) :
    (Fin r ⊕ Fin r) ⊕ Fin 2 → Fin (2 * r + k + 1) → ℂ
  | Sum.inl (Sum.inl b) => if b = b0 then (d b0.castSucc / (s : ℂ)) • (ν' - (s : ℂ)⁻¹ • z')
      else d b.castSucc • es k r (piX π b)
  | Sum.inl (Sum.inr b) => if b = b0 then (2 * conj (d b0.castSucc))⁻¹ • (z' + (s : ℂ) • ν')
      else (conj (d b.castSucc))⁻¹ • ee k r (piX π b)
  | Sum.inr j => ![d (Fin.last r) • es k r a0 - ((s : ℂ) ^ 2 / (2 * conj (d (Fin.last r)))) • ee k r a0,
      ((s : ℂ) / (2 * conj (d (Fin.last r)))) • ee k r a0 + (d (Fin.last r) / (s : ℂ)) • es k r a0] j

theorem YA_gram (hz : inWb k r z') (hν : inWb k r ν') (hs : 0 < s)
    (hzz : herm (Hpk k r) z' z' = -((s : ℂ) ^ 2)) (hνz : herm (Hpk k r) ν' z' = 0)
    (hνν : herm (Hpk k r) ν' ν' = 1) (hd : ∀ a, d a ≠ 0) (a0 b0 : Fin r)
    (ha : π (Fin.last r) = a0.castSucc) (hb : π b0.castSucc = Fin.last r) (i j : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    herm (Hpk k r) (YA π d z' ν' s a0 b0 i) (YA π d z' ν' s a0 b0 j) =
      herm (Hpk k r) (uB z' ν' i) (uB z' ν' j) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hne : ∀ b : Fin r, b ≠ b0 → π b.castSucc ≠ Fin.last r := by
    intro b hb' h; rw [← hb] at h; exact hb' (Fin.castSucc_injective _ (π.injective h))
  have hdl := hd (Fin.last r)
  have hdb := hd b0.castSucc
  have hdl' : conj (d (Fin.last r)) ≠ 0 := by simpa using hdl
  have hdb' : conj (d b0.castSucc) ≠ 0 := by simpa using hdb
  have hzν := herm_zν hνz
  rcases i with ((b | b) | i) <;> rcases j with ((c | c) | j)
  all_goals try fin_cases i
  all_goals try fin_cases j
  · by_cases hb0 : b = b0 <;> by_cases hc0 : c = b0
    · subst hb0 hc0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · subst hb0; have h2 := hne c hc0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hc0, Ne.symm hc0, piX_ne π h2 ha, (piX_ne π h2 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · subst hc0; have h1 := hne b hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, Ne.symm hb0, piX_ne π h1 ha, (piX_ne π h1 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · have h1 := hne b hb0; have h2 := hne c hc0
      simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, hc0, piX_inj π h1 h2, piX_ne π h1 ha, piX_ne π h2 ha]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · by_cases hb0 : b = b0 <;> by_cases hc0 : c = b0
    · subst hb0 hc0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · subst hb0; have h2 := hne c hc0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hc0, Ne.symm hc0, piX_ne π h2 ha, (piX_ne π h2 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · subst hc0; have h1 := hne b hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, Ne.symm hb0, piX_ne π h1 ha, (piX_ne π h1 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · have h1 := hne b hb0; have h2 := hne c hc0
      simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, hc0, piX_inj π h1 h2, piX_ne π h1 ha, piX_ne π h2 ha]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · by_cases hb0 : b = b0
    · subst hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · have h1 := hne b hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, piX_ne π h1 ha, (piX_ne π h1 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · by_cases hb0 : b = b0
    · subst hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · have h1 := hne b hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, piX_ne π h1 ha, (piX_ne π h1 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · by_cases hb0 : b = b0 <;> by_cases hc0 : c = b0
    · subst hb0 hc0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · subst hb0; have h2 := hne c hc0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hc0, Ne.symm hc0, piX_ne π h2 ha, (piX_ne π h2 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · subst hc0; have h1 := hne b hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, Ne.symm hb0, piX_ne π h1 ha, (piX_ne π h1 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · have h1 := hne b hb0; have h2 := hne c hc0
      simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, hc0, piX_inj π h1 h2, piX_ne π h1 ha, piX_ne π h2 ha]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · by_cases hb0 : b = b0 <;> by_cases hc0 : c = b0
    · subst hb0 hc0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · subst hb0; have h2 := hne c hc0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hc0, Ne.symm hc0, piX_ne π h2 ha, (piX_ne π h2 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · subst hc0; have h1 := hne b hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, Ne.symm hb0, piX_ne π h1 ha, (piX_ne π h1 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · have h1 := hne b hb0; have h2 := hne c hc0
      simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, hc0, piX_inj π h1 h2, piX_ne π h1 ha, piX_ne π h2 ha]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · by_cases hb0 : b = b0
    · subst hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · have h1 := hne b hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, piX_ne π h1 ha, (piX_ne π h1 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · by_cases hb0 : b = b0
    · subst hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · have h1 := hne b hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, piX_ne π h1 ha, (piX_ne π h1 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · by_cases hb0 : c = b0
    · subst hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · have h1 := hne c hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, piX_ne π h1 ha, (piX_ne π h1 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · by_cases hb0 : c = b0
    · subst hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · have h1 := hne c hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, piX_ne π h1 ha, (piX_ne π h1 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · by_cases hb0 : c = b0
    · subst hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · have h1 := hne c hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, piX_ne π h1 ha, (piX_ne π h1 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · by_cases hb0 : c = b0
    · subst hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
    · have h1 := hne c hb0; simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal, hb0, piX_ne π h1 ha, (piX_ne π h1 ha).symm]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])
  · simp [YA, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]; all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]) <;> (try field_simp) <;> (try ring) <;> (try simp [hd])

theorem YA_perp (a0 b0 : Fin r) (x : Fin (2 * r + k + 1) → ℂ)
    (hx : ∀ j, herm (Hpk k r) x (uB z' ν' j) = 0) (i : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    herm (Hpk k r) x (YA π d z' ν' s a0 b0 i) = 0 := by
  have he : ∀ b, herm (Hpk k r) x (ee k r b) = 0 := fun b => hx (Sum.inl (Sum.inl b))
  have hs : ∀ b, herm (Hpk k r) x (es k r b) = 0 := fun b => hx (Sum.inl (Sum.inr b))
  have hz : herm (Hpk k r) x z' = 0 := hx (Sum.inr 0)
  have hn : herm (Hpk k r) x ν' = 0 := hx (Sum.inr 1)
  rcases i with ((b | b) | i)
  · simp only [YA]; split_ifs <;> simp [B2x4.herm_smul_right, herm_rsmul_right, B2x4.herm_sub_right, B2x4.herm_add_right, he, hs, hz, hn]
  · simp only [YA]; split_ifs <;> simp [B2x4.herm_smul_right, herm_rsmul_right, B2x4.herm_sub_right, B2x4.herm_add_right, he, hs, hz, hn]
  · fin_cases i <;> simp [YA, B2x4.herm_smul_right, herm_rsmul_right, B2x4.herm_sub_right, B2x4.herm_add_right, he, hs, hz, hn]

theorem piX_injB (hB : π (Fin.last r) = Fin.last r) (b c : Fin r) : piX π b = piX π c ↔ b = c := by
  have hne : ∀ b : Fin r, π b.castSucc ≠ Fin.last r := by
    intro b h; rw [← hB] at h; exact Fin.castSucc_ne_last b (π.injective h)
  exact piX_inj π (hne b) (hne c)

def YB (z' ν' : Fin (2 * r + k + 1) → ℂ) (s κ : ℝ) : (Fin r ⊕ Fin r) ⊕ Fin 2 → Fin (2 * r + k + 1) → ℂ
  | Sum.inl (Sum.inl b) => d b.castSucc • es k r (piX π b)
  | Sum.inl (Sum.inr b) => (conj (d b.castSucc))⁻¹ • ee k r (piX π b)
  | Sum.inr j => ![(d (Fin.last r) / (s : ℂ) ^ 2) • (((κ : ℂ) * (s : ℂ) ^ 2) • ν' - z'),
      (d (Fin.last r) / (s : ℂ) ^ 2) • (ν' - (κ : ℂ) • z')] j

theorem YB_gram (hz : inWb k r z') (hν : inWb k r ν') (hs : 0 < s)
    (hzz : herm (Hpk k r) z' z' = -((s : ℂ) ^ 2)) (hνz : herm (Hpk k r) ν' z' = 0)
    (hνν : herm (Hpk k r) ν' ν' = 1) (hd : ∀ a, d a ≠ 0) (κ : ℝ)
    (hκ : (κ : ℂ) ^ 2 * (s : ℂ) ^ 2 * (d (Fin.last r) * conj (d (Fin.last r))) =
      d (Fin.last r) * conj (d (Fin.last r)) - (s : ℂ) ^ 4)
    (hB : π (Fin.last r) = Fin.last r) (i j : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    herm (Hpk k r) (YB π d z' ν' s κ i) (YB π d z' ν' s κ j) =
      herm (Hpk k r) (uB z' ν' i) (uB z' ν' j) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hne : ∀ b : Fin r, π b.castSucc ≠ Fin.last r := by
    intro b h; rw [← hB] at h; exact Fin.castSucc_ne_last b (π.injective h)
  have hzν := herm_zν hνz
  rcases i with ((b | b) | i) <;> rcases j with ((c | c) | j)
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [YB, uB, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right,
    B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right,
    h_w_ee hz, h_w_ee hν, h_w_es hz, h_w_es hν, h_ee_w hz, h_ee_w hν, h_es_w hz, h_es_w hν, hzz, hνz, hνν, hzν,
    Complex.conj_ofReal, piX_injB π hB, hd]
  all_goals (try split_ifs with hh) <;> (try subst hh) <;> (try simp [hd])
  all_goals (try (right; field_simp; ring_nf; done))
  all_goals (field_simp; first | linear_combination hκ | linear_combination -hκ)

end caseA

section sigma

variable {k r : ℕ} {z' ν' : Fin (2 * r + k + 1) → ℂ} {s : ℝ}

theorem YB_perp (π : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (κ : ℝ) (x : Fin (2 * r + k + 1) → ℂ)
    (hx : ∀ j, herm (Hpk k r) x (uB z' ν' j) = 0) (i : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    herm (Hpk k r) x (YB π d z' ν' s κ i) = 0 := by
  have he : ∀ b, herm (Hpk k r) x (ee k r b) = 0 := fun b => hx (Sum.inl (Sum.inl b))
  have hs : ∀ b, herm (Hpk k r) x (es k r b) = 0 := fun b => hx (Sum.inl (Sum.inr b))
  have hz : herm (Hpk k r) x z' = 0 := hx (Sum.inr 0)
  have hn : herm (Hpk k r) x ν' = 0 := hx (Sum.inr 1)
  rcases i with ((b | b) | i)
  · simp [YB, B2x4.herm_smul_right, he, hs]
  · simp [YB, B2x4.herm_smul_right, he, hs]
  · fin_cases i <;> simp [YB, B2x4.herm_smul_right, herm_rsmul_right, B2x4.herm_sub_right, B2x4.herm_add_right, hz, hn]

variable (Y : (Fin r ⊕ Fin r) ⊕ Fin 2 → Fin (2 * r + k + 1) → ℂ)

theorem sig_UH (hz : inWb k r z') (hν : inWb k r ν') (hs : 0 < s)
    (hzz : herm (Hpk k r) z' z' = -((s : ℂ) ^ 2)) (hνz : herm (Hpk k r) ν' z' = 0)
    (hνν : herm (Hpk k r) ν' ν' = 1)
    (h3 : ∀ i j, herm (Hpk k r) (Y i) (Y j) = herm (Hpk k r) (uB z' ν' i) (uB z' ν' j))
    (h4 : ∀ x, (∀ j, herm (Hpk k r) x (uB z' ν' j) = 0) → ∀ i, herm (Hpk k r) x (Y i) = 0) :
    smat (Hpk k r) (uB z' ν') (wB z' ν' s) Y ∈ UH (Hpk k r) :=
  smat_UH _ (B2x4.Hpk_herm k r) _ _ _ (uw_complete hz hν hs hzz hνz hνν) h3 h4

theorem sig_u (hz : inWb k r z') (hν : inWb k r ν') (hs : 0 < s)
    (hzz : herm (Hpk k r) z' z' = -((s : ℂ) ^ 2)) (hνz : herm (Hpk k r) ν' z' = 0)
    (hνν : herm (Hpk k r) ν' ν' = 1) (i : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    smat (Hpk k r) (uB z' ν') (wB z' ν' s) Y *ᵥ uB z' ν' i = Y i := by
  rw [smat_mulVec]; exact smap_apply_u _ _ _ _ (uw_dual hz hν hs hzz hνz hνν) i

theorem sig_fix (x : Fin (2 * r + k + 1) → ℂ) (hx : ∀ i, herm (Hpk k r) x (wB z' ν' s i) = 0) :
    smat (Hpk k r) (uB z' ν') (wB z' ν' s) Y *ᵥ x = x := by
  rw [smat_mulVec]; exact smap_fix _ _ _ _ x hx

end sigma

section frame

variable {k r : ℕ}

def Wb (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := fun i => if r ≤ i.val ∧ i.val ≤ r + k then v i else 0

theorem prW_eq (z v : Fin (2 * r + k + 1) → ℂ) :
    D.prW k r z v = Wb v - (herm (Hpk k r) (Wb v) z / herm (Hpk k r) z z) • z := rfl

theorem Wb_of_inWb {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) : Wb w = w := by
  ext i; simp only [Wb]; split_ifs with h
  · rfl
  · exact (hw i (by omega)).symm

theorem inWb_of_coords {w : Fin (2 * r + k + 1) → ℂ} (h1 : ∀ a : Fin r, w (eI k r a) = 0)
    (h2 : ∀ a : Fin r, w (esI k r a) = 0) : inWb k r w := by
  intro i hi
  rcases hi with hi | hi
  · have := h1 ⟨i.val, hi⟩; simpa [eI] using this
  · have hlt : 2 * r + k - i.val < r := by omega
    have := h2 ⟨2 * r + k - i.val, hlt⟩
    have e : esI k r ⟨2 * r + k - i.val, hlt⟩ = i := by ext; simp [esI]; omega
    rwa [e] at this

theorem decomp (v : Fin (2 * r + k + 1) → ℂ) :
    v = (∑ a : Fin r, v (eI k r a) • ee k r a) + (∑ a : Fin r, v (esI k r a) • es k r a) + Wb v := by
  ext i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, Wb, mul_ite,
    mul_one, mul_zero]
  by_cases h1 : i.val < r
  · have e : ∀ a : Fin r, (i = eI k r a) ↔ a = ⟨i.val, h1⟩ := by
      intro a; constructor
      · intro h; ext; simp [h, eI]
      · intro h; subst h; ext; simp [eI]
    have e2 : ∀ a : Fin r, ¬ (i = esI k r a) := by
      intro a h; have e := congrArg Fin.val h; have ha := a.isLt; simp [esI] at e; omega
    simp only [e, e2, Finset.sum_ite_eq', Finset.mem_univ, if_true, if_false, Finset.sum_const_zero]
    rw [if_neg (by omega)]
    have : eI k r ⟨i.val, h1⟩ = i := by ext; simp [eI]
    rw [this]; ring
  · by_cases h2 : r + k < i.val
    · have hlt : 2 * r + k - i.val < r := by omega
      have e : ∀ a : Fin r, (i = esI k r a) ↔ a = ⟨2 * r + k - i.val, hlt⟩ := by
        intro a; constructor
        · intro h; have := congrArg Fin.val h; ext; simp [esI] at this ⊢; omega
        · intro h; subst h; ext; simp [esI]; omega
      have e2 : ∀ a : Fin r, ¬ (i = eI k r a) := by
        intro a h; have e := congrArg Fin.val h; have ha := a.isLt; simp [eI] at e; omega
      simp only [e, e2, Finset.sum_ite_eq', Finset.mem_univ, if_true, if_false, Finset.sum_const_zero]
      rw [if_neg (by omega)]
      have : esI k r ⟨2 * r + k - i.val, hlt⟩ = i := by ext; simp [esI]; omega
      rw [this]; ring
    · have e2 : ∀ a : Fin r, ¬ (i = eI k r a) := by
        intro a h; have e := congrArg Fin.val h; have ha := a.isLt; simp [eI] at e; omega
      have e3 : ∀ a : Fin r, ¬ (i = esI k r a) := by
        intro a h; have e := congrArg Fin.val h; have ha := a.isLt; simp [esI] at e; omega
      simp only [e2, e3, if_false, Finset.sum_const_zero]
      rw [if_pos (by omega)]; ring

theorem Wb_add (v w : Fin (2 * r + k + 1) → ℂ) : Wb (v + w) = Wb v + Wb w := by
  ext i; simp only [Wb, Pi.add_apply]; split_ifs <;> simp

theorem Wb_smul (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) : Wb (c • v) = c • Wb v := by
  ext i; simp only [Wb, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

theorem Wb_sum {ι : Type*} (s : Finset ι) (f : ι → Fin (2 * r + k + 1) → ℂ) :
    Wb (∑ i ∈ s, f i) = ∑ i ∈ s, Wb (f i) := by
  ext j; simp only [Wb, Finset.sum_apply]; split_ifs <;> simp

theorem Wb_ee (a : Fin r) : Wb (ee k r a) = 0 := by
  ext i; simp only [Wb, bvec, Pi.single_apply, Pi.zero_apply]
  split_ifs with h1 h2 <;> try rfl
  exfalso; subst h2; have := a.isLt; simp [eI] at h1; omega

theorem Wb_es (a : Fin r) : Wb (es k r a) = 0 := by
  ext i; simp only [Wb, bvec, Pi.single_apply, Pi.zero_apply]
  split_ifs with h1 h2 <;> try rfl
  exfalso; subst h2; have := a.isLt; simp [esI] at h1; omega

variable (m₀ : B.Mat k r) (hmU : m₀ ∈ UH (Hpk k r)) (hme : ∀ a : Fin r, m₀ *ᵥ ee k r a = ee k r a)
  (hms : ∀ a : Fin r, m₀ *ᵥ es k r a = es k r a)

include hmU in
theorem herm_m0_mulVec_invariant (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) (m₀ *ᵥ v) (m₀ *ᵥ w) = herm (Hpk k r) v w := by
  rw [B2x4.herm_mulVec]; rw [show m₀ᴴ * Hpk k r * m₀ = Hpk k r from hmU]

include hmU hme hms in
theorem m0_mulVec_mem_orthogonal {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) : inWb k r (m₀ *ᵥ w) := by
  apply inWb_of_coords
  · intro a; rw [← herm_es (m₀ *ᵥ w) a, ← hms a, herm_m0_mulVec_invariant m₀ hmU, herm_es, wb_eI hw]
  · intro a; rw [← herm_ee (m₀ *ᵥ w) a, ← hme a, herm_m0_mulVec_invariant m₀ hmU, herm_ee, wb_esI hw]

include hmU hme hms in
theorem reflection_commutes_m0_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Wb (m₀ *ᵥ v) = m₀ *ᵥ Wb v := by
  have hW : inWb k r (Wb v) := by
    intro i hi; simp only [Wb]; rw [if_neg (by omega)]
  conv_lhs => rw [decomp v]
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_sum, Wb_add, Wb_add, Wb_sum, Wb_sum]
  simp only [Matrix.mulVec_smul, hme, hms, Wb_smul, Wb_ee, Wb_es, smul_zero, Finset.sum_const_zero, zero_add]
  exact Wb_of_inWb (m0_mulVec_mem_orthogonal m₀ hmU hme hms hW)

include hmU hme hms in

theorem orthoProj_m0_intertwine {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (μ : ℝ) (hμ : μ ≠ 0)
    (hmz : m₀ *ᵥ z' = (μ : ℂ) • z) (hzz : herm (Hpk k r) z' z' ≠ 0) (v : Fin (2 * r + k + 1) → ℂ) :
    D.prW k r z (m₀ *ᵥ v) = m₀ *ᵥ D.prW k r z' v := by
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  have hzeq : z = (μ : ℂ)⁻¹ • (m₀ *ᵥ z') := by rw [hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
  rw [prW_eq, prW_eq, reflection_commutes_m0_mulVec m₀ hmU hme hms, Matrix.mulVec_sub, Matrix.mulVec_smul]
  congr 1
  rw [hzeq, B2x4.herm_smul_right, B2x4.herm_smul_right, B2x4.herm_smul_left, herm_m0_mulVec_invariant m₀ hmU, herm_m0_mulVec_invariant m₀ hmU,
    smul_smul]
  congr 1
  have : star ((μ : ℂ)⁻¹) = (μ : ℂ)⁻¹ := by simp
  rw [this]
  field_simp

end frame

section prWlin

variable {k r : ℕ}

theorem prW_add (z v w : Fin (2 * r + k + 1) → ℂ) : D.prW k r z (v + w) = D.prW k r z v + D.prW k r z w := by
  rw [prW_eq, prW_eq, prW_eq, Wb_add, B2x4.herm_add_left, add_div, add_smul]; abel

theorem prW_smul (z v : Fin (2 * r + k + 1) → ℂ) (c : ℂ) : D.prW k r z (c • v) = c • D.prW k r z v := by
  rw [prW_eq, prW_eq, Wb_smul, B2x4.herm_smul_left, smul_sub, smul_smul, mul_div_assoc]

theorem prW_sub (z v w : Fin (2 * r + k + 1) → ℂ) : D.prW k r z (v - w) = D.prW k r z v - D.prW k r z w := by
  rw [sub_eq_add_neg, prW_add, show -w = (-1 : ℂ) • w by simp, prW_smul]; simp [sub_eq_add_neg]

theorem prW_self {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hzz : herm (Hpk k r) z z ≠ 0) :
    D.prW k r z z = 0 := by
  rw [prW_eq, Wb_of_inWb hz, div_self hzz, one_smul, sub_self]

theorem prW_perp {z ν : Fin (2 * r + k + 1) → ℂ} (hν : inWb k r ν) (hνz : herm (Hpk k r) ν z = 0) :
    D.prW k r z ν = ν := by
  rw [prW_eq, Wb_of_inWb hν, hνz, zero_div, zero_smul, sub_zero]

end prWlin

section adj

theorem monomialMatrix_inv {m : ℕ} (π : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    (C2.monoP π d)⁻¹ = Matrix.of fun b i => if π b = i then (d b)⁻¹ else 0 := by
  apply Matrix.inv_eq_left_inv
  ext b c
  simp only [C2.monoP, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (π b)]
  · simp only [if_true]
    by_cases h : b = c
    · subst h; simp [hd]
    · have : ¬ π b = π c := fun e => h (π.injective e)
      simp [this, h]
  · intro i _ hi; simp [Ne.symm hi]
  · simp

theorem monomialMatrix_adj {m : ℕ} (π : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) (b i : Fin m) :
    (C2.monoP π d).adjugate b i = (C2.monoP π d).det * (if π b = i then (d b)⁻¹ else 0) := by
  have hdet : IsUnit (C2.monoP π d).det := by
    have hinv : (C2.monoP π d)⁻¹ * C2.monoP π d = 1 := by
      rw [monomialMatrix_inv π d hd]
      ext b c
      simp only [C2.monoP, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
      rw [Finset.sum_eq_single (π b)]
      · simp only [if_true]
        by_cases h : b = c
        · subst h; simp [hd]
        · have : ¬ π b = π c := fun e => h (π.injective e)
          simp [this, h]
      · intro i _ hi; simp [Ne.symm hi]
      · simp
    exact (Matrix.isUnit_det_of_left_inverse hinv)
  have e : (C2.monoP π d).adjugate = (C2.monoP π d).det • (C2.monoP π d)⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hdet, one_smul]
  rw [e, monomialMatrix_inv π d hd]
  simp [Matrix.smul_apply]

end adj

section assemble

variable {k r : ℕ}

theorem mul_UH {m₀ σ : B.Mat k r} (h1 : m₀ ∈ UH (Hpk k r)) (h2 : σ ∈ UH (Hpk k r)) : m₀ * σ ∈ UH (Hpk k r) := by
  show (m₀ * σ)ᴴ * Hpk k r * (m₀ * σ) = Hpk k r
  have e1 : m₀ᴴ * Hpk k r * m₀ = Hpk k r := h1
  have e2 : σᴴ * Hpk k r * σ = Hpk k r := h2
  rw [Matrix.conjTranspose_mul]
  calc σᴴ * m₀ᴴ * Hpk k r * (m₀ * σ) = σᴴ * (m₀ᴴ * Hpk k r * m₀) * σ := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [e1, e2]

theorem fvec_cs (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : fvec k r z a.castSucc = ee k r a := by
  simp [fvec, a.isLt]

theorem fvec_lastI (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

theorem reduced_matrix_of_stabilizer {z z' : Fin (2 * r + k + 1) → ℂ} (m₀ σ : B.Mat k r) (hmU : m₀ ∈ UH (Hpk k r))
    (hme : ∀ a : Fin r, m₀ *ᵥ ee k r a = ee k r a) (μ : ℝ) (hμ : μ ≠ 0) (hmz : m₀ *ᵥ z' = (μ : ℂ) • z)
    (a b : Fin (r + 1)) :
    Zhat k r z z' (m₀ * σ) a b = herm (Hpk k r) (σ *ᵥ fvec k r z' b) (fvec k r ((μ : ℂ)⁻¹ • z') a) := by
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  have hf : fvec k r z a = m₀ *ᵥ fvec k r ((μ : ℂ)⁻¹ • z') a := by
    induction a using Fin.lastCases with
    | last => rw [fvec_lastI, fvec_lastI, Matrix.mulVec_smul, hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    | cast a => rw [fvec_cs, fvec_cs, hme]
  show herm (Hpk k r) ((m₀ * σ) *ᵥ fvec k r z' b) (fvec k r z a) = _
  rw [hf, ← Matrix.mulVec_mulVec, herm_m0_mulVec_invariant m₀ hmU]

end assemble

section caseAmain

variable {k r : ℕ}

theorem cast_or_last (b : Fin (r + 1)) : b = Fin.last r ∨ ∃ b' : Fin r, b = b'.castSucc := by
  induction b using Fin.lastCases with
  | last => exact Or.inl rfl
  | cast b' => exact Or.inr ⟨b', rfl⟩

theorem caseA {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀) (π : Equiv.Perm (Fin (r + 1))) (d0 : Fin (r + 1) → ℂ)
    (hd0 : ∀ a, d0 a ≠ 0) (a0 b0 : Fin r) (ha : π (Fin.last r) = a0.castSucc)
    (hb : π b0.castSucc = Fin.last r) :
    ∃ γ ∈ B.GV k r, Zhat k r S.z S.z' γ = C2.monoP π d0 ∧ Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ γ := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := hbase
  have hme : ∀ a : Fin r, m₀ *ᵥ ee k r a = ee k r a := fun a => (hmfix a a.isLt).1
  have hms : ∀ a : Fin r, m₀ *ᵥ es k r a = es k r a := fun a => (hmfix a a.isLt).2
  have hz := S.z_mem
  have hz' := S.z'_mem
  have hT := S.T_pos
  have hT' := S.T'_pos
  set s := Real.sqrt (Tz k r S.z') with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hT'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hs2 : s ^ 2 = Tz k r S.z' := Real.sq_sqrt hT'.le
  have hzz : herm (Hpk k r) S.z' S.z' = -((s : ℂ) ^ 2) := by
    rw [herm_self_alt]; congr 1; exact_mod_cast hs2.symm
  have hzz0 : herm (Hpk k r) S.z' S.z' ≠ 0 := by rw [hzz]; simpa using hs'
  set μ := Real.sqrt (Tz k r S.z' / Tz k r S.z) with hμdef
  have hμ : 0 < μ := Real.sqrt_pos.2 (div_pos hT' hT)
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  set d' : Fin (r + 1) → ℂ := fun b => if π b = Fin.last r then (μ : ℂ) * d0 b else d0 b with hd'def
  have hd' : ∀ b, d' b ≠ 0 := by
    intro b; simp only [hd'def]; split_ifs
    · exact mul_ne_zero hμ' (hd0 b)
    · exact hd0 b
  have hne : ∀ b : Fin r, b ≠ b0 → π b.castSucc ≠ Fin.last r := by
    intro b hb' h; rw [← hb] at h; exact hb' (Fin.castSucc_injective _ (π.injective h))
  have hdb0 : d' b0.castSucc = (μ : ℂ) * d0 b0.castSucc := by simp [hd'def, hb]
  have hdl : d' (Fin.last r) = d0 (Fin.last r) := by
    simp only [hd'def]; rw [if_neg (by rw [ha]; exact Fin.castSucc_ne_last a0)]
  have hdb : ∀ b : Fin r, b ≠ b0 → d' b.castSucc = d0 b.castSucc := by
    intro b h; simp only [hd'def]; rw [if_neg (hne b h)]
  set Y := YA π d' S.z' ν' s a0 b0 with hYdef
  set σ := smat (Hpk k r) (uB S.z' ν') (wB S.z' ν' s) Y with hσdef
  have hσU : σ ∈ UH (Hpk k r) :=
    sig_UH Y hz' hν hs hzz hνz hνν (YA_gram π d' hz' hν hs hzz hνz hνν hd' a0 b0 ha hb)
      (fun x hx i => YA_perp π d' a0 b0 x hx i)
  have hσu : ∀ i, σ *ᵥ uB S.z' ν' i = Y i := sig_u Y hz' hν hs hzz hνz hνν
  have hγ : m₀ * σ ∈ UH (Hpk k r) := mul_UH hmU hσU
  have hzν := herm_zν hνz
  have hσe : ∀ b : Fin r, σ *ᵥ ee k r b = Y (Sum.inl (Sum.inl b)) := fun b => hσu (Sum.inl (Sum.inl b))
  have hσz : σ *ᵥ S.z' = Y (Sum.inr 0) := hσu (Sum.inr 0)
  have hσn : σ *ᵥ ν' = Y (Sum.inr 1) := hσu (Sum.inr 1)
  have hZ : Zhat k r S.z S.z' (m₀ * σ) = C2.monoP π d0 := by
    ext a b
    rw [reduced_matrix_of_stabilizer m₀ σ hmU hme μ hμ.ne' hmz]
    rcases cast_or_last b with hbl | ⟨b', rfl⟩ <;> rcases cast_or_last a with hal | ⟨a', rfl⟩
    · subst hbl hal
      rw [fvec_lastI, fvec_lastI, hσz]
      have h1 : ¬ (Fin.last r = π (Fin.last r)) := by rw [ha]; exact (Fin.castSucc_ne_last a0).symm
      simp [hYdef, YA, C2.monoP, h1, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
    · subst hbl
      rw [fvec_lastI, fvec_cs, hσz]
      have e : (a'.castSucc = π (Fin.last r)) ↔ (a0 = a') := by
        rw [ha]; constructor
        · intro h; exact (Fin.castSucc_injective _ h).symm
        · rintro rfl; rfl
      simp [hYdef, YA, C2.monoP, e, hdl, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
    · subst hal
      rw [fvec_lastI, fvec_cs, hσe]
      by_cases hb' : b' = b0
      · subst hb'
        simp [hYdef, YA, C2.monoP, hb, hdb0, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
        field_simp
      · have h1 : ¬ (Fin.last r = π b'.castSucc) := fun h => hne b' hb' h.symm
        simp [hYdef, YA, C2.monoP, hb', h1, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
    · rw [fvec_cs, fvec_cs, hσe]
      by_cases hb' : b' = b0
      · subst hb'
        have h1 : ¬ (a'.castSucc = π b'.castSucc) := by rw [hb]; exact Fin.castSucc_ne_last a'
        simp [hYdef, YA, C2.monoP, h1, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
      · have e : (a'.castSucc = π b'.castSucc) ↔ (piX π b' = a') := by
          rw [← piX_spec π b' (hne b' hb')]; constructor
          · intro h; exact (Fin.castSucc_injective _ h).symm
          · rintro rfl; rfl
        simp [hYdef, YA, C2.monoP, hb', e, hdb b' hb', B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
  have hγu : IsUnit (m₀ * σ).det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hγ
  have hm0u : IsUnit m₀.det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hmU
  have hDl : d0 (Fin.last r) ≠ 0 := hd0 _
  have hDc : conj (d0 (Fin.last r)) ≠ 0 := by simpa using hDl
  refine ⟨m₀ * σ, hγ, hZ, ?_, ?_, ?_⟩
  ·
    refine ⟨μ / s, div_pos hμ hs, ?_⟩
    have hcof : Formalism.FourierDecayAlt.D.cofR S (m₀ * σ) =
        ((C2.monoP π d0).det * (d0 b0.castSucc)⁻¹) • (m₀ *ᵥ (σ *ᵥ ee k r b0)) := by
      unfold Formalism.FourierDecayAlt.D.cofR; rw [hZ]
      rw [Finset.sum_eq_single b0.castSucc]
      · rw [monomialMatrix_adj π d0 hd0, if_pos hb, fvec_cs, Matrix.mulVec_mulVec]
      · intro b _ hbne
        have : π b ≠ Fin.last r := by intro h; rw [← hb] at h; exact hbne (π.injective h)
        rw [monomialMatrix_adj π d0 hd0, if_neg this]; simp
      · simp
    rw [hcof, prW_smul, orthoProj_m0_intertwine m₀ hmU hme hms hz hz' μ hμ.ne' hmz hzz0, hσe]
    simp only [hYdef, YA, if_true]
    rw [prW_smul, prW_sub, prW_smul, prW_perp hν hνz, prW_self hz' hzz0, smul_zero, sub_zero, hZ,
      Matrix.mulVec_smul, smul_smul, hdb0]
    congr 1
    have := hd0 b0.castSucc
    push_cast; field_simp
  ·
    refine ⟨1 / s, by positivity, ?_⟩
    have hcof : Formalism.FourierDecayAlt.D.cofL S (m₀ * σ) =
        (conj ((C2.monoP π d0).det * (d0 (Fin.last r))⁻¹)) • ee k r a0 := by
      unfold Formalism.FourierDecayAlt.D.cofL; rw [hZ]
      rw [Finset.sum_eq_single (π (Fin.last r))]
      · rw [monomialMatrix_adj π d0 hd0, if_pos rfl, ha, fvec_cs]
      · intro a _ hane; rw [monomialMatrix_adj π d0 hd0, if_neg (Ne.symm hane)]; simp
      · simp
    set Dl := d0 (Fin.last r) with hDldef
    have hvec : (-(conj Dl / (s : ℂ) ^ 2)) • Y (Sum.inr 0) + (conj Dl / (s : ℂ)) • Y (Sum.inr 1) = ee k r a0 := by
      simp only [hYdef, YA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hdl]
      rw [show ∀ (α β p q c1 c2 : ℂ), α • (p • es k r a0 - c1 • ee k r a0) + β • (c2 • ee k r a0 + q • es k r a0) =
          (α * p + β * q) • es k r a0 + (β * c2 - α * c1) • ee k r a0 from by intros; module]
      have h0 : -(conj Dl / (s : ℂ) ^ 2) * Dl + conj Dl / (s : ℂ) * (Dl / (s : ℂ)) = 0 := by ring
      have h1 : conj Dl / (s : ℂ) * ((s : ℂ) / (2 * conj Dl)) - -(conj Dl / (s : ℂ) ^ 2) * ((s : ℂ) ^ 2 / (2 * conj Dl)) = 1 := by
        field_simp; ring
      rw [h0, h1, zero_smul, zero_add, one_smul]
    have hw : (m₀ * σ) *ᵥ ((-(conj Dl / (s : ℂ) ^ 2)) • S.z' + (conj Dl / (s : ℂ)) • ν') = ee k r a0 := by
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hσz, hσn, hvec, hme]
    have hinv : (m₀ * σ)⁻¹ *ᵥ ee k r a0 = (-(conj Dl / (s : ℂ) ^ 2)) • S.z' + (conj Dl / (s : ℂ)) • ν' := by
      rw [← hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hγu, Matrix.one_mulVec]
    rw [hcof, Matrix.mulVec_smul, hinv, prW_smul, prW_add, prW_smul, prW_smul, prW_self hz' hzz0,
      prW_perp hν hνz, hZ, smul_zero, zero_add, smul_smul]
    congr 1
    simp only [map_mul, map_inv₀]
    push_cast
    field_simp
  ·
    intro u hu
    set v := m₀⁻¹ *ᵥ u with hvdef
    have hmv : m₀ *ᵥ v = u := by
      rw [hvdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hm0u, Matrix.one_mulVec]
    have hv1 : ∀ a : Fin r, herm (Hpk k r) v (ee k r a) = 0 := by
      intro a; have := (hu a.castSucc).1; rw [fvec_cs, ← hmv, ← hme a, herm_m0_mulVec_invariant m₀ hmU] at this; exact this
    have hzeq : S.z = (μ : ℂ)⁻¹ • (m₀ *ᵥ S.z') := by rw [hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    have hv2 : herm (Hpk k r) v S.z' = 0 := by
      have := (hu (Fin.last r)).1
      rw [fvec_lastI, ← hmv, hzeq, B2x4.herm_smul_right, herm_m0_mulVec_invariant m₀ hmU] at this
      simpa [hμ'] using this
    have hvY : ∀ a, herm (Hpk k r) v (σ *ᵥ fvec k r S.z' a) = 0 := by
      intro a; have := (hu a).2; rw [← hmv, ← Matrix.mulVec_mulVec, herm_m0_mulVec_invariant m₀ hmU] at this; exact this
    have hv3 : herm (Hpk k r) v ν' = 0 := by
      have := hvY b0.castSucc
      rw [fvec_cs, hσe] at this
      simp only [hYdef, YA, if_true, B2x4.herm_smul_right, B2x4.herm_sub_right, hv2, mul_zero, sub_zero] at this
      rcases mul_eq_zero.1 this with h | h
      · exfalso; have := hd' b0.castSucc; simp at h
        rcases h with h | h
        · exact this h
        · exact hs.ne' h
      · exact h
    have hv4 : ∀ c : Fin r, herm (Hpk k r) v (es k r c) = 0 := by
      intro c
      by_cases hc : c = a0
      · subst hc
        have := hvY (Fin.last r)
        rw [fvec_lastI, hσz] at this
        simp only [hYdef, YA, Matrix.cons_val_zero, B2x4.herm_smul_right, B2x4.herm_sub_right, hv1, mul_zero,
          sub_zero, hdl] at this
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hDc
        · exact h
      · have hbl : π.symm c.castSucc ≠ Fin.last r := by
          intro h; have h2 := congrArg π h; rw [π.apply_symm_apply, ha] at h2
          exact hc (Fin.castSucc_injective _ h2)
        obtain ⟨b', hb'⟩ := (cast_or_last (π.symm c.castSucc)).resolve_left hbl
        have hb'0 : b' ≠ b0 := by
          intro h; subst h; rw [← hb', π.apply_symm_apply] at hb; exact Fin.castSucc_ne_last c hb
        have hpx : piX π b' = c := by
          apply Fin.castSucc_injective; rw [piX_spec π b' (hne b' hb'0), ← hb', π.apply_symm_apply]
        have := hvY b'.castSucc
        rw [fvec_cs, hσe] at this
        simp only [hYdef, YA, if_neg hb'0, hpx, B2x4.herm_smul_right] at this
        rcases mul_eq_zero.1 this with h | h
        · exfalso; have := hd' b'.castSucc; simp at h; exact this h
        · exact h
    have hfix : σ *ᵥ v = v := by
      apply sig_fix Y v
      intro i
      rcases i with ((b | b) | i)
      · exact hv4 b
      · exact hv1 b
      · fin_cases i
        · simp [wB, B2x4.herm_smul_right, herm_neg_right, hv2]
        · simpa [wB] using hv3
    have hinv : (m₀ * σ)⁻¹ *ᵥ u = v := by
      have : (m₀ * σ) *ᵥ v = u := by rw [← Matrix.mulVec_mulVec, hfix, hmv]
      rw [← this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hγu, Matrix.one_mulVec]
    rw [hinv, ← hmv, orthoProj_m0_intertwine m₀ hmU hme hms hz hz' μ hμ.ne' hmz hzz0]

theorem caseB {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀) (π : Equiv.Perm (Fin (r + 1))) (d0 : Fin (r + 1) → ℂ)
    (hd0 : ∀ a, d0 a ≠ 0) (hB : π (Fin.last r) = Fin.last r)
    (hG : Tz k r S.z * Tz k r S.z' < Complex.normSq (d0 (Fin.last r))) :
    ∃ γ ∈ B.GV k r, Zhat k r S.z S.z' γ = C2.monoP π d0 ∧ Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ γ := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := hbase
  have hme : ∀ a : Fin r, m₀ *ᵥ ee k r a = ee k r a := fun a => (hmfix a a.isLt).1
  have hms : ∀ a : Fin r, m₀ *ᵥ es k r a = es k r a := fun a => (hmfix a a.isLt).2
  have hz := S.z_mem
  have hz' := S.z'_mem
  have hT := S.T_pos
  have hT' := S.T'_pos
  set s := Real.sqrt (Tz k r S.z') with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hT'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hs2 : s ^ 2 = Tz k r S.z' := Real.sq_sqrt hT'.le
  have hzz : herm (Hpk k r) S.z' S.z' = -((s : ℂ) ^ 2) := by
    rw [herm_self_alt]; congr 1; exact_mod_cast hs2.symm
  have hzz0 : herm (Hpk k r) S.z' S.z' ≠ 0 := by rw [hzz]; simpa using hs'
  set μ := Real.sqrt (Tz k r S.z' / Tz k r S.z) with hμdef
  have hμ : 0 < μ := Real.sqrt_pos.2 (div_pos hT' hT)
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hμ2 : μ ^ 2 = Tz k r S.z' / Tz k r S.z := Real.sq_sqrt (div_pos hT' hT).le
  set d' : Fin (r + 1) → ℂ := fun b => if π b = Fin.last r then (μ : ℂ) * d0 b else d0 b with hd'def
  have hd' : ∀ b, d' b ≠ 0 := by
    intro b; simp only [hd'def]; split_ifs
    · exact mul_ne_zero hμ' (hd0 b)
    · exact hd0 b
  have hne : ∀ b : Fin r, π b.castSucc ≠ Fin.last r := by
    intro b h; rw [← hB] at h; exact Fin.castSucc_ne_last b (π.injective h)
  have hdl : d' (Fin.last r) = (μ : ℂ) * d0 (Fin.last r) := by simp [hd'def, hB]
  have hdb : ∀ b : Fin r, d' b.castSucc = d0 b.castSucc := by
    intro b; simp only [hd'def]; rw [if_neg (hne b)]

  set N := Complex.normSq (d' (Fin.last r)) with hNdef
  have hN : s ^ 4 < N := by
    rw [hNdef, hdl, Complex.normSq_mul, Complex.normSq_ofReal]
    have : s ^ 4 = μ * μ * (Tz k r S.z * Tz k r S.z') := by
      have e1 : μ * μ = μ ^ 2 := by ring
      rw [e1, hμ2, show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]; field_simp
    rw [this]; exact mul_lt_mul_of_pos_left hG (by positivity)
  have hN0 : 0 < N := lt_trans (by positivity) hN
  set κ := Real.sqrt (1 / s ^ 2 - s ^ 2 / N) with hκdef
  have hκarg : 0 < 1 / s ^ 2 - s ^ 2 / N := by
    rw [sub_pos, div_lt_div_iff₀ hN0 (by positivity)]; nlinarith [hN]
  have hκ0 : 0 < κ := Real.sqrt_pos.2 hκarg
  have hκ2 : κ ^ 2 = 1 / s ^ 2 - s ^ 2 / N := Real.sq_sqrt hκarg.le
  have hκr : κ ^ 2 * s ^ 2 * N = N - s ^ 4 := by rw [hκ2]; field_simp
  have hDD : d' (Fin.last r) * conj (d' (Fin.last r)) = ((N : ℝ) : ℂ) := by rw [hNdef, Complex.mul_conj]
  have hκ : (κ : ℂ) ^ 2 * (s : ℂ) ^ 2 * (d' (Fin.last r) * conj (d' (Fin.last r))) =
      d' (Fin.last r) * conj (d' (Fin.last r)) - (s : ℂ) ^ 4 := by
    rw [hDD]; exact_mod_cast hκr
  set Y := YB π d' S.z' ν' s κ with hYdef
  set σ := smat (Hpk k r) (uB S.z' ν') (wB S.z' ν' s) Y with hσdef
  have hσU : σ ∈ UH (Hpk k r) :=
    sig_UH Y hz' hν hs hzz hνz hνν (YB_gram π d' hz' hν hs hzz hνz hνν hd' κ hκ hB)
      (fun x hx i => YB_perp π d' κ x hx i)
  have hσu : ∀ i, σ *ᵥ uB S.z' ν' i = Y i := sig_u Y hz' hν hs hzz hνz hνν
  have hγ : m₀ * σ ∈ UH (Hpk k r) := mul_UH hmU hσU
  have hzν := herm_zν hνz
  have hσe : ∀ b : Fin r, σ *ᵥ ee k r b = Y (Sum.inl (Sum.inl b)) := fun b => hσu (Sum.inl (Sum.inl b))
  have hσz : σ *ᵥ S.z' = Y (Sum.inr 0) := hσu (Sum.inr 0)
  have hσn : σ *ᵥ ν' = Y (Sum.inr 1) := hσu (Sum.inr 1)
  have hZ : Zhat k r S.z S.z' (m₀ * σ) = C2.monoP π d0 := by
    ext a b
    rw [reduced_matrix_of_stabilizer m₀ σ hmU hme μ hμ.ne' hmz]
    rcases cast_or_last b with hbl | ⟨b', rfl⟩ <;> rcases cast_or_last a with hal | ⟨a', rfl⟩
    · subst hbl hal
      rw [fvec_lastI, fvec_lastI, hσz]
      simp [hYdef, YB, C2.monoP, hB, hdl, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
      field_simp
    · subst hbl
      rw [fvec_lastI, fvec_cs, hσz]
      have h1 : ¬ (a'.castSucc = π (Fin.last r)) := by rw [hB]; exact Fin.castSucc_ne_last a'
      simp [hYdef, YB, C2.monoP, h1, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
    · subst hal
      rw [fvec_lastI, fvec_cs, hσe]
      have h1 : ¬ (Fin.last r = π b'.castSucc) := fun h => hne b' h.symm
      simp [hYdef, YB, C2.monoP, h1, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
    · rw [fvec_cs, fvec_cs, hσe]
      have e : (a'.castSucc = π b'.castSucc) ↔ (piX π b' = a') := by
        rw [← piX_spec π b' (hne b')]; constructor
        · intro h; exact (Fin.castSucc_injective _ h).symm
        · rintro rfl; rfl
      simp [hYdef, YB, C2.monoP, e, hdb b', B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
  have hγu : IsUnit (m₀ * σ).det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hγ
  have hm0u : IsUnit m₀.det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hmU
  have hDl : d0 (Fin.last r) ≠ 0 := hd0 _
  have hDc : conj (d0 (Fin.last r)) ≠ 0 := by simpa using hDl
  refine ⟨m₀ * σ, hγ, hZ, ?_, ?_, ?_⟩
  ·
    refine ⟨μ * κ, mul_pos hμ hκ0, ?_⟩
    have hcof : Formalism.FourierDecayAlt.D.cofR S (m₀ * σ) =
        ((C2.monoP π d0).det * (d0 (Fin.last r))⁻¹) • (m₀ *ᵥ (σ *ᵥ S.z')) := by
      unfold Formalism.FourierDecayAlt.D.cofR; rw [hZ]
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [monomialMatrix_adj π d0 hd0, if_pos hB, fvec_lastI, Matrix.mulVec_mulVec]
      · intro b _ hbne
        have : π b ≠ Fin.last r := by intro h; rw [← hB] at h; exact hbne (π.injective h)
        rw [monomialMatrix_adj π d0 hd0, if_neg this]; simp
      · simp
    rw [hcof, prW_smul, orthoProj_m0_intertwine m₀ hmU hme hms hz hz' μ hμ.ne' hmz hzz0, hσz]
    simp only [hYdef, YB, Matrix.cons_val_zero]
    rw [prW_smul, prW_sub, prW_smul, prW_perp hν hνz, prW_self hz' hzz0, sub_zero, hZ,
      Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, smul_smul, hdl]
    congr 1
    push_cast; field_simp
  ·
    refine ⟨κ, hκ0, ?_⟩
    have hcof : Formalism.FourierDecayAlt.D.cofL S (m₀ * σ) =
        (conj ((C2.monoP π d0).det * (d0 (Fin.last r))⁻¹)) • S.z := by
      unfold Formalism.FourierDecayAlt.D.cofL; rw [hZ]
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [monomialMatrix_adj π d0 hd0, if_pos hB, fvec_lastI]
      · intro a _ hane; rw [monomialMatrix_adj π d0 hd0, if_neg (by rw [hB]; exact Ne.symm hane)]; simp
      · simp
    set Dp := d' (Fin.last r) with hDpdef
    have hvec : (-(conj Dp / (s : ℂ) ^ 2)) • Y (Sum.inr 0) + ((κ : ℂ) * conj Dp) • Y (Sum.inr 1) = S.z' := by
      simp only [hYdef, YB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [show ∀ (α β p q c1 c2 : ℂ), α • (p • (c1 • ν' - S.z')) + β • (q • (ν' - c2 • S.z')) =
          (α * p * c1 + β * q) • ν' + (-(α * p) - β * q * c2) • S.z' from by intros; module]
      have h0 : -(conj Dp / (s : ℂ) ^ 2) * (Dp / (s : ℂ) ^ 2) * ((κ : ℂ) * (s : ℂ) ^ 2) +
          (κ : ℂ) * conj Dp * (Dp / (s : ℂ) ^ 2) = 0 := by field_simp; ring
      have h1 : -(-(conj Dp / (s : ℂ) ^ 2) * (Dp / (s : ℂ) ^ 2)) - (κ : ℂ) * conj Dp * (Dp / (s : ℂ) ^ 2) * (κ : ℂ) = 1 := by
        field_simp
        first | linear_combination -hκ | linear_combination hκ | linear_combination (-1 : ℂ) * hκ
      rw [h0, h1, zero_smul, zero_add, one_smul]
    set w := (μ : ℂ)⁻¹ • ((-(conj Dp / (s : ℂ) ^ 2)) • S.z' + ((κ : ℂ) * conj Dp) • ν') with hwdef
    have hw : (m₀ * σ) *ᵥ w = S.z := by
      rw [hwdef, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hσz, hσn, hvec, hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    have hinv : (m₀ * σ)⁻¹ *ᵥ S.z = w := by
      rw [← hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hγu, Matrix.one_mulVec]
    rw [hcof, Matrix.mulVec_smul, hinv, hwdef, prW_smul, prW_smul, prW_add, prW_smul, prW_smul, prW_self hz' hzz0,
      prW_perp hν hνz, hZ, smul_zero, zero_add, smul_smul, smul_smul, hdl]
    congr 1
    simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    field_simp
  ·
    intro u hu
    set v := m₀⁻¹ *ᵥ u with hvdef
    have hmv : m₀ *ᵥ v = u := by
      rw [hvdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hm0u, Matrix.one_mulVec]
    have hv1 : ∀ a : Fin r, herm (Hpk k r) v (ee k r a) = 0 := by
      intro a; have := (hu a.castSucc).1; rw [fvec_cs, ← hmv, ← hme a, herm_m0_mulVec_invariant m₀ hmU] at this; exact this
    have hzeq : S.z = (μ : ℂ)⁻¹ • (m₀ *ᵥ S.z') := by rw [hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    have hv2 : herm (Hpk k r) v S.z' = 0 := by
      have := (hu (Fin.last r)).1
      rw [fvec_lastI, ← hmv, hzeq, B2x4.herm_smul_right, herm_m0_mulVec_invariant m₀ hmU] at this
      simpa [hμ'] using this
    have hvY : ∀ a, herm (Hpk k r) v (σ *ᵥ fvec k r S.z' a) = 0 := by
      intro a; have := (hu a).2; rw [← hmv, ← Matrix.mulVec_mulVec, herm_m0_mulVec_invariant m₀ hmU] at this; exact this
    have hv3 : herm (Hpk k r) v ν' = 0 := by
      have := hvY (Fin.last r)
      rw [fvec_lastI, hσz] at this
      simp only [hYdef, YB, Matrix.cons_val_zero, B2x4.herm_smul_right, B2x4.herm_sub_right, hv2, sub_zero] at this
      rcases mul_eq_zero.1 this with h | h
      · exfalso; have := hd' (Fin.last r); simp at h
        rcases h with h | h
        · exact this h
        · exact hs.ne' h
      · rcases mul_eq_zero.1 h with h | h
        · exfalso; simp at h
          rcases h with h | h
          · exact hκ0.ne' h
          · exact hs.ne' h
        · exact h
    have hv4 : ∀ c : Fin r, herm (Hpk k r) v (es k r c) = 0 := by
      intro c
      have hbl : π.symm c.castSucc ≠ Fin.last r := by
        intro h; have h2 := congrArg π h; rw [π.apply_symm_apply, hB] at h2
        exact Fin.castSucc_ne_last c h2
      obtain ⟨b', hb'⟩ := (cast_or_last (π.symm c.castSucc)).resolve_left hbl
      have hpx : piX π b' = c := by
        apply Fin.castSucc_injective; rw [piX_spec π b' (hne b'), ← hb', π.apply_symm_apply]
      have := hvY b'.castSucc
      rw [fvec_cs, hσe] at this
      simp only [hYdef, YB, hpx, B2x4.herm_smul_right] at this
      rcases mul_eq_zero.1 this with h | h
      · exfalso; have := hd' b'.castSucc; simp at h; exact this h
      · exact h
    have hfix : σ *ᵥ v = v := by
      apply sig_fix Y v
      intro i
      rcases i with ((b | b) | i)
      · exact hv4 b
      · exact hv1 b
      · fin_cases i
        · simp [wB, B2x4.herm_smul_right, herm_neg_right, hv2]
        · simpa [wB] using hv3
    have hinv : (m₀ * σ)⁻¹ *ᵥ u = v := by
      have : (m₀ * σ) *ᵥ v = u := by rw [← Matrix.mulVec_mulVec, hfix, hmv]
      rw [← this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hγu, Matrix.one_mulVec]
    rw [hinv, ← hmv, orthoProj_m0_intertwine m₀ hmU hme hms hz hz' μ hμ.ne' hmz hzz0]

end caseAmain

end Formalism.FourierDecayAlt.P.Dx2.DF

namespace Formalism.FourierDecayAlt.P.Dx2

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

section final

theorem ptMatN_mono (p : C.LPt) (n : ℕ) (hn : D.ptSize p = n) (hp : ∀ b ∈ p, 1 ≤ b.1 ∧ b.2 ≠ 0) :
    ∃ (π : Equiv.Perm (Fin n)) (d : Fin n → ℂ), (∀ a, d a ≠ 0) ∧ D.ptMatN p n = C2.monoP π d := by
  subst hn
  refine ⟨D.ptPerm p, D.ptDiag p, fun a => Formalism.FourierDecayAlt.P.Dx1.Rel.scal_ne p hp a a.isLt, ?_⟩
  exact Formalism.FourierDecayAlt.P.Dx1.ptMat_monoP p

theorem det_monomialMatrix_last {r : ℕ} (π : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ)
    (hB : π (Fin.last r) = Fin.last r) :
    (C2.monoP π d).det = d (Fin.last r) * ((C2.monoP π d).submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · simp [C2.monoP, hB, Fin.succAbove_last]
  · intro j _ hj
    have : ¬ (Fin.last r = π j) := by intro h; rw [← hB] at h; exact hj (π.injective h).symm
    simp [C2.monoP, this]
  · simp

theorem dFrameExists : Formalism.FourierDecayAlt.D.DFrameExists := by
  intro k r Wp Wq _ _ _ _ S ν' m₀ p hbase hp hG
  obtain ⟨π, d0, hd0, hP⟩ := ptMatN_mono p (r + 1) hp.2 hp.1
  by_cases hB : π (Fin.last r) = Fin.last r
  · have hsub : D.ptMatN p r = (C2.monoP π d0).submatrix Fin.castSucc Fin.castSucc := by
      rw [← hP]; ext a b; rfl
    have hG' : Tz k r S.z * Tz k r S.z' < Complex.normSq (d0 (Fin.last r)) := by
      unfold D.ptG at hG
      rw [hP, hsub, det_monomialMatrix_last π d0 hB, Complex.normSq_mul] at hG
      have h : 0 < Complex.normSq ((C2.monoP π d0).submatrix Fin.castSucc Fin.castSucc).det *
          (Complex.normSq (d0 (Fin.last r)) - Tz k r S.z * Tz k r S.z') := by linarith
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with h1 | h1
      · linarith [h1.2]
      · exact absurd h1.1 (not_lt.2 (Complex.normSq_nonneg _))
    obtain ⟨γ, hγ, hZ, hF⟩ := Formalism.FourierDecayAlt.P.Dx2.DF.caseB S ν' m₀ hbase π d0 hd0 hB hG'
    exact ⟨γ, hγ, hZ.trans hP.symm, hF⟩
  · obtain ⟨a0, ha⟩ := (Formalism.FourierDecayAlt.P.Dx2.DF.cast_or_last (π (Fin.last r))).resolve_left hB
    have hbl : π.symm (Fin.last r) ≠ Fin.last r := by
      intro h; apply hB; conv_lhs => rw [← h]; rw [π.apply_symm_apply]
    obtain ⟨b0, hb0⟩ := (Formalism.FourierDecayAlt.P.Dx2.DF.cast_or_last (π.symm (Fin.last r))).resolve_left hbl
    have hb : π b0.castSucc = Fin.last r := by rw [← hb0, π.apply_symm_apply]
    obtain ⟨γ, hγ, hZ, hF⟩ := Formalism.FourierDecayAlt.P.Dx2.DF.caseA S ν' m₀ hbase π d0 hd0 a0 b0 ha hb
    exact ⟨γ, hγ, hZ.trans hP.symm, hF⟩

end final

end Formalism.FourierDecayAlt.P.Dx2

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Formalism.FourierDecayAlt.P.Dx2.Split

variable {k j ρ : ℕ}

def c1v (x1 : U.RC k 1 (j + ρ)) : Fin (2 * (j + ρ) + k + 1) → ℂ := fun i => x1.1 i 0
def cX (x1 : U.RC k 1 (j + ρ)) : Fin j → ℂ := fun a => c1v x1 (U.eB k j ρ (Sum.inl (Sum.inl a)))
def cV (x1 : U.RC k 1 (j + ρ)) : Fin (2 * ρ + k + 1) → ℂ := fun v => c1v x1 (U.eB k j ρ (Sum.inl (Sum.inr v)))
def cS (x1 : U.RC k 1 (j + ρ)) : Fin j → ℂ := fun a => c1v x1 (U.eB k j ρ (Sum.inr a))
def s1 (x1 : U.RC k 1 (j + ρ)) : ℝ := x1.2.2 0

def nc (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) : Fin j → ℂ :=
  G.wMat j *ᵥ cX x1 - U.skewOf x.2 *ᵥ cS x1 + (1 / 2 : ℂ) • (((Matrix.of x.1)ᴴ * Hpk k ρ) *ᵥ cV x1)

def q2L (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) : ℝ :=
  s1 x1 + (star (cX x1) ⬝ᵥ (G.wMat j *ᵥ cS x1)).im + (star (cS x1) ⬝ᵥ (U.skewOf x.2 *ᵥ cS x1)).im +
    (star (cV x1) ⬝ᵥ (Hpk k ρ *ᵥ (Matrix.of x.1 *ᵥ cS x1))).im

def Cm (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) : Matrix (Fin (2 * ρ + k + 1)) (Fin (j + 1)) ℂ :=
  fun v b => Fin.lastCases (motive := fun _ => ℂ) (cV x1 v - (Matrix.of x.1 *ᵥ cS x1) v) (fun b' => x.1 v b') b

def Sm (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ :=
  fun a b => Fin.lastCases (motive := fun _ => ℂ)
    (Fin.lastCases (motive := fun _ => ℂ) (Complex.I * (q2L x1 x : ℂ)) (fun b' => -star (nc x1 x b')) b)
    (fun a' => Fin.lastCases (motive := fun _ => ℂ) (nc x1 x a') (fun b' => U.skewOf x.2 a' b') b) a

def Um (x1 : U.RC k 1 (j + ρ)) : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ :=
  fun a b => Fin.cases (motive := fun _ => ℂ)
    (Fin.cases (motive := fun _ => ℂ) 1 (fun b' => -(Matrix.vecMul (star (cS x1)) (G.wMat j)) b') b)
    (fun a' => Fin.cases (motive := fun _ => ℂ) 0 (fun b' => (1 : Matrix (Fin j) (Fin j) ℂ) a' b') b) a

def Ut0 (x1 : U.RC k 1 (j + ρ)) : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ :=
  fun a b => Fin.lastCases (motive := fun _ => ℂ)
    (Fin.lastCases (motive := fun _ => ℂ) 1 (fun _ => 0) b)
    (fun a' => Fin.lastCases (motive := fun _ => ℂ) (cS x1 a') (fun b' => (1 : Matrix (Fin j) (Fin j) ℂ) a' b') b) a

def TX (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) : U.RC k (j + 1) ρ :=
  (fun v b => Cm x1 x v b, (fun p => Sm x1 x p.1.1 p.1.2, fun a => (Sm x1 x a a).im))

def TU (x1 : U.RC k 1 (j + ρ)) : G.UT (j + 1) → ℂ := fun p => Um x1 p.1.1 p.1.2

theorem skew_diag_re (q : (G.UT j → ℂ) × (Fin j → ℝ)) (a : Fin j) : (U.skewOf q a a).re = 0 := by
  rw [Ux2.skewOf_diag]; simp

theorem skewOf_TX (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) : U.skewOf (TX x1 x).2 = Sm x1 x := by
  ext a b
  rcases lt_trichotomy a b with h | h | h
  · rw [Ux2.skewOf_lt _ h]; rfl
  · subst h
    rw [Ux2.skewOf_diag]
    show Complex.I * ((Sm x1 x a a).im : ℂ) = Sm x1 x a a
    cases a using Fin.lastCases with
    | last => simp [Sm]
    | cast a =>
      simp only [Sm, Fin.lastCases_castSucc]
      apply Complex.ext <;> simp [skew_diag_re]
  · have hs := congrFun (congrFun (Ux2.skewOf_ct (TX x1 x).2) a) b
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at hs
    have h1 : U.skewOf (TX x1 x).2 a b = -star (U.skewOf (TX x1 x).2 b a) := by rw [hs]; simp
    rw [h1, Ux2.skewOf_lt _ h]
    show -star (Sm x1 x b a) = Sm x1 x a b
    cases a using Fin.lastCases with
    | last =>
      cases b using Fin.lastCases with
      | last => exact absurd h (lt_irrefl _)
      | cast b => simp [Sm]
    | cast a =>
      cases b using Fin.lastCases with
      | last => exact absurd h (not_lt.mpr (Fin.castSucc_lt_last a).le)
      | cast b =>
        simp only [Sm, Fin.lastCases_castSucc]
        have hs2 := congrFun (congrFun (Ux2.skewOf_ct x.2) a) b
        simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at hs2
        rw [hs2]; simp

theorem um_uni (x1 : U.RC k 1 (j + ρ)) : Ux2.uniK (Ux2.kU (j + 1)) (Um x1) := by
  refine ⟨fun i => ?_, fun a b hab => ?_⟩
  · cases i using Fin.cases with
    | zero => simp [Um]
    | succ i => simp [Um]
  · rw [Ux2.kU_lt] at hab
    cases a using Fin.cases with
    | zero => exact absurd hab (Fin.not_lt_zero _)
    | succ a =>
      cases b using Fin.cases with
      | zero => simp [Um]
      | succ b =>
        simp only [Um, Fin.cases_succ]
        rw [Matrix.one_apply_ne]
        intro h; subst h; exact lt_irrefl _ hab

theorem rev_zero' (n : ℕ) : Fin.rev (0 : Fin (n + 1)) = Fin.last n := by ext; simp
theorem rev_succ' {n : ℕ} (a : Fin n) : Fin.rev a.succ = (Fin.rev a).castSucc := by ext; simp [Fin.val_rev]; try omega
theorem rev_last' (n : ℕ) : Fin.rev (Fin.last n) = 0 := by ext; simp
theorem rev_castSucc' {n : ℕ} (a : Fin n) : Fin.rev a.castSucc = (Fin.rev a).succ := by ext; simp [Fin.val_rev]; try omega

theorem wvec_apply (v : Fin j → ℂ) (a : Fin j) : (G.wMat j *ᵥ v) a = v a.rev := by
  simp [G.wMat, Matrix.mulVec, dotProduct]

theorem vecMul_w_apply (v : Fin j → ℂ) (a : Fin j) : Matrix.vecMul v (G.wMat j) a = v a.rev := by
  simp only [Matrix.vecMul, dotProduct, G.wMat, Matrix.of_apply]
  rw [Finset.sum_eq_single a.rev]
  · simp
  · intro b _ hb; rw [if_neg]; · simp
    intro h; apply hb; rw [h, Fin.rev_rev]
  · simp

theorem mul_w_apply {n : ℕ} {m : Type*} (A : Matrix m (Fin n) ℂ) (a : m) (b : Fin n) :
    (A * G.wMat n) a b = A a b.rev := by
  simp only [Matrix.mul_apply, G.wMat, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single b.rev]
  · simp
  · intro c _ hc; rw [if_neg]; intro h; apply hc; rw [h, Fin.rev_rev]
  · simp

theorem w_conj_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (G.wMat n * M * G.wMat n) a b = M a.rev b.rev := by
  rw [mul_w_apply, Ux3.wMat_mul_apply]

theorem um_ct_mul (x1 : U.RC k 1 (j + ρ)) :
    (Um x1)ᴴ * (G.wMat (j + 1) * Ut0 x1 * G.wMat (j + 1)) = 1 := by
  ext a b
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [w_conj_apply, Matrix.conjTranspose_apply]
  cases a using Fin.cases with
  | zero =>
    cases b using Fin.cases with
    | zero => simp [Um, Ut0, rev_zero', rev_succ']
    | succ b =>
      simp [Um, Ut0, rev_zero', rev_succ', Matrix.one_apply]
      exact (Fin.succ_ne_zero b).symm
  | succ a =>
    cases b using Fin.cases with
    | zero =>
      simp only [Um, Ut0, rev_zero', rev_succ', Fin.cases_zero, Fin.cases_succ, Fin.lastCases_last,
        Fin.lastCases_castSucc, vecMul_w_apply, Pi.star_apply, star_neg, star_star]
      rw [Finset.sum_eq_single a]
      · simp
      · intro c _ hc; simp [Matrix.one_apply_ne hc]
      · simp
    | succ b =>
      simp only [Um, Ut0, rev_zero', rev_succ', Fin.cases_zero, Fin.cases_succ, Fin.lastCases_last,
        Fin.lastCases_castSucc]
      by_cases h : a = b
      · subst h; simp [Matrix.one_apply]
      · simp [Matrix.one_apply, h, Ne.symm h]

theorem ut_eq (x1 : U.RC k 1 (j + ρ)) :
    G.wMat (j + 1) * (Um x1)ᴴ⁻¹ * G.wMat (j + 1) = Ut0 x1 := by
  rw [Matrix.inv_eq_right_inv (um_ct_mul x1)]
  simp only [← Matrix.mul_assoc, Ux3.wMat_mul_self, Matrix.one_mul]
  rw [Matrix.mul_assoc, Ux3.wMat_mul_self, Matrix.mul_one]

theorem castM_apply {a b : ℕ} (h : a = b) (g : B.Mat k a) (p q : Fin (2 * b + k + 1)) :
    D.castM h g p q = g (Fin.cast (by omega) p) (Fin.cast (by omega) q) := by
  subst h; simp [D.castM, Matrix.reindex_apply]

theorem hh (k j ρ : ℕ) : 2 * ((j + 1) + ρ) + k + 1 = 2 * (1 + (j + ρ)) + k + 1 := by omega

theorem pos0 : Fin.cast (hh k j ρ) (U.eB k (j + 1) ρ (Sum.inl (Sum.inl 0))) = U.eB k 1 (j + ρ) (Sum.inl (Sum.inl 0)) := by
  ext; simp [Ux3.block_index_first_val]

theorem posX (a : Fin j) : Fin.cast (hh k j ρ) (U.eB k (j + 1) ρ (Sum.inl (Sum.inl a.succ))) =
    U.eB k 1 (j + ρ) (Sum.inl (Sum.inr (U.eB k j ρ (Sum.inl (Sum.inl a))))) := by
  ext; simp [Ux3.block_index_first_val, Ux3.block_index_middle_val]; omega

theorem posV (v : Fin (2 * ρ + k + 1)) : Fin.cast (hh k j ρ) (U.eB k (j + 1) ρ (Sum.inl (Sum.inr v))) =
    U.eB k 1 (j + ρ) (Sum.inl (Sum.inr (U.eB k j ρ (Sum.inl (Sum.inr v))))) := by
  ext; simp [Ux3.block_index_middle_val]; omega

theorem posS (b : Fin j) : Fin.cast (hh k j ρ) (U.eB k (j + 1) ρ (Sum.inr b.castSucc)) =
    U.eB k 1 (j + ρ) (Sum.inl (Sum.inr (U.eB k j ρ (Sum.inr b)))) := by
  ext; simp [Ux3.block_index_middle_val, Ux3.block_index_last_val]; omega

theorem posL : Fin.cast (hh k j ρ) (U.eB k (j + 1) ρ (Sum.inr (Fin.last j))) = U.eB k 1 (j + ρ) (Sum.inr 0) := by
  ext; simp [Ux3.block_index_last_val]; omega

theorem lhs_form (x1 : U.RC k 1 (j + ρ)) (Q : B.Mat k (j + ρ)) :
    U.Rn k 1 (j + ρ) x1 * U.embG k 1 (j + ρ) Q =
      U.blk3 1 (-(G.wMat 1 * (Matrix.of x1.1)ᴴ * Hpk k (j + ρ)) * Q)
        (G.wMat 1 * ((-(1 / 2 : ℂ)) • ((Matrix.of x1.1)ᴴ * Hpk k (j + ρ) * Matrix.of x1.1) + U.skewOf x1.2))
        0 Q (Matrix.of x1.1) 0 0 1 := by
  rw [Ux3.rn_eq, U.embG, Ux3.block3_mul]
  congr 1 <;> simp

theorem rhs_form (X : U.RC k (j + 1) ρ) (V : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ) :
    U.Rn k (j + 1) ρ X * U.muP k (j + 1) ρ V =
      U.blk3 V (-(G.wMat (j + 1) * (Matrix.of X.1)ᴴ * Hpk k ρ))
        (G.wMat (j + 1) * ((-(1 / 2 : ℂ)) • ((Matrix.of X.1)ᴴ * Hpk k ρ * Matrix.of X.1) + U.skewOf X.2) *
          (G.wMat (j + 1) * Vᴴ⁻¹ * G.wMat (j + 1)))
        0 1 (Matrix.of X.1 * (G.wMat (j + 1) * Vᴴ⁻¹ * G.wMat (j + 1))) 0 0 (G.wMat (j + 1) * Vᴴ⁻¹ * G.wMat (j + 1)) := by
  rw [Ux3.rn_eq, U.muP, Ux3.block3_mul]
  congr 1 <;> simp

theorem hrn_form (x : U.RC k j ρ) :
    Hpk k (j + ρ) * U.Rn k j ρ x =
      U.blk3 0 0 (G.wMat j) 0 (Hpk k ρ) (Hpk k ρ * Matrix.of x.1) (G.wMat j) (-((Matrix.of x.1)ᴴ * Hpk k ρ))
        ((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + U.skewOf x.2) := by
  rw [Ux3.hpkBlocks k j ρ, Ux3.rn_eq, Ux3.block3_mul]
  congr 1 <;> simp [← Matrix.mul_assoc, Ux3.wMat_mul_self]

theorem vecMul_block3_first_coords (y : Fin (2 * (j + ρ) + k + 1) → ℂ)
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (a : Fin j) :
    Matrix.vecMul y (U.blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) (U.eB k j ρ (Sum.inl (Sum.inl a))) =
      Matrix.vecMul (fun a => y (U.eB k j ρ (Sum.inl (Sum.inl a)))) A11 a +
        Matrix.vecMul (fun v => y (U.eB k j ρ (Sum.inl (Sum.inr v)))) A21 a +
        Matrix.vecMul (fun a => y (U.eB k j ρ (Sum.inr a))) A31 a := by
  simp only [Matrix.vecMul, dotProduct]
  rw [← (U.eB k j ρ).sum_comp]
  simp only [Fintype.sum_sum_type, Ux3.block3_apply]
  simp

theorem vecMul_block3_middle_coords (y : Fin (2 * (j + ρ) + k + 1) → ℂ)
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (v : Fin (2 * ρ + k + 1)) :
    Matrix.vecMul y (U.blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) (U.eB k j ρ (Sum.inl (Sum.inr v))) =
      Matrix.vecMul (fun a => y (U.eB k j ρ (Sum.inl (Sum.inl a)))) A12 v +
        Matrix.vecMul (fun v => y (U.eB k j ρ (Sum.inl (Sum.inr v)))) A22 v +
        Matrix.vecMul (fun a => y (U.eB k j ρ (Sum.inr a))) A32 v := by
  simp only [Matrix.vecMul, dotProduct]
  rw [← (U.eB k j ρ).sum_comp]
  simp only [Fintype.sum_sum_type, Ux3.block3_apply]
  simp

theorem vecMul_block3_last_coord (y : Fin (2 * (j + ρ) + k + 1) → ℂ)
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (b : Fin j) :
    Matrix.vecMul y (U.blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) (U.eB k j ρ (Sum.inr b)) =
      Matrix.vecMul (fun a => y (U.eB k j ρ (Sum.inl (Sum.inl a)))) A13 b +
        Matrix.vecMul (fun v => y (U.eB k j ρ (Sum.inl (Sum.inr v)))) A23 b +
        Matrix.vecMul (fun a => y (U.eB k j ρ (Sum.inr a))) A33 b := by
  simp only [Matrix.vecMul, dotProduct]
  rw [← (U.eB k j ρ).sum_comp]
  simp only [Fintype.sum_sum_type, Ux3.block3_apply]
  simp

theorem rowP (x1 : U.RC k 1 (j + ρ)) (Q : B.Mat k (j + ρ)) (z : Fin (2 * (j + ρ) + k + 1)) :
    (G.wMat 1 * (Matrix.of x1.1)ᴴ * Hpk k (j + ρ) * Q) 0 z = Matrix.vecMul (star (c1v x1)) (Hpk k (j + ρ) * Q) z := by
  have hw : G.wMat 1 = 1 := by ext a b; fin_cases a; fin_cases b; simp [G.wMat]
  rw [hw, Matrix.one_mul, Matrix.mul_assoc]
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, c1v]

theorem star_column_components (x1 : U.RC k 1 (j + ρ)) :
    ((fun a => star (c1v x1) (U.eB k j ρ (Sum.inl (Sum.inl a)))) = star (cX x1)) ∧
    ((fun v => star (c1v x1) (U.eB k j ρ (Sum.inl (Sum.inr v)))) = star (cV x1)) ∧
    ((fun a => star (c1v x1) (U.eB k j ρ (Sum.inr a))) = star (cS x1)) := ⟨rfl, rfl, rfl⟩

theorem mul_unitriangular_castSucc_col {m : Type*} (x1 : U.RC k 1 (j + ρ)) (M : Matrix m (Fin (j + 1)) ℂ) (a : m) (b : Fin j) :
    (M * Ut0 x1) a b.castSucc = M a b.castSucc := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [Ut0, Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, add_zero]
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc; simp [Matrix.one_apply_ne hc]
  · simp

theorem mul_unitriangular_last_col {m : Type*} (x1 : U.RC k 1 (j + ρ)) (M : Matrix m (Fin (j + 1)) ℂ) (a : m) :
    (M * Ut0 x1) a (Fin.last j) = ∑ b : Fin j, M a b.castSucc * cS x1 b + M a (Fin.last j) := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp [Ut0]

theorem Cm_cs (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) (v : Fin (2 * ρ + k + 1)) (b : Fin j) :
    (TX x1 x).1 v b.castSucc = x.1 v b := by simp [TX, Cm]

theorem Cm_last (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) (v : Fin (2 * ρ + k + 1)) :
    (TX x1 x).1 v (Fin.last j) = (cV x1 - Matrix.of x.1 *ᵥ cS x1) v := by
  simp [TX, Cm]

theorem Z_cc (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) (a b : Fin j) :
    ((-(1 / 2 : ℂ)) • ((Matrix.of (TX x1 x).1)ᴴ * Hpk k ρ * Matrix.of (TX x1 x).1) + Sm x1 x) a.castSucc b.castSucc =
      ((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + U.skewOf x.2) a b := by
  simp [Matrix.mul_apply, Cm_cs, Sm]

theorem Z_cl (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) (a : Fin j) :
    ((-(1 / 2 : ℂ)) • ((Matrix.of (TX x1 x).1)ᴴ * Hpk k ρ * Matrix.of (TX x1 x).1) + Sm x1 x) a.castSucc (Fin.last j) =
      (-(1 / 2 : ℂ)) * (((Matrix.of x.1)ᴴ * Hpk k ρ) *ᵥ (cV x1 - Matrix.of x.1 *ᵥ cS x1)) a + nc x1 x a := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Sm, Fin.lastCases_castSucc, Fin.lastCases_last]
  congr 2
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply, Cm_cs, Cm_last,
    Finset.sum_mul]

theorem Z_lc (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) (b : Fin j) :
    ((-(1 / 2 : ℂ)) • ((Matrix.of (TX x1 x).1)ᴴ * Hpk k ρ * Matrix.of (TX x1 x).1) + Sm x1 x) (Fin.last j) b.castSucc =
      (-(1 / 2 : ℂ)) * Matrix.vecMul (star (cV x1 - Matrix.of x.1 *ᵥ cS x1)) (Hpk k ρ * Matrix.of x.1) b -
        star (nc x1 x b) := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Sm, Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [sub_eq_add_neg]
  congr 2
  simp only [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply, Cm_cs, Cm_last,
    Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro l _; ring

theorem Z_ll (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) :
    ((-(1 / 2 : ℂ)) • ((Matrix.of (TX x1 x).1)ᴴ * Hpk k ρ * Matrix.of (TX x1 x).1) + Sm x1 x) (Fin.last j) (Fin.last j) =
      (-(1 / 2 : ℂ)) * (star (cV x1 - Matrix.of x.1 *ᵥ cS x1) ⬝ᵥ (Hpk k ρ *ᵥ (cV x1 - Matrix.of x.1 *ᵥ cS x1))) +
        Complex.I * (q2L x1 x : ℂ) := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Sm, Fin.lastCases_last]
  congr 2
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply, Cm_last,
    Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro l _; ring

theorem dot_symm {n : Type*} [Fintype n] (H : Matrix n n ℂ) (u w : n → ℂ) :
    star (star w ⬝ᵥ (H *ᵥ u)) = star u ⬝ᵥ (Hᴴ *ᵥ w) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, star_sum, star_mul', Pi.star_apply, star_star,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro l _; ring

theorem kl0 (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) :
    D.castM (by omega : 1 + (j + ρ) = (j + 1) + ρ) (U.Rn k 1 (j + ρ) x1 * U.embG k 1 (j + ρ) (U.Rn k j ρ x)) =
      U.Rn k (j + 1) ρ (TX x1 x) * U.muP k (j + 1) ρ (Um x1) := by
  rw [lhs_form, rhs_form, ut_eq, skewOf_TX]
  apply Ux2.mat_ext_eB (k := k) (j := j + 1) (ρ := ρ)
  intro x y
  rw [castM_apply, Ux3.block3_apply]
  have e1 := (star_column_components x1).1
  have e2 := (star_column_components x1).2.1
  have e3 := (star_column_components x1).2.2
  rcases x with ((a | v) | b) <;> rcases y with ((a' | v') | b')
  · cases a using Fin.cases with
    | zero =>
      cases a' using Fin.cases with
      | zero => simp only [pos0, Ux3.block3_apply]; simp [Um]
      | succ a' =>
        simp only [pos0, posX, Ux3.block3_apply]
        simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.neg_mul]
        rw [rowP, hrn_form, vecMul_block3_first_coords, e1, e2, e3]
        simp [Um]
        done
    | succ a =>
      cases a' using Fin.cases with
      | zero => simp only [posX, pos0, Ux3.block3_apply]; simp [Um]
      | succ a' => simp only [posX, Ux3.block3_apply]; simp [Um, Ux3.rn_eq, Ux3.block3_apply]
  · cases a using Fin.cases with
    | zero =>
      simp only [pos0, posV, Ux3.block3_apply]
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.neg_mul]
      rw [rowP, hrn_form, vecMul_block3_middle_coords, e1, e2, e3, Matrix.mul_assoc, Ux3.wMat_mul_apply, rev_zero']
      simp only [TX, Cm, Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Fin.lastCases_last, Matrix.mulVec, Pi.star_apply, star_sub, Matrix.zero_apply, mul_zero, Finset.sum_const_zero,
        zero_add, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, star_sum, star_mul', sub_mul, Finset.sum_sub_distrib,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm (γ := Fin j)]
      congr 1
      rw [sub_eq_add_neg]; congr 2
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro l _; ring
    | succ a =>
      simp only [posX, posV, Ux3.block3_apply]
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.neg_apply, Ux3.rn_eq, Ux3.block3_apply]
      rw [Matrix.mul_assoc, Ux3.wMat_mul_apply, Matrix.mul_assoc, Ux3.wMat_mul_apply, rev_succ']
      simp [TX, Cm, Matrix.mul_apply]
  · cases a using Fin.cases with
    | zero =>
      cases b' using Fin.lastCases with
      | last =>
        simp only [pos0, posL, Ux3.block3_apply]
        simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr]
        rw [Matrix.mul_assoc (G.wMat (j + 1)), Ux3.wMat_mul_apply (n := j + 1), rev_zero', mul_unitriangular_last_col]
        simp only [Z_lc, Z_ll]
        have hw1 : G.wMat 1 = 1 := by ext a b; fin_cases a; fin_cases b; simp [G.wMat]
        rw [hw1, Matrix.one_mul]
        have hH : (Hpk k ρ)ᴴ = Hpk k ρ := Ux4.hpk_conjTranspose k ρ
        have hw : (G.wMat j)ᴴ = G.wMat j := Ux4.wMat_conjTranspose j
        have hS : (U.skewOf x.2)ᴴ = -U.skewOf x.2 := Ux2.skewOf_ct x.2
        set c := Matrix.of x.1 with hc
        set S := U.skewOf x.2 with hSdef
        set Cl := cV x1 - c *ᵥ cS x1 with hCl
        set P := star (cX x1) ⬝ᵥ (G.wMat j *ᵥ cS x1) with hP
        set Q0 := star (cV x1) ⬝ᵥ (Hpk k ρ *ᵥ cV x1) with hQ0
        set B0 := star (cV x1) ⬝ᵥ (Hpk k ρ *ᵥ (c *ᵥ cS x1)) with hB0
        set Cc := star (cS x1) ⬝ᵥ (S *ᵥ cS x1) with hCc
        set E0 := star (c *ᵥ cS x1) ⬝ᵥ (Hpk k ρ *ᵥ (c *ᵥ cS x1)) with hE0

        have hL1 : ((Matrix.of x1.1)ᴴ * Hpk k (j + ρ) * Matrix.of x1.1) 0 0 =
            star (c1v x1) ⬝ᵥ (Hpk k (j + ρ) *ᵥ c1v x1) := by
          simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Matrix.of_apply, c1v,
            Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro l _; ring
        have hL2 : star (c1v x1) ⬝ᵥ (Hpk k (j + ρ) *ᵥ c1v x1) = star P + Q0 + P := by
          rw [Matrix.dotProduct_mulVec, Ux3.hpkBlocks k j ρ]
          simp only [dotProduct]
          rw [← (U.eB k j ρ).sum_comp]
          simp only [Fintype.sum_sum_type, vecMul_block3_first_coords, vecMul_block3_middle_coords, vecMul_block3_last_coord, e1, e2, e3]
          simp only [Matrix.vecMul_zero, Pi.zero_apply, zero_add, add_zero]
          have h1 : star P = Matrix.vecMul (star (cS x1)) (G.wMat j) ⬝ᵥ cX x1 := by
            rw [hP, ← Matrix.dotProduct_mulVec]
            have := dot_symm (G.wMat j) (cS x1) (cX x1)
            rw [hw] at this
            rw [this, Matrix.dotProduct_mulVec]
          have h2 : Q0 = Matrix.vecMul (star (cV x1)) (Hpk k ρ) ⬝ᵥ cV x1 := by rw [hQ0, Matrix.dotProduct_mulVec]
          have h3 : P = Matrix.vecMul (star (cX x1)) (G.wMat j) ⬝ᵥ cS x1 := by rw [hP, Matrix.dotProduct_mulVec]
          rw [h1, h2, h3]
          simp only [dotProduct, c1v, cX, cV, cS]
        have hLHS : ((-(1 / 2 : ℂ)) • ((Matrix.of x1.1)ᴴ * Hpk k (j + ρ) * Matrix.of x1.1) + U.skewOf x1.2) 0 0 =
            (-(1 / 2 : ℂ)) * (star P + Q0 + P) + Complex.I * (s1 x1 : ℂ) := by
          rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hL1, hL2, Ux2.skewOf_diag]; rfl
        rw [hLHS]

        have hsum : ∑ b : Fin j, ((-(1 / 2 : ℂ)) * Matrix.vecMul (star Cl) (Hpk k ρ * c) b - star (nc x1 x b)) * cS x1 b =
            (-(1 / 2 : ℂ)) * (Matrix.vecMul (star Cl) (Hpk k ρ * c) ⬝ᵥ cS x1) - star (nc x1 x) ⬝ᵥ cS x1 := by
          simp only [dotProduct, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc, Pi.star_apply]
        rw [hsum]
        have hN : star (nc x1 x) ⬝ᵥ cS x1 = P + Cc + (1 / 2 : ℂ) * B0 := by
          simp only [nc, star_add, star_sub, star_smul, Matrix.star_mulVec, Matrix.conjTranspose_mul, hH, hw, hS,
            Matrix.conjTranspose_conjTranspose, add_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul]
          rw [← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec]
          have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
          rw [Ux2.skewOf_ct, Matrix.neg_mulVec, dotProduct_neg, ← Matrix.mulVec_mulVec, h2]
          rw [hP, hCc, hB0, hSdef, hc]; ring
        have hC1 : Matrix.vecMul (star Cl) (Hpk k ρ * c) ⬝ᵥ cS x1 = B0 - E0 := by
          rw [← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, hCl, star_sub, sub_dotProduct, Matrix.star_mulVec]
          rw [hB0, hE0, Matrix.star_mulVec]
        have hC2 : star Cl ⬝ᵥ (Hpk k ρ *ᵥ Cl) = Q0 - B0 - star B0 + E0 := by
          have hsB : star B0 = star (c *ᵥ cS x1) ⬝ᵥ (Hpk k ρ *ᵥ cV x1) := by
            have := dot_symm (Hpk k ρ) (c *ᵥ cS x1) (cV x1)
            rw [hH] at this
            rw [hB0, this]
          rw [hsB, hCl, star_sub, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
          rw [hQ0, hB0, hE0]; ring
        rw [hN, hC1, hC2]
        have hCre : Cc.re = 0 := by
          have h1 := dot_symm S (cS x1) (cS x1)
          rw [hS, Matrix.neg_mulVec, dotProduct_neg, ← hCc] at h1
          have h2 := congrArg Complex.re h1
          simp at h2
          linarith
        have hq : (q2L x1 x : ℂ) = (s1 x1 : ℂ) + (P.im : ℂ) + (Cc.im : ℂ) + (B0.im : ℂ) := by
          simp [q2L, hP, hCc, hB0, hc, hSdef]
        rw [hq]
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hCre] <;> ring
      | cast b' =>
        simp only [pos0, posS, Ux3.block3_apply]
        simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.neg_mul, Matrix.neg_apply]
        rw [rowP, hrn_form, vecMul_block3_last_coord, e1, e2, e3, Matrix.mul_assoc (G.wMat (j + 1)), Ux3.wMat_mul_apply, rev_zero',
          mul_unitriangular_castSucc_col, Z_lc]
        have hH : (Hpk k ρ)ᴴ = Hpk k ρ := Ux4.hpk_conjTranspose k ρ
        have hw : (G.wMat j)ᴴ = G.wMat j := Ux4.wMat_conjTranspose j
        have hS : (U.skewOf x.2)ᴴ = -U.skewOf x.2 := Ux2.skewOf_ct x.2
        have key : -(Matrix.vecMul (star (cX x1)) (G.wMat j) + Matrix.vecMul (star (cV x1)) (Hpk k ρ * Matrix.of x.1) +
            Matrix.vecMul (star (cS x1)) ((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + U.skewOf x.2)) =
            (-(1 / 2 : ℂ)) • Matrix.vecMul (star (cV x1 - Matrix.of x.1 *ᵥ cS x1)) (Hpk k ρ * Matrix.of x.1) -
              star (nc x1 x) := by
          simp only [nc, star_add, star_sub, star_smul, Matrix.star_mulVec, Matrix.conjTranspose_mul, hH, hw, hS,
            Matrix.vecMul_add, Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_neg, Matrix.add_vecMul, Matrix.sub_vecMul,
            Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
          have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
          rw [h2]
          module
        have := congrFun key b'
        simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply] at this
        exact this
    | succ a =>
      cases b' using Fin.lastCases with
      | last =>
        simp only [posX, posL, Ux3.block3_apply]
        simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr]
        rw [Matrix.mul_assoc, Ux3.wMat_mul_apply, rev_succ', mul_unitriangular_last_col]
        simp only [Z_cc, Z_cl]
        show cX x1 a = _
        have hv : (((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + U.skewOf x.2) *ᵥ cS x1) +
            (-(1 / 2 : ℂ)) • (((Matrix.of x.1)ᴴ * Hpk k ρ) *ᵥ (cV x1 - Matrix.of x.1 *ᵥ cS x1)) + nc x1 x =
            G.wMat j *ᵥ cX x1 := by
          simp only [nc, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec]
          module
        have := congrFun hv a.rev
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wvec_apply, Fin.rev_rev] at this
        rw [← this]
        simp [Matrix.mulVec, dotProduct, add_assoc]
      | cast b' =>
        simp only [posX, posS, Ux3.block3_apply]
        simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.rn_eq, Ux3.block3_apply]
        rw [Ux3.wMat_mul_apply]
        rw [Matrix.mul_assoc (G.wMat (j + 1)), Ux3.wMat_mul_apply, rev_succ', mul_unitriangular_castSucc_col, Z_cc]
  ·
    cases a' using Fin.cases with
    | zero => simp only [posV, pos0, Ux3.block3_apply]; simp
    | succ a' => simp only [posV, posX, Ux3.block3_apply]; simp [Ux3.rn_eq, Ux3.block3_apply]
  ·
    simp only [posV, Ux3.block3_apply]; simp [Ux3.rn_eq, Ux3.block3_apply]
  ·
    cases b' using Fin.lastCases with
    | last =>
      simp only [posV, posL, Ux3.block3_apply]
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, mul_unitriangular_last_col, Matrix.of_apply, Cm_cs, Cm_last]
      simp [c1v, cV, Matrix.mulVec, dotProduct]
    | cast b' =>
      simp only [posV, posS, Ux3.block3_apply]
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, mul_unitriangular_castSucc_col, Matrix.of_apply, Cm_cs, Ux3.rn_eq, Ux3.block3_apply]
  ·
    cases b using Fin.lastCases with
    | last =>
      cases a' using Fin.cases with
      | zero => simp only [posL, pos0, Ux3.block3_apply]; simp
      | succ a' => simp only [posL, posX, Ux3.block3_apply]; simp
    | cast b =>
      cases a' using Fin.cases with
      | zero => simp only [posS, pos0, Ux3.block3_apply]; simp
      | succ a' => simp only [posS, posX, Ux3.block3_apply]; simp [Ux3.rn_eq, Ux3.block3_apply]
  ·
    cases b using Fin.lastCases with
    | last => simp only [posL, posV, Ux3.block3_apply]; simp
    | cast b => simp only [posS, posV, Ux3.block3_apply]; simp [Ux3.rn_eq, Ux3.block3_apply]
  ·
    cases b using Fin.lastCases with
    | last =>
      cases b' using Fin.lastCases with
      | last => simp only [posL, Ux3.block3_apply]; simp [Ut0]
      | cast b' => simp only [posL, posS, Ux3.block3_apply]; simp [Ut0]
    | cast b =>
      cases b' using Fin.lastCases with
      | last => simp only [posS, posL, Ux3.block3_apply]; simp [Ut0, c1v, cS]
      | cast b' => simp only [posS, Ux3.block3_apply]; simp [Ut0, Ux3.rn_eq, Ux3.block3_apply]

theorem castM_mul {a b : ℕ} (h : a = b) (A B' : B.Mat k a) : D.castM h (A * B') = D.castM h A * D.castM h B' := by
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem embG_mul {j' ρ' : ℕ} (A B' : B.Mat k ρ') : U.embG k j' ρ' (A * B') = U.embG k j' ρ' A * U.embG k j' ρ' B' := by
  rw [U.embG, U.embG, U.embG, Ux3.block3_mul]; congr 1 <;> simp

theorem leviElement_mul {j' ρ' : ℕ} (q1 q2 : Matrix (Fin j') (Fin j') ℂ) :
    U.muP k j' ρ' q1 * U.muP k j' ρ' q2 = U.muP k j' ρ' (q1 * q2) := by
  rw [U.muP, U.muP, U.muP, Ux3.block3_mul]
  congr 1 <;> simp [Matrix.conjTranspose_mul, Matrix.mul_inv_rev, Matrix.mul_assoc]
  simp [← Matrix.mul_assoc, Ux3.wMat_mul_self]

def Dm (q : Matrix (Fin j) (Fin j) ℂ) : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ :=
  fun a b => Fin.cases (motive := fun _ => ℂ) (Fin.cases (motive := fun _ => ℂ) 1 (fun _ => 0) b)
    (fun a' => Fin.cases (motive := fun _ => ℂ) 0 (fun b' => q a' b') b) a

theorem Dm_mul (q1 q2 : Matrix (Fin j) (Fin j) ℂ) : Dm q1 * Dm q2 = Dm (q1 * q2) := by
  ext a b
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  cases a using Fin.cases <;> cases b using Fin.cases <;> simp [Dm, Matrix.mul_apply]

theorem Dm_ct (q : Matrix (Fin j) (Fin j) ℂ) : (Dm q)ᴴ = Dm qᴴ := by
  ext a b
  cases a using Fin.cases <;> cases b using Fin.cases <;> simp [Dm]

theorem Dm_one : Dm (1 : Matrix (Fin j) (Fin j) ℂ) = 1 := by
  ext a b
  cases a using Fin.cases <;> cases b using Fin.cases <;> simp [Dm, Matrix.one_apply, Fin.succ_ne_zero]
  exact (Fin.succ_ne_zero _).symm

theorem Dm_inv (q : Matrix (Fin j) (Fin j) ℂ) (hq : IsUnit q.det) : (Dm q)⁻¹ = Dm q⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Dm_mul, Matrix.mul_nonsing_inv _ hq, Dm_one]

theorem emb_muP (q : Matrix (Fin j) (Fin j) ℂ) (hq : IsUnit q.det) :
    D.castM (by omega : 1 + (j + ρ) = (j + 1) + ρ) (U.embG k 1 (j + ρ) (U.muP k j ρ q)) = U.muP k (j + 1) ρ (Dm q) := by
  have hq' : IsUnit qᴴ.det := by rw [Matrix.det_conjTranspose]; exact hq.star
  rw [show U.muP k (j + 1) ρ (Dm q) = U.blk3 (Dm q) 0 0 0 1 0 0 0 (G.wMat (j + 1) * (Dm q)ᴴ⁻¹ * G.wMat (j + 1)) from rfl,
    Dm_ct, Dm_inv _ hq']
  apply Ux2.mat_ext_eB (k := k) (j := j + 1) (ρ := ρ)
  intro x y
  rw [castM_apply, Ux3.block3_apply]
  rcases x with ((a | v) | b) <;> rcases y with ((a' | v') | b')
  · cases a using Fin.cases <;> cases a' using Fin.cases <;>
      simp only [pos0, posX, U.embG, U.muP, Ux3.block3_apply] <;> simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Dm, Ux3.block3_apply]
  · cases a using Fin.cases <;> simp only [pos0, posX, posV, U.embG, U.muP, Ux3.block3_apply] <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply]
  · cases a using Fin.cases <;> cases b' using Fin.lastCases <;>
      simp only [pos0, posX, posS, posL, U.embG, U.muP, Ux3.block3_apply] <;> simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply]
  · cases a' using Fin.cases <;> simp only [pos0, posX, posV, U.embG, U.muP, Ux3.block3_apply] <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply]
  · simp only [posV, U.embG, U.muP, Ux3.block3_apply]; simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply]
  · cases b' using Fin.lastCases <;> simp only [posV, posS, posL, U.embG, U.muP, Ux3.block3_apply] <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply]
  · cases b using Fin.lastCases <;> cases a' using Fin.cases <;>
      simp only [pos0, posX, posS, posL, U.embG, U.muP, Ux3.block3_apply] <;> simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply]
  · cases b using Fin.lastCases <;> simp only [posV, posS, posL, U.embG, U.muP, Ux3.block3_apply] <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply]
  · cases b using Fin.lastCases <;> cases b' using Fin.lastCases <;>
      simp only [posS, posL, U.embG, U.muP, Ux3.block3_apply] <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply, w_conj_apply, rev_last', rev_castSucc', Dm]

theorem emb_emb (y : B.Mat k ρ) :
    D.castM (by omega : 1 + (j + ρ) = (j + 1) + ρ) (U.embG k 1 (j + ρ) (U.embG k j ρ y)) = U.embG k (j + 1) ρ y := by
  apply Ux2.mat_ext_eB (k := k) (j := j + 1) (ρ := ρ)
  intro x y'
  rw [show U.embG k (j + 1) ρ y = U.blk3 1 0 0 0 y 0 0 0 1 from rfl, castM_apply, Ux3.block3_apply]
  rcases x with ((a | v) | b) <;> rcases y' with ((a' | v') | b')
  · cases a using Fin.cases <;> cases a' using Fin.cases <;>
      simp only [pos0, posX, U.embG, Ux3.block3_apply] <;> simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply, Matrix.one_apply, Fin.succ_ne_zero] <;>
      exact (Fin.succ_ne_zero _).symm
  · cases a using Fin.cases <;> simp only [pos0, posX, posV, U.embG, Ux3.block3_apply] <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply]
  · cases a using Fin.cases <;> cases b' using Fin.lastCases <;>
      simp only [pos0, posX, posS, posL, U.embG, Ux3.block3_apply] <;> simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply]
  · cases a' using Fin.cases <;> simp only [pos0, posX, posV, U.embG, Ux3.block3_apply] <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply]
  · simp only [posV, U.embG, Ux3.block3_apply]; simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply]
  · cases b' using Fin.lastCases <;> simp only [posV, posS, posL, U.embG, Ux3.block3_apply] <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply]
  · cases b using Fin.lastCases <;> cases a' using Fin.cases <;>
      simp only [pos0, posX, posS, posL, U.embG, Ux3.block3_apply] <;> simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply]
  · cases b using Fin.lastCases <;> simp only [posV, posS, posL, U.embG, Ux3.block3_apply] <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply]
  · cases b using Fin.lastCases <;> cases b' using Fin.lastCases <;>
      simp only [posS, posL, U.embG, Ux3.block3_apply] <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Ux3.block3_apply, Matrix.one_apply] <;> exact (Fin.castSucc_lt_last _).ne'

def TUU (x1 : U.RC k 1 (j + ρ)) (u : G.UT j → ℂ) : G.UT (j + 1) → ℂ :=
  fun p => (Um x1 * Dm (G.upper u)) p.1.1 p.1.2

theorem dm_uni (q : Matrix (Fin j) (Fin j) ℂ) (hq : Ux2.uniK (Ux2.kU j) q) : Ux2.uniK (Ux2.kU (j + 1)) (Dm q) := by
  refine ⟨fun i => ?_, fun a b hab => ?_⟩
  · cases i using Fin.cases with
    | zero => simp [Dm]
    | succ i => simp [Dm, hq.1 i]
  · rw [Ux2.kU_lt] at hab
    cases a using Fin.cases with
    | zero => exact absurd hab (Fin.not_lt_zero _)
    | succ a =>
      cases b using Fin.cases with
      | zero => simp [Dm]
      | succ b => simp only [Dm, Fin.cases_succ]; exact hq.2 a b (Ux2.kU_lt.mpr (Fin.succ_lt_succ_iff.mp hab))

theorem upper_TUU (x1 : U.RC k 1 (j + ρ)) (u : G.UT j → ℂ) : G.upper (TUU x1 u) = Um x1 * Dm (G.upper u) := by
  have hk : Function.Injective (Ux2.kU (j + 1)) := Ux2.kU_inj
  exact (Ux2.upper_eq (Ux2.uniK_mul hk (um_uni x1) (dm_uni _ (Ux2.upper_uni u)))).symm

theorem upper_det (u : G.UT j → ℂ) : IsUnit (G.upper u).det := Ux2.upK_unit (Ux2.upper_uni u)

theorem kl (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) (u : G.UT j → ℂ) (y : B.Mat k ρ) :
    D.castM (by omega : 1 + (j + ρ) = (j + 1) + ρ)
        (U.Rn k 1 (j + ρ) x1 * U.embG k 1 (j + ρ) (U.Rn k j ρ x * U.muP k j ρ (G.upper u) * U.embG k j ρ y)) =
      U.Rn k (j + 1) ρ (TX x1 x) * U.muP k (j + 1) ρ (G.upper (TUU x1 u)) * U.embG k (j + 1) ρ y := by
  rw [embG_mul, embG_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, castM_mul, castM_mul, kl0, emb_muP _ (upper_det u),
    emb_emb, Matrix.mul_assoc (U.Rn k (j + 1) ρ (TX x1 x)), leviElement_mul, upper_TUU]

end Formalism.FourierDecayAlt.P.Dx2.Split

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Formalism.FourierDecayAlt.P.Dx2.SplitM

open Formalism.FourierDecayAlt.P.Dx2.Split

variable {k j ρ : ℕ}

theorem conj_mp : MeasurePreserving (fun z : ℂ => star z) volume volume := by
  have e := Complex.volume_preserving_equiv_real_prod
  have h2 : MeasurePreserving (fun p : ℝ × ℝ => (p.1, -p.2)) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)
  have h3 := (e.symm Complex.measurableEquivRealProd).comp (h2.comp e)
  have heq : (fun z : ℂ => star z) =
      ⇑Complex.measurableEquivRealProd.symm ∘ (fun p : ℝ × ℝ => (p.1, -p.2)) ∘ ⇑Complex.measurableEquivRealProd := by
    funext z; apply Complex.ext <;> simp [Complex.measurableEquivRealProd_symm_apply, Complex.measurableEquivRealProd_apply]
  rw [heq]; exact h3

theorem vconj_mp {ι : Type*} [Fintype ι] : MeasurePreserving (fun v : ι → ℂ => star v) volume volume :=
  volume_preserving_pi (fun _ => conj_mp)

theorem mp_vec {m : Type*} [Fintype m] [DecidableEq m] (g : Matrix m m ℂ) (h : ‖g.det‖ = 1) :
    MeasurePreserving (fun x : m → ℂ => g *ᵥ x) volume volume := by
  have hdet : LinearMap.det ((Matrix.toLin' g).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, h]; norm_num
  have h1 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (m → ℂ))
    (f := (Matrix.toLin' g).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h1
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h1
  refine ⟨?_, h1⟩
  exact (LinearMap.continuous_of_finiteDimensional ((Matrix.toLin' g).restrictScalars ℝ)).measurable

theorem norm_det_w (j : ℕ) : ‖(G.wMat j).det‖ = 1 := by
  have h := congrArg Matrix.det (Ux3.wMat_mul_self j)
  rw [Matrix.det_mul, Matrix.det_one] at h
  have h2 : ‖(G.wMat j).det‖ ^ 2 = 1 := by rw [sq, ← norm_mul, h, norm_one]
  have h3 : 0 ≤ ‖(G.wMat j).det‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖(G.wMat j).det‖ - 1)]

theorem det_upper (u : G.UT j → ℂ) : (G.upper u).det = 1 := by
  have hu := Ux2.upper_uni u
  rw [Matrix.det_of_isUpperTriangular]
  · simp [hu.1]
  · intro a b hab
    exact hu.2 a b (Ux2.kU_lt.mpr hab)

theorem middle_four_swap_measure_preserving {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ) [SigmaFinite μa] [SigmaFinite μb]
    [SigmaFinite μc] [SigmaFinite μd] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (measurePreserving_prodAssoc μb μc μd).symm
  have h3 := (Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd)
  have h4 := measurePreserving_prodAssoc μc μb μd
  have h5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm
  have hin := h4.comp (h3.comp h2)
  have hall := h5.comp (((MeasurePreserving.id μa).prod hin).comp h1)
  convert hall using 1
  funext ⟨⟨a, b⟩, c, d⟩; rfl

section fibre

variable (k j ρ)

abbrev Bs := U.RC k j ρ × (G.UT j → ℂ)

abbrev Fs := (((Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) × (Fin j → ℂ)) × ℝ

variable {k j ρ}

def unipotentTranslateCoord (b : Bs k j ρ) (s : Fin j → ℂ) : Fin j → ℂ := -(Matrix.vecMul (star s) (G.wMat j * G.upper b.2))

def ncf (b : Bs k j ρ) (s : Fin j → ℂ) (v : Fin (2 * ρ + k + 1) → ℂ) (a : Fin j → ℂ) : Fin j → ℂ :=
  G.wMat j *ᵥ a + (-(U.skewOf b.1.2 *ᵥ s) + (1 / 2 : ℂ) • (((Matrix.of b.1.1)ᴴ * Hpk k ρ) *ᵥ v))

def q2f (b : Bs k j ρ) (s : Fin j → ℂ) (v : Fin (2 * ρ + k + 1) → ℂ) (a : Fin j → ℂ) (t : ℝ) : ℝ :=
  t + ((star a ⬝ᵥ (G.wMat j *ᵥ s)).im + (star s ⬝ᵥ (U.skewOf b.1.2 *ᵥ s)).im +
    (star v ⬝ᵥ (Hpk k ρ *ᵥ (Matrix.of b.1.1 *ᵥ s))).im)

def lev1 (b : Bs k j ρ) (p : (Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) : (Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ) :=
  (unipotentTranslateCoord b p.1, p.2 - Matrix.of b.1.1 *ᵥ p.1)

def lev2 (b : Bs k j ρ) (p : ((Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) × (Fin j → ℂ)) :
    ((Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) × (Fin j → ℂ) :=
  (lev1 b p.1, ncf b p.1.1 p.1.2 p.2)

def lev3 (b : Bs k j ρ) (p : Fs k j ρ) : Fs k j ρ := (lev2 b p.1, q2f b p.1.1.1 p.1.1.2 p.1.2 p.2)

end fibre

theorem continuous_upper : Continuous (G.upper (d := j)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply]
  split_ifs <;> fun_prop

theorem continuous_skew : Continuous (U.skewOf (j := j)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [U.skewOf, G.strictUpper, Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    Matrix.diagonal_apply]
  split_ifs <;> fun_prop

theorem unipotent_coordinates_measure_preserving (b : Bs k j ρ) : MeasurePreserving (unipotentTranslateCoord b) volume volume := by
  set Mx := G.wMat j * G.upper b.2
  have hdet : ‖(-Mxᵀ).det‖ = 1 := by
    rw [Matrix.det_neg, Matrix.det_transpose, Matrix.det_mul, det_upper, mul_one, norm_mul, norm_pow, norm_neg,
      norm_one, one_pow, one_mul, norm_det_w]
  have h := (mp_vec (-Mxᵀ) hdet).comp vconj_mp
  convert h using 1
  funext s
  simp only [unipotentTranslateCoord, Mx, Function.comp, Matrix.neg_mulVec]
  rw [Matrix.mulVec_transpose]

theorem measurePreserving_first_level_map (b : Bs k j ρ) : MeasurePreserving (lev1 b) volume volume := by
  rw [Measure.volume_eq_prod]
  refine (unipotent_coordinates_measure_preserving b).skew_product (g := fun s v => v - Matrix.of b.1.1 *ᵥ s) ?_ ?_
  · exact (Continuous.measurable (by fun_prop))
  · exact Filter.Eventually.of_forall fun s => (measurePreserving_sub_right volume _).map_eq

theorem measurePreserving_second_level_map (b : Bs k j ρ) : MeasurePreserving (lev2 b) volume volume := by
  rw [Measure.volume_eq_prod]
  refine (measurePreserving_first_level_map b).skew_product (g := fun p a => ncf b p.1 p.2 a) ?_ ?_
  · exact (Continuous.measurable (by unfold ncf; fun_prop))
  · refine Filter.Eventually.of_forall fun p => ?_
    exact ((measurePreserving_add_right volume _).comp (mp_vec (G.wMat j) (norm_det_w j))).map_eq

theorem measurePreserving_third_level_map (b : Bs k j ρ) : MeasurePreserving (lev3 b) volume volume := by
  rw [Measure.volume_eq_prod]
  refine (measurePreserving_second_level_map b).skew_product (g := fun p t => q2f b p.1.1 p.1.2 p.2 t) ?_ ?_
  · exact (Continuous.measurable (by unfold q2f; fun_prop))
  · exact Filter.Eventually.of_forall fun p => (measurePreserving_add_right volume _).map_eq

theorem tskew_mp : MeasurePreserving (fun p : Bs k j ρ × Fs k j ρ => (p.1, lev3 p.1 p.2)) volume volume := by
  haveI h1 : SigmaFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI h2 : SigmaFinite (volume : Measure (U.RC k j ρ)) := inferInstance
  haveI h3 : SigmaFinite (volume : Measure (Bs k j ρ)) := inferInstance
  haveI h4 : SigmaFinite (volume : Measure (Fs k j ρ)) := inferInstance
  rw [Measure.volume_eq_prod]
  refine (MeasurePreserving.id volume).skew_product (g := fun b f => lev3 b f) ?_ ?_
  · haveI : BorelSpace ((Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) := Prod.borelSpace
    haveI : BorelSpace (((Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) × (Fin j → ℂ)) := Prod.borelSpace
    haveI : BorelSpace (Fs k j ρ) := Prod.borelSpace
    haveI : BorelSpace ((G.UT j → ℂ) × (Fin j → ℝ)) := Prod.borelSpace
    haveI : BorelSpace (U.RC k j ρ) := Prod.borelSpace
    haveI : BorelSpace (Bs k j ρ) := Prod.borelSpace
    haveI : BorelSpace (Bs k j ρ × Fs k j ρ) := Prod.borelSpace
    apply Continuous.measurable
    have hu : Continuous fun p : Bs k j ρ × Fs k j ρ => G.upper p.1.2 := continuous_upper.comp (by fun_prop)
    have hs : Continuous fun p : Bs k j ρ × Fs k j ρ => U.skewOf p.1.1.2 := continuous_skew.comp (by fun_prop)
    unfold lev3 lev2 lev1 unipotentTranslateCoord ncf q2f
    fun_prop
  · exact Filter.Eventually.of_forall fun b => (measurePreserving_third_level_map b).map_eq

def swapIx : U.Ix k j ρ ≃ U.Ix k j ρ where
  toFun := fun z => match z with
    | Sum.inl (Sum.inl a) => Sum.inr a
    | Sum.inl (Sum.inr v) => Sum.inl (Sum.inr v)
    | Sum.inr a => Sum.inl (Sum.inl a)
  invFun := fun z => match z with
    | Sum.inl (Sum.inl a) => Sum.inr a
    | Sum.inl (Sum.inr v) => Sum.inl (Sum.inr v)
    | Sum.inr a => Sum.inl (Sum.inl a)
  left_inv := by rintro ((a | v) | a) <;> rfl
  right_inv := by rintro ((a | v) | a) <;> rfl

def e1 (x1 : U.RC k 1 (j + ρ)) : Fs k j ρ := (((cS x1, cV x1), cX x1), s1 x1)

instance isEmpty_upperTriangular_one : IsEmpty (G.UT 1) := ⟨fun ⟨⟨a, b⟩, h⟩ => by
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst ha hb; exact lt_irrefl _ h⟩

theorem measurePreserving_coord_equiv : MeasurePreserving (e1 (k := k) (j := j) (ρ := ρ)) volume volume := by

  have g1 : MeasurePreserving (fun (c : Fin (2 * (j + ρ) + k + 1) → Fin 1 → ℂ) (i : Fin (2 * (j + ρ) + k + 1)) => c i 0)
      volume volume :=
    measurePreserving_pi (fun _ => (volume : Measure (Fin 1 → ℂ))) (fun _ => (volume : Measure ℂ))
      (f := fun _ => MeasurableEquiv.funUnique (Fin 1) ℂ) (fun _ => measurePreserving_funUnique volume (Fin 1))
  set σ : U.Ix k j ρ ≃ Fin (2 * (j + ρ) + k + 1) := swapIx.trans (U.eB k j ρ)
  have g2 := (measurePreserving_piCongrLeft (fun _ : Fin (2 * (j + ρ) + k + 1) => (volume : Measure ℂ)) σ).symm
  have g3a := measurePreserving_sumPiEquivProdPi (X := fun _ : (Fin j ⊕ Fin (2 * ρ + k + 1)) ⊕ Fin j => ℂ)
    (fun _ => (volume : Measure ℂ))
  have g3b := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin j ⊕ Fin (2 * ρ + k + 1) => ℂ)
    (fun _ => (volume : Measure ℂ))
  have g3 := (g3b.prod (MeasurePreserving.id (volume : Measure (Fin j → ℂ)))).comp g3a
  have ga := g3.comp (g2.comp g1)

  have hP : IsProbabilityMeasure (volume : Measure (G.UT 1 → ℂ)) := by
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]; infer_instance
  have gb : MeasurePreserving (fun (q : (G.UT 1 → ℂ) × (Fin 1 → ℝ)) => q.2 0) volume volume := by
    have a := (measurePreserving_funUnique (volume : Measure ℝ) (Fin 1))
    have b : MeasurePreserving (Prod.snd : (G.UT 1 → ℂ) × (Fin 1 → ℝ) → (Fin 1 → ℝ)) volume volume :=
      measurePreserving_snd
    exact a.comp b
  have h := ga.prod gb
  have heq : (e1 (k := k) (j := j) (ρ := ρ)) = Prod.map
      ((Prod.map (⇑(MeasurableEquiv.sumPiEquivProdPi fun _ : Fin j ⊕ Fin (2 * ρ + k + 1) => ℂ)) id ∘
        ⇑(MeasurableEquiv.sumPiEquivProdPi fun _ : (Fin j ⊕ Fin (2 * ρ + k + 1)) ⊕ Fin j => ℂ)) ∘
        ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * (j + ρ) + k + 1) => ℂ) σ).symm ∘
          fun (c : Fin (2 * (j + ρ) + k + 1) → Fin 1 → ℂ) i => c i 0)
      (fun q : (G.UT 1 → ℂ) × (Fin 1 → ℝ) => q.2 0) := by
    funext x1
    rfl
  rw [heq]; exact h

theorem src_mp : MeasurePreserving (fun z : U.RC k 1 (j + ρ) × Bs k j ρ => (z.2, e1 z.1)) volume volume := by
  haveI : SigmaFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k j ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Bs k j ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k 1 (j + ρ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fs k j ρ)) := inferInstance
  have h1 : MeasurePreserving (Prod.swap : U.RC k 1 (j + ρ) × Bs k j ρ → Bs k j ρ × U.RC k 1 (j + ρ)) volume volume :=
    Measure.measurePreserving_swap
  have h2 := ((MeasurePreserving.id (volume : Measure (Bs k j ρ))).prod (measurePreserving_coord_equiv (k := k) (j := j) (ρ := ρ))).comp h1
  exact h2

def eL : G.UT j ⊕ Fin j ≃ G.UT (j + 1) where
  toFun := fun z => match z with
    | Sum.inl p => ⟨(p.1.1.castSucc, p.1.2.castSucc), Fin.castSucc_lt_castSucc_iff.mpr p.2⟩
    | Sum.inr a => ⟨(a.castSucc, Fin.last j), Fin.castSucc_lt_last a⟩
  invFun := fun q =>
    if h : q.1.2 = Fin.last j then
      Sum.inr (q.1.1.castPred (Fin.ne_last_of_lt (h ▸ q.2)))
    else
      Sum.inl ⟨(q.1.1.castPred (Fin.ne_last_of_lt q.2), q.1.2.castPred h), by
        rw [Fin.castPred_lt_castPred_iff]; exact q.2⟩
  left_inv := by
    rintro (p | a)
    · have : p.1.2.castSucc ≠ Fin.last j := Fin.castSucc_ne_last _
      simp [this]
    · simp
  right_inv := by
    rintro ⟨⟨a, b⟩, h⟩
    by_cases hb : b = Fin.last j
    · subst hb; simp
    · simp [hb]

def eZ : Fin j ⊕ G.UT j ≃ G.UT (j + 1) where
  toFun := fun z => match z with
    | Sum.inl b => ⟨(0, b.succ), Fin.succ_pos b⟩
    | Sum.inr p => ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_lt_succ_iff.mpr p.2⟩
  invFun := fun q =>
    if h : q.1.1 = 0 then
      Sum.inl (q.1.2.pred (Fin.ne_zero_of_lt (h ▸ q.2)))
    else
      Sum.inr ⟨(q.1.1.pred h, q.1.2.pred (Fin.ne_zero_of_lt q.2)), by
        rw [Fin.pred_lt_pred_iff]; exact q.2⟩
  left_inv := by
    rintro (b | p)
    · simp
    · have : p.1.1.succ ≠ 0 := Fin.succ_ne_zero _
      simp [this]
  right_inv := by
    rintro ⟨⟨a, b⟩, h⟩
    by_cases ha : a = 0
    · subst ha; simp
    · simp [ha]

section combine

def rowE {α : Type*} [MeasurableSpace α] (p : (Fin j → α) × α) : Fin (j + 1) → α :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => α) (Fin.last j)).symm (p.2, p.1)

theorem rowE_cs {α : Type*} [MeasurableSpace α] (p : (Fin j → α) × α) (b : Fin j) : rowE p b.castSucc = p.1 b := by
  simp [rowE, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_last']

theorem rowE_last {α : Type*} [MeasurableSpace α] (p : (Fin j → α) × α) : rowE p (Fin.last j) = p.2 := by
  simp [rowE, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_last']

theorem rowE_mp {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)] :
    MeasurePreserving (rowE (j := j) (α := α)) volume volume := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (j + 1) => α) (Fin.last j)).symm.comp
    (Measure.measurePreserving_swap (μ := (volume : Measure (Fin j → α))) (ν := (volume : Measure α)))
  have e : (rowE (j := j) (α := α)) =
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => α) (Fin.last j)).symm ∘ Prod.swap := funext fun p => rfl
  rw [e]; exact h

def combC (p : (Fin (2 * ρ + k + 1) → Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) :
    Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ := fun v => rowE (p.1 v, p.2 v)

theorem combC_mp : MeasurePreserving (combC (k := k) (j := j) (ρ := ρ)) volume volume := by
  have h1 := (measurePreserving_arrowProdEquivProdArrow (Fin j → ℂ) ℂ (Fin (2 * ρ + k + 1))
    (fun _ => (volume : Measure (Fin j → ℂ))) (fun _ => (volume : Measure ℂ))).symm
  have h2 : MeasurePreserving (fun (g : Fin (2 * ρ + k + 1) → (Fin j → ℂ) × ℂ) v => rowE (g v)) volume volume :=
    volume_preserving_pi (fun _ => rowE_mp)
  exact h2.comp h1

def combineUpperTriangularCoords (p : (G.UT j → ℂ) × (Fin j → ℂ)) : G.UT (j + 1) → ℂ :=
  MeasurableEquiv.piCongrLeft (fun _ : G.UT (j + 1) => ℂ) eL ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ)).symm p)

def combU (p : (Fin j → ℂ) × (G.UT j → ℂ)) : G.UT (j + 1) → ℂ :=
  MeasurableEquiv.piCongrLeft (fun _ : G.UT (j + 1) => ℂ) eZ ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ)).symm p)

theorem combined_coordinates_measure_preserving : MeasurePreserving (combineUpperTriangularCoords (j := j)) volume volume :=
  (measurePreserving_piCongrLeft (fun _ : G.UT (j + 1) => (volume : Measure ℂ)) eL).comp
    (measurePreserving_sumPiEquivProdPi_symm (X := fun _ : G.UT j ⊕ Fin j => ℂ) (fun _ => (volume : Measure ℂ)))

theorem combU_mp : MeasurePreserving (combU (j := j)) volume volume :=
  (measurePreserving_piCongrLeft (fun _ : G.UT (j + 1) => (volume : Measure ℂ)) eZ).comp
    (measurePreserving_sumPiEquivProdPi_symm (X := fun _ : Fin j ⊕ G.UT j => ℂ) (fun _ => (volume : Measure ℂ)))

theorem combined_coordinates_left (p : (G.UT j → ℂ) × (Fin j → ℂ)) (w : G.UT j) : combineUpperTriangularCoords p (eL (Sum.inl w)) = p.1 w := by
  simp [combineUpperTriangularCoords, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply]; rfl

theorem combineUpperTriangular_inr (p : (G.UT j → ℂ) × (Fin j → ℂ)) (a : Fin j) : combineUpperTriangularCoords p (eL (Sum.inr a)) = p.2 a := by
  simp [combineUpperTriangularCoords, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply]; rfl

theorem combU_inl (p : (Fin j → ℂ) × (G.UT j → ℂ)) (b : Fin j) : combU p (eZ (Sum.inl b)) = p.1 b := by
  simp [combU, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply]; rfl

theorem combU_inr (p : (Fin j → ℂ) × (G.UT j → ℂ)) (w : G.UT j) : combU p (eZ (Sum.inr w)) = p.2 w := by
  simp [combU, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply]; rfl

end combine

abbrev Ts := (((Fin (2 * ρ + k + 1) → Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) ×
    (((G.UT j → ℂ) × (Fin j → ℂ)) × ((Fin j → ℝ) × ℝ))) × ((Fin j → ℂ) × (G.UT j → ℂ))

def perm8 (q : Bs k j ρ × Fs k j ρ) : Ts (k := k) (j := j) (ρ := ρ) :=
  (((q.1.1.1, q.2.1.1.2), ((q.1.1.2.1, q.2.1.2), (q.1.1.2.2, q.2.2))), (q.2.1.1.1, q.1.2))

theorem measurePreserving_coord_permutation : MeasurePreserving (perm8 (k := k) (j := j) (ρ := ρ)) volume volume := by
  haveI : SigmaFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT j → ℂ) × (Fin j → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k j ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((Fin (2 * ρ + k + 1) → ℂ) × ((Fin j → ℂ) × ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure ((Fin j → ℂ) × ℝ)) := inferInstance
  set μc := (volume : Measure (Fin (2 * ρ + k + 1) → Fin j → ℂ))
  set μq1 := (volume : Measure (G.UT j → ℂ))
  set μq2 := (volume : Measure (Fin j → ℝ))
  set μu := (volume : Measure (G.UT j → ℂ))
  set μU0 := (volume : Measure (Fin j → ℂ))
  set μCL := (volume : Measure (Fin (2 * ρ + k + 1) → ℂ))
  set μQ1L := (volume : Measure (Fin j → ℂ))
  set μQ2L := (volume : Measure ℝ)
  have a1 := measurePreserving_prodAssoc (μU0.prod μCL) μQ1L μQ2L
  have a2 := measurePreserving_prodAssoc μU0 μCL (μQ1L.prod μQ2L)
  have s1 := (MeasurePreserving.id ((μc.prod (μq1.prod μq2)).prod μu)).prod (a2.comp a1)
  have s2 := (MeasurePreserving.id ((μc.prod (μq1.prod μq2)).prod μu)).prod
    (Measure.measurePreserving_swap (μ := μU0) (ν := μCL.prod (μQ1L.prod μQ2L)))
  have s3 := middle_four_swap_measure_preserving (μc.prod (μq1.prod μq2)) μu (μCL.prod (μQ1L.prod μQ2L)) μU0
  have s4 := (MeasurePreserving.id ((μc.prod (μq1.prod μq2)).prod (μCL.prod (μQ1L.prod μQ2L)))).prod
    (Measure.measurePreserving_swap (μ := μu) (ν := μU0))
  have s5 := (middle_four_swap_measure_preserving μc (μq1.prod μq2) μCL (μQ1L.prod μQ2L)).prod (MeasurePreserving.id (μU0.prod μu))
  have s6 := ((MeasurePreserving.id (μc.prod μCL)).prod (middle_four_swap_measure_preserving μq1 μq2 μQ1L μQ2L)).prod
    (MeasurePreserving.id (μU0.prod μu))
  have hall := s6.comp (s5.comp (s4.comp (s3.comp (s2.comp s1))))
  have e : (perm8 (k := k) (j := j) (ρ := ρ)) = _ := funext fun q => rfl
  exact hall

def tgt (q : Bs k j ρ × Fs k j ρ) : U.RC k (j + 1) ρ × (G.UT (j + 1) → ℂ) :=
  ((combC (perm8 q).1.1, (combineUpperTriangularCoords (perm8 q).1.2.1, rowE (perm8 q).1.2.2)), combU (perm8 q).2)

theorem tgt_mp : MeasurePreserving (tgt (k := k) (j := j) (ρ := ρ)) volume volume := by
  haveI : SigmaFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite ((volume : Measure (G.UT (j + 1) → ℂ)).prod (volume : Measure (Fin (j + 1) → ℝ))) :=
    inferInstance
  haveI : SigmaFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT j → ℂ) × (Fin j → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure ((Fin j → ℂ) × (G.UT j → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((Fin j → ℝ) × ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((Fin (2 * ρ + k + 1) → Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ))) :=
    inferInstance
  haveI : SigmaFinite (volume : Measure (((G.UT j → ℂ) × (Fin j → ℂ)) × ((Fin j → ℝ) × ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (((Fin (2 * ρ + k + 1) → Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) ×
    (((G.UT j → ℂ) × (Fin j → ℂ)) × ((Fin j → ℝ) × ℝ)))) := inferInstance
  have h := (((combC_mp (k := k) (j := j) (ρ := ρ)).prod ((combined_coordinates_measure_preserving (j := j)).prod
    (rowE_mp (j := j) (α := ℝ)))).prod (combU_mp (j := j))).comp measurePreserving_coord_permutation
  exact h

theorem tgt_id (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) (u : G.UT j → ℂ) :
    tgt ((x, u), lev3 (x, u) (e1 x1)) = (TX x1 x, TUU x1 u) := by
  simp only [tgt, perm8, lev3, lev2, lev1, e1]
  refine Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) ?_
  · funext v b
    cases b using Fin.lastCases with
    | last => simp only [combC, rowE_last]; rw [Cm_last]
    | cast b => simp only [combC, rowE_cs]; rw [Cm_cs]
  · funext p
    obtain ⟨w, rfl⟩ := eL.surjective p
    rcases w with w | a
    · dsimp only
      rw [combined_coordinates_left]
      show x.2.1 w = Sm x1 x w.1.1.castSucc w.1.2.castSucc
      simp only [Sm, Fin.lastCases_castSucc]
      rw [Ux2.skewOf_lt _ w.2]
    · dsimp only
      rw [combineUpperTriangular_inr]
      show ncf (x, u) (cS x1) (cV x1) (cX x1) a = Sm x1 x a.castSucc (Fin.last j)
      simp only [Sm, Fin.lastCases_castSucc, Fin.lastCases_last, ncf, nc]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply]
      ring
  · funext a
    cases a using Fin.lastCases with
    | last =>
      dsimp only
      rw [rowE_last]
      show q2f (x, u) (cS x1) (cV x1) (cX x1) (s1 x1) = (Sm x1 x (Fin.last j) (Fin.last j)).im
      simp only [Sm, Fin.lastCases_last, q2f, q2L]
      simp
      ring
    | cast a =>
      dsimp only
      rw [rowE_cs]
      show x.2.2 a = (Sm x1 x a.castSucc a.castSucc).im
      simp only [Sm, Fin.lastCases_castSucc]
      rw [Ux2.skewOf_diag]; simp
  · funext p
    obtain ⟨w, rfl⟩ := eZ.surjective p
    rcases w with b | w
    · dsimp only
      rw [combU_inl]
      show unipotentTranslateCoord (x, u) (cS x1) b = (Um x1 * Dm (G.upper u)) 0 b.succ
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp only [Um, Dm, Fin.cases_zero, Fin.cases_succ, mul_zero, zero_add, unipotentTranslateCoord, Pi.neg_apply]
      rw [← Matrix.vecMul_vecMul]
      simp [Matrix.vecMul, dotProduct, Finset.sum_neg_distrib]
    · dsimp only
      rw [combU_inr]
      show u w = (Um x1 * Dm (G.upper u)) w.1.1.succ w.1.2.succ
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp only [Um, Dm, Fin.cases_zero, Fin.cases_succ, zero_mul, zero_add]
      rw [Finset.sum_eq_single w.1.1]
      · simp [G.upper, G.strictUpper, w.2, ne_of_lt w.2]
      · intro c _ hc; simp [Matrix.one_apply_ne (Ne.symm hc)]
      · simp

theorem T_mp : MeasurePreserving (fun z : U.RC k 1 (j + ρ) × Bs k j ρ => (TX z.1 z.2.1, TUU z.1 z.2.2))
    volume volume := by
  have h := ((tgt_mp (k := k) (j := j) (ρ := ρ)).comp (tskew_mp (k := k) (j := j) (ρ := ρ))).comp
    (src_mp (k := k) (j := j) (ρ := ρ))
  have e : (fun z : U.RC k 1 (j + ρ) × Bs k j ρ => (TX z.1 z.2.1, TUU z.1 z.2.2)) =
      tgt ∘ (fun p : Bs k j ρ × Fs k j ρ => (p.1, lev3 p.1 p.2)) ∘ (fun z : U.RC k 1 (j + ρ) × Bs k j ρ => (z.2, e1 z.1)) :=
    funext fun z => (tgt_id z.1 z.2.1 z.2.2).symm
  rw [e]; exact h

end Formalism.FourierDecayAlt.P.Dx2.SplitM

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Formalism.FourierDecayAlt.P.Dx2.SplitF

open Formalism.FourierDecayAlt.P.Dx2.Split Formalism.FourierDecayAlt.P.Dx2.SplitM Formalism.FourierDecayAlt.P.Dx2.MN

variable {k : ℕ}

def Psi (k j ρ : ℕ) (z : U.RC k j ρ × ((G.UT j → ℂ) × Mt k ρ)) : Mt k (j + ρ) :=
  Matrix.of.symm (U.Rn k j ρ z.1 * U.muP k j ρ (G.upper z.2.1) * U.embG k j ρ (Matrix.of z.2.2))

theorem muN_cast {a b : ℕ} (h : a = b) : D.muN k b = (D.muN k a).map (castMt h) := by
  subst h
  have : (castMt (k := k) (rfl : a = a)) = id := by funext x; simp [castMt, castM_rfl]
  rw [this, Measure.map_id]

theorem castM_castM {a b c : ℕ} (h1 : a = b) (h2 : b = c) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM (h1.trans h2) g := by
  subst h1 h2; rw [castM_rfl, castM_rfl]

theorem sf_muN (ρ : ℕ) : SigmaFinite (D.muN k ρ) := sigma_of_haar (haar ρ)

theorem block_three_zero_size_eq {ρ : ℕ} (A11 : Matrix (Fin 0) (Fin 0) ℂ) (A12 : Matrix (Fin 0) (Fin (2 * ρ + k + 1)) ℂ)
    (A13 : Matrix (Fin 0) (Fin 0) ℂ) (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin 0) ℂ) (A22 : B.Mat k ρ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin 0) ℂ) (A31 : Matrix (Fin 0) (Fin 0) ℂ)
    (A32 : Matrix (Fin 0) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin 0) (Fin 0) ℂ) :
    U.blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 = D.castM (by omega : ρ = 0 + ρ) A22 := by
  apply Ux2.mat_ext_eB (k := k) (j := 0) (ρ := ρ)
  rintro ((a | v) | a) ((b | w) | b)
  all_goals first | exact a.elim0 | exact b.elim0 | skip
  rw [Ux3.block3_apply, Split.castM_apply]
  simp only [Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁]
  try (congr 1 <;> ext <;> simp [Ux3.block_index_middle_val])

theorem psi_zero (ρ : ℕ) (z : U.RC k 0 ρ × ((G.UT 0 → ℂ) × Mt k ρ)) :
    Psi k 0 ρ z = castMt (by omega : ρ = 0 + ρ) z.2.2 := by
  simp only [Psi, castMt, Ux3.rn_eq, U.muP, U.embG, block_three_zero_size_eq, ← castM_mul, Matrix.one_mul]

theorem radial_measure_is_probability (ρ : ℕ) : IsProbabilityMeasure (U.muRC k 0 ρ) := by
  haveI : IsEmpty (G.UT 0) := ⟨fun ⟨⟨a, _⟩, _⟩ => a.elim0⟩
  have h1 : IsProbabilityMeasure (volume : Measure (Fin (2 * ρ + k + 1) → Fin 0 → ℂ)) := by
    rw [MeasureTheory.volume_pi]
    haveI : ∀ _ : Fin (2 * ρ + k + 1), IsProbabilityMeasure (volume : Measure (Fin 0 → ℂ)) := fun _ => by
      rw [MeasureTheory.volume_pi, Measure.pi_of_empty]; infer_instance
    infer_instance
  have h2 : IsProbabilityMeasure (volume : Measure (G.UT 0 → ℂ)) := by
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]; infer_instance
  have h3 : IsProbabilityMeasure (volume : Measure (Fin 0 → ℝ)) := by
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]; infer_instance
  unfold U.muRC
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  infer_instance

theorem split_zero (ρ : ℕ) :
    D.muN k (0 + ρ) = ((U.muRC k 0 ρ).prod ((volume : Measure (G.UT 0 → ℂ)).prod (D.muN k ρ))).map (Psi k 0 ρ) := by
  haveI := radial_measure_is_probability (k := k) ρ
  haveI : IsEmpty (G.UT 0) := ⟨fun ⟨⟨a, _⟩, _⟩ => a.elim0⟩
  haveI h2 : IsProbabilityMeasure (volume : Measure (G.UT 0 → ℂ)) := by
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]; infer_instance
  haveI := sf_muN (k := k) ρ
  have e : Psi k 0 ρ = castMt (by omega : ρ = 0 + ρ) ∘ Prod.snd ∘ Prod.snd := funext fun z => psi_zero ρ z
  have hc : Measurable (castMt (k := k) (by omega : ρ = 0 + ρ)) := (castMt_cont _).measurable
  rw [e, ← Measure.map_map hc (measurable_snd.comp measurable_snd), ← Measure.map_map measurable_snd measurable_snd,
    (measurePreserving_snd (μ := U.muRC k 0 ρ) (ν := (volume : Measure (G.UT 0 → ℂ)).prod (D.muN k ρ))).map_eq,
    (measurePreserving_snd (μ := (volume : Measure (G.UT 0 → ℂ))) (ν := D.muN k ρ)).map_eq]
  exact muN_cast _

theorem continuous_block3_matrix {X : Type*} [TopologicalSpace X] {j ρ : ℕ}
    {f11 : X → Matrix (Fin j) (Fin j) ℂ} {f12 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {f13 : X → Matrix (Fin j) (Fin j) ℂ} {f21 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {f22 : X → B.Mat k ρ}
    {f23 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {f31 : X → Matrix (Fin j) (Fin j) ℂ}
    {f32 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {f33 : X → Matrix (Fin j) (Fin j) ℂ}
    (h11 : Continuous f11) (h12 : Continuous f12) (h13 : Continuous f13) (h21 : Continuous f21)
    (h22 : Continuous f22) (h23 : Continuous f23) (h31 : Continuous f31) (h32 : Continuous f32)
    (h33 : Continuous f33) :
    Continuous (fun x => U.blk3 (f11 x) (f12 x) (f13 x) (f21 x) (f22 x) (f23 x) (f31 x) (f32 x) (f33 x)) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  obtain ⟨a, rfl⟩ := (U.eB k j ρ).surjective p
  obtain ⟨b, rfl⟩ := (U.eB k j ρ).surjective q
  simp only [Ux3.block3_apply]
  rcases a with ((a | a) | a) <;> rcases b with ((b | b) | b) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr] <;>
    first | exact h11.matrix_elem _ _ | exact h12.matrix_elem _ _ | exact h13.matrix_elem _ _ |
      exact h21.matrix_elem _ _ | exact h22.matrix_elem _ _ | exact h23.matrix_elem _ _ |
      exact h31.matrix_elem _ _ | exact h32.matrix_elem _ _ | exact h33.matrix_elem _ _

theorem rn_cont (j ρ : ℕ) : Continuous (fun x : U.RC k j ρ => U.Rn k j ρ x) := by
  have hof : Continuous fun x : U.RC k j ρ => (Matrix.of x.1 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) := continuous_fst
  simp only [Ux3.rn_eq]
  refine continuous_block3_matrix continuous_const ?_ ?_ continuous_const continuous_const hof continuous_const continuous_const
    continuous_const
  · exact ((continuous_const.matrix_mul hof.matrix_conjTranspose).matrix_mul continuous_const).neg
  · apply Continuous.matrix_mul continuous_const
    apply Continuous.add
    · exact Continuous.const_smul (c := (-(1 / 2 : ℂ))) ((hof.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hof)
    · exact continuous_skew.comp continuous_snd

theorem inv_upper_eq {j : ℕ} (u : G.UT j → ℂ) : (G.upper u)ᴴ⁻¹ = ((G.upper u)ᴴ).adjugate := by
  rw [Matrix.inv_def, Matrix.det_conjTranspose, det_upper]; simp

theorem mup_cont (j ρ : ℕ) : Continuous (fun u : G.UT j → ℂ => U.muP k j ρ (G.upper u)) := by
  have h : Continuous fun u : G.UT j → ℂ => (G.upper u)ᴴ⁻¹ := by
    simp only [inv_upper_eq]; exact continuous_upper.matrix_conjTranspose.matrix_adjugate
  exact continuous_block3_matrix continuous_upper continuous_const continuous_const continuous_const continuous_const continuous_const
    continuous_const continuous_const ((continuous_const.matrix_mul h).matrix_mul continuous_const)

theorem embg_cont (j ρ : ℕ) : Continuous (fun y : Mt k ρ => U.embG k j ρ (Matrix.of y)) :=
  continuous_block3_matrix continuous_const continuous_const continuous_const continuous_const continuous_id continuous_const
    continuous_const continuous_const continuous_const

theorem psi_cont (j ρ : ℕ) : Continuous (Psi k j ρ) := by
  unfold Psi
  exact (((rn_cont j ρ).comp continuous_fst).matrix_mul ((mup_cont j ρ).comp (continuous_fst.comp continuous_snd))).matrix_mul
    ((embg_cont j ρ).comp (continuous_snd.comp continuous_snd))

theorem psi_meas (j ρ : ℕ) : Measurable (Psi k j ρ) := by
  haveI : BorelSpace ((G.UT j → ℂ) × (Fin j → ℝ)) := Prod.borelSpace
  haveI : BorelSpace (U.RC k j ρ) := Prod.borelSpace
  haveI : BorelSpace ((G.UT j → ℂ) × Mt k ρ) := Prod.borelSpace
  haveI : BorelSpace (U.RC k j ρ × ((G.UT j → ℂ) × Mt k ρ)) := Prod.borelSpace
  exact (psi_cont j ρ).measurable

theorem sf_RC (j' ρ' : ℕ) : SigmaFinite (U.muRC k j' ρ') := by
  haveI : SigmaFinite (volume : Measure (G.UT j' → ℂ)) := by rw [MeasureTheory.volume_pi]; infer_instance
  haveI : SigmaFinite (volume : Measure (Fin j' → ℝ)) := by rw [MeasureTheory.volume_pi]; infer_instance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ' + k + 1) → Fin j' → ℂ)) := by
    rw [MeasureTheory.volume_pi]; infer_instance
  unfold U.muRC; rw [Measure.volume_eq_prod, Measure.volume_eq_prod]; infer_instance

def Phi (k j ρ : ℕ) (z : U.RC k 1 (j + ρ) × (U.RC k j ρ × ((G.UT j → ℂ) × Mt k ρ))) :
    U.RC k (j + 1) ρ × ((G.UT (j + 1) → ℂ) × Mt k ρ) :=
  (TX z.1 z.2.1, (TUU z.1 z.2.2.1, z.2.2.2))

theorem phi_mp (j ρ : ℕ) [SigmaFinite (D.muN k ρ)] :
    MeasurePreserving (Phi k j ρ)
      ((U.muRC k 1 (j + ρ)).prod ((U.muRC k j ρ).prod ((volume : Measure (G.UT j → ℂ)).prod (D.muN k ρ))))
      ((U.muRC k (j + 1) ρ).prod ((volume : Measure (G.UT (j + 1) → ℂ)).prod (D.muN k ρ))) := by
  haveI : SigmaFinite (volume : Measure (G.UT j → ℂ)) := by rw [MeasureTheory.volume_pi]; infer_instance
  haveI : SigmaFinite (volume : Measure (G.UT (j + 1) → ℂ)) := by rw [MeasureTheory.volume_pi]; infer_instance
  haveI : SigmaFinite (U.muRC k j ρ) := sf_RC j ρ
  haveI : SigmaFinite (U.muRC k 1 (j + ρ)) := sf_RC 1 (j + ρ)
  haveI : SigmaFinite (U.muRC k (j + 1) ρ) := sf_RC (j + 1) ρ
  haveI : SigmaFinite ((U.muRC k j ρ).prod (volume : Measure (G.UT j → ℂ))) := inferInstance
  haveI : SigmaFinite ((U.muRC k 1 (j + ρ)).prod ((U.muRC k j ρ).prod (volume : Measure (G.UT j → ℂ)))) :=
    inferInstance
  haveI : SigmaFinite ((U.muRC k (j + 1) ρ).prod (volume : Measure (G.UT (j + 1) → ℂ))) := inferInstance
  have a1 := (MeasurePreserving.id (U.muRC k 1 (j + ρ))).prod
    (measurePreserving_prodAssoc (U.muRC k j ρ) (volume : Measure (G.UT j → ℂ)) (D.muN k ρ)).symm
  have a2 := (measurePreserving_prodAssoc (U.muRC k 1 (j + ρ)) ((U.muRC k j ρ).prod (volume : Measure (G.UT j → ℂ)))
    (D.muN k ρ)).symm
  haveI : SigmaFinite (volume : Measure (U.RC k 1 (j + ρ) × Bs k j ρ)) :=
    (inferInstance : SigmaFinite ((U.muRC k 1 (j + ρ)).prod ((U.muRC k j ρ).prod (volume : Measure (G.UT j → ℂ)))))
  have a3 := (T_mp (k := k) (j := j) (ρ := ρ)).prod (MeasurePreserving.id (D.muN k ρ))
  have a4 := measurePreserving_prodAssoc (U.muRC k (j + 1) ρ) (volume : Measure (G.UT (j + 1) → ℂ)) (D.muN k ρ)
  have hall := a4.comp (a3.comp (a2.comp a1))
  have e : Phi k j ρ = _ := funext fun z => rfl
  exact hall

theorem split_succ (j : ℕ)
    (ih : ∀ ρ, D.muN k (j + ρ) =
      ((U.muRC k j ρ).prod ((volume : Measure (G.UT j → ℂ)).prod (D.muN k ρ))).map (Psi k j ρ)) (ρ : ℕ) :
    D.muN k ((j + 1) + ρ) =
      ((U.muRC k (j + 1) ρ).prod ((volume : Measure (G.UT (j + 1) → ℂ)).prod (D.muN k ρ))).map (Psi k (j + 1) ρ) := by
  haveI := sf_muN (k := k) ρ
  haveI := sf_muN (k := k) (j + ρ)
  haveI : SigmaFinite (volume : Measure (G.UT j → ℂ)) := by rw [MeasureTheory.volume_pi]; infer_instance
  haveI : SigmaFinite (U.muRC k j ρ) := sf_RC j ρ
  haveI : SigmaFinite (U.muRC k 1 (j + ρ)) := sf_RC 1 (j + ρ)
  haveI : SigmaFinite ((U.muRC k j ρ).prod ((volume : Measure (G.UT j → ℂ)).prod (D.muN k ρ))) := inferInstance
  rw [muN_cast (show (j + ρ) + 1 = (j + 1) + ρ by omega)]
  show (((U.muRC k 1 (j + ρ)).prod (D.muN k (j + ρ))).map
    (fun x => Matrix.of.symm (D.castM (Nat.add_comm 1 (j + ρ))
      (U.Rn k 1 (j + ρ) x.1 * U.embG k 1 (j + ρ) (Matrix.of x.2))))).map _ = _
  rw [ih ρ]
  have hΨ : Measurable (Psi k j ρ) := psi_meas j ρ
  have hF : Measurable (fun x : U.RC k 1 (j + ρ) × Mt k (j + ρ) => Matrix.of.symm (D.castM (Nat.add_comm 1 (j + ρ))
      (U.Rn k 1 (j + ρ) x.1 * U.embG k 1 (j + ρ) (Matrix.of x.2)))) := by
    have h1 : Continuous (fun x : U.RC k 1 (j + ρ) × Mt k (j + ρ) =>
        (Matrix.of.symm (U.Rn k 1 (j + ρ) x.1 * U.embG k 1 (j + ρ) (Matrix.of x.2)) : Mt k (1 + (j + ρ)))) :=
      ((rn_cont 1 (j + ρ)).comp continuous_fst).matrix_mul ((embg_cont 1 (j + ρ)).comp continuous_snd)
    exact ((castMt_cont (k := k) (Nat.add_comm 1 (j + ρ))).comp h1).measurable
  have hc : Measurable (castMt (k := k) (show (j + ρ) + 1 = (j + 1) + ρ by omega)) := (castMt_cont _).measurable
  have hp : (U.muRC k 1 (j + ρ)).prod
      (((U.muRC k j ρ).prod ((volume : Measure (G.UT j → ℂ)).prod (D.muN k ρ))).map (Psi k j ρ)) =
      ((U.muRC k 1 (j + ρ)).prod ((U.muRC k j ρ).prod ((volume : Measure (G.UT j → ℂ)).prod (D.muN k ρ)))).map
        (Prod.map id (Psi k j ρ)) := by
    rw [← Measure.map_prod_map _ _ measurable_id hΨ, Measure.map_id]
  rw [hp, Measure.map_map hF (measurable_id.prodMap hΨ), Measure.map_map hc (hF.comp (measurable_id.prodMap hΨ))]
  have hfun : (castMt (k := k) (show (j + ρ) + 1 = (j + 1) + ρ by omega) ∘
      (fun x : U.RC k 1 (j + ρ) × Mt k (j + ρ) => Matrix.of.symm (D.castM (Nat.add_comm 1 (j + ρ))
        (U.Rn k 1 (j + ρ) x.1 * U.embG k 1 (j + ρ) (Matrix.of x.2)))) ∘ Prod.map id (Psi k j ρ)) =
      Psi k (j + 1) ρ ∘ Phi k j ρ := by
    funext z
    obtain ⟨x1, x, u, y⟩ := z
    simp only [Function.comp, Prod.map, id, castMt, Psi, Phi, Equiv.apply_symm_apply]
    rw [castM_castM]
    exact congrArg Matrix.of.symm (kl x1 x u (Matrix.of y))
  rw [hfun, ← Measure.map_map (psi_meas (j + 1) ρ) (phi_mp j ρ).measurable, (phi_mp j ρ).map_eq]

theorem split_all : ∀ j ρ : ℕ, D.muN k (j + ρ) =
    ((U.muRC k j ρ).prod ((volume : Measure (G.UT j → ℂ)).prod (D.muN k ρ))).map (Psi k j ρ) := by
  intro j
  induction j with
  | zero => exact split_zero
  | succ j ih => exact split_succ j ih

end Formalism.FourierDecayAlt.P.Dx2.SplitF

namespace Formalism.FourierDecayAlt.P

theorem unipotent_measure_splitting : Formalism.FourierDecayAlt.D.MuNSplit := by
  intro k r j hj
  have h := Dx2.SplitF.split_all (k := k) j (r - j)
  rw [Dx2.SplitF.muN_cast (show j + (r - j) = r by omega), h,
    Measure.map_map (Dx2.MN.castMt_cont _).measurable (Dx2.SplitF.psi_meas j (r - j))]
  rfl

end Formalism.FourierDecayAlt.P

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.Dx2.Rad

section pattern
variable {m : ℕ} (w : Equiv.Perm (Fin m))

def low (x : C2.Lstidx w → ℂ) : Matrix (Fin m) (Fin m) ℂ := C2.lowOf (fun q : C2.Lstidx w => q.1) x

theorem low_apply (x : C2.Lstidx w → ℂ) (i j : Fin m) :
    low w x i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j +
      if h : j < i ∧ w.symm i < w.symm j then x ⟨(i, j), h⟩ else 0 :=
  Formalism.FourierDecayAlt.P.c2x2_lowOf_sub (fun q : Fin m × Fin m => q.2 < q.1 ∧ w.symm q.1 < w.symm q.2) x i j

theorem low_coord (x : C2.Lstidx w → ℂ) (q : C2.Lstidx w) : low w x q.1.1 q.1.2 = x q := by
  rw [low_apply, Matrix.one_apply_ne (ne_of_gt q.2.1), zero_add, dif_pos q.2]

variable (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
include hd

theorem low_mem (x : C2.Lstidx w → ℂ) : low w x ∈ C2.Lstg (C2.monoP w d) := by
  rw [← (Formalism.FourierDecayAlt.P.lower_parabolic_coordinates m w d hd).2]; exact ⟨x, rfl⟩

theorem eq_low {M : Matrix (Fin m) (Fin m) ℂ} (hM : M ∈ C2.Lstg (C2.monoP w d)) :
    M = low w (fun q => M q.1.1 q.1.2) := by
  rw [← (Formalism.FourierDecayAlt.P.lower_parabolic_coordinates m w d hd).2] at hM
  obtain ⟨y, rfl⟩ := hM
  congr 1; funext q; exact (low_coord w y q).symm

theorem lstg_mul {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.Lstg (C2.monoP w d))
    (hB : B ∈ C2.Lstg (C2.monoP w d)) : A * B ∈ C2.Lstg (C2.monoP w d) := by
  have hP := Formalism.FourierDecayAlt.P.C2x2.isUnit_det_monomialMatrix w d hd
  refine ⟨Formalism.FourierDecayAlt.P.C2x2.lt_mul hA.1 hB.1, ?_⟩
  have : (C2.monoP w d)⁻¹ * (A * B) * C2.monoP w d =
      ((C2.monoP w d)⁻¹ * A * C2.monoP w d) * ((C2.monoP w d)⁻¹ * B * C2.monoP w d) := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hP]
  rw [this]; exact Formalism.FourierDecayAlt.P.C2x2.ut_mul hA.2 hB.2

end pattern

section posG
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)

theorem std : C2.Std k r D.z D.z' := ⟨D.k_pos, ⟨D.z_mem, D.T_pos⟩, ⟨D.z'_mem, D.T'_pos⟩⟩

theorem isUnit_G {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) : IsUnit γ.det :=
  (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit γ hγ

variable {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) (hpos : 0 < Gf k r D.z D.z' γ)
include hγ hpos

theorem rset_eq : C6.Rset γ = C2.Rst k r D.z D.z' γ := by
  rw [(Formalism.FourierDecayAlt.P.stabilizer_split k r D.z D.z' γ (std D) ⟨hγ, hpos⟩).2.1]
  have hu := isUnit_G hγ
  ext ρ
  simp only [C6.Rset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, _, h2, ?_⟩
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  · rintro ⟨h1, n, hn, rfl⟩
    refine ⟨h1, ?_⟩
    have : γ⁻¹ * (γ * n * γ⁻¹) * γ = n := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [this]; exact hn

variable {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d)
include hd hZ

theorem u_lstg {ρ : B.Mat k r} (hρ : ρ ∈ C6.Rset γ) : (C2.uMap k r D.z ρ)ᴴ ∈ C2.Lstg (C2.monoP w d) := by
  rw [rset_eq D hγ hpos] at hρ
  have h1 := (Formalism.FourierDecayAlt.P.stabilizer_pairs k r D.z D.z' γ (std D) ⟨hγ, hpos⟩).1.mapsTo hρ
  simp only [Set.mem_ofPred_eq] at h1
  rw [hZ] at h1
  have h2 : C2.uMap k r D.z ρ ∈ {u | u ∈ C2.UTset (r + 1) ∧ ∃ u' ∈ C2.UTset (r + 1), uᴴ * C2.monoP w d * u' =
      C2.monoP w d} := ⟨h1.1, _, h1.2.1, h1.2.2⟩
  rw [Formalism.FourierDecayAlt.P.unipotent_radical_image (r + 1) _ ⟨w, d, hd, rfl⟩] at h2
  exact h2.2

theorem exists_rho (x : C2.Lstidx w → ℂ) : ∃ ρ ∈ C6.Rset γ, C2.uMap k r D.z ρ = (low w x)ᴴ := by
  have hl := low_mem w d hd x
  have hu : (low w x)ᴴ ∈ {u | u ∈ C2.UTset (r + 1) ∧ uᴴ ∈ C2.Lstg (C2.monoP w d)} :=
    ⟨Formalism.FourierDecayAlt.P.C2x2.lt_conjT hl.1, by rw [Matrix.conjTranspose_conjTranspose]; exact hl⟩
  rw [← Formalism.FourierDecayAlt.P.unipotent_radical_image (r + 1) _ ⟨w, d, hd, rfl⟩] at hu
  obtain ⟨hu1, u', hu', he⟩ := hu
  have hmem : ((low w x)ᴴ, u') ∈ {p : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ × Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ |
      p.1 ∈ C2.UTset (r + 1) ∧ p.2 ∈ C2.UTset (r + 1) ∧ p.1ᴴ * Zhat k r D.z D.z' γ * p.2 = Zhat k r D.z D.z' γ} := by
    refine ⟨hu1, hu', ?_⟩; rw [hZ]; exact he
  obtain ⟨ρ, hρ, hρe⟩ := (Formalism.FourierDecayAlt.P.stabilizer_pairs k r D.z D.z' γ (std D) ⟨hγ, hpos⟩).1.surjOn hmem
  refine ⟨ρ, by rw [rset_eq D hγ hpos]; exact hρ, ?_⟩
  exact congrArg Prod.fst hρe

theorem u_inj : Set.InjOn (C2.uMap k r D.z) (C6.Rset γ) := by
  rw [rset_eq D hγ hpos]
  exact (Formalism.FourierDecayAlt.P.stabilizer_pairs k r D.z D.z' γ (std D) ⟨hγ, hpos⟩).2.1

end posG

structure Good {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
    (d : Fin (r + 1) → ℂ) : Prop where
  ex : ∀ x : C2.Lstidx w → ℂ, ∃ ρ ∈ C6.Rset γ, C2.uMap k r D.z ρ = (low w x)ᴴ
  inj : Set.InjOn (C2.uMap k r D.z) (C6.Rset γ)
  lst : ∀ ρ ∈ C6.Rset γ, (C2.uMap k r D.z ρ)ᴴ ∈ C2.Lstg (C2.monoP w d)

section meas
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hG : Good D γ w d)

def rhoF (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1))) (x : C2.Lstidx w → ℂ) : B.Mat k r := Formalism.FourierDecayAlt.D.rhoOfU D γ (low w x)ᴴ

include hγ hd hG

theorem rhoF_spec (x : C2.Lstidx w → ℂ) :
    rhoF D γ w x ∈ C6.Rset γ ∧ C2.uMap k r D.z (rhoF D γ w x) = (low w x)ᴴ := by
  have h := hG.ex x
  unfold rhoF Formalism.FourierDecayAlt.D.rhoOfU
  rw [dif_pos h]
  exact h.choose_spec

theorem rhoF_unique (x : C2.Lstidx w → ℂ) {ρ : B.Mat k r} (hρ : ρ ∈ C6.Rset γ)
    (hu : C2.uMap k r D.z ρ = (low w x)ᴴ) : ρ = rhoF D γ w x :=
  hG.inj hρ (rhoF_spec D hγ hd hG x).1 (by rw [hu, (rhoF_spec D hγ hd hG x).2])

omit hγ hd hG in

def phi0 (w : Equiv.Perm (Fin (r + 1))) (x : Mt k r) : C2.Lstidx w → ℂ :=
  fun q => conj (C2.uMap k r D.z (Matrix.of x) q.1.2 q.1.1)

theorem u_eq_low {ρ : B.Mat k r} (hρ : ρ ∈ C6.Rset γ) :
    (C2.uMap k r D.z ρ)ᴴ = low w (phi0 D w (Matrix.of.symm ρ)) := by
  rw [eq_low w d hd (hG.lst _ hρ)]
  congr 1

theorem coordMap_hermRep_leftInverse (x : C2.Lstidx w → ℂ) : phi0 D w (Matrix.of.symm (rhoF D γ w x)) = x := by
  funext q
  have h := (rhoF_spec D hγ hd hG x).2
  simp only [phi0, Equiv.apply_symm_apply]
  rw [h]
  simp [Matrix.conjTranspose_apply, low_coord]

omit hγ hd hG in
theorem cont_uMap_entry (a b : Fin (r + 1)) : Continuous fun x : Mt k r => C2.uMap k r D.z (Matrix.of x) a b := by
  unfold C2.uMap
  split_ifs with h
  · exact (B2x5.continuous_herm _).comp ((Continuous.matrix_mulVec continuous_id continuous_const).prodMk continuous_const)
  · exact ((B2x5.continuous_herm _).comp ((Continuous.matrix_mulVec continuous_id continuous_const).prodMk
      continuous_const)).div_const _

omit hγ hd hG in
theorem continuous_radial_phi : Continuous (phi0 D w : Mt k r → C2.Lstidx w → ℂ) := by
  refine continuous_pi fun q => ?_
  exact (cont_uMap_entry D q.1.2 q.1.1).star

theorem rhoF_meas : Measurable fun x : C2.Lstidx w → ℂ => (Matrix.of.symm (rhoF D γ w x) : Mt k r) := by
  set S : Set (Mt k r) := {x | Matrix.of x ∈ C6.Rset γ} with hS
  have hcl : IsClosed S := (Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (isUnit_G hγ)).closed
  have hemb := ContinuousOn.measurableEmbedding hcl.measurableSet (continuous_radial_phi D (w := w)).continuousOn
    (fun a ha b hb hab => by
      have e1 := u_eq_low D hγ hd hG (ρ := Matrix.of a) ha
      have e2 := u_eq_low D hγ hd hG (ρ := Matrix.of b) hb
      have hab' : phi0 D w (Matrix.of.symm (Matrix.of a)) = phi0 D w (Matrix.of.symm (Matrix.of b)) := by
        simpa using hab
      have key : C2.uMap k r D.z (Matrix.of a) = C2.uMap k r D.z (Matrix.of b) := by
        rw [← Matrix.conjTranspose_conjTranspose (C2.uMap k r D.z (Matrix.of a)),
          ← Matrix.conjTranspose_conjTranspose (C2.uMap k r D.z (Matrix.of b)), e1, e2, hab']
      exact Matrix.of.injective (hG.inj ha hb key))
  let f : (C2.Lstidx w → ℂ) → S := fun x => ⟨Matrix.of.symm (rhoF D γ w x), by
    show Matrix.of (Matrix.of.symm (rhoF D γ w x)) ∈ C6.Rset γ
    simpa using (rhoF_spec D hγ hd hG x).1⟩
  have hcomp : S.domRestrict (phi0 D w) ∘ f = id := by
    funext x; exact coordMap_hermRep_leftInverse D hγ hd hG x
  have hf : Measurable f := by
    rw [← hemb.measurable_comp_iff, hcomp]; exact measurable_id
  exact measurable_subtype_coe.comp hf

end meas

section shears
variable {m : ℕ} (w : Equiv.Perm (Fin m))

theorem sum_sub_single (f : Fin m → ℂ) (j : Fin m) (c : ℂ) :
    (∑ k, f k) - c = ∑ k, (f k - if k = j then c else 0) := by
  rw [Finset.sum_sub_distrib]; simp

def rank (q : C2.Lstidx w) : ℕ := q.1.1.val - q.1.2.val

def Tl (L0 : Matrix (Fin m) (Fin m) ℂ) (x : C2.Lstidx w → ℂ) : C2.Lstidx w → ℂ :=
  fun q => (low w x * L0) q.1.1 q.1.2

def Tr (L0 : Matrix (Fin m) (Fin m) ℂ) (x : C2.Lstidx w → ℂ) : C2.Lstidx w → ℂ :=
  fun q => (L0 * low w x) q.1.1 q.1.2

theorem cont_low : Continuous (low w) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun x : C2.Lstidx w → ℂ => low w x i j) = fun x => (1 : Matrix (Fin m) (Fin m) ℂ) i j +
      if h : j < i ∧ w.symm i < w.symm j then x ⟨(i, j), h⟩ else 0 := by
    funext x; exact low_apply w x i j
  show Continuous (fun x : C2.Lstidx w → ℂ => low w x i j)
  rw [this]
  refine continuous_const.add ?_
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const

theorem Tl_mp (L0 : Matrix (Fin m) (Fin m) ℂ) (hL : L0 ∈ C2.LTset m) :
    MeasurePreserving (Tl w L0) volume volume := by
  refine Formalism.FourierDecayAlt.P.ShearMeasurability.shear_mp (rank w) (Tl w L0) ?_ ?_
  · refine measurable_pi_lambda _ fun q => ?_
    exact (((cont_low w).matrix_mul continuous_const).matrix_elem q.1.1 q.1.2).measurable
  · intro q x y hxy
    simp only [Tl, Matrix.mul_apply]
    rw [sum_sub_single _ q.1.2 (x q), sum_sub_single _ q.1.2 (y q)]
    apply Finset.sum_congr rfl
    intro k _
    have hq := q.2
    by_cases hkj : k = q.1.2
    · subst hkj
      rw [if_pos rfl, if_pos rfl, low_apply, low_apply, Matrix.one_apply_ne (ne_of_gt q.2.1), dif_pos hq, dif_pos hq,
        zero_add, zero_add, hL.2]
      simp
    · rw [if_neg hkj, if_neg hkj, sub_zero, sub_zero]
      rcases lt_or_gt_of_ne hkj with hk | hk
      · rw [hL.1 k q.1.2 hk, mul_zero, mul_zero]
      · rw [low_apply, low_apply]
        congr 2
        split_ifs with h
        · apply hxy
          simp only [rank]
          have := h.1; have := q.2.1
          rw [Fin.lt_def] at *; omega
        · rfl

theorem Tr_mp (L0 : Matrix (Fin m) (Fin m) ℂ) (hL : L0 ∈ C2.LTset m) :
    MeasurePreserving (Tr w L0) volume volume := by
  refine Formalism.FourierDecayAlt.P.ShearMeasurability.shear_mp (rank w) (Tr w L0) ?_ ?_
  · refine measurable_pi_lambda _ fun q => ?_
    exact ((continuous_const.matrix_mul (cont_low w)).matrix_elem q.1.1 q.1.2).measurable
  · intro q x y hxy
    simp only [Tr, Matrix.mul_apply]
    rw [sum_sub_single _ q.1.1 (x q), sum_sub_single _ q.1.1 (y q)]
    apply Finset.sum_congr rfl
    intro k _
    have hq := q.2
    by_cases hki : k = q.1.1
    · subst hki
      rw [if_pos rfl, if_pos rfl, low_apply, low_apply, Matrix.one_apply_ne (ne_of_gt q.2.1), dif_pos hq, dif_pos hq,
        zero_add, zero_add, hL.2]
      simp
    · rw [if_neg hki, if_neg hki, sub_zero, sub_zero]
      rcases lt_or_gt_of_ne hki with hk | hk
      · rw [low_apply, low_apply]
        congr 2
        split_ifs with h
        · apply hxy
          simp only [rank]
          have := h.1
          rw [Fin.lt_def] at *; omega
        · rfl
      · rw [hL.1 q.1.1 k hk, zero_mul, zero_mul]

end shears

section haarPos
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)

theorem one_UW (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z :=
  ⟨by simp [UH], fun a => by simp, by simp⟩

theorem N_sub_S (z : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ Nset k r) : g ∈ Sset k r z :=
  ⟨1, one_UW z, g, hg, (Matrix.one_mul g).symm⟩

theorem uMap_mul {a b : B.Mat k r} (ha : a ∈ Nset k r) (hb : b ∈ Nset k r) :
    C2.uMap k r D.z (a * b) = C2.uMap k r D.z a * C2.uMap k r D.z b :=
  ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r D.z ⟨D.z_mem, D.T_pos⟩).1 a (N_sub_S D.z ha)).2.2 b (N_sub_S D.z hb)

variable {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hG : Good D γ w d)
include hγ hd hG

theorem left_shift {a : B.Mat k r} (ha : a ∈ C6.Rset γ) (x : C2.Lstidx w → ℂ) :
    a * rhoF D γ w x = rhoF D γ w (Tl w (C2.uMap k r D.z a)ᴴ x) := by
  have hR := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (isUnit_G hγ)
  obtain ⟨hx1, hx2⟩ := rhoF_spec D hγ hd hG x
  apply rhoF_unique D hγ hd hG _ (hR.mul_mem a ha _ hx1)
  have hl := lstg_mul w d hd (low_mem w d hd x) (hG.lst _ ha)
  rw [uMap_mul D ha.1 hx1.1, hx2, show Tl w (C2.uMap k r D.z a)ᴴ x =
    fun q => (low w x * (C2.uMap k r D.z a)ᴴ) q.1.1 q.1.2 from rfl, ← eq_low w d hd hl, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

theorem right_shift {a : B.Mat k r} (ha : a ∈ C6.Rset γ) (x : C2.Lstidx w → ℂ) :
    rhoF D γ w x * a = rhoF D γ w (Tr w (C2.uMap k r D.z a)ᴴ x) := by
  have hR := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (isUnit_G hγ)
  obtain ⟨hx1, hx2⟩ := rhoF_spec D hγ hd hG x
  apply rhoF_unique D hγ hd hG _ (hR.mul_mem _ hx1 a ha)
  have hl := lstg_mul w d hd (hG.lst _ ha) (low_mem w d hd x)
  rw [uMap_mul D hx1.1 ha.1, hx2, show Tr w (C2.uMap k r D.z a)ᴴ x =
    fun q => ((C2.uMap k r D.z a)ᴴ * low w x) q.1.1 q.1.2 from rfl, ← eq_low w d hd hl, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

theorem haar_good : B.IsHaarOn (C6.Rset γ) (Formalism.FourierDecayAlt.D.muR D γ w) := by
  have hR := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (isUnit_G hγ)
  have hm := rhoF_meas D hγ hd hG
  have hmu : Formalism.FourierDecayAlt.D.muR D γ w = (volume : Measure (C2.Lstidx w → ℂ)).map
      (fun x => (Matrix.of.symm (rhoF D γ w x) : Mt k r)) := rfl
  rw [hmu]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · let S : Set (Mt k r) := {x | Matrix.of x ∈ C6.Rset γ}
    have hcl : IsClosed S := hR.closed
    show (Measure.map (fun x : C2.Lstidx w → ℂ => (Matrix.of.symm (rhoF D γ w x) : Mt k r)) volume) Sᶜ = 0
    rw [Measure.map_apply hm hcl.measurableSet.compl]
    have : (fun x : C2.Lstidx w → ℂ => (Matrix.of.symm (rhoF D γ w x) : Mt k r)) ⁻¹' Sᶜ = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not, S,
        Set.mem_setOf_eq, Equiv.apply_symm_apply]
      exact (rhoF_spec D hγ hd hG x).1
    rw [this, measure_empty]
  · intro a ha
    rw [Measure.map_map (B2x5.measurable_lmulM a) hm]
    have e : (lmulM a ∘ fun x : C2.Lstidx w → ℂ => (Matrix.of.symm (rhoF D γ w x) : Mt k r)) =
        (fun x => (Matrix.of.symm (rhoF D γ w x) : Mt k r)) ∘ Tl w (C2.uMap k r D.z a)ᴴ := by
      funext x
      simp only [Function.comp, lmulM, Equiv.apply_symm_apply]
      rw [left_shift D hγ hd hG ha x]; rfl
    have hL : (C2.uMap k r D.z a)ᴴ ∈ C2.LTset (r + 1) := (hG.lst _ ha).1
    rw [e, ← Measure.map_map hm (Tl_mp w _ hL).measurable, (Tl_mp w _ hL).map_eq]
  · intro a ha
    rw [Measure.map_map (B2x5.measurable_rmulF a) hm]
    have e : (B.rmulF a ∘ fun x : C2.Lstidx w → ℂ => (Matrix.of.symm (rhoF D γ w x) : Mt k r)) =
        (fun x => (Matrix.of.symm (rhoF D γ w x) : Mt k r)) ∘ Tr w (C2.uMap k r D.z a)ᴴ := by
      funext x
      simp only [Function.comp, B.rmulF, Equiv.apply_symm_apply]
      rw [right_shift D hγ hd hG ha x]; rfl
    have hL : (C2.uMap k r D.z a)ᴴ ∈ C2.LTset (r + 1) := (hG.lst _ ha).1
    rw [e, ← Measure.map_map hm (Tr_mp w _ hL).measurable, (Tr_mp w _ hL).map_eq]
  · intro K hK
    rw [Measure.map_apply hm hK.isClosed.measurableSet]
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_radial_phi D (w := w)).continuousOn
    refine lt_of_le_of_lt (measure_mono (t := Metric.closedBall 0 C) ?_)
      (isCompact_closedBall (0 : C2.Lstidx w → ℂ) C).measure_lt_top
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have := hC _ hx
    rwa [coordMap_hermRep_leftInverse D hγ hd hG x] at this
  · intro h0
    have h1 : (Measure.map (fun x : C2.Lstidx w → ℂ => (Matrix.of.symm (rhoF D γ w x) : Mt k r)) volume)
        Set.univ = 0 := by rw [h0]; rfl
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ] at h1
    exact (isOpen_univ.measure_pos (volume : Measure (C2.Lstidx w → ℂ)) Set.univ_nonempty).ne' h1

end haarPos

section degen
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) = Fin.last r)

def yv (γ : B.Mat k r) (b : Fin r) : Fin (2 * r + k + 1) → ℂ := γ *ᵥ DF.ee k r b

theorem fvec_cs (z : Fin (2 * r + k + 1) → ℂ) (b : Fin r) : fvec k r z b.castSucc = DF.ee k r b := by
  simp only [fvec, Fin.val_castSucc, dif_pos b.isLt]

theorem fvec_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

include hZ in
theorem pz (a b : Fin (r + 1)) :
    herm (Hpk k r) (γ *ᵥ fvec k r D.z' b) (fvec k r D.z a) = if a = w b then d b else 0 := by
  have := congrFun (congrFun hZ a) b
  simp only [Zhat, C2.monoP, Matrix.of_apply] at this
  exact this

include hB in
theorem w_cs (b : Fin r) : w b.castSucc ≠ Fin.last r := by
  intro h; rw [← hB] at h; exact Fin.castSucc_ne_last b (w.injective h)

include hB in
theorem w_cs' (b : Fin r) : (DF.piX w b).castSucc = w b.castSucc := DF.piX_spec w b (w_cs hB b)

include hB in
theorem piX_bij : Function.Bijective (DF.piX w) := by
  refine Function.Injective.bijective_of_finite fun b c h => ?_
  exact (DF.piX_inj w (w_cs hB b) (w_cs hB c)).mp h

def sX (hB : w (Fin.last r) = Fin.last r) : Equiv.Perm (Fin r) := Equiv.ofBijective _ (piX_bij hB)

theorem sX_apply (b : Fin r) : sX hB b = DF.piX w b := rfl

include hZ hB in
theorem y_ee (a b : Fin r) : herm (Hpk k r) (yv γ b) (DF.ee k r a) = if a = sX hB b then d b.castSucc else 0 := by
  have := pz D hZ a.castSucc b.castSucc
  rw [fvec_cs, fvec_cs] at this
  rw [yv, this, sX_apply, ← w_cs' hB b]
  simp [Fin.castSucc_inj]

include hγ in
theorem y_y (b c : Fin r) : herm (Hpk k r) (yv γ b) (yv γ c) = 0 := by
  rw [yv, yv, B2x4.herm_mulVec, hγ]; exact DF.h_ee_ee b c

include hZ hB in
theorem y_z (b : Fin r) : herm (Hpk k r) (yv γ b) D.z = 0 := by
  have := pz D hZ (Fin.last r) b.castSucc
  rw [fvec_cs, fvec_last] at this
  rw [yv, this, if_neg (fun h => w_cs hB b h.symm)]

end degen

section degen2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) = Fin.last r)

def uvD (γ : B.Mat k r) : Fin r ⊕ Fin r → Fin (2 * r + k + 1) → ℂ
  | Sum.inl a => DF.ee k r a
  | Sum.inr b => yv γ b

def wvD (γ : B.Mat k r) (d : Fin (r + 1) → ℂ) (hB : w (Fin.last r) = Fin.last r) :
    Fin r ⊕ Fin r → Fin (2 * r + k + 1) → ℂ
  | Sum.inl a => (d ((sX hB).symm a).castSucc)⁻¹ • yv γ ((sX hB).symm a)
  | Sum.inr b => (star (d b.castSucc))⁻¹ • DF.ee k r (sX hB b)

def YD (γ : B.Mat k r) (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Fin r ⊕ Fin r → Fin (2 * r + k + 1) → ℂ
  | Sum.inl b => ∑ a, u a.castSucc b.castSucc • DF.ee k r a
  | Sum.inr b => ∑ c, u' c.castSucc b.castSucc • yv γ c

include hγ hd hZ hB

theorem h1D (i j : Fin r ⊕ Fin r) :
    herm (Hpk k r) (uvD γ i) (wvD γ d hB j) = if i = j then 1 else 0 := by
  rcases i with a | b <;> rcases j with a' | b'
  · simp only [uvD, wvD, B2x4.herm_smul_right, Sum.inl.injEq]
    rw [DF.herm_symm', y_ee D hZ hB, Equiv.apply_symm_apply]
    by_cases h : a = a'
    · subst h; simp [hd]
    · simp [h]
  · simp [uvD, wvD, B2x4.herm_smul_right]
  · simp only [uvD, wvD, B2x4.herm_smul_right, y_y hγ, mul_zero, reduceCtorEq, if_false]
  · simp only [uvD, wvD, B2x4.herm_smul_right, y_ee D hZ hB, Sum.inr.injEq]
    by_cases h : b = b'
    · subst h; simp [hd]
    · have : ¬ (sX hB b' = sX hB b) := fun e => h ((sX hB).injective e).symm
      simp [h, this]

end degen2

section degen3
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) = Fin.last r)
include hγ hd hZ hB

theorem h2D (x : Fin (2 * r + k + 1) → ℂ) (j : Fin r ⊕ Fin r) :
    herm (Hpk k r) x (uvD γ j) =
      ∑ i, herm (Hpk k r) x (wvD γ d hB i) * herm (Hpk k r) (uvD γ i) (uvD γ j) := by
  rw [Fintype.sum_sum_type]
  rcases j with c | c
  · simp only [uvD, wvD, DF.h_ee_ee, mul_zero, Finset.sum_const_zero, zero_add, B2x4.herm_smul_right,
      y_ee D hZ hB]
    rw [Finset.sum_eq_single ((sX hB).symm c)]
    · rw [Equiv.apply_symm_apply, if_pos rfl, star_inv₀, star_star]
      field_simp [hd]
    · intro b _ hb
      rw [if_neg]; · ring
      intro h; apply hb; rw [h, Equiv.symm_apply_apply]
    · simp
  · have e : ∀ a, herm (Hpk k r) (DF.ee k r a) (yv γ c) = star (if a = sX hB c then d c.castSucc else 0) := by
      intro a; rw [DF.herm_symm' (yv γ c), y_ee D hZ hB]
    simp only [uvD, wvD, y_y hγ, mul_zero, Finset.sum_const_zero, add_zero, B2x4.herm_smul_right, e]
    rw [Finset.sum_eq_single (sX hB c)]
    · rw [if_pos rfl, Equiv.symm_apply_apply, star_inv₀]
      field_simp [hd]
    · intro a _ ha
      rw [if_neg ha]; simp
    · simp

theorem hermitian_radial_mixed_pair (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hrel : ∀ a b : Fin r, ∑ c, ∑ e, u' c.castSucc b.castSucc * star (u e.castSucc a.castSucc) *
      herm (Hpk k r) (yv γ c) (DF.ee k r e) = herm (Hpk k r) (yv γ b) (DF.ee k r a)) (a b : Fin r) :
    herm (Hpk k r) (YD γ u u' (Sum.inr b)) (YD γ u u' (Sum.inl a)) = herm (Hpk k r) (yv γ b) (DF.ee k r a) := by
  simp only [YD, DF.herm_sum_left, DF.herm_sum_right, B2x4.herm_smul_left, B2x4.herm_smul_right]
  rw [← hrel a b, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro e _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c _
  ring

theorem h3D (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hrel : ∀ a b : Fin r, ∑ c, ∑ e, u' c.castSucc b.castSucc * star (u e.castSucc a.castSucc) *
      herm (Hpk k r) (yv γ c) (DF.ee k r e) = herm (Hpk k r) (yv γ b) (DF.ee k r a))
    (i j : Fin r ⊕ Fin r) :
    herm (Hpk k r) (YD γ u u' i) (YD γ u u' j) = herm (Hpk k r) (uvD γ i) (uvD γ j) := by
  rcases i with b | b <;> rcases j with a | a
  · simp only [YD, uvD, DF.herm_sum_left, DF.herm_sum_right, B2x4.herm_smul_left, B2x4.herm_smul_right,
      DF.h_ee_ee, mul_zero, Finset.sum_const_zero]
  · rw [DF.herm_symm' (YD γ u u' (Sum.inr a)), hermitian_radial_mixed_pair D hγ hd hZ hB u u' hrel b a, uvD, uvD,
      DF.herm_symm' (yv γ a)]
  · exact hermitian_radial_mixed_pair D hγ hd hZ hB u u' hrel a b
  · simp only [YD, uvD, DF.herm_sum_left, DF.herm_sum_right, B2x4.herm_smul_left, B2x4.herm_smul_right,
      y_y hγ, mul_zero, Finset.sum_const_zero]

omit hd hZ hB in
theorem h4D (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (x : Fin (2 * r + k + 1) → ℂ)
    (hx : ∀ j, herm (Hpk k r) x (uvD γ j) = 0) (i : Fin r ⊕ Fin r) : herm (Hpk k r) x (YD γ u u' i) = 0 := by
  rcases i with b | b
  · simp only [YD, DF.herm_sum_right, B2x4.herm_smul_right]
    apply Finset.sum_eq_zero; intro a _; rw [show herm (Hpk k r) x (DF.ee k r a) = 0 from hx (Sum.inl a)]; simp
  · simp only [YD, DF.herm_sum_right, B2x4.herm_smul_right]
    apply Finset.sum_eq_zero; intro a _; rw [show herm (Hpk k r) x (yv γ a) = 0 from hx (Sum.inr a)]; simp

end degen3

section degen4
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) = Fin.last r)

def uP (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (x : C2.Lstidx w → ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := (C2.monoP w d)⁻¹ * (low w x)⁻¹ * C2.monoP w d

def rhoD (γ : B.Mat k r) (hB : w (Fin.last r) = Fin.last r) (d : Fin (r + 1) → ℂ) (x : C2.Lstidx w → ℂ) :
    B.Mat k r :=
  DF.smat (Hpk k r) (uvD γ) (wvD γ d hB) (YD γ (low w x)ᴴ (uP w d x))

include hd in
theorem upperUnipotent_mem_upperTriangular (x : C2.Lstidx w → ℂ) : uP w d x ∈ C2.UTset (r + 1) := by
  have hl := low_mem w d hd x
  have hP := Formalism.FourierDecayAlt.P.C2x2.isUnit_det_monomialMatrix w d hd
  have e : uP w d x = ((C2.monoP w d)⁻¹ * low w x * C2.monoP w d)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hP, uP, Matrix.mul_assoc]
  rw [e]; exact Formalism.FourierDecayAlt.P.C2x2.ut_inv hl.2

theorem low_last (x : C2.Lstidx w → ℂ) (a : Fin r) : low w x a.castSucc (Fin.last r) = 0 := by
  rw [low_apply, Matrix.one_apply_ne (Fin.castSucc_ne_last a), dif_neg]; · simp
  rintro ⟨h, _⟩; exact absurd h (not_lt.mpr (Fin.castSucc_lt_last a).le)

include hB in
theorem low_last' (x : C2.Lstidx w → ℂ) (a : Fin r) : low w x (Fin.last r) a.castSucc = 0 := by
  rw [low_apply, Matrix.one_apply_ne (Fin.castSucc_ne_last a).symm, dif_neg]; · simp
  rintro ⟨_, h⟩
  have hl : w.symm (Fin.last r) = Fin.last r := by rw [Equiv.symm_apply_eq, hB]
  rw [hl] at h
  exact absurd h (not_lt.mpr (Fin.le_last _))

include hγ hd hZ hB

theorem hrelD (x : C2.Lstidx w → ℂ) (a b : Fin r) :
    ∑ c, ∑ e, uP w d x c.castSucc b.castSucc * star ((low w x)ᴴ e.castSucc a.castSucc) *
      herm (Hpk k r) (yv γ c) (DF.ee k r e) = herm (Hpk k r) (yv γ b) (DF.ee k r a) := by
  have hP := Formalism.FourierDecayAlt.P.C2x2.isUnit_det_monomialMatrix w d hd
  have hyE : ∀ c e : Fin r, herm (Hpk k r) (yv γ c) (DF.ee k r e) = C2.monoP w d e.castSucc c.castSucc := by
    intro c e
    have := pz D hZ e.castSucc c.castSucc
    rw [fvec_cs, fvec_cs] at this
    rw [yv, this]; rfl
  have hM : ((low w x)ᴴ)ᴴ * C2.monoP w d * uP w d x = C2.monoP w d := by
    rw [Matrix.conjTranspose_conjTranspose, uP]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ hP, Matrix.mul_nonsing_inv _ (Formalism.FourierDecayAlt.P.C2x2.lt_unit (low_mem w d hd x).1),
      Matrix.one_mul]
  have hut := upperUnipotent_mem_upperTriangular hd x
  have key := congrFun (congrFun hM a.castSucc) b.castSucc
  rw [hyE, ← key]
  simp only [Matrix.mul_apply, Fin.sum_univ_castSucc]
  rw [hut.1 (Fin.last r) b.castSucc (Fin.castSucc_lt_last b), mul_zero, add_zero]
  simp only [Matrix.conjTranspose_apply, star_star, low_last x a, zero_mul, add_zero, hyE]
  apply Finset.sum_congr rfl; intro c _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro e _
  ring

theorem rhoD_UH (x : C2.Lstidx w → ℂ) : rhoD γ hB d x ∈ UH (Hpk k r) :=
  DF.smat_UH (Hpk k r) (B2x4.Hpk_herm k r) _ _ _ (h2D D hγ hd hZ hB) (h3D D hγ hd hZ hB _ _ (hrelD D hγ hd hZ hB x))
    (h4D hγ _ _)

theorem rhoD_mulVec (x : C2.Lstidx w → ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rhoD γ hB d x *ᵥ v = v + ∑ i, herm (Hpk k r) v (wvD γ d hB i) •
      (YD γ (low w x)ᴴ (uP w d x) i - uvD γ i) := by
  rw [rhoD, DF.smat_mulVec]; rfl

theorem rhoD_u (x : C2.Lstidx w → ℂ) (i : Fin r ⊕ Fin r) :
    rhoD γ hB d x *ᵥ uvD γ i = YD γ (low w x)ᴴ (uP w d x) i := by
  rw [rhoD, DF.smat_mulVec]; exact DF.smap_apply_u _ _ _ _ (h1D D hγ hd hZ hB) i

theorem rhoD_fix (x : C2.Lstidx w → ℂ) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ i, herm (Hpk k r) v (wvD γ d hB i) = 0) : rhoD γ hB d x *ᵥ v = v := by
  rw [rhoD, DF.smat_mulVec]; exact DF.smap_fix _ _ _ _ _ hv

end degen4

section degen5
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) = Fin.last r)

omit D in
theorem entry (M : B.Mat k r) (i j : Fin (2 * r + k + 1)) : M i j = (M *ᵥ bvec j) i := by
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

omit D in
theorem ee_apply_hi (a : Fin r) (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) : DF.ee k r a i = 0 := by
  simp only [DF.ee, bvec, Pi.single_apply]
  rw [if_neg]; intro h; rw [h] at hi; simp [eI] at hi; omega

omit D in
theorem ee_sum_hi (t : Fin r → ℂ) (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) :
    (∑ c, t c • DF.ee k r c) i = 0 := by
  simp [Finset.sum_apply, ee_apply_hi _ i hi]

omit D in
theorem ee_sum_lo (t : Fin r → ℂ) (c0 : Fin r) : (∑ c, t c • DF.ee k r c) (eI k r c0) = t c0 := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, DF.ee, bvec, Pi.single_apply, DF.eI_inj]
  simp

omit D in

theorem mem_N (M : B.Mat k r) (hM : M ∈ UH (Hpk k r)) (U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hU : U ∈ C2.UTset (r + 1)) (he : ∀ a, M *ᵥ DF.ee k r a = ∑ c, U c.castSucc a.castSucc • DF.ee k r c)
    (hw : ∀ j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → ∀ i : Fin (2 * r + k + 1), r ≤ i.val →
      (M *ᵥ bvec j) i = bvec j i) : M ∈ Nset k r := by
  refine ⟨hM, ?_, ?_⟩
  · intro a i hai
    rw [entry M i (eI k r a), show bvec (eI k r a) = DF.ee k r a from rfl, he a]
    by_cases hi : i.val < r
    · have ei : i = eI k r ⟨i.val, hi⟩ := Fin.ext rfl
      rw [ei, ee_sum_lo]
      by_cases hc : (⟨i.val, hi⟩ : Fin r) = a
      · rw [hc, if_pos rfl]; exact hU.2 _
      · have hlt : a.castSucc < (⟨i.val, hi⟩ : Fin r).castSucc := by
          rw [Fin.lt_def]; simp only [Fin.val_castSucc]
          have : a.val ≠ i.val := fun e => hc (Fin.ext e.symm)
          omega
        rw [hU.1 _ _ hlt, if_neg]; intro e; exact hc (DF.eI_inj.mp e)
    · rw [ee_sum_hi _ i (by omega), if_neg]; intro e; rw [e] at hi; simp [eI] at hi
  · intro i j hj1 hj2 hi
    rw [entry M i j, hw j hj1 hj2 i hi]
    simp [bvec, Pi.single_apply, eq_comm]

include hγ hd hZ hB

theorem herm_basis_isotropic_perp (b : Fin r) (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    herm (Hpk k r) (bvec j) (wvD γ d hB (Sum.inr b)) = 0 := by
  show herm (Hpk k r) (bvec j) ((star (d b.castSucc))⁻¹ • DF.ee k r (sX hB b)) = 0
  rw [B2x4.herm_smul_right, DF.herm_ee]
  simp only [bvec, Pi.single_apply]
  rw [if_neg]; · simp
  intro e
  have h1 := congrArg Fin.val e
  have h2 : (esI k r (sX hB b)).val = 2 * r + k - (sX hB b).val := rfl
  have := (sX hB b).isLt
  omega

theorem rhoD_N (x : C2.Lstidx w → ℂ) : rhoD γ hB d x ∈ Nset k r := by
  refine mem_N _ (rhoD_UH D hγ hd hZ hB x) _ (Formalism.FourierDecayAlt.P.C2x2.lt_conjT (low_mem w d hd x).1) ?_ ?_
  · intro a; exact rhoD_u D hγ hd hZ hB x (Sum.inl a)
  · intro j hj1 hj2 i hi
    rw [rhoD_mulVec D hγ hd hZ hB, Fintype.sum_sum_type]
    simp only [herm_basis_isotropic_perp D hγ hd hZ hB _ j hj1 hj2, zero_smul, Finset.sum_const_zero, add_zero, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, YD, uvD, smul_eq_mul]
    rw [Finset.sum_eq_zero, add_zero]
    intro a _
    simp only [ee_apply_hi _ i hi, mul_zero, Finset.sum_const_zero, sub_zero]

theorem rhoD'_N (x : C2.Lstidx w → ℂ) : γ⁻¹ * rhoD γ hB d x * γ ∈ Nset k r := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have hu := isUnit_G hγ
  have hinv : ∀ v, γ⁻¹ *ᵥ (γ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  refine mem_N _ (hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem γ hγ) _ (rhoD_UH D hγ hd hZ hB x)) γ hγ) _ (upperUnipotent_mem_upperTriangular hd x) ?_ ?_
  · intro a
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, show γ *ᵥ DF.ee k r a = uvD γ (Sum.inr a) from rfl,
      rhoD_u D hγ hd hZ hB x (Sum.inr a)]
    simp only [YD, Matrix.mulVec_sum, Matrix.mulVec_smul, yv, hinv]
  · intro j hj1 hj2 i hi
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rhoD_mulVec D hγ hd hZ hB, Fintype.sum_sum_type]
    have hγ' : γᴴ * Hpk k r * γ = Hpk k r := hγ
    have h0 : ∀ a, herm (Hpk k r) (γ *ᵥ bvec j) (wvD γ d hB (Sum.inl a)) = 0 := by
      intro a
      simp only [wvD, B2x4.herm_smul_right, yv, B2x4.herm_mulVec, hγ']
      rw [show herm (Hpk k r) (bvec j) (DF.ee k r ((sX hB).symm a)) = 0 by
        rw [DF.herm_ee]; simp only [bvec, Pi.single_apply]; rw [if_neg]
        intro e
        have h1 := congrArg Fin.val e
        have h2 : (esI k r ((sX hB).symm a)).val = 2 * r + k - ((sX hB).symm a).val := rfl
        have := ((sX hB).symm a).isLt
        omega]
      simp
    simp only [h0, zero_smul, Finset.sum_const_zero, zero_add, Matrix.mulVec_add, hinv, Matrix.mulVec_sum,
      Matrix.mulVec_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_zero, add_zero]
    intro b _
    simp only [YD, uvD, Matrix.mulVec_sub, Matrix.mulVec_sum, Matrix.mulVec_smul, yv, hinv, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ee_apply_hi _ i hi, mul_zero, Finset.sum_const_zero, sub_zero]

end degen5

section degen6
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) = Fin.last r)
include hγ hd hZ hB

theorem rhoD_alt (x : C2.Lstidx w → ℂ) : rhoD γ hB d x *ᵥ D.z = D.z := by
  apply rhoD_fix D hγ hd hZ hB
  rintro (a | b)
  · simp only [wvD, B2x4.herm_smul_right]
    rw [DF.herm_symm' (yv γ _), y_z D hZ hB]; simp
  · simp only [wvD, B2x4.herm_smul_right, DF.h_w_ee D.z_mem]; simp

theorem herm_zz_ne : herm (Hpk k r) D.z D.z ≠ 0 := by
  rw [DF.herm_self_alt]
  have := D.T_pos
  intro h
  have h2 := congrArg Complex.re h
  simp at h2; linarith

theorem uMap_rhoD (x : C2.Lstidx w → ℂ) : C2.uMap k r D.z (rhoD γ hB d x) = (low w x)ᴴ := by
  ext a b
  rcases DF.cast_or_last b with hb | ⟨b', rfl⟩ <;> rcases DF.cast_or_last a with ha | ⟨a', rfl⟩
  · subst ha hb
    simp only [C2.uMap, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true, fvec_last, rhoD_alt D hγ hd hZ hB x]
    rw [div_self (herm_zz_ne D hγ hd hZ hB), Matrix.conjTranspose_apply, low_apply]
    simp
  · subst hb
    simp only [C2.uMap, Fin.val_castSucc, a'.isLt, dif_pos, fvec_last, rhoD_alt D hγ hd hZ hB x]
    rw [show (bvec (esI k r ⟨a'.val, a'.isLt⟩)) = DF.es k r a' from rfl, DF.h_w_es D.z_mem,
      Matrix.conjTranspose_apply, low_last' hB x]; simp
  · subst ha
    simp only [C2.uMap, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true, fvec_cs]
    rw [show DF.ee k r b' = uvD γ (Sum.inl b') from rfl, rhoD_u D hγ hd hZ hB x (Sum.inl b')]
    simp only [YD, DF.herm_sum_left, B2x4.herm_smul_left, DF.h_ee_w D.z_mem, mul_zero, Finset.sum_const_zero,
      zero_div]
    rw [Matrix.conjTranspose_apply, low_last x b']; simp
  · simp only [C2.uMap, Fin.val_castSucc, a'.isLt, dif_pos, fvec_cs]
    rw [show DF.ee k r b' = uvD γ (Sum.inl b') from rfl, rhoD_u D hγ hd hZ hB x (Sum.inl b'),
      show (bvec (esI k r ⟨a'.val, a'.isLt⟩)) = DF.es k r a' from rfl]
    simp only [YD, DF.herm_sum_left, B2x4.herm_smul_left, DF.h_ee_es, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem ex_degen (x : C2.Lstidx w → ℂ) : ∃ ρ ∈ C6.Rset γ, C2.uMap k r D.z ρ = (low w x)ᴴ :=
  ⟨rhoD γ hB d x, ⟨rhoD_N D hγ hd hZ hB x, rhoD'_N D hγ hd hZ hB x⟩, uMap_rhoD D hγ hd hZ hB x⟩

end degen6

section gen
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d)

theorem rel_uu' {ρ : B.Mat k r} (hρ : ρ ∈ C6.Rset γ) (hγ : γ ∈ B.GV k r) :
    (C2.uMap k r D.z ρ)ᴴ * Zhat k r D.z D.z' γ * C2.uMap k r D.z' (γ⁻¹ * ρ * γ) = Zhat k r D.z D.z' γ := by
  have hu := isUnit_G hγ
  have hρu : IsUnit ρ.det := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).unit ρ hρ.1
  have e := Formalism.FourierDecayAlt.P.zhat_equivalence k r D.z D.z' ⟨D.z_mem, D.T_pos⟩ ⟨D.z'_mem, D.T'_pos⟩ ρ
    (N_sub_S D.z hρ.1) _ (N_sub_S D.z' hρ.2) γ
  have e2 : ρ⁻¹ * γ * (γ⁻¹ * ρ * γ) = γ := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc ρ⁻¹ γ γ⁻¹, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.nonsing_inv_mul _ hρu,
      Matrix.one_mul]
  rw [e2] at e; exact e.symm

include hγ hd hZ in
theorem lst_gen {ρ : B.Mat k r} (hρ : ρ ∈ C6.Rset γ) : (C2.uMap k r D.z ρ)ᴴ ∈ C2.Lstg (C2.monoP w d) := by
  have e := rel_uu' D hρ hγ
  rw [hZ] at e
  have hut := ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r D.z ⟨D.z_mem, D.T_pos⟩).1 ρ (N_sub_S D.z hρ.1)).2.1
  have hut' := ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r D.z' ⟨D.z'_mem, D.T'_pos⟩).1 _ (N_sub_S D.z' hρ.2)).2.1
  have h2 : C2.uMap k r D.z ρ ∈ {u | u ∈ C2.UTset (r + 1) ∧ ∃ u' ∈ C2.UTset (r + 1), uᴴ * C2.monoP w d * u' =
      C2.monoP w d} := ⟨hut, _, hut', e⟩
  rw [Formalism.FourierDecayAlt.P.unipotent_radical_image (r + 1) _ ⟨w, d, hd, rfl⟩] at h2
  exact h2.2

end gen

section degenInj
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) = Fin.last r)

omit D in
theorem pos_cases (i : Fin (2 * r + k + 1)) :
    (∃ c : Fin r, i = eI k r c) ∨ (r ≤ i.val ∧ i.val ≤ r + k) ∨ (∃ c : Fin r, i = esI k r c) := by
  by_cases h1 : i.val < r
  · exact Or.inl ⟨⟨i.val, h1⟩, Fin.ext rfl⟩
  · by_cases h2 : i.val ≤ r + k
    · exact Or.inr (Or.inl ⟨by omega, h2⟩)
    · refine Or.inr (Or.inr ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext ?_⟩)
      show i.val = 2 * r + k - (2 * r + k - i.val); omega

omit D in
theorem decompX (v : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0) :
    v = ∑ c, v (eI k r c) • DF.ee k r c := by
  funext i
  by_cases hi : i.val < r
  · have ei : i = eI k r ⟨i.val, hi⟩ := Fin.ext rfl
    rw [ei, ee_sum_lo]
  · rw [ee_sum_hi _ i (by omega), hv i (by omega)]

omit D in
theorem uMap_one (z : Fin (2 * r + k + 1) → ℂ) (hz : C2.StdZ k r z) : C2.uMap k r z (1 : B.Mat k r) = 1 :=
  (Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz).2 1 (one_UW z)

include hγ hd hZ hB

theorem trivial_of_u_one {ρ : B.Mat k r} (hρ : ρ ∈ C6.Rset γ) (hu1 : C2.uMap k r D.z ρ = 1) : ρ = 1 := by
  have hu := isUnit_G hγ
  have hP := Formalism.FourierDecayAlt.P.C2x2.isUnit_det_monomialMatrix w d hd
  have hγ' : γᴴ * Hpk k r * γ = Hpk k r := hγ
  have hρU : ρᴴ * Hpk k r * ρ = Hpk k r := hρ.1.1

  have hF := ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r D.z ⟨D.z_mem, D.T_pos⟩).1 ρ (N_sub_S D.z hρ.1)).1
  have hee : ∀ b : Fin r, ρ *ᵥ DF.ee k r b = DF.ee k r b := by
    intro b
    have := hF b.castSucc
    rw [hu1, fvec_cs] at this
    rw [this]
    simp [Matrix.one_apply, ite_smul, Finset.sum_ite_eq', fvec_cs]

  have hu' : C2.uMap k r D.z' (γ⁻¹ * ρ * γ) = 1 := by
    have e := rel_uu' D hρ hγ
    rw [hu1, Matrix.conjTranspose_one, Matrix.one_mul, hZ] at e
    calc C2.uMap k r D.z' (γ⁻¹ * ρ * γ) = (C2.monoP w d)⁻¹ * (C2.monoP w d * C2.uMap k r D.z' (γ⁻¹ * ρ * γ)) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
      _ = 1 := by rw [e, Matrix.nonsing_inv_mul _ hP]
  have hF' := ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r D.z' ⟨D.z'_mem, D.T'_pos⟩).1 _ (N_sub_S D.z' hρ.2)).1
  have hy : ∀ b : Fin r, ρ *ᵥ yv γ b = yv γ b := by
    intro b
    have := hF' b.castSucc
    rw [hu', fvec_cs] at this
    have h1 : (γ⁻¹ * ρ * γ) *ᵥ DF.ee k r b = DF.ee k r b := by
      rw [this]; simp [Matrix.one_apply, ite_smul, Finset.sum_ite_eq', fvec_cs]
    have h2 : ρ *ᵥ yv γ b = γ *ᵥ ((γ⁻¹ * ρ * γ) *ᵥ DF.ee k r b) := by
      rw [yv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    rw [h2, h1]; rfl

  have hW : ∀ j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → ρ *ᵥ bvec j = bvec j := by
    intro j hj1 hj2
    set t := ρ *ᵥ bvec j - bvec j with ht
    have htX : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → t i = 0 := by
      intro i hi
      rw [ht, Pi.sub_apply, ← entry, hρ.1.2.2 i j hj1 hj2 hi]
      simp [bvec, Pi.single_apply, eq_comm]
    have hty : ∀ b : Fin r, herm (Hpk k r) t (yv γ b) = 0 := by
      intro b
      rw [ht, B2x4.herm_sub_left]
      conv_lhs => rw [← hy b]
      rw [B2x4.herm_mulVec, hρU, hy b, sub_self]
    have hc : ∀ c : Fin r, t (eI k r c) = 0 := by
      intro c
      have := hty ((sX hB).symm c)
      rw [decompX t htX, DF.herm_sum_left] at this
      simp only [B2x4.herm_smul_left] at this
      rw [Finset.sum_eq_single c] at this
      · rw [DF.herm_symm' (yv γ _), y_ee D hZ hB, Equiv.apply_symm_apply, if_pos rfl] at this
        have hdn := hd ((sX hB).symm c).castSucc
        have : t (eI k r c) * star (d ((sX hB).symm c).castSucc) = 0 := this
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd (star_eq_zero.mp h) hdn
      · intro c' _ hc'
        rw [DF.herm_symm' (yv γ _), y_ee D hZ hB, Equiv.apply_symm_apply, if_neg hc']; simp
      · simp
    have ht0 : t = 0 := by
      rw [decompX t htX]; simp [hc]
    rw [ht, sub_eq_zero] at ht0; exact ht0

  have hno : ∀ q : Fin (2 * r + k + 1) → ℂ, (∀ c : Fin r, q (esI k r c) = 0) → ρ *ᵥ q = q := by
    intro q hq
    have eq : q = ∑ i, q i • bvec i := by
      funext m; simp [Finset.sum_apply, bvec, Pi.single_apply]
    rw [eq, Matrix.mulVec_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Matrix.mulVec_smul]
    rcases pos_cases i with ⟨c, rfl⟩ | ⟨h1, h2⟩ | ⟨c, rfl⟩
    · rw [show bvec (eI k r c) = DF.ee k r c from rfl, hee c]
    · rw [hW i h1 h2]
    · rw [hq c]; simp

  have hes : ∀ c : Fin r, ρ *ᵥ DF.es k r c = DF.es k r c := by
    intro c
    set b := (sX hB).symm c
    have hdb := hd b.castSucc
    set q := yv γ b - d b.castSucc • DF.es k r c with hq
    have hq0 : ∀ c' : Fin r, q (esI k r c') = 0 := by
      intro c'
      rw [hq, Pi.sub_apply, ← DF.herm_ee (yv γ b) c', y_ee D hZ hB, Pi.smul_apply]
      simp only [DF.es, bvec, Pi.single_apply, DF.esI_inj, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases h : c' = c
      · subst h; simp [b]
      · have : ¬ (c' = sX hB b) := by simp [b, h]
        simp [this, h]
    have e1 : d b.castSucc • DF.es k r c = yv γ b - q := by rw [hq]; abel
    have e2 : ρ *ᵥ (d b.castSucc • DF.es k r c) = d b.castSucc • DF.es k r c := by
      rw [e1, Matrix.mulVec_sub, hy b, hno q hq0]
    rw [Matrix.mulVec_smul] at e2
    exact smul_right_injective _ hdb e2

  ext i j
  rw [entry ρ i j]
  rcases pos_cases j with ⟨c, rfl⟩ | ⟨h1, h2⟩ | ⟨c, rfl⟩
  · rw [show bvec (eI k r c) = DF.ee k r c from rfl, hee c]; simp [Matrix.one_apply, DF.ee, bvec, Pi.single_apply, eq_comm]
  · rw [hW j h1 h2]; simp [Matrix.one_apply, bvec, Pi.single_apply, eq_comm]
  · rw [show bvec (esI k r c) = DF.es k r c from rfl, hes c]; simp [Matrix.one_apply, DF.es, bvec, Pi.single_apply, eq_comm]

theorem inj_degen : Set.InjOn (C2.uMap k r D.z) (C6.Rset γ) := by
  intro ρ1 h1 ρ2 h2 heq
  have hR := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (isUnit_G hγ)
  have hu1 : IsUnit ρ1.det := hR.unit ρ1 h1
  have hi := hR.inv_mem ρ1 h1
  have hm := hR.mul_mem _ hi ρ2 h2
  have hinv : C2.uMap k r D.z ρ1⁻¹ * C2.uMap k r D.z ρ1 = 1 := by
    rw [← uMap_mul D hi.1 h1.1, Matrix.nonsing_inv_mul _ hu1, uMap_one D.z ⟨D.z_mem, D.T_pos⟩]
  have h1' : C2.uMap k r D.z (ρ1⁻¹ * ρ2) = 1 := by
    rw [uMap_mul D hi.1 h2.1, ← heq, hinv]
  have := trivial_of_u_one D hγ hd hZ hB hm h1'
  calc ρ1 = ρ1 * (ρ1⁻¹ * ρ2) := by rw [this, Matrix.mul_one]
    _ = ρ2 := by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.one_mul]

end degenInj

section final
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)

theorem pos_of_w {γ : B.Mat k r} {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) ≠ Fin.last r) : 0 < Gf k r D.z D.z' γ := by
  have hP := Formalism.FourierDecayAlt.P.C2x2.isUnit_det_monomialMatrix w d hd
  have h1 : Dmin k r D.z D.z' γ (Fin.last (r + 1)) = (C2.monoP w d).det := by
    unfold Dmin; rw [hZ]; congr 1
  have h0 : Dmin k r D.z D.z' γ ⟨r, by omega⟩ = 0 := by
    unfold Dmin; rw [hZ]
    have hbl : w.symm (Fin.last r) ≠ Fin.last r := by
      intro h; apply hB; conv_lhs => rw [← h]; rw [w.apply_symm_apply]
    obtain ⟨j0, hj0⟩ := (DF.cast_or_last (w.symm (Fin.last r))).resolve_left hbl
    apply Matrix.det_eq_zero_of_column_eq_zero ⟨j0.val, j0.isLt⟩
    intro i
    simp only [Matrix.submatrix_apply, C2.monoP, Matrix.of_apply]
    rw [if_neg]
    intro h
    have e : Fin.castLE (Nat.le_of_lt_succ (show r < r + 2 by omega)) (⟨j0.val, j0.isLt⟩ : Fin r) = j0.castSucc :=
      Fin.ext rfl
    rw [e, ← hj0, w.apply_symm_apply] at h
    have := congrArg Fin.val h
    simp at this; omega
  unfold Gf
  rw [h1, h0, Complex.normSq_zero, mul_zero, sub_zero]
  exact Complex.normSq_pos.mpr hP.ne_zero

end final

theorem muRHaar : Formalism.FourierDecayAlt.D.MuRHaar := by
  intro k r Wp Wq _ _ _ _ D γ w d hγ hd hZ
  by_cases hB : w (Fin.last r) = Fin.last r
  · exact haar_good D hγ hd ⟨ex_degen D hγ hd hZ hB, inj_degen D hγ hd hZ hB, fun ρ hρ => lst_gen D hγ hd hZ hρ⟩
  · have hpos := pos_of_w D hd hZ hB
    exact haar_good D hγ hd ⟨exists_rho D hγ hpos hd hZ, u_inj D hγ hpos hd hZ, fun ρ hρ => u_lstg D hγ hpos hd hZ hρ⟩

end Formalism.FourierDecayAlt.P.Dx2.Rad

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Formalism.FourierDecayAlt.P.Dx2.VV

section law
variable {k r : ℕ}

def Tp (hA nA hB nB : B.Mat k r) (p : B.SS k r) : B.SS k r :=
  ((Matrix.of.symm (hA * Matrix.of p.1.1), Matrix.of.symm (hA * nA * Matrix.of p.1.2 * hA⁻¹)),
   (Matrix.of.symm (hB * Matrix.of p.2.1), Matrix.of.symm (hB * nB * Matrix.of p.2.2 * hB⁻¹)))

def Tq (hA nA hB nB : B.Mat k r) (p : B.SS k r) : B.SS k r :=
  ((Matrix.of.symm (hA⁻¹ * Matrix.of p.1.1), Matrix.of.symm (nA⁻¹ * hA⁻¹ * Matrix.of p.1.2 * hA)),
   (Matrix.of.symm (hB⁻¹ * Matrix.of p.2.1), Matrix.of.symm (nB⁻¹ * hB⁻¹ * Matrix.of p.2.2 * hB)))

theorem cont_Tp (hA nA hB nB : B.Mat k r) : Continuous (Tp hA nA hB nB) := by
  unfold Tp
  refine Continuous.prodMk (Continuous.prodMk ?_ ?_) (Continuous.prodMk ?_ ?_)
  · exact continuous_const.matrix_mul (continuous_fst.fst : Continuous fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r))
  · exact ((continuous_const.matrix_mul
      (continuous_fst.snd : Continuous fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r))).matrix_mul continuous_const)
  · exact continuous_const.matrix_mul (continuous_snd.fst : Continuous fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r))
  · exact ((continuous_const.matrix_mul
      (continuous_snd.snd : Continuous fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r))).matrix_mul continuous_const)

theorem cont_Tq (hA nA hB nB : B.Mat k r) : Continuous (Tq hA nA hB nB) := by
  unfold Tq
  refine Continuous.prodMk (Continuous.prodMk ?_ ?_) (Continuous.prodMk ?_ ?_)
  · exact continuous_const.matrix_mul (continuous_fst.fst : Continuous fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r))
  · exact ((continuous_const.matrix_mul
      (continuous_fst.snd : Continuous fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r))).matrix_mul continuous_const)
  · exact continuous_const.matrix_mul (continuous_snd.fst : Continuous fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r))
  · exact ((continuous_const.matrix_mul
      (continuous_snd.snd : Continuous fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r))).matrix_mul continuous_const)

variable {hA nA hB nB : B.Mat k r}

theorem Tq_Tp (uA : IsUnit hA.det) (vA : IsUnit nA.det) (uB : IsUnit hB.det) (vB : IsUnit nB.det) (p : B.SS k r) :
    Tq hA nA hB nB (Tp hA nA hB nB p) = p := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := p
  simp only [Tp, Tq, Equiv.apply_symm_apply]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> simp only <;> apply Matrix.of.injective <;>
    simp only [Equiv.apply_symm_apply, Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uA, Matrix.one_mul]
  · rw [← Matrix.mul_assoc hA⁻¹ hA, Matrix.nonsing_inv_mul _ uA, Matrix.one_mul, ← Matrix.mul_assoc nA⁻¹ nA,
      Matrix.nonsing_inv_mul _ vA, Matrix.one_mul, Matrix.mul_one]
  · rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uB, Matrix.one_mul]
  · rw [← Matrix.mul_assoc hB⁻¹ hB, Matrix.nonsing_inv_mul _ uB, Matrix.one_mul, ← Matrix.mul_assoc nB⁻¹ nB,
      Matrix.nonsing_inv_mul _ vB, Matrix.one_mul, Matrix.mul_one]

theorem Tp_Tq (uA : IsUnit hA.det) (vA : IsUnit nA.det) (uB : IsUnit hB.det) (vB : IsUnit nB.det) (p : B.SS k r) :
    Tp hA nA hB nB (Tq hA nA hB nB p) = p := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := p
  simp only [Tp, Tq, Equiv.apply_symm_apply]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> simp only <;> apply Matrix.of.injective <;>
    simp only [Equiv.apply_symm_apply, Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uA, Matrix.one_mul]
  · rw [← Matrix.mul_assoc nA nA⁻¹, Matrix.mul_nonsing_inv _ vA, Matrix.one_mul, ← Matrix.mul_assoc hA hA⁻¹,
      Matrix.mul_nonsing_inv _ uA, Matrix.one_mul, Matrix.mul_one]
  · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uB, Matrix.one_mul]
  · rw [← Matrix.mul_assoc nB nB⁻¹, Matrix.mul_nonsing_inv _ vB, Matrix.one_mul, ← Matrix.mul_assoc hB hB⁻¹,
      Matrix.mul_nonsing_inv _ uB, Matrix.one_mul, Matrix.mul_one]

def Te (uA : IsUnit hA.det) (vA : IsUnit nA.det) (uB : IsUnit hB.det) (vB : IsUnit nB.det) : B.SS k r ≃ᵐ B.SS k r where
  toFun := Tp hA nA hB nB
  invFun := Tq hA nA hB nB
  left_inv := Tq_Tp uA vA uB vB
  right_inv := Tp_Tq uA vA uB vB
  measurable_toFun := (cont_Tp hA nA hB nB).measurable
  measurable_invFun := (cont_Tq hA nA hB nB).measurable

end law

section law2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)
variable {hA nA hB nB : B.Mat k r}

theorem Tp_eq : Tp hA nA hB nB = Prod.map (Prod.map (lmulM hA) (conjM hA ∘ lmulM nA))
    (Prod.map (lmulM hB) (conjM hB ∘ lmulM nB)) := by
  funext p
  show ((Matrix.of.symm (hA * Matrix.of p.1.1), Matrix.of.symm (hA * nA * Matrix.of p.1.2 * hA⁻¹)),
      (Matrix.of.symm (hB * Matrix.of p.2.1), Matrix.of.symm (hB * nB * Matrix.of p.2.2 * hB⁻¹))) =
    ((Matrix.of.symm (hA * Matrix.of p.1.1), Matrix.of.symm (hA * (nA * Matrix.of p.1.2) * hA⁻¹)),
      (Matrix.of.symm (hB * Matrix.of p.2.1), Matrix.of.symm (hB * (nB * Matrix.of p.2.2) * hB⁻¹)))
  simp only [Matrix.mul_assoc]

theorem mp_Tp (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) :
    MeasurePreserving (Tp hA nA hB nB) S.μSS S.μSS := by
  have sW := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF S.haarW
  have sN := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF S.haarN
  have sW' := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF S.haarW'
  have hci := Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq S
  have m1 : MeasurePreserving (lmulM (k := k) (r := r) hA) S.μW S.μW :=
    ⟨B2x5.measurable_lmulM _, S.haarW.left hA hhA⟩
  have m2 : MeasurePreserving (conjM hA ∘ lmulM (k := k) (r := r) nA) S.μN S.μN :=
    (MeasurePreserving.mk (B2x5.measurable_conjM _) (hci hA (Or.inl hhA))).comp
      ⟨B2x5.measurable_lmulM _, S.haarN.left nA hnA⟩
  have m3 : MeasurePreserving (lmulM (k := k) (r := r) hB) S.μW' S.μW' :=
    ⟨B2x5.measurable_lmulM _, S.haarW'.left hB hhB⟩
  have m4 : MeasurePreserving (conjM hB ∘ lmulM (k := k) (r := r) nB) S.μN S.μN :=
    (MeasurePreserving.mk (B2x5.measurable_conjM _) (hci hB (Or.inr hhB))).comp
      ⟨B2x5.measurable_lmulM _, S.haarN.left nB hnB⟩
  rw [Tp_eq]
  exact (m1.prod m2).prod (m3.prod m4)

end law2

section alg
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)
variable {hA nA hB nB : B.Mat k r}

theorem sgs_Tp (uA : IsUnit hA.det) (uB : IsUnit hB.det) (p : B.SS k r) (γ : B.Mat k r) :
    B.sgs (Tp hA nA hB nB p) γ = B.sgs p ((hA * nA)⁻¹ * γ * (hB * nB)) := by
  simp only [B.sgs, Tp, Equiv.apply_symm_apply, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ uA,
    Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ uA, Matrix.nonsing_inv_mul_cancel_left _ _ uB]

theorem act_Tp (uA : IsUnit hA.det) (vA : IsUnit nA.det) (uB : IsUnit hB.det) (vB : IsUnit nB.det) (γ : B.Mat k r)
    (uγ : IsUnit γ.det) (y : B.Mat k r) (p : B.SS k r) :
    Tp hA nA hB nB (C6.actR ((hA * nA)⁻¹ * γ * (hB * nB)) ((hA * nA)⁻¹ * y * (hA * nA)) p) =
      C6.actR γ y (Tp hA nA hB nB p) := by
  have sA : IsUnit (hA * nA).det := by rw [Matrix.det_mul]; exact uA.mul vA
  have sB : IsUnit (hB * nB).det := by rw [Matrix.det_mul]; exact uB.mul vB
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := p
  simp only [Tp, C6.actR, Equiv.apply_symm_apply]
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_) <;> simp only <;> apply Matrix.of.symm.injective.eq_iff.mpr ?_
  ·
    rw [show hA * nA * ((hA * nA)⁻¹ * y * (hA * nA) * Matrix.of b) * hA⁻¹ =
        (hA * nA * (hA * nA)⁻¹) * y * (hA * nA * Matrix.of b * hA⁻¹) by simp only [Matrix.mul_assoc],
      Matrix.mul_nonsing_inv _ sA, Matrix.one_mul]
  ·
    have e : ((hA * nA)⁻¹ * γ * (hB * nB))⁻¹ = (hB * nB)⁻¹ * γ⁻¹ * (hA * nA) := by
      rw [Matrix.mul_inv_rev ((hA * nA)⁻¹ * γ) (hB * nB), Matrix.mul_inv_rev (hA * nA)⁻¹ γ,
        Matrix.nonsing_inv_nonsing_inv _ sA]
      simp only [Matrix.mul_assoc]
    rw [e]
    have e2 : hB * nB * ((hB * nB)⁻¹ * γ⁻¹ * (hA * nA) * ((hA * nA)⁻¹ * y * (hA * nA)) *
        ((hA * nA)⁻¹ * γ * (hB * nB)) * Matrix.of d) * hB⁻¹ =
        (hB * nB * (hB * nB)⁻¹) * γ⁻¹ * ((hA * nA) * (hA * nA)⁻¹) * y * ((hA * nA) * (hA * nA)⁻¹) * γ *
          (hB * nB * Matrix.of d * hB⁻¹) := by simp only [Matrix.mul_assoc]
    rw [e2, Matrix.mul_nonsing_inv _ sB, Matrix.mul_nonsing_inv _ sA, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_one]

theorem ell_fix {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n : B.Mat k r}
    (hf : ∀ b, n *ᵥ fvec k r z b = fvec k r z b) : ell k r z n = 0 := by
  unfold ell
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with h
  · have := congrFun (hf ⟨a.val + 1, by omega⟩) (eI k r a)
    simp only [fvec, show a.val + 1 < r from h, dif_pos] at this
    have e : n (eI k r a) (eI k r ⟨a.val + 1, h⟩) = (n *ᵥ bvec (eI k r ⟨a.val + 1, h⟩)) (eI k r a) := by
      simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [e, this]
    simp [bvec, Pi.single_apply, eI, Fin.ext_iff]
  · have := congrFun (hf (Fin.last r)) (eI k r a)
    simp only [fvec, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true] at this
    rw [this]
    exact hz (eI k r a) (Or.inl (by simp [eI]))

theorem lam_Tp {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h n x : B.Mat k r} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) (hf : ∀ b, n *ᵥ fvec k r z b = fvec k r z b) (hx : x ∈ Nset k r) :
    B.lam k r z (h * n * x * h⁻¹) = B.lam k r z x := by
  have hnx : n * x ∈ Nset k r := WeylGroupFacts.mem_n_mul hn hx
  have := (uWNormal k r z hz h hh (n * x) hnx).2
  unfold B.lam
  rw [show h * n * x * h⁻¹ = h * (n * x) * h⁻¹ by simp only [Matrix.mul_assoc], this,
    Formalism.QuantumDeterminants.length_additive_holds k r z hz n hn x hx, ell_fix hz hf, zero_add]

end alg

section integrand
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)
variable {hA nA hB nB : B.Mat k r}

theorem xiTau_Tp (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hfA : ∀ b, nA *ᵥ fvec k r S.z b = fvec k r S.z b)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) (hfB : ∀ b, nB *ᵥ fvec k r S.z' b = fvec k r S.z' b)
    (p : B.SS k r) (h1 : Matrix.of p.1.2 ∈ Nset k r) (h2 : Matrix.of p.2.2 ∈ Nset k r) :
    B.xiTau S (1, 1) (Tp hA nA hB nB p) = B.xiTau S (1, 1) p := by
  unfold B.xiTau
  simp only [Tp, Equiv.apply_symm_apply]
  rw [lam_Tp S.z_mem hhA hnA hfA h1, lam_Tp S.z'_mem hhB hnB hfB h2]

def Cin (hA hB : B.Mat k r) (X : Wq →L[ℂ] Wp) : Wq →L[ℂ] Wp := (S.π hA).comp (X.comp (S.π' hB⁻¹))

theorem rho_Tp (uA : IsUnit hA.det) (uB : IsUnit hB.det) (hhA : hA ∈ UWset k r S.z) (hhB : hB ∈ UWset k r S.z')
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (p : B.SS k r)
    (h1 : Matrix.of p.1.1 ∈ UWset k r S.z) (h2 : Matrix.of p.2.1 ∈ UWset k r S.z') :
    B.rho S (Tp hA nA hB nB p) F γ = Cin S hA hB (B.rho S p F ((hA * nA)⁻¹ * γ * (hB * nB))) := by
  unfold B.rho Cin
  rw [sgs_Tp uA uB]
  simp only [Tp, Equiv.apply_symm_apply]
  rw [S.π_rep.2 hA hhA _ h1, show (hB * Matrix.of p.2.1)⁻¹ = (Matrix.of p.2.1)⁻¹ * hB⁻¹ from Matrix.mul_inv_rev _ _,
    S.π'_rep.2 _ (WeylGroupFacts.uw_inv h2) _ (WeylGroupFacts.uw_inv hhB)]
  simp only [ContinuousLinearMap.comp_assoc]

theorem integrand_Tp (uA : IsUnit hA.det) (uB : IsUnit hB.det) (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r)
    (hfA : ∀ b, nA *ᵥ fvec k r S.z b = fvec k r S.z b)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) (hfB : ∀ b, nB *ᵥ fvec k r S.z' b = fvec k r S.z' b)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (p : B.SS k r) (hp : S.inSS p) :
    Formalism.FourierDecayAlt.D.orbIntegrand S γ F (Tp hA nA hB nB p) = Cin S hA hB (Formalism.FourierDecayAlt.D.orbIntegrand S ((hA * nA)⁻¹ * γ * (hB * nB)) F p) := by
  unfold Formalism.FourierDecayAlt.D.orbIntegrand
  rw [xiTau_Tp S hhA hnA hfA hhB hnB hfB p hp.2.1 hp.2.2.2, rho_Tp S uA uB hhA hhB F γ p hp.1 hp.2.2.1]
  simp only [Cin, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]

end integrand

section lawMain
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)
variable {hA nA hB nB : B.Mat k r}

def conjA (hA nA : B.Mat k r) (x : Mt k r) : Mt k r := Matrix.of.symm ((hA * nA)⁻¹ * Matrix.of x * (hA * nA))

theorem cont_conjA (hA nA : B.Mat k r) : Continuous (conjA hA nA) := by
  unfold conjA
  exact (continuous_const.matrix_mul (continuous_id : Continuous fun x : Mt k r => (Matrix.of x : B.Mat k r))).matrix_mul
    continuous_const

theorem inSS_Tp (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r)
    {p : B.SS k r} (hp : S.inSS p) : S.inSS (Tp hA nA hB nB p) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tp, Equiv.apply_symm_apply]
  · exact WeylGroupFacts.uw_mul hhA h1
  · rw [show hA * nA * Matrix.of p.1.2 * hA⁻¹ = hA * (nA * Matrix.of p.1.2) * hA⁻¹ by simp only [Matrix.mul_assoc]]
    exact (uWNormal k r S.z S.z_mem hA hhA _ (WeylGroupFacts.mem_n_mul hnA h2)).1
  · exact WeylGroupFacts.uw_mul hhB h3
  · rw [show hB * nB * Matrix.of p.2.2 * hB⁻¹ = hB * (nB * Matrix.of p.2.2) * hB⁻¹ by simp only [Matrix.mul_assoc]]
    exact (uWNormal k r S.z' S.z'_mem hB hhB _ (WeylGroupFacts.mem_n_mul hnB h4)).1

theorem inSS_Tq (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r)
    {p : B.SS k r} (hp : S.inSS p) : S.inSS (Tq hA nA hB nB p) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have uA := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1
  have uB := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhB.1
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tq, Equiv.apply_symm_apply]
  · exact WeylGroupFacts.uw_mul (WeylGroupFacts.uw_inv hhA) h1
  · have := (uWNormal k r S.z S.z_mem hA⁻¹ (WeylGroupFacts.uw_inv hhA) _ h2).1
    rw [Matrix.nonsing_inv_nonsing_inv _ uA] at this
    rw [show nA⁻¹ * hA⁻¹ * Matrix.of p.1.2 * hA = nA⁻¹ * (hA⁻¹ * Matrix.of p.1.2 * hA) by simp only [Matrix.mul_assoc]]
    exact WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_inv hnA) this
  · exact WeylGroupFacts.uw_mul (WeylGroupFacts.uw_inv hhB) h3
  · have := (uWNormal k r S.z' S.z'_mem hB⁻¹ (WeylGroupFacts.uw_inv hhB) _ h4).1
    rw [Matrix.nonsing_inv_nonsing_inv _ uB] at this
    rw [show nB⁻¹ * hB⁻¹ * Matrix.of p.2.2 * hB = nB⁻¹ * (hB⁻¹ * Matrix.of p.2.2 * hB) by simp only [Matrix.mul_assoc]]
    exact WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_inv hnB) this

theorem cut_Tp (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r)
    {γ : B.Mat k r} (uγ : IsUnit γ.det) {μR : Measure (Mt k r)} {θ : B.SS k r → ℝ}
    (hθ : Formalism.FourierDecayAlt.D.IsNormCut S γ μR θ) :
    Formalism.FourierDecayAlt.D.IsNormCut S ((hA * nA)⁻¹ * γ * (hB * nB)) (μR.map (conjA hA nA)) (θ ∘ Tp hA nA hB nB) := by
  have uA := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1
  have uB := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhB.1
  have vA := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N hnA
  have vB := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N hnB
  refine ⟨hθ.1.comp (cont_Tp _ _ _ _).measurable, fun p => hθ.2.1 _, fun p hp => ?_⟩
  have hm : Measurable fun x : Mt k r => (θ ∘ Tp hA nA hB nB)
      (C6.actR ((hA * nA)⁻¹ * γ * (hB * nB)) (Matrix.of x) p) :=
    hθ.1.comp ((cont_Tp _ _ _ _).comp ((Formalism.FourierDecayAlt.P.Dx2.OrbJ.contT _).comp
      (continuous_const.prodMk continuous_id))).measurable
  rw [integral_map (cont_conjA hA nA).measurable.aemeasurable hm.aestronglyMeasurable]
  simp only [Function.comp, conjA, Equiv.apply_symm_apply]
  simp_rw [act_Tp uA vA uB vB γ uγ]
  exact hθ.2.2 _ (inSS_Tp S hhA hnA hhB hnB hp)

theorem cut_Tq (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r)
    {γ : B.Mat k r} (uγ : IsUnit γ.det) {μR : Measure (Mt k r)} {θ : B.SS k r → ℝ}
    (hθ : Formalism.FourierDecayAlt.D.IsNormCut S ((hA * nA)⁻¹ * γ * (hB * nB)) (μR.map (conjA hA nA)) θ) :
    Formalism.FourierDecayAlt.D.IsNormCut S γ μR (θ ∘ Tq hA nA hB nB) := by
  have uA := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1
  have uB := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhB.1
  have vA := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N hnA
  have vB := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N hnB
  refine ⟨hθ.1.comp (cont_Tq _ _ _ _).measurable, fun p => hθ.2.1 _, fun q hq => ?_⟩
  have key : ∀ y : Mt k r, Tq hA nA hB nB (C6.actR γ (Matrix.of y) q) =
      C6.actR ((hA * nA)⁻¹ * γ * (hB * nB)) (Matrix.of (conjA hA nA y)) (Tq hA nA hB nB q) := by
    intro y
    have := act_Tp uA vA uB vB γ uγ (Matrix.of y) (Tq hA nA hB nB q)
    rw [Tp_Tq uA vA uB vB] at this
    rw [← this, Tq_Tp uA vA uB vB]; rfl
  have hm : Measurable fun x : Mt k r => θ (C6.actR ((hA * nA)⁻¹ * γ * (hB * nB)) (Matrix.of x) (Tq hA nA hB nB q)) :=
    hθ.1.comp ((Formalism.FourierDecayAlt.P.Dx2.OrbJ.contT _).comp (continuous_const.prodMk continuous_id)).measurable
  have := hθ.2.2 _ (inSS_Tq S hhA hnA hhB hnB hq)
  rw [integral_map (cont_conjA hA nA).measurable.aemeasurable hm.aestronglyMeasurable] at this
  simp only [Function.comp]
  simp_rw [key]
  exact this

end lawMain

section lawFinal
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)
variable {hA nA hB nB : B.Mat k r}

def CinL (hA hB : B.Mat k r) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp (S.π hA)).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (S.π' hB⁻¹))

theorem CinL_apply (hA hB : B.Mat k r) (X : Wq →L[ℂ] Wp) : CinL S hA hB X = Cin S hA hB X := rfl

theorem CinL_inv (hhA : hA ∈ UWset k r S.z) (hhB : hB ∈ UWset k r S.z') (X : Wq →L[ℂ] Wp) :
    CinL S hA⁻¹ hB⁻¹ (CinL S hA hB X) = X := by
  have uA := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1
  have uB := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhB.1
  have e1 : ∀ w, S.π hA⁻¹ (S.π hA w) = w := by
    intro w
    have := congrArg (fun L : Wp →L[ℂ] Wp => L w) (S.π_rep.2 _ (WeylGroupFacts.uw_inv hhA) _ hhA)
    simp only [Matrix.nonsing_inv_mul _ uA, S.π_rep.1, ContinuousLinearMap.comp_apply] at this
    rw [← this]; rfl
  have e2 : ∀ v, S.π' hB⁻¹ (S.π' hB v) = v := by
    intro v
    have := congrArg (fun L : Wq →L[ℂ] Wq => L v) (S.π'_rep.2 _ (WeylGroupFacts.uw_inv hhB) _ hhB)
    simp only [Matrix.nonsing_inv_mul _ uB, S.π'_rep.1, ContinuousLinearMap.comp_apply] at this
    rw [← this]; rfl
  simp only [CinL_apply, Cin]
  rw [Matrix.nonsing_inv_nonsing_inv _ uB]
  ext v
  simp only [ContinuousLinearMap.comp_apply]
  rw [e2, e1]

def IndepAt (γ : B.Mat k r) (μR : Measure (Mt k r)) : Prop :=
  ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (θ θ' : B.SS k r → ℝ),
    Formalism.FourierDecayAlt.D.IsNormCut S γ μR θ → Formalism.FourierDecayAlt.D.IsNormCut S γ μR θ' →
    Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand S γ F p) S.μSS →
    Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand S γ F p) S.μSS →
    ∫ p, θ p • Formalism.FourierDecayAlt.D.orbIntegrand S γ F p ∂S.μSS = ∫ p, θ' p • Formalism.FourierDecayAlt.D.orbIntegrand S γ F p ∂S.μSS

theorem orbJ_law (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hfA : ∀ b, nA *ᵥ fvec k r S.z b = fvec k r S.z b)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) (hfB : ∀ b, nB *ᵥ fvec k r S.z' b = fvec k r S.z' b)
    {γ : B.Mat k r} (uγ : IsUnit γ.det) (μR : Measure (Mt k r))
    (hInd : IndepAt S ((hA * nA)⁻¹ * γ * (hB * nB)) (μR.map (conjA hA nA))) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    CinL S hA hB (Formalism.FourierDecayAlt.D.orbJ S ((hA * nA)⁻¹ * γ * (hB * nB)) (μR.map (conjA hA nA)) F) =
      Formalism.FourierDecayAlt.D.orbJ S γ μR F := by
  have uA := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1
  have uB := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhB.1
  have vA := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N hnA
  have vB := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N hnB
  have hmp := mp_Tp S hhA hnA hhB hnB
  have hemb : MeasurableEmbedding (Tp hA nA hB nB) := (Te uA vA uB vB).measurableEmbedding
  have hae := Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_inSS S
  set γ1 := (hA * nA)⁻¹ * γ * (hB * nB) with hγ1

  have hint : ∀ θ : B.SS k r → ℝ, ∀ᵐ p ∂S.μSS,
      CinL S hA hB (θ (Tp hA nA hB nB p) • Formalism.FourierDecayAlt.D.orbIntegrand S γ1 F p) =
        θ (Tp hA nA hB nB p) • Formalism.FourierDecayAlt.D.orbIntegrand S γ F (Tp hA nA hB nB p) := by
    intro θ
    filter_upwards [hae] with p hp
    rw [integrand_Tp S uA uB hhA hnA hfA hhB hnB hfB F γ p hp, (CinL S hA hB).map_smul_of_tower, CinL_apply]

  have tr1 : ∀ θ : B.SS k r → ℝ, Integrable (fun q => θ q • Formalism.FourierDecayAlt.D.orbIntegrand S γ F q) S.μSS →
      Integrable (fun p => θ (Tp hA nA hB nB p) • Formalism.FourierDecayAlt.D.orbIntegrand S γ1 F p) S.μSS := by
    intro θ hθ
    have h1 : Integrable ((fun q => θ q • Formalism.FourierDecayAlt.D.orbIntegrand S γ F q) ∘ Tp hA nA hB nB) S.μSS :=
      (hmp.integrable_comp_emb hemb).mpr hθ
    have h2 := (CinL S hA⁻¹ hB⁻¹).integrable_comp h1
    refine h2.congr ?_
    filter_upwards [hint θ] with p hp
    simp only [Function.comp]
    rw [← hp, CinL_inv S hhA hhB]
  have tr2 : ∀ θ : B.SS k r → ℝ, Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand S γ1 F p) S.μSS →
      Integrable (fun q => θ (Tq hA nA hB nB q) • Formalism.FourierDecayAlt.D.orbIntegrand S γ F q) S.μSS := by
    intro θ hθ
    refine (hmp.integrable_comp_emb hemb).mp ?_
    have h2 := (CinL S hA hB).integrable_comp hθ
    refine h2.congr ?_
    filter_upwards [hint (θ ∘ Tq hA nA hB nB)] with p hp
    simp only [Function.comp, Tq_Tp uA vA uB vB] at hp ⊢
    exact hp
  by_cases hE : CompleteSpace (Wq →L[ℂ] Wp)
  swap
  · unfold Formalism.FourierDecayAlt.D.orbJ
    split_ifs <;> simp only [integral_of_not_completeSpace hE, map_zero]
  unfold Formalism.FourierDecayAlt.D.orbJ
  by_cases h0 : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut S γ μR θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand S γ F p) S.μSS
  · set θ0 := h0.choose with hθ0
    have hc0 := h0.choose_spec
    have hcut : Formalism.FourierDecayAlt.D.IsNormCut S γ1 (μR.map (conjA hA nA)) (θ0 ∘ Tp hA nA hB nB) :=
      cut_Tp S hhA hnA hhB hnB uγ hc0.1
    have hi1 := tr1 θ0 hc0.2
    have h1 : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut S γ1 (μR.map (conjA hA nA)) θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand S γ1 F p) S.μSS := ⟨_, hcut, hi1⟩
    rw [dif_pos h1, dif_pos h0]
    rw [hInd F _ (θ0 ∘ Tp hA nA hB nB) h1.choose_spec.1 hcut h1.choose_spec.2 hi1]
    simp only [Function.comp]
    rw [← (CinL S hA hB).integral_comp_comm hi1]
    rw [integral_congr_ae (hint θ0)]
    exact hmp.integral_comp hemb (fun q => θ0 q • Formalism.FourierDecayAlt.D.orbIntegrand S γ F q)
  · have h1 : ¬ ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut S γ1 (μR.map (conjA hA nA)) θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand S γ1 F p) S.μSS := by
      rintro ⟨θ, hc, hi⟩
      exact h0 ⟨θ ∘ Tq hA nA hB nB, cut_Tq S hhA hnA hhB hnB uγ hc, tr2 θ hi⟩
    rw [dif_neg h1, dif_neg h0, map_zero]

end lawFinal

section muRconj
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)
variable {hA nA hB nB : B.Mat k r}

theorem conjN_in {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h n x : B.Mat k r} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) (hx : x ∈ Nset k r) : (h * n)⁻¹ * x * (h * n) ∈ Nset k r := by
  have uh := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hh.1
  have h1 := (uWNormal k r z hz h⁻¹ (WeylGroupFacts.uw_inv hh) x hx).1
  rw [Matrix.nonsing_inv_nonsing_inv _ uh] at h1
  rw [Matrix.mul_inv_rev, show n⁻¹ * h⁻¹ * x * (h * n) = n⁻¹ * (h⁻¹ * x * h) * n by simp only [Matrix.mul_assoc]]
  exact WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_inv hn) h1) hn

theorem conjN_out {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h n x : B.Mat k r} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) (hx : x ∈ Nset k r) : (h * n) * x * (h * n)⁻¹ ∈ Nset k r := by
  have h1 := (uWNormal k r z hz h hh (n * x * n⁻¹) (WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul hn hx) (WeylGroupFacts.mem_n_inv hn))).1
  rw [Matrix.mul_inv_rev, show h * n * x * (n⁻¹ * h⁻¹) = h * (n * x * n⁻¹) * h⁻¹ by simp only [Matrix.mul_assoc]]
  exact h1

theorem rset_conj (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r)
    {γ : B.Mat k r} (uγ : IsUnit γ.det) (ρ : B.Mat k r) :
    ρ ∈ C6.Rset γ ↔ (hA * nA)⁻¹ * ρ * (hA * nA) ∈ C6.Rset ((hA * nA)⁻¹ * γ * (hB * nB)) := by
  have uA := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1
  have uB := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhB.1
  have vA := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N hnA
  have vB := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N hnB
  have sA : IsUnit (hA * nA).det := by rw [Matrix.det_mul]; exact uA.mul vA
  have sB : IsUnit (hB * nB).det := by rw [Matrix.det_mul]; exact uB.mul vB
  have e : ((hA * nA)⁻¹ * γ * (hB * nB))⁻¹ * ((hA * nA)⁻¹ * ρ * (hA * nA)) * ((hA * nA)⁻¹ * γ * (hB * nB)) =
      (hB * nB)⁻¹ * (γ⁻¹ * ρ * γ) * (hB * nB) := by
    rw [Matrix.mul_inv_rev ((hA * nA)⁻¹ * γ) (hB * nB), Matrix.mul_inv_rev (hA * nA)⁻¹ γ,
      Matrix.nonsing_inv_nonsing_inv _ sA]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ sA]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨conjN_in S.z_mem hhA hnA h1, ?_⟩
    rw [e]; exact conjN_in S.z'_mem hhB hnB h2
  · rintro ⟨h1, h2⟩
    rw [e] at h2
    have h1' := conjN_out S.z_mem hhA hnA h1
    have h2' := conjN_out S.z'_mem hhB hnB h2
    have c1 : (hA * nA) * ((hA * nA)⁻¹ * ρ * (hA * nA)) * (hA * nA)⁻¹ = ρ := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ sA, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ sA]
    have c2 : (hB * nB) * ((hB * nB)⁻¹ * (γ⁻¹ * ρ * γ) * (hB * nB)) * (hB * nB)⁻¹ = γ⁻¹ * ρ * γ := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ sB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ sB]
    rw [c1] at h1'; rw [c2] at h2'
    exact ⟨h1', h2'⟩

theorem uMap_conj (hz : C2.StdZ k r S.z) {s ρ : B.Mat k r} (us : IsUnit s.det)
    (hs : ∀ b, s *ᵥ fvec k r S.z b = fvec k r S.z b) (hρ : ρ ∈ Nset k r) :
    C2.uMap k r S.z (s⁻¹ * ρ * s) = C2.uMap k r S.z ρ := by
  have hsi : ∀ b, s⁻¹ *ᵥ fvec k r S.z b = fvec k r S.z b := by
    intro b
    have := congrArg (fun v => s⁻¹ *ᵥ v) (hs b)
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ us, Matrix.one_mulVec] at this
    exact this.symm
  have hρS : ρ ∈ Sset k r S.z := Formalism.FourierDecayAlt.P.Dx2.Rad.N_sub_S S.z hρ
  have hexp := ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r S.z hz).1 ρ hρS).1
  have e : ∀ b, (s⁻¹ * ρ * s) *ᵥ fvec k r S.z b = ρ *ᵥ fvec k r S.z b := by
    intro b
    rw [← Matrix.mulVec_mulVec, hs b, ← Matrix.mulVec_mulVec, hexp b, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hsi]
  unfold C2.uMap
  ext a b
  simp only [e b]

end muRconj

section muRconj2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)
variable {hA nA hB nB : B.Mat k r}

theorem rhoOfU_conj (hz : C2.StdZ k r S.z) (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r)
    (hsfix : ∀ b, (hA * nA) *ᵥ fvec k r S.z b = fvec k r S.z b)
    {γ : B.Mat k r} (uγ : IsUnit γ.det)
    (hinj : Set.InjOn (C2.uMap k r S.z) (C6.Rset ((hA * nA)⁻¹ * γ * (hB * nB))))
    (u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Formalism.FourierDecayAlt.D.rhoOfU S ((hA * nA)⁻¹ * γ * (hB * nB)) u = (hA * nA)⁻¹ * Formalism.FourierDecayAlt.D.rhoOfU S γ u * (hA * nA) := by
  have uA := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1
  have vA := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N hnA
  have sA : IsUnit (hA * nA).det := by rw [Matrix.det_mul]; exact uA.mul vA
  unfold Formalism.FourierDecayAlt.D.rhoOfU
  by_cases h : ∃ ρ ∈ C6.Rset γ, C2.uMap k r S.z ρ = u
  · obtain ⟨h0m, h0u⟩ := h.choose_spec
    have hm1 := (rset_conj S hhA hnA hhB hnB uγ h.choose).mp h0m
    have hu1 : C2.uMap k r S.z ((hA * nA)⁻¹ * h.choose * (hA * nA)) = u := by
      rw [uMap_conj S hz sA hsfix h0m.1, h0u]
    have h1 : ∃ ρ ∈ C6.Rset ((hA * nA)⁻¹ * γ * (hB * nB)), C2.uMap k r S.z ρ = u := ⟨_, hm1, hu1⟩
    rw [dif_pos h1, dif_pos h]
    exact hinj h1.choose_spec.1 hm1 (by rw [h1.choose_spec.2, hu1])
  · have h1 : ¬ ∃ ρ ∈ C6.Rset ((hA * nA)⁻¹ * γ * (hB * nB)), C2.uMap k r S.z ρ = u := by
      rintro ⟨ρ1, hρ1, hu⟩
      apply h
      refine ⟨(hA * nA) * ρ1 * (hA * nA)⁻¹, ?_, ?_⟩
      · rw [rset_conj S hhA hnA hhB hnB uγ]
        have : (hA * nA)⁻¹ * ((hA * nA) * ρ1 * (hA * nA)⁻¹) * (hA * nA) = ρ1 := by
          have c : ∀ s : B.Mat k r, IsUnit s.det → s⁻¹ * (s * ρ1 * s⁻¹) * s = ρ1 := fun s hs => by
            simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hs, Matrix.mul_one,
              Matrix.nonsing_inv_mul_cancel_left _ _ hs]
          exact c _ sA
        rw [this]; exact hρ1
      · have hN : (hA * nA) * ρ1 * (hA * nA)⁻¹ ∈ Nset k r := conjN_out S.z_mem hhA hnA hρ1.1
        rw [← uMap_conj S hz sA hsfix hN]
        have : (hA * nA)⁻¹ * ((hA * nA) * ρ1 * (hA * nA)⁻¹) * (hA * nA) = ρ1 := by
          have c : ∀ s : B.Mat k r, IsUnit s.det → s⁻¹ * (s * ρ1 * s⁻¹) * s = ρ1 := fun s hs => by
            simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hs, Matrix.mul_one,
              Matrix.nonsing_inv_mul_cancel_left _ _ hs]
          exact c _ sA
        rw [this, hu]
    rw [dif_neg h1, dif_neg h, Matrix.mul_one, Matrix.nonsing_inv_mul _ sA]

theorem muR_conj (hz : C2.StdZ k r S.z) (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r)
    (hsfix : ∀ b, (hA * nA) *ᵥ fvec k r S.z b = fvec k r S.z b)
    {γ : B.Mat k r} (uγ : IsUnit γ.det) (w : Equiv.Perm (Fin (r + 1)))
    (hinj : Set.InjOn (C2.uMap k r S.z) (C6.Rset ((hA * nA)⁻¹ * γ * (hB * nB))))
    (hm : Measurable fun x : C2.Lstidx w → ℂ =>
      (Matrix.of.symm (Formalism.FourierDecayAlt.D.rhoOfU S γ (Matrix.conjTranspose (C2.lowOf (fun q => q.1) x))) : Mt k r)) :
    Formalism.FourierDecayAlt.D.muR S ((hA * nA)⁻¹ * γ * (hB * nB)) w = (Formalism.FourierDecayAlt.D.muR S γ w).map (conjA hA nA) := by
  unfold Formalism.FourierDecayAlt.D.muR
  rw [Measure.map_map (cont_conjA hA nA).measurable hm]
  congr 1
  funext x
  simp only [Function.comp, conjA, Equiv.apply_symm_apply]
  rw [rhoOfU_conj S hz hhA hnA hhB hnB hsfix uγ hinj]

end muRconj2

section atPoints
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)

theorem ptMatN_monoP' (p : C.LPt) (n : ℕ) (h : Formalism.FourierDecayAlt.D.ptSize p = n) (hb : ∀ b ∈ p, 1 ≤ b.1 ∧ b.2 ≠ 0) :
    Formalism.FourierDecayAlt.D.ptMatN p n = C2.monoP (h ▸ Formalism.FourierDecayAlt.D.ptPerm p) (h ▸ Formalism.FourierDecayAlt.D.ptDiag p) ∧
      ∀ a, (h ▸ Formalism.FourierDecayAlt.D.ptDiag p) a ≠ 0 := by
  subst h
  exact ⟨Formalism.FourierDecayAlt.P.Dx1.ptMat_monoP p, fun a => Formalism.FourierDecayAlt.P.Dx1.Rel.scal_ne p hb a a.isLt⟩

theorem uMap_fix {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {s : B.Mat k r}
    (hs : ∀ b, s *ᵥ fvec k r z b = fvec k r z b) : C2.uMap k r z s = 1 := by
  rw [← Formalism.FourierDecayAlt.P.Dx2.Rad.uMap_one z hz]
  unfold C2.uMap
  ext a b
  simp only [hs b, Matrix.one_mulVec]

theorem std_vector_z : C2.StdZ k r S.z := ⟨S.z_mem, S.T_pos⟩
theorem std_vector_z_prime : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩

theorem UW_fix {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) (b : Fin (r + 1)) :
    h *ᵥ fvec k r z b = fvec k r z b := by
  unfold fvec
  split_ifs with hb
  · exact (hh.2.1 ⟨b.val, hb⟩).1
  · exact hh.2.2

theorem mul_fix {z : Fin (2 * r + k + 1) → ℂ} {h n : B.Mat k r} (hh : h ∈ UWset k r z)
    (hn : ∀ b, n *ᵥ fvec k r z b = fvec k r z b) (b : Fin (r + 1)) :
    (h * n) *ᵥ fvec k r z b = fvec k r z b := by
  rw [← Matrix.mulVec_mulVec, hn b, UW_fix hh b]

theorem zhat_conj {hA nA hB nB : B.Mat k r} (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r)
    (hfA : ∀ b, nA *ᵥ fvec k r S.z b = fvec k r S.z b)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) (hfB : ∀ b, nB *ᵥ fvec k r S.z' b = fvec k r S.z' b)
    (γ : B.Mat k r) : Zhat k r S.z S.z' ((hA * nA)⁻¹ * γ * (hB * nB)) = Zhat k r S.z S.z' γ := by
  rw [Formalism.FourierDecayAlt.P.zhat_equivalence k r S.z S.z' (std_vector_z S) (std_vector_z_prime S) (hA * nA) ⟨hA, hhA, nA, hnA, rfl⟩
    (hB * nB) ⟨hB, hhB, nB, hnB, rfl⟩ γ, uMap_fix (std_vector_z S) (mul_fix hhA hfA), uMap_fix (std_vector_z_prime S) (mul_fix hhB hfB)]
  simp

theorem mem_GV_conj {hA nA hB nB : B.Mat k r} (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) :
    (hA * nA)⁻¹ * γ * (hB * nB) ∈ B.GV k r := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  exact hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ (hG.mul_mem _ hhA.1 _ hnA.1)) _ hγ) _ (hG.mul_mem _ hhB.1 _ hnB.1)

theorem gf_eq {γ γ' : B.Mat k r} (h : Zhat k r S.z S.z' γ = Zhat k r S.z S.z' γ') :
    Gf k r S.z S.z' γ = Gf k r S.z S.z' γ' := by
  unfold Gf Dmin; rw [h]

theorem orbJ_pt (p : C.LPt) (hp : Formalism.FourierDecayAlt.D.IsLocPt p (r + 1)) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    (hZ : Zhat k r S.z S.z' γ = Formalism.FourierDecayAlt.D.ptMatN p (r + 1)) (hpos : 0 < Gf k r S.z S.z' γ)
    {hA nA hB nB : B.Mat k r} (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r)
    (hfA : ∀ b, nA *ᵥ fvec k r S.z b = fvec k r S.z b)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) (hfB : ∀ b, nB *ᵥ fvec k r S.z' b = fvec k r S.z' b)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    CinL S hA hB (Formalism.FourierDecayAlt.D.orbJ S ((hA * nA)⁻¹ * γ * (hB * nB))
        (Formalism.FourierDecayAlt.D.muR S ((hA * nA)⁻¹ * γ * (hB * nB)) (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F) =
      Formalism.FourierDecayAlt.D.orbJ S γ (Formalism.FourierDecayAlt.D.muR S γ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F := by
  obtain ⟨hw, hd⟩ := ptMatN_monoP' p (r + 1) hp.2 hp.1
  set w := hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p with hwdef
  set d := hp.2 ▸ Formalism.FourierDecayAlt.D.ptDiag p with hddef
  have uγ := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγ
  have hZ1 := zhat_conj S hhA hnA hfA hhB hnB hfB γ
  have hγ1 := mem_GV_conj S hhA hnA hhB hnB hγ
  have hpos1 : 0 < Gf k r S.z S.z' ((hA * nA)⁻¹ * γ * (hB * nB)) := by rw [gf_eq S hZ1]; exact hpos
  have hZw : Zhat k r S.z S.z' γ = C2.monoP w d := hZ.trans hw
  have hZ1w : Zhat k r S.z S.z' ((hA * nA)⁻¹ * γ * (hB * nB)) = C2.monoP w d := hZ1.trans hZw
  have hinj1 := Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj S hγ1 hpos1 hd hZ1w
  have hGood : Formalism.FourierDecayAlt.P.Dx2.Rad.Good S γ w d :=
    ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho S hγ hpos hd hZw, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj S hγ hpos hd hZw,
      fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg S hγ hpos hd hZw hρ⟩
  have hm := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_meas S hγ hd hGood
  have hμ := muR_conj S (std_vector_z S) hhA hnA hhB hnB (mul_fix hhA hfA) uγ w hinj1 hm
  have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq S p _ hp hγ1 (hZ1.trans hZ)
  have hhaar := Formalism.FourierDecayAlt.P.Dx2.Rad.muRHaar k r Wp Wq S _ w d hγ1 hd hZ1w
  have hInd : IndepAt S ((hA * nA)⁻¹ * γ * (hB * nB)) (Formalism.FourierDecayAlt.D.muR S ((hA * nA)⁻¹ * γ * (hB * nB)) w) :=
    fun F θ θ' => Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq S _ _ hrel hhaar F θ θ'
  rw [hμ] at hInd ⊢
  exact orbJ_law S hhA hnA hfA hhB hnB hfB uγ _ hInd F

end atPoints

section explicit
open Formalism.FourierDecayAlt.P.Dx2.DF

theorem smat_comm_Hpk {k r : ℕ} {ι : Type*} [Fintype ι] (u w Y : ι → Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hg : g ∈ UH (Hpk k r)) (hu : ∀ i, g *ᵥ u i = u i) (hw : ∀ i, g *ᵥ w i = w i) (hY : ∀ i, g *ᵥ Y i = Y i) :
    smat (Hpk k r) u w Y * g = g * smat (Hpk k r) u w Y := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, smat_mulVec, smap]
  rw [Matrix.mulVec_add, Matrix.mulVec_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have e := herm_m0_mulVec_invariant g hg x (w i)
  rw [hw i] at e
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hY i, hu i]
  rw [e]

end explicit

section explicit2
open Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate
variable {k r : ℕ}

theorem caseA' {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀) (π : Equiv.Perm (Fin (r + 1))) (d0 : Fin (r + 1) → ℂ)
    (hd0 : ∀ a, d0 a ≠ 0) (a0 b0 : Fin r) (ha : π (Fin.last r) = a0.castSucc)
    (hb : π b0.castSucc = Fin.last r) :
    ∃ σ : B.Mat k r, m₀ * σ ∈ B.GV k r ∧ Zhat k r S.z S.z' (m₀ * σ) = C2.monoP π d0 ∧
      Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ (m₀ * σ) ∧ σ ∈ UH (Hpk k r) ∧
      (∀ x, inWb k r x → herm (Hpk k r) x S.z' = 0 → herm (Hpk k r) x ν' = 0 → σ *ᵥ x = x) ∧
      (∀ g ∈ UH (Hpk k r), (∀ a : Fin r, g *ᵥ ee k r a = ee k r a ∧ g *ᵥ es k r a = es k r a) →
        g *ᵥ S.z' = S.z' → g *ᵥ ν' = ν' → σ * g = g * σ) := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := hbase
  have hme : ∀ a : Fin r, m₀ *ᵥ ee k r a = ee k r a := fun a => (hmfix a a.isLt).1
  have hms : ∀ a : Fin r, m₀ *ᵥ es k r a = es k r a := fun a => (hmfix a a.isLt).2
  have hz := S.z_mem
  have hz' := S.z'_mem
  have hT := S.T_pos
  have hT' := S.T'_pos
  set s := Real.sqrt (Tz k r S.z') with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hT'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hs2 : s ^ 2 = Tz k r S.z' := Real.sq_sqrt hT'.le
  have hzz : herm (Hpk k r) S.z' S.z' = -((s : ℂ) ^ 2) := by
    rw [herm_self_alt]; congr 1; exact_mod_cast hs2.symm
  have hzz0 : herm (Hpk k r) S.z' S.z' ≠ 0 := by rw [hzz]; simpa using hs'
  set μ := Real.sqrt (Tz k r S.z' / Tz k r S.z) with hμdef
  have hμ : 0 < μ := Real.sqrt_pos.2 (div_pos hT' hT)
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  set d' : Fin (r + 1) → ℂ := fun b => if π b = Fin.last r then (μ : ℂ) * d0 b else d0 b with hd'def
  have hd' : ∀ b, d' b ≠ 0 := by
    intro b; simp only [hd'def]; split_ifs
    · exact mul_ne_zero hμ' (hd0 b)
    · exact hd0 b
  have hne : ∀ b : Fin r, b ≠ b0 → π b.castSucc ≠ Fin.last r := by
    intro b hb' h; rw [← hb] at h; exact hb' (Fin.castSucc_injective _ (π.injective h))
  have hdb0 : d' b0.castSucc = (μ : ℂ) * d0 b0.castSucc := by simp [hd'def, hb]
  have hdl : d' (Fin.last r) = d0 (Fin.last r) := by
    simp only [hd'def]; rw [if_neg (by rw [ha]; exact Fin.castSucc_ne_last a0)]
  have hdb : ∀ b : Fin r, b ≠ b0 → d' b.castSucc = d0 b.castSucc := by
    intro b h; simp only [hd'def]; rw [if_neg (hne b h)]
  set Y := YA π d' S.z' ν' s a0 b0 with hYdef
  set σ := smat (Hpk k r) (uB S.z' ν') (wB S.z' ν' s) Y with hσdef
  have hσU : σ ∈ UH (Hpk k r) :=
    sig_UH Y hz' hν hs hzz hνz hνν (YA_gram π d' hz' hν hs hzz hνz hνν hd' a0 b0 ha hb)
      (fun x hx i => YA_perp π d' a0 b0 x hx i)
  have hσu : ∀ i, σ *ᵥ uB S.z' ν' i = Y i := sig_u Y hz' hν hs hzz hνz hνν
  have hγ : m₀ * σ ∈ UH (Hpk k r) := mul_UH hmU hσU
  have hzν := herm_zν hνz
  have hσe : ∀ b : Fin r, σ *ᵥ ee k r b = Y (Sum.inl (Sum.inl b)) := fun b => hσu (Sum.inl (Sum.inl b))
  have hσz : σ *ᵥ S.z' = Y (Sum.inr 0) := hσu (Sum.inr 0)
  have hσn : σ *ᵥ ν' = Y (Sum.inr 1) := hσu (Sum.inr 1)
  have hZ : Zhat k r S.z S.z' (m₀ * σ) = C2.monoP π d0 := by
    ext a b
    rw [reduced_matrix_of_stabilizer m₀ σ hmU hme μ hμ.ne' hmz]
    rcases cast_or_last b with hbl | ⟨b', rfl⟩ <;> rcases cast_or_last a with hal | ⟨a', rfl⟩
    · subst hbl hal
      rw [fvec_lastI, fvec_lastI, hσz]
      have h1 : ¬ (Fin.last r = π (Fin.last r)) := by rw [ha]; exact (Fin.castSucc_ne_last a0).symm
      simp [hYdef, YA, C2.monoP, h1, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
    · subst hbl
      rw [fvec_lastI, fvec_cs, hσz]
      have e : (a'.castSucc = π (Fin.last r)) ↔ (a0 = a') := by
        rw [ha]; constructor
        · intro h; exact (Fin.castSucc_injective _ h).symm
        · rintro rfl; rfl
      simp [hYdef, YA, C2.monoP, e, hdl, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
    · subst hal
      rw [fvec_lastI, fvec_cs, hσe]
      by_cases hb' : b' = b0
      · subst hb'
        simp [hYdef, YA, C2.monoP, hb, hdb0, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
        field_simp
      · have h1 : ¬ (Fin.last r = π b'.castSucc) := fun h => hne b' hb' h.symm
        simp [hYdef, YA, C2.monoP, hb', h1, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
    · rw [fvec_cs, fvec_cs, hσe]
      by_cases hb' : b' = b0
      · subst hb'
        have h1 : ¬ (a'.castSucc = π b'.castSucc) := by rw [hb]; exact Fin.castSucc_ne_last a'
        simp [hYdef, YA, C2.monoP, h1, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
      · have e : (a'.castSucc = π b'.castSucc) ↔ (piX π b' = a') := by
          rw [← piX_spec π b' (hne b' hb')]; constructor
          · intro h; exact (Fin.castSucc_injective _ h).symm
          · rintro rfl; rfl
        simp [hYdef, YA, C2.monoP, hb', e, hdb b' hb', B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
  have hγu : IsUnit (m₀ * σ).det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hγ
  have hm0u : IsUnit m₀.det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hmU
  have hDl : d0 (Fin.last r) ≠ 0 := hd0 _
  have hDc : conj (d0 (Fin.last r)) ≠ 0 := by simpa using hDl
  refine ⟨σ, hγ, hZ, ⟨?_, ?_, ?_⟩, hσU, ?_, ?_⟩
  ·
    refine ⟨μ / s, div_pos hμ hs, ?_⟩
    have hcof : Formalism.FourierDecayAlt.D.cofR S (m₀ * σ) =
        ((C2.monoP π d0).det * (d0 b0.castSucc)⁻¹) • (m₀ *ᵥ (σ *ᵥ ee k r b0)) := by
      unfold Formalism.FourierDecayAlt.D.cofR; rw [hZ]
      rw [Finset.sum_eq_single b0.castSucc]
      · rw [monomialMatrix_adj π d0 hd0, if_pos hb, fvec_cs, Matrix.mulVec_mulVec]
      · intro b _ hbne
        have : π b ≠ Fin.last r := by intro h; rw [← hb] at h; exact hbne (π.injective h)
        rw [monomialMatrix_adj π d0 hd0, if_neg this]; simp
      · simp
    rw [hcof, prW_smul, orthoProj_m0_intertwine m₀ hmU hme hms hz hz' μ hμ.ne' hmz hzz0, hσe]
    simp only [hYdef, YA, if_true]
    rw [prW_smul, prW_sub, prW_smul, prW_perp hν hνz, prW_self hz' hzz0, smul_zero, sub_zero, hZ,
      Matrix.mulVec_smul, smul_smul, hdb0]
    congr 1
    have := hd0 b0.castSucc
    push_cast; field_simp
  ·
    refine ⟨1 / s, by positivity, ?_⟩
    have hcof : Formalism.FourierDecayAlt.D.cofL S (m₀ * σ) =
        (conj ((C2.monoP π d0).det * (d0 (Fin.last r))⁻¹)) • ee k r a0 := by
      unfold Formalism.FourierDecayAlt.D.cofL; rw [hZ]
      rw [Finset.sum_eq_single (π (Fin.last r))]
      · rw [monomialMatrix_adj π d0 hd0, if_pos rfl, ha, fvec_cs]
      · intro a _ hane; rw [monomialMatrix_adj π d0 hd0, if_neg (Ne.symm hane)]; simp
      · simp
    set Dl := d0 (Fin.last r) with hDldef
    have hvec : (-(conj Dl / (s : ℂ) ^ 2)) • Y (Sum.inr 0) + (conj Dl / (s : ℂ)) • Y (Sum.inr 1) = ee k r a0 := by
      simp only [hYdef, YA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hdl]
      rw [show ∀ (α β p q c1 c2 : ℂ), α • (p • es k r a0 - c1 • ee k r a0) + β • (c2 • ee k r a0 + q • es k r a0) =
          (α * p + β * q) • es k r a0 + (β * c2 - α * c1) • ee k r a0 from by intros; module]
      have h0 : -(conj Dl / (s : ℂ) ^ 2) * Dl + conj Dl / (s : ℂ) * (Dl / (s : ℂ)) = 0 := by ring
      have h1 : conj Dl / (s : ℂ) * ((s : ℂ) / (2 * conj Dl)) - -(conj Dl / (s : ℂ) ^ 2) * ((s : ℂ) ^ 2 / (2 * conj Dl)) = 1 := by
        field_simp; ring
      rw [h0, h1, zero_smul, zero_add, one_smul]
    have hw : (m₀ * σ) *ᵥ ((-(conj Dl / (s : ℂ) ^ 2)) • S.z' + (conj Dl / (s : ℂ)) • ν') = ee k r a0 := by
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hσz, hσn, hvec, hme]
    have hinv : (m₀ * σ)⁻¹ *ᵥ ee k r a0 = (-(conj Dl / (s : ℂ) ^ 2)) • S.z' + (conj Dl / (s : ℂ)) • ν' := by
      rw [← hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hγu, Matrix.one_mulVec]
    rw [hcof, Matrix.mulVec_smul, hinv, prW_smul, prW_add, prW_smul, prW_smul, prW_self hz' hzz0,
      prW_perp hν hνz, hZ, smul_zero, zero_add, smul_smul]
    congr 1
    simp only [map_mul, map_inv₀]
    push_cast
    field_simp
  ·
    intro u hu
    set v := m₀⁻¹ *ᵥ u with hvdef
    have hmv : m₀ *ᵥ v = u := by
      rw [hvdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hm0u, Matrix.one_mulVec]
    have hv1 : ∀ a : Fin r, herm (Hpk k r) v (ee k r a) = 0 := by
      intro a; have := (hu a.castSucc).1; rw [fvec_cs, ← hmv, ← hme a, herm_m0_mulVec_invariant m₀ hmU] at this; exact this
    have hzeq : S.z = (μ : ℂ)⁻¹ • (m₀ *ᵥ S.z') := by rw [hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    have hv2 : herm (Hpk k r) v S.z' = 0 := by
      have := (hu (Fin.last r)).1
      rw [fvec_lastI, ← hmv, hzeq, B2x4.herm_smul_right, herm_m0_mulVec_invariant m₀ hmU] at this
      simpa [hμ'] using this
    have hvY : ∀ a, herm (Hpk k r) v (σ *ᵥ fvec k r S.z' a) = 0 := by
      intro a; have := (hu a).2; rw [← hmv, ← Matrix.mulVec_mulVec, herm_m0_mulVec_invariant m₀ hmU] at this; exact this
    have hv3 : herm (Hpk k r) v ν' = 0 := by
      have := hvY b0.castSucc
      rw [fvec_cs, hσe] at this
      simp only [hYdef, YA, if_true, B2x4.herm_smul_right, B2x4.herm_sub_right, hv2, mul_zero, sub_zero] at this
      rcases mul_eq_zero.1 this with h | h
      · exfalso; have := hd' b0.castSucc; simp at h
        rcases h with h | h
        · exact this h
        · exact hs.ne' h
      · exact h
    have hv4 : ∀ c : Fin r, herm (Hpk k r) v (es k r c) = 0 := by
      intro c
      by_cases hc : c = a0
      · subst hc
        have := hvY (Fin.last r)
        rw [fvec_lastI, hσz] at this
        simp only [hYdef, YA, Matrix.cons_val_zero, B2x4.herm_smul_right, B2x4.herm_sub_right, hv1, mul_zero,
          sub_zero, hdl] at this
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hDc
        · exact h
      · have hbl : π.symm c.castSucc ≠ Fin.last r := by
          intro h; have h2 := congrArg π h; rw [π.apply_symm_apply, ha] at h2
          exact hc (Fin.castSucc_injective _ h2)
        obtain ⟨b', hb'⟩ := (cast_or_last (π.symm c.castSucc)).resolve_left hbl
        have hb'0 : b' ≠ b0 := by
          intro h; subst h; rw [← hb', π.apply_symm_apply] at hb; exact Fin.castSucc_ne_last c hb
        have hpx : piX π b' = c := by
          apply Fin.castSucc_injective; rw [piX_spec π b' (hne b' hb'0), ← hb', π.apply_symm_apply]
        have := hvY b'.castSucc
        rw [fvec_cs, hσe] at this
        simp only [hYdef, YA, if_neg hb'0, hpx, B2x4.herm_smul_right] at this
        rcases mul_eq_zero.1 this with h | h
        · exfalso; have := hd' b'.castSucc; simp at h; exact this h
        · exact h
    have hfix : σ *ᵥ v = v := by
      apply sig_fix Y v
      intro i
      rcases i with ((b | b) | i)
      · exact hv4 b
      · exact hv1 b
      · fin_cases i
        · simp [wB, B2x4.herm_smul_right, herm_neg_right, hv2]
        · simpa [wB] using hv3
    have hinv : (m₀ * σ)⁻¹ *ᵥ u = v := by
      have : (m₀ * σ) *ᵥ v = u := by rw [← Matrix.mulVec_mulVec, hfix, hmv]
      rw [← this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hγu, Matrix.one_mulVec]
    rw [hinv, ← hmv, orthoProj_m0_intertwine m₀ hmU hme hms hz hz' μ hμ.ne' hmz hzz0]

  ·
    intro x hx hxz hxν
    apply sig_fix Y x
    intro i
    rcases i with ((b | b) | i)
    · show herm (Hpk k r) x (es k r b) = 0
      rw [herm_es]; exact wb_eI hx b
    · show herm (Hpk k r) x (ee k r b) = 0
      rw [herm_ee]; exact wb_esI hx b
    · fin_cases i
      · simp [wB, B2x4.herm_smul_right, herm_neg_right, hxz]
      · simpa [wB] using hxν
  ·
    intro g hg hge hgz hgν
    apply smat_comm_Hpk _ _ _ g hg
    · intro i; rcases i with ((b | b) | i)
      · exact (hge b).1
      · exact (hge b).2
      · fin_cases i
        · exact hgz
        · exact hgν
    · intro i; rcases i with ((b | b) | i)
      · exact (hge b).2
      · exact (hge b).1
      · fin_cases i
        · simp [wB, Matrix.mulVec_smul, Matrix.mulVec_neg, hgz]
        · simpa [wB] using hgν
    · intro i
      simp only [hYdef]
      rcases i with ((b | b) | i)
      · simp only [YA]; (try split_ifs) <;> simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_neg, (hge _).1, (hge _).2, hgz, hgν]
      · simp only [YA]; (try split_ifs) <;> simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_neg, (hge _).1, (hge _).2, hgz, hgν]
      · fin_cases i <;> simp [YA, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_neg, (hge _).1, (hge _).2, hgz, hgν]

theorem caseB' {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀) (π : Equiv.Perm (Fin (r + 1))) (d0 : Fin (r + 1) → ℂ)
    (hd0 : ∀ a, d0 a ≠ 0) (hB : π (Fin.last r) = Fin.last r)
    (hG : Tz k r S.z * Tz k r S.z' < Complex.normSq (d0 (Fin.last r))) :
    ∃ σ : B.Mat k r, m₀ * σ ∈ B.GV k r ∧ Zhat k r S.z S.z' (m₀ * σ) = C2.monoP π d0 ∧
      Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ (m₀ * σ) ∧ σ ∈ UH (Hpk k r) ∧
      (∀ x, inWb k r x → herm (Hpk k r) x S.z' = 0 → herm (Hpk k r) x ν' = 0 → σ *ᵥ x = x) ∧
      (∀ g ∈ UH (Hpk k r), (∀ a : Fin r, g *ᵥ ee k r a = ee k r a ∧ g *ᵥ es k r a = es k r a) →
        g *ᵥ S.z' = S.z' → g *ᵥ ν' = ν' → σ * g = g * σ) := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := hbase
  have hme : ∀ a : Fin r, m₀ *ᵥ ee k r a = ee k r a := fun a => (hmfix a a.isLt).1
  have hms : ∀ a : Fin r, m₀ *ᵥ es k r a = es k r a := fun a => (hmfix a a.isLt).2
  have hz := S.z_mem
  have hz' := S.z'_mem
  have hT := S.T_pos
  have hT' := S.T'_pos
  set s := Real.sqrt (Tz k r S.z') with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hT'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hs2 : s ^ 2 = Tz k r S.z' := Real.sq_sqrt hT'.le
  have hzz : herm (Hpk k r) S.z' S.z' = -((s : ℂ) ^ 2) := by
    rw [herm_self_alt]; congr 1; exact_mod_cast hs2.symm
  have hzz0 : herm (Hpk k r) S.z' S.z' ≠ 0 := by rw [hzz]; simpa using hs'
  set μ := Real.sqrt (Tz k r S.z' / Tz k r S.z) with hμdef
  have hμ : 0 < μ := Real.sqrt_pos.2 (div_pos hT' hT)
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hμ2 : μ ^ 2 = Tz k r S.z' / Tz k r S.z := Real.sq_sqrt (div_pos hT' hT).le
  set d' : Fin (r + 1) → ℂ := fun b => if π b = Fin.last r then (μ : ℂ) * d0 b else d0 b with hd'def
  have hd' : ∀ b, d' b ≠ 0 := by
    intro b; simp only [hd'def]; split_ifs
    · exact mul_ne_zero hμ' (hd0 b)
    · exact hd0 b
  have hne : ∀ b : Fin r, π b.castSucc ≠ Fin.last r := by
    intro b h; rw [← hB] at h; exact Fin.castSucc_ne_last b (π.injective h)
  have hdl : d' (Fin.last r) = (μ : ℂ) * d0 (Fin.last r) := by simp [hd'def, hB]
  have hdb : ∀ b : Fin r, d' b.castSucc = d0 b.castSucc := by
    intro b; simp only [hd'def]; rw [if_neg (hne b)]

  set N := Complex.normSq (d' (Fin.last r)) with hNdef
  have hN : s ^ 4 < N := by
    rw [hNdef, hdl, Complex.normSq_mul, Complex.normSq_ofReal]
    have : s ^ 4 = μ * μ * (Tz k r S.z * Tz k r S.z') := by
      have e1 : μ * μ = μ ^ 2 := by ring
      rw [e1, hμ2, show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]; field_simp
    rw [this]; exact mul_lt_mul_of_pos_left hG (by positivity)
  have hN0 : 0 < N := lt_trans (by positivity) hN
  set κ := Real.sqrt (1 / s ^ 2 - s ^ 2 / N) with hκdef
  have hκarg : 0 < 1 / s ^ 2 - s ^ 2 / N := by
    rw [sub_pos, div_lt_div_iff₀ hN0 (by positivity)]; nlinarith [hN]
  have hκ0 : 0 < κ := Real.sqrt_pos.2 hκarg
  have hκ2 : κ ^ 2 = 1 / s ^ 2 - s ^ 2 / N := Real.sq_sqrt hκarg.le
  have hκr : κ ^ 2 * s ^ 2 * N = N - s ^ 4 := by rw [hκ2]; field_simp
  have hDD : d' (Fin.last r) * conj (d' (Fin.last r)) = ((N : ℝ) : ℂ) := by rw [hNdef, Complex.mul_conj]
  have hκ : (κ : ℂ) ^ 2 * (s : ℂ) ^ 2 * (d' (Fin.last r) * conj (d' (Fin.last r))) =
      d' (Fin.last r) * conj (d' (Fin.last r)) - (s : ℂ) ^ 4 := by
    rw [hDD]; exact_mod_cast hκr
  set Y := YB π d' S.z' ν' s κ with hYdef
  set σ := smat (Hpk k r) (uB S.z' ν') (wB S.z' ν' s) Y with hσdef
  have hσU : σ ∈ UH (Hpk k r) :=
    sig_UH Y hz' hν hs hzz hνz hνν (YB_gram π d' hz' hν hs hzz hνz hνν hd' κ hκ hB)
      (fun x hx i => YB_perp π d' κ x hx i)
  have hσu : ∀ i, σ *ᵥ uB S.z' ν' i = Y i := sig_u Y hz' hν hs hzz hνz hνν
  have hγ : m₀ * σ ∈ UH (Hpk k r) := mul_UH hmU hσU
  have hzν := herm_zν hνz
  have hσe : ∀ b : Fin r, σ *ᵥ ee k r b = Y (Sum.inl (Sum.inl b)) := fun b => hσu (Sum.inl (Sum.inl b))
  have hσz : σ *ᵥ S.z' = Y (Sum.inr 0) := hσu (Sum.inr 0)
  have hσn : σ *ᵥ ν' = Y (Sum.inr 1) := hσu (Sum.inr 1)
  have hZ : Zhat k r S.z S.z' (m₀ * σ) = C2.monoP π d0 := by
    ext a b
    rw [reduced_matrix_of_stabilizer m₀ σ hmU hme μ hμ.ne' hmz]
    rcases cast_or_last b with hbl | ⟨b', rfl⟩ <;> rcases cast_or_last a with hal | ⟨a', rfl⟩
    · subst hbl hal
      rw [fvec_lastI, fvec_lastI, hσz]
      simp [hYdef, YB, C2.monoP, hB, hdl, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
      field_simp
    · subst hbl
      rw [fvec_lastI, fvec_cs, hσz]
      have h1 : ¬ (a'.castSucc = π (Fin.last r)) := by rw [hB]; exact Fin.castSucc_ne_last a'
      simp [hYdef, YB, C2.monoP, h1, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
    · subst hal
      rw [fvec_lastI, fvec_cs, hσe]
      have h1 : ¬ (Fin.last r = π b'.castSucc) := fun h => hne b' h.symm
      simp [hYdef, YB, C2.monoP, h1, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
    · rw [fvec_cs, fvec_cs, hσe]
      have e : (a'.castSucc = π b'.castSucc) ↔ (piX π b' = a') := by
        rw [← piX_spec π b' (hne b')]; constructor
        · intro h; exact (Fin.castSucc_injective _ h).symm
        · rintro rfl; rfl
      simp [hYdef, YB, C2.monoP, e, hdb b', B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
  have hγu : IsUnit (m₀ * σ).det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hγ
  have hm0u : IsUnit m₀.det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hmU
  have hDl : d0 (Fin.last r) ≠ 0 := hd0 _
  have hDc : conj (d0 (Fin.last r)) ≠ 0 := by simpa using hDl
  refine ⟨σ, hγ, hZ, ⟨?_, ?_, ?_⟩, hσU, ?_, ?_⟩
  ·
    refine ⟨μ * κ, mul_pos hμ hκ0, ?_⟩
    have hcof : Formalism.FourierDecayAlt.D.cofR S (m₀ * σ) =
        ((C2.monoP π d0).det * (d0 (Fin.last r))⁻¹) • (m₀ *ᵥ (σ *ᵥ S.z')) := by
      unfold Formalism.FourierDecayAlt.D.cofR; rw [hZ]
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [monomialMatrix_adj π d0 hd0, if_pos hB, fvec_lastI, Matrix.mulVec_mulVec]
      · intro b _ hbne
        have : π b ≠ Fin.last r := by intro h; rw [← hB] at h; exact hbne (π.injective h)
        rw [monomialMatrix_adj π d0 hd0, if_neg this]; simp
      · simp
    rw [hcof, prW_smul, orthoProj_m0_intertwine m₀ hmU hme hms hz hz' μ hμ.ne' hmz hzz0, hσz]
    simp only [hYdef, YB, Matrix.cons_val_zero]
    rw [prW_smul, prW_sub, prW_smul, prW_perp hν hνz, prW_self hz' hzz0, sub_zero, hZ,
      Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, smul_smul, hdl]
    congr 1
    push_cast; field_simp
  ·
    refine ⟨κ, hκ0, ?_⟩
    have hcof : Formalism.FourierDecayAlt.D.cofL S (m₀ * σ) =
        (conj ((C2.monoP π d0).det * (d0 (Fin.last r))⁻¹)) • S.z := by
      unfold Formalism.FourierDecayAlt.D.cofL; rw [hZ]
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [monomialMatrix_adj π d0 hd0, if_pos hB, fvec_lastI]
      · intro a _ hane; rw [monomialMatrix_adj π d0 hd0, if_neg (by rw [hB]; exact Ne.symm hane)]; simp
      · simp
    set Dp := d' (Fin.last r) with hDpdef
    have hvec : (-(conj Dp / (s : ℂ) ^ 2)) • Y (Sum.inr 0) + ((κ : ℂ) * conj Dp) • Y (Sum.inr 1) = S.z' := by
      simp only [hYdef, YB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [show ∀ (α β p q c1 c2 : ℂ), α • (p • (c1 • ν' - S.z')) + β • (q • (ν' - c2 • S.z')) =
          (α * p * c1 + β * q) • ν' + (-(α * p) - β * q * c2) • S.z' from by intros; module]
      have h0 : -(conj Dp / (s : ℂ) ^ 2) * (Dp / (s : ℂ) ^ 2) * ((κ : ℂ) * (s : ℂ) ^ 2) +
          (κ : ℂ) * conj Dp * (Dp / (s : ℂ) ^ 2) = 0 := by field_simp; ring
      have h1 : -(-(conj Dp / (s : ℂ) ^ 2) * (Dp / (s : ℂ) ^ 2)) - (κ : ℂ) * conj Dp * (Dp / (s : ℂ) ^ 2) * (κ : ℂ) = 1 := by
        field_simp
        first | linear_combination -hκ | linear_combination hκ | linear_combination (-1 : ℂ) * hκ
      rw [h0, h1, zero_smul, zero_add, one_smul]
    set w := (μ : ℂ)⁻¹ • ((-(conj Dp / (s : ℂ) ^ 2)) • S.z' + ((κ : ℂ) * conj Dp) • ν') with hwdef
    have hw : (m₀ * σ) *ᵥ w = S.z := by
      rw [hwdef, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hσz, hσn, hvec, hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    have hinv : (m₀ * σ)⁻¹ *ᵥ S.z = w := by
      rw [← hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hγu, Matrix.one_mulVec]
    rw [hcof, Matrix.mulVec_smul, hinv, hwdef, prW_smul, prW_smul, prW_add, prW_smul, prW_smul, prW_self hz' hzz0,
      prW_perp hν hνz, hZ, smul_zero, zero_add, smul_smul, smul_smul, hdl]
    congr 1
    simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    field_simp
  ·
    intro u hu
    set v := m₀⁻¹ *ᵥ u with hvdef
    have hmv : m₀ *ᵥ v = u := by
      rw [hvdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hm0u, Matrix.one_mulVec]
    have hv1 : ∀ a : Fin r, herm (Hpk k r) v (ee k r a) = 0 := by
      intro a; have := (hu a.castSucc).1; rw [fvec_cs, ← hmv, ← hme a, herm_m0_mulVec_invariant m₀ hmU] at this; exact this
    have hzeq : S.z = (μ : ℂ)⁻¹ • (m₀ *ᵥ S.z') := by rw [hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    have hv2 : herm (Hpk k r) v S.z' = 0 := by
      have := (hu (Fin.last r)).1
      rw [fvec_lastI, ← hmv, hzeq, B2x4.herm_smul_right, herm_m0_mulVec_invariant m₀ hmU] at this
      simpa [hμ'] using this
    have hvY : ∀ a, herm (Hpk k r) v (σ *ᵥ fvec k r S.z' a) = 0 := by
      intro a; have := (hu a).2; rw [← hmv, ← Matrix.mulVec_mulVec, herm_m0_mulVec_invariant m₀ hmU] at this; exact this
    have hv3 : herm (Hpk k r) v ν' = 0 := by
      have := hvY (Fin.last r)
      rw [fvec_lastI, hσz] at this
      simp only [hYdef, YB, Matrix.cons_val_zero, B2x4.herm_smul_right, B2x4.herm_sub_right, hv2, sub_zero] at this
      rcases mul_eq_zero.1 this with h | h
      · exfalso; have := hd' (Fin.last r); simp at h
        rcases h with h | h
        · exact this h
        · exact hs.ne' h
      · rcases mul_eq_zero.1 h with h | h
        · exfalso; simp at h
          rcases h with h | h
          · exact hκ0.ne' h
          · exact hs.ne' h
        · exact h
    have hv4 : ∀ c : Fin r, herm (Hpk k r) v (es k r c) = 0 := by
      intro c
      have hbl : π.symm c.castSucc ≠ Fin.last r := by
        intro h; have h2 := congrArg π h; rw [π.apply_symm_apply, hB] at h2
        exact Fin.castSucc_ne_last c h2
      obtain ⟨b', hb'⟩ := (cast_or_last (π.symm c.castSucc)).resolve_left hbl
      have hpx : piX π b' = c := by
        apply Fin.castSucc_injective; rw [piX_spec π b' (hne b'), ← hb', π.apply_symm_apply]
      have := hvY b'.castSucc
      rw [fvec_cs, hσe] at this
      simp only [hYdef, YB, hpx, B2x4.herm_smul_right] at this
      rcases mul_eq_zero.1 this with h | h
      · exfalso; have := hd' b'.castSucc; simp at h; exact this h
      · exact h
    have hfix : σ *ᵥ v = v := by
      apply sig_fix Y v
      intro i
      rcases i with ((b | b) | i)
      · exact hv4 b
      · exact hv1 b
      · fin_cases i
        · simp [wB, B2x4.herm_smul_right, herm_neg_right, hv2]
        · simpa [wB] using hv3
    have hinv : (m₀ * σ)⁻¹ *ᵥ u = v := by
      have : (m₀ * σ) *ᵥ v = u := by rw [← Matrix.mulVec_mulVec, hfix, hmv]
      rw [← this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hγu, Matrix.one_mulVec]
    rw [hinv, ← hmv, orthoProj_m0_intertwine m₀ hmU hme hms hz hz' μ hμ.ne' hmz hzz0]

  ·
    intro x hx hxz hxν
    apply sig_fix Y x
    intro i
    rcases i with ((b | b) | i)
    · show herm (Hpk k r) x (es k r b) = 0
      rw [herm_es]; exact wb_eI hx b
    · show herm (Hpk k r) x (ee k r b) = 0
      rw [herm_ee]; exact wb_esI hx b
    · fin_cases i
      · simp [wB, B2x4.herm_smul_right, herm_neg_right, hxz]
      · simpa [wB] using hxν
  ·
    intro g hg hge hgz hgν
    apply smat_comm_Hpk _ _ _ g hg
    · intro i; rcases i with ((b | b) | i)
      · exact (hge b).1
      · exact (hge b).2
      · fin_cases i
        · exact hgz
        · exact hgν
    · intro i; rcases i with ((b | b) | i)
      · exact (hge b).2
      · exact (hge b).1
      · fin_cases i
        · simp [wB, Matrix.mulVec_smul, Matrix.mulVec_neg, hgz]
        · simpa [wB] using hgν
    · intro i
      simp only [hYdef]
      rcases i with ((b | b) | i)
      · simp only [YB]; (try split_ifs) <;> simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_neg, (hge _).1, (hge _).2, hgz, hgν]
      · simp only [YB]; (try split_ifs) <;> simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_neg, (hge _).1, (hge _).2, hgz, hgν]
      · fin_cases i <;> simp [YB, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_neg, (hge _).1, (hge _).2, hgz, hgν]

end explicit2

section frameHelpers
open Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate
variable {k r : ℕ}

theorem Wb_N {n : B.Mat k r} (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ a : Fin r, v (esI k r a) = 0) : Wb (n *ᵥ v) = Wb v := by
  ext i
  simp only [Wb]
  split_ifs with hi
  · simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · rw [hn.2.2 i i (by omega) (by omega) (by omega), if_pos rfl, one_mul]
    · intro j _ hji
      by_cases hj1 : j.val < r
      · have e : eI k r ⟨j.val, hj1⟩ = j := by ext; simp [eI]
        have := hn.2.1 ⟨j.val, hj1⟩ i (by simp; omega)
        rw [e, if_neg (Ne.symm hji)] at this
        rw [this, zero_mul]
      · by_cases hj2 : j.val ≤ r + k
        · rw [hn.2.2 i j (by omega) hj2 (by omega), if_neg (Ne.symm hji), zero_mul]
        · have hlt : 2 * r + k - j.val < r := by omega
          have e : esI k r ⟨2 * r + k - j.val, hlt⟩ = j := by ext; simp [esI]; omega
          have := hv ⟨2 * r + k - j.val, hlt⟩
          rw [e] at this
          rw [this, mul_zero]
    · simp
  · rfl

theorem prW_N {z : Fin (2 * r + k + 1) → ℂ} {n : B.Mat k r} (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ a : Fin r, v (esI k r a) = 0) : D.prW k r z (n *ᵥ v) = D.prW k r z v := by
  rw [prW_eq, prW_eq, Wb_N hn hv]

theorem free_of_fix {h : B.Mat k r} (hU : h ∈ UH (Hpk k r)) (hme : ∀ a : Fin r, h *ᵥ ee k r a = ee k r a)
    {v : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) (a : Fin r) : (h *ᵥ v) (esI k r a) = 0 := by
  rw [← herm_ee (h *ᵥ v) a, ← hme a, herm_m0_mulVec_invariant h hU, herm_ee, hv]

theorem uw_parts {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) :
    h ∈ UH (Hpk k r) ∧ (∀ a : Fin r, h *ᵥ ee k r a = ee k r a) ∧ (∀ a : Fin r, h *ᵥ es k r a = es k r a) ∧
      h *ᵥ z = z :=
  ⟨hh.1, fun a => (hh.2.1 a).1, fun a => (hh.2.1 a).2, hh.2.2⟩

theorem prW_sinv {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hzz : herm (Hpk k r) z z ≠ 0)
    {h n : B.Mat k r} (hh : h ∈ UWset k r z) (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ a : Fin r, v (esI k r a) = 0) : D.prW k r z ((h * n)⁻¹ *ᵥ v) = h⁻¹ *ᵥ D.prW k r z v := by
  obtain ⟨hU, hme, hms, hfz⟩ := uw_parts (WeylGroupFacts.uw_inv hh)
  rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, prW_N (WeylGroupFacts.mem_n_inv hn) (free_of_fix hU hme hv)]
  exact orthoProj_m0_intertwine h⁻¹ hU hme hms hz hz 1 one_ne_zero (by rw [hfz]; simp) hzz v

theorem unit_c {x y : Fin (2 * r + k + 1) → ℂ} (hx : herm (Hpk k r) x x = 1) (c : ℝ) (hc : 0 < c)
    (hy : herm (Hpk k r) y y = 1) (h : y = (c : ℂ) • x) : y = x := by
  subst h
  rw [B2x4.herm_smul_left, B2x4.herm_smul_right, hx, mul_one] at hy
  have : (c : ℂ) * (c : ℂ) = 1 := by simpa using hy
  have hc1 : c * c = 1 := by exact_mod_cast this
  have : c = 1 := by nlinarith
  subst this; simp

end frameHelpers

section cof
open Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)

theorem cofR_conj {sA sB γ : B.Mat k r} (hfB : ∀ b, sB *ᵥ fvec k r S.z' b = fvec k r S.z' b)
    (hZ1 : Zhat k r S.z S.z' (sA⁻¹ * γ * sB) = Zhat k r S.z S.z' γ) :
    Formalism.FourierDecayAlt.D.cofR S (sA⁻¹ * γ * sB) = sA⁻¹ *ᵥ Formalism.FourierDecayAlt.D.cofR S γ := by
  unfold Formalism.FourierDecayAlt.D.cofR
  rw [hZ1, Matrix.mulVec_sum]
  apply Finset.sum_congr rfl; intro b _
  rw [Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfB b]

theorem cofL_eq {γ1 γ : B.Mat k r} (hZ1 : Zhat k r S.z S.z' γ1 = Zhat k r S.z S.z' γ) :
    Formalism.FourierDecayAlt.D.cofL S γ1 = Formalism.FourierDecayAlt.D.cofL S γ := by
  unfold Formalism.FourierDecayAlt.D.cofL; rw [hZ1]

theorem cofR_free (γ : B.Mat k r) (a : Fin r) : Formalism.FourierDecayAlt.D.cofR S γ (esI k r a) = 0 := by
  rw [← herm_ee (Formalism.FourierDecayAlt.D.cofR S γ) a]
  unfold Formalism.FourierDecayAlt.D.cofR
  rw [herm_sum_left]
  simp only [B2x4.herm_smul_left]
  have h := congrFun (congrFun (Matrix.mul_adjugate (Zhat k r S.z S.z' γ)) a.castSucc) (Fin.last r)
  rw [Matrix.mul_apply] at h
  simp only [Matrix.smul_apply, Matrix.one_apply_ne (Fin.castSucc_ne_last a), smul_zero] at h
  rw [← h]
  apply Finset.sum_congr rfl; intro b _
  rw [mul_comm]; congr 1
  simp only [Zhat, fvec_cs]

theorem cofL_free {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) (a : Fin r) :
    (γ⁻¹ *ᵥ Formalism.FourierDecayAlt.D.cofL S γ) (esI k r a) = 0 := by
  have hu := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγ
  have hinv : γ⁻¹ ∈ UH (Hpk k r) := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).inv_mem _ hγ
  rw [← herm_ee (γ⁻¹ *ᵥ Formalism.FourierDecayAlt.D.cofL S γ) a]
  have e : ee k r a = γ⁻¹ *ᵥ (γ *ᵥ ee k r a) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  rw [e, herm_m0_mulVec_invariant _ hinv]
  unfold Formalism.FourierDecayAlt.D.cofL
  rw [herm_sum_left]
  simp only [B2x4.herm_smul_left]
  have h := congrFun (congrFun (Matrix.adjugate_mul (Zhat k r S.z S.z' γ)) (Fin.last r)) a.castSucc
  rw [Matrix.mul_apply] at h
  simp only [Matrix.smul_apply, Matrix.one_apply_ne (Fin.castSucc_ne_last a).symm, smul_zero] at h
  have h2 := congrArg (starRingEnd ℂ) h
  rw [map_sum, map_zero] at h2
  rw [← h2]
  apply Finset.sum_congr rfl; intro c _
  rw [map_mul]; congr 1
  rw [herm_symm']
  simp only [Zhat, fvec_cs]
  rfl

end cof

section frameFix
open Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)

theorem ext_basis {z' ν' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (hν : inWb k r ν')
    (hzz : herm (Hpk k r) z' z' ≠ 0) (hνz : herm (Hpk k r) ν' z' = 0) (hνν : herm (Hpk k r) ν' ν' = 1)
    {M N : B.Mat k r} (he : ∀ a, M *ᵥ ee k r a = N *ᵥ ee k r a) (hs : ∀ a, M *ᵥ es k r a = N *ᵥ es k r a)
    (hz : M *ᵥ z' = N *ᵥ z') (hn : M *ᵥ ν' = N *ᵥ ν')
    (hw : ∀ w, inWb k r w → herm (Hpk k r) w z' = 0 → herm (Hpk k r) w ν' = 0 → M *ᵥ w = N *ᵥ w) : M = N := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_apply]
  have hW : inWb k r (Wb x) := by intro i hi; simp only [Wb]; rw [if_neg (by omega)]
  set y := Wb x with hy
  set α := herm (Hpk k r) y z' / herm (Hpk k r) z' z' with hα
  set β := herm (Hpk k r) y ν' with hβ
  set w := y - α • z' - β • ν' with hwdef
  have hzν := herm_zν hνz
  have hw1 : inWb k r w := by
    intro i hi; simp only [hwdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hW i hi, hz' i hi, hν i hi]; ring
  have hw2 : herm (Hpk k r) w z' = 0 := by
    simp only [hwdef, B2x4.herm_sub_left, B2x4.herm_smul_left, hνz, hα]
    field_simp; ring
  have hw3 : herm (Hpk k r) w ν' = 0 := by
    simp only [hwdef, B2x4.herm_sub_left, B2x4.herm_smul_left, hzν, hνν, hβ]; ring
  have hyd : y = α • z' + β • ν' + w := by simp only [hwdef]; abel
  rw [decomp x, ← hy, hyd]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, he, hs, hz, hn, hw w hw1 hw2 hw3]

theorem frame_fix (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀)
    {σ : B.Mat k r} (hσU : σ ∈ UH (Hpk k r))
    (hE3 : ∀ x, inWb k r x → herm (Hpk k r) x S.z' = 0 → herm (Hpk k r) x ν' = 0 → σ *ᵥ x = x)
    (hE2 : ∀ g ∈ UH (Hpk k r), (∀ a : Fin r, g *ᵥ ee k r a = ee k r a ∧ g *ᵥ es k r a = es k r a) →
        g *ᵥ S.z' = S.z' → g *ᵥ ν' = ν' → σ * g = g * σ)
    (hγe : m₀ * σ ∈ B.GV k r) (hDe : Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ (m₀ * σ))
    (hdet : (Zhat k r S.z S.z' (m₀ * σ)).det ≠ 0)
    {hA nA hB nB : B.Mat k r} (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r)
    (hfA : ∀ b, nA *ᵥ fvec k r S.z b = fvec k r S.z b)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) (hfB : ∀ b, nB *ᵥ fvec k r S.z' b = fvec k r S.z' b)
    (hD1 : Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ ((hA * nA)⁻¹ * (m₀ * σ) * (hB * nB))) :
    hA⁻¹ * (m₀ * σ) * hB = m₀ * σ := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := hbase
  have hme : ∀ a : Fin r, m₀ *ᵥ ee k r a = ee k r a := fun a => (hmfix a a.isLt).1
  have hms : ∀ a : Fin r, m₀ *ᵥ es k r a = es k r a := fun a => (hmfix a a.isLt).2
  have hz := S.z_mem
  have hz' := S.z'_mem
  have hzz : herm (Hpk k r) S.z S.z ≠ 0 := by
    rw [herm_self_alt]; simp only [ne_eq, neg_eq_zero, Complex.ofReal_eq_zero]; exact S.T_pos.ne'
  have hz'z' : herm (Hpk k r) S.z' S.z' ≠ 0 := by
    rw [herm_self_alt]; simp only [ne_eq, neg_eq_zero, Complex.ofReal_eq_zero]; exact S.T'_pos.ne'
  set μ := Real.sqrt (Tz k r S.z' / Tz k r S.z) with hμdef
  have hμ : 0 < μ := Real.sqrt_pos.2 (div_pos S.T'_pos S.T_pos)
  set γe := m₀ * σ with hγedef
  have hZ1 := zhat_conj S hhA hnA hfA hhB hnB hfB γe
  have uA := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1
  have uB := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhB.1
  have vA := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N hnA
  have vB := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N hnB
  have sA : IsUnit (hA * nA).det := by rw [Matrix.det_mul]; exact uA.mul vA
  have sB : IsUnit (hB * nB).det := by rw [Matrix.det_mul]; exact uB.mul vB
  have uγ := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγe
  have um := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hmU
  have hsfA := mul_fix hhA hfA
  have hsfB := mul_fix hhB hfB
  obtain ⟨hAiU, hAie, hAis, hAiz⟩ := uw_parts (WeylGroupFacts.uw_inv hhA)
  obtain ⟨hBiU, hBie, hBis, hBiz⟩ := uw_parts (WeylGroupFacts.uw_inv hhB)
  have hinv : ((hA * nA)⁻¹ * γe * (hB * nB))⁻¹ = (hB * nB)⁻¹ * γe⁻¹ * (hA * nA) := by
    rw [Matrix.mul_inv_rev ((hA * nA)⁻¹ * γe) (hB * nB), Matrix.mul_inv_rev (hA * nA)⁻¹ γe,
      Matrix.nonsing_inv_nonsing_inv _ sA]
    simp only [Matrix.mul_assoc]

  have ha : hA⁻¹ *ᵥ (m₀ *ᵥ ν') = m₀ *ᵥ ν' := by
    obtain ⟨a1, ha1, h1⟩ := hD1.1
    obtain ⟨ae, hae, he⟩ := hDe.1
    rw [cofR_conj S hsfB hZ1, prW_sinv hz hzz hhA hnA (cofR_free S γe), he, hZ1, Matrix.mulVec_smul] at h1
    have hne : ((ae : ℂ) * (Zhat k r S.z S.z' γe).det) ≠ 0 := mul_ne_zero (by exact_mod_cast hae.ne') hdet
    have hc : hA⁻¹ *ᵥ (m₀ *ᵥ ν') = ((a1 / ae : ℝ) : ℂ) • (m₀ *ᵥ ν') := by
      have := congrArg (fun v => ((ae : ℂ) * (Zhat k r S.z S.z' γe).det)⁻¹ • v) h1
      simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
      rw [this]; congr 1; push_cast; field_simp
    exact unit_c (by rw [herm_m0_mulVec_invariant m₀ hmU, hνν]) _ (div_pos ha1 hae)
      (by rw [herm_m0_mulVec_invariant _ hAiU, herm_m0_mulVec_invariant m₀ hmU, hνν]) hc

  have hb : hB⁻¹ *ᵥ ν' = ν' := by
    obtain ⟨a1, ha1, h1⟩ := hD1.2.1
    obtain ⟨ae, hae, he⟩ := hDe.2.1
    have hcl : (hA * nA) *ᵥ Formalism.FourierDecayAlt.D.cofL S γe = Formalism.FourierDecayAlt.D.cofL S γe := by
      unfold Formalism.FourierDecayAlt.D.cofL; rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, hsfA]
    rw [cofL_eq S hZ1, hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcl,
      prW_sinv hz' hz'z' hhB hnB (cofL_free S hγe), he, hZ1, Matrix.mulVec_smul] at h1
    have hcd : conj (Zhat k r S.z S.z' γe).det ≠ 0 := by simpa using hdet
    have hne : ((ae : ℂ) * conj (Zhat k r S.z S.z' γe).det) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hae.ne') hcd
    have hc : hB⁻¹ *ᵥ ν' = ((a1 / ae : ℝ) : ℂ) • ν' := by
      have := congrArg (fun v => ((ae : ℂ) * conj (Zhat k r S.z S.z' γe).det)⁻¹ • v) h1
      simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
      rw [this]; congr 1; push_cast; field_simp
    exact unit_c hνν _ (div_pos ha1 hae) (by rw [herm_m0_mulVec_invariant _ hBiU, hνν]) hc

  have hc : ∀ w, inWb k r w → herm (Hpk k r) w S.z' = 0 → herm (Hpk k r) w ν' = 0 →
      hA⁻¹ *ᵥ (m₀ *ᵥ w) = m₀ *ᵥ (hB⁻¹ *ᵥ w) := by
    intro w hw hwz hwν
    have hσw := hE3 w hw hwz hwν
    have hγw : γe⁻¹ *ᵥ (m₀ *ᵥ w) = w := by
      have : γe *ᵥ w = m₀ *ᵥ w := by rw [hγedef, ← Matrix.mulVec_mulVec, hσw]
      rw [← this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uγ, Matrix.one_mulVec]
    have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
    have hsAiU : (hA * nA)⁻¹ ∈ UH (Hpk k r) := hG.inv_mem _ (hG.mul_mem _ hhA.1 _ hnA.1)
    have hfAi : ∀ b, fvec k r S.z b = (hA * nA)⁻¹ *ᵥ fvec k r S.z b := by
      intro b; conv_rhs => rw [← hsfA b]
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ sA, Matrix.one_mulVec]
    have hzeq : S.z = ((μ : ℂ))⁻¹ • (m₀ *ᵥ S.z') := by
      have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
      rw [hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    have hu : ∀ a, herm (Hpk k r) ((hA * nA)⁻¹ *ᵥ (m₀ *ᵥ w)) (fvec k r S.z a) = 0 ∧
        herm (Hpk k r) ((hA * nA)⁻¹ *ᵥ (m₀ *ᵥ w)) (((hA * nA)⁻¹ * γe * (hB * nB)) *ᵥ fvec k r S.z' a) = 0 := by
      intro a
      constructor
      · rw [hfAi a, herm_m0_mulVec_invariant _ hsAiU]
        rcases cast_or_last a with ha' | ⟨a', rfl⟩
        · subst ha'; rw [fvec_lastI, hzeq, B2x4.herm_smul_right, herm_m0_mulVec_invariant m₀ hmU, hwz, mul_zero]
        · rw [fvec_cs, ← hme a', herm_m0_mulVec_invariant m₀ hmU, herm_ee, wb_esI hw]
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hsfB a, herm_m0_mulVec_invariant _ hsAiU, hγedef,
          ← Matrix.mulVec_mulVec, herm_m0_mulVec_invariant m₀ hmU, ← hσw, herm_m0_mulVec_invariant σ hσU]
        rcases cast_or_last a with ha' | ⟨a', rfl⟩
        · subst ha'; rw [fvec_lastI, hwz]
        · rw [fvec_cs, herm_ee, wb_esI hw]
    have h3 := hD1.2.2 _ hu
    have hm0w : ∀ a : Fin r, (m₀ *ᵥ w) (esI k r a) = 0 := free_of_fix hmU hme (fun a => wb_esI hw a)
    rw [prW_sinv hz hzz hhA hnA hm0w, orthoProj_m0_intertwine m₀ hmU hme hms hz hz' μ hμ.ne' hmz hz'z' w, prW_perp hw hwz] at h3
    have hγ1u : ((hA * nA)⁻¹ * γe * (hB * nB))⁻¹ *ᵥ ((hA * nA)⁻¹ *ᵥ (m₀ *ᵥ w)) = (hB * nB)⁻¹ *ᵥ w := by
      rw [hinv, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ sA, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, hγw]
    rw [hγ1u, prW_sinv hz' hz'z' hhB hnB (fun a => wb_esI hw a), prW_perp hw hwz] at h3
    exact h3

  have hd : hA⁻¹ * m₀ = m₀ * hB⁻¹ := by
    apply ext_basis hz' hν hz'z' hνz hνν
    · intro a; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hme, hAie, hBie, hme]
    · intro a; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hms, hAis, hBis, hms]
    · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmz, hBiz, hmz, Matrix.mulVec_smul, hAiz]
    · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]
    · intro w hw hwz hwν; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; exact hc w hw hwz hwν
  have hBν : hB *ᵥ ν' = ν' := by
    conv_lhs => rw [← hb]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ uB, Matrix.one_mulVec]
  have hcomm := hE2 hB hhB.1 (fun a => hhB.2.1 a) hhB.2.2 hBν
  calc hA⁻¹ * (m₀ * σ) * hB = (hA⁻¹ * m₀) * (σ * hB) := by simp only [Matrix.mul_assoc]
    _ = (m₀ * hB⁻¹) * (hB * σ) := by rw [hd, hcomm]
    _ = m₀ * (hB⁻¹ * hB) * σ := by simp only [Matrix.mul_assoc]
    _ = m₀ * σ := by rw [Matrix.nonsing_inv_mul _ uB, Matrix.mul_one]

end frameFix

section final
open Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)

theorem exE (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀) (p : C.LPt)
    (hp : Formalism.FourierDecayAlt.D.IsLocPt p (r + 1)) (hG : 0 < Formalism.FourierDecayAlt.D.ptG (Tz k r S.z * Tz k r S.z') r p) :
    ∃ σ : B.Mat k r, m₀ * σ ∈ B.GV k r ∧ Zhat k r S.z S.z' (m₀ * σ) = Formalism.FourierDecayAlt.D.ptMatN p (r + 1) ∧
      Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ (m₀ * σ) ∧ σ ∈ UH (Hpk k r) ∧
      (∀ x, inWb k r x → herm (Hpk k r) x S.z' = 0 → herm (Hpk k r) x ν' = 0 → σ *ᵥ x = x) ∧
      (∀ g ∈ UH (Hpk k r), (∀ a : Fin r, g *ᵥ ee k r a = ee k r a ∧ g *ᵥ es k r a = es k r a) →
        g *ᵥ S.z' = S.z' → g *ᵥ ν' = ν' → σ * g = g * σ) := by
  obtain ⟨π, d0, hd0, hP⟩ := Formalism.FourierDecayAlt.P.Dx2.ptMatN_mono p (r + 1) hp.2 hp.1
  by_cases hB : π (Fin.last r) = Fin.last r
  · have hsub : Formalism.FourierDecayAlt.D.ptMatN p r = (C2.monoP π d0).submatrix Fin.castSucc Fin.castSucc := by
      rw [← hP]; ext a b; rfl
    have hG' : Tz k r S.z * Tz k r S.z' < Complex.normSq (d0 (Fin.last r)) := by
      unfold Formalism.FourierDecayAlt.D.ptG at hG
      rw [hP, hsub, Formalism.FourierDecayAlt.P.Dx2.det_monomialMatrix_last π d0 hB, Complex.normSq_mul] at hG
      have h : 0 < Complex.normSq ((C2.monoP π d0).submatrix Fin.castSucc Fin.castSucc).det *
          (Complex.normSq (d0 (Fin.last r)) - Tz k r S.z * Tz k r S.z') := by linarith
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with h1 | h1
      · linarith [h1.2]
      · exact absurd h1.1 (not_lt.2 (Complex.normSq_nonneg _))
    obtain ⟨σ, h1, h2, h3, h4, h5, h6⟩ := caseB' S ν' m₀ hbase π d0 hd0 hB hG'
    exact ⟨σ, h1, h2.trans hP.symm, h3, h4, h5, h6⟩
  · obtain ⟨a0, ha⟩ := (cast_or_last (π (Fin.last r))).resolve_left hB
    have hbl : π.symm (Fin.last r) ≠ Fin.last r := by
      intro h; apply hB; conv_lhs => rw [← h]; rw [π.apply_symm_apply]
    obtain ⟨b0, hb0⟩ := (cast_or_last (π.symm (Fin.last r))).resolve_left hbl
    have hb : π b0.castSucc = Fin.last r := by rw [← hb0, π.apply_symm_apply]
    obtain ⟨σ, h1, h2, h3, h4, h5, h6⟩ := caseA' S ν' m₀ hbase π d0 hd0 a0 b0 ha hb
    exact ⟨σ, h1, h2.trans hP.symm, h3, h4, h5, h6⟩

theorem stabilizer_decomp_unitary_mul_unipotent {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {s : B.Mat k r} (hs : s ∈ C2.CurvatureSupportSet k r z) :
    ∃ h ∈ UWset k r z, ∃ n ∈ Nset k r, (∀ b, n *ᵥ fvec k r z b = fvec k r z b) ∧ s = h * n := by
  obtain ⟨⟨h, hh, n, hn, rfl⟩, hu⟩ := hs
  refine ⟨h, hh, n, hn, ?_, rfl⟩
  have hsf : ∀ b, (h * n) *ᵥ fvec k r z b = fvec k r z b := by
    intro b
    rw [(((Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz).1 (h * n) ⟨h, hh, n, hn, rfl⟩).1 b), hu]
    simp [Matrix.one_apply]
  intro b
  have uh := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hh.1
  have e : n = h⁻¹ * (h * n) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uh, Matrix.one_mul]
  rw [e, ← Matrix.mulVec_mulVec, hsf b]
  obtain ⟨_, _, _, hfz⟩ := uw_parts (WeylGroupFacts.uw_inv hh)
  exact UW_fix (WeylGroupFacts.uw_inv hh) b

theorem orbJ_rep (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (p : C.LPt) (hp : Formalism.FourierDecayAlt.D.IsLocPt p (r + 1))
    (hG : 0 < Formalism.FourierDecayAlt.D.ptG (Tz k r S.z * Tz k r S.z') r p) {σ : B.Mat k r}
    (hE : m₀ * σ ∈ B.GV k r ∧ Zhat k r S.z S.z' (m₀ * σ) = Formalism.FourierDecayAlt.D.ptMatN p (r + 1) ∧
      Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ (m₀ * σ) ∧ σ ∈ UH (Hpk k r) ∧
      (∀ x, inWb k r x → herm (Hpk k r) x S.z' = 0 → herm (Hpk k r) x ν' = 0 → σ *ᵥ x = x) ∧
      (∀ g ∈ UH (Hpk k r), (∀ a : Fin r, g *ᵥ ee k r a = ee k r a ∧ g *ᵥ es k r a = es k r a) →
        g *ᵥ S.z' = S.z' → g *ᵥ ν' = ν' → σ * g = g * σ))
    {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) (hZ : Zhat k r S.z S.z' γ = Formalism.FourierDecayAlt.D.ptMatN p (r + 1))
    (hD : Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ γ) :
    Formalism.FourierDecayAlt.D.orbJ S γ (Formalism.FourierDecayAlt.D.muR S γ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F =
      Formalism.FourierDecayAlt.D.orbJ S (m₀ * σ) (Formalism.FourierDecayAlt.D.muR S (m₀ * σ) (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F := by
  obtain ⟨hγe, hZe, hDe, hσU, hE3, hE2⟩ := hE
  have hpos : 0 < Gf k r S.z S.z' (m₀ * σ) := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec k r S.z S.z' p _ hp hZe]; exact hG
  have hdet := Formalism.FourierDecayAlt.P.determinant_nonzero k r S.z S.z' (std_vector_z S) (std_vector_z_prime S) _ hpos
  obtain ⟨s, hs, s', hs', hγs⟩ := Formalism.FourierDecayAlt.P.fibre_orbit_description k r S.z S.z'
    ⟨S.k_pos, std_vector_z S, std_vector_z_prime S⟩ _ hγe γ hγ hpos (hZe.trans hZ.symm)
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := stabilizer_decomp_unitary_mul_unipotent (std_vector_z S) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := stabilizer_decomp_unitary_mul_unipotent (std_vector_z_prime S) hs'
  subst hγs
  have hfix := frame_fix S ν' m₀ hbase hσU hE3 hE2 hγe hDe hdet hhA hnA hfA hhB hnB hfB hD
  have h1 := orbJ_pt S p hp hγe hZe hpos hhA hnA hfA hhB hnB hfB F
  have h2 := orbJ_pt S p hp hγe hZe hpos hhA WeylGroupFacts.mem_n_one (fun b => Matrix.one_mulVec _) hhB WeylGroupFacts.mem_n_one
    (fun b => Matrix.one_mulVec _) F
  rw [Matrix.mul_one, Matrix.mul_one, hfix] at h2
  rw [← h2] at h1
  have := congrArg (CinL S hA⁻¹ hB⁻¹) h1
  rwa [CinL_inv S hhA hhB, CinL_inv S hhA hhB] at this

end final

end Formalism.FourierDecayAlt.P.Dx2.VV

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.Dx2.VV in
theorem isotropic_vectors_linear_indep : Formalism.FourierDecayAlt.D.VecVIndep := by
  intro k r Wp Wq _ _ _ _ S ν' m₀ F p hp γ hbase hG hγ hZ hD
  obtain ⟨σ, hE⟩ := exE S ν' m₀ hbase p hp hG
  unfold Formalism.FourierDecayAlt.D.vecV
  have h' : ∃ γ ∈ B.GV k r, Zhat k r S.z S.z' γ = Formalism.FourierDecayAlt.D.ptMatN p (r + 1) ∧ Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ γ :=
    ⟨γ, hγ, hZ, hD⟩
  rw [dif_pos ⟨hp, hG⟩, dif_pos h']
  obtain ⟨hc1, hc2, hc3⟩ := h'.choose_spec
  rw [orbJ_rep S ν' m₀ hbase F p hp hG hE hc1 hc2 hc3, orbJ_rep S ν' m₀ hbase F p hp hG hE hγ hZ hD]

end Formalism.FourierDecayAlt.P

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.Dx2.SL

theorem curry_mp (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : (volume : Measure (ι × κ → ℂ)) = (volume : Measure (ι → κ → ℂ)).map (MeasurableEquiv.curry ι κ ℂ).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry ι κ ℂ).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

variable {ph n : ℕ}

def sigP (σ : Equiv.Perm (Fin ph)) : Equiv.Perm (Fin (ph + (n + 1))) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr σ Fin.revPerm)).trans finSumFinEquiv

theorem blockPerm_castAdd (σ : Equiv.Perm (Fin ph)) (i : Fin ph) :
    sigP (n := n) σ (Fin.castAdd (n + 1) i) = Fin.castAdd (n + 1) (σ i) := by
  simp [sigP]

theorem blockPerm_natAdd (σ : Equiv.Perm (Fin ph)) (i : Fin (n + 1)) :
    sigP σ (Fin.natAdd ph i) = Fin.natAdd ph (Fin.rev i) := by
  simp [sigP]

theorem blockPerm_symm_castAdd (σ : Equiv.Perm (Fin ph)) (i : Fin ph) :
    (sigP (n := n) σ).symm (Fin.castAdd (n + 1) i) = Fin.castAdd (n + 1) (σ.symm i) := by
  rw [Equiv.symm_apply_eq, blockPerm_castAdd, Equiv.apply_symm_apply]

theorem blockPerm_symm_natAdd (σ : Equiv.Perm (Fin ph)) (i : Fin (n + 1)) :
    (sigP σ).symm (Fin.natAdd ph i) = Fin.natAdd ph (Fin.rev i) := by
  rw [Equiv.symm_apply_eq, blockPerm_natAdd, Fin.rev_rev]

def dP (d : Fin ph → ℂ) (t : ℂ) : Fin (ph + (n + 1)) → ℂ := Fin.addCases d (fun _ => t)

def lwIn (σ : Equiv.Perm (Fin ph)) : U.LW σ ⊕ (Fin (n + 1) × Fin ph) → U.LW (sigP (n := n) σ)
  | Sum.inl q => ⟨(Fin.castAdd (n + 1) q.1.1, Fin.castAdd (n + 1) q.1.2), by
      refine ⟨q.2.1, ?_⟩
      show (sigP (n := n) σ).symm (Fin.castAdd (n + 1) q.1.2) < (sigP σ).symm (Fin.castAdd (n + 1) q.1.1)
      rw [blockPerm_symm_castAdd, blockPerm_symm_castAdd]; exact q.2.2⟩
  | Sum.inr (i, j) => ⟨(Fin.natAdd ph i, Fin.castAdd (n + 1) j), by
      refine ⟨show j.val < ph + i.val by omega, ?_⟩
      show (sigP (n := n) σ).symm (Fin.castAdd (n + 1) j) < (sigP σ).symm (Fin.natAdd ph i)
      rw [blockPerm_symm_castAdd, blockPerm_symm_natAdd]
      show (σ.symm j).val < ph + (Fin.rev i).val
      have := (σ.symm j).isLt; omega⟩

theorem lwIn_bij (σ : Equiv.Perm (Fin ph)) : Function.Bijective (lwIn (n := n) σ) := by
  constructor
  · rintro (⟨⟨a, b⟩, h⟩ | ⟨i, j⟩) (⟨⟨a', b'⟩, h'⟩ | ⟨i', j'⟩) e <;>
      simp only [lwIn, Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at e
    · have e1 : a = a' := Fin.ext e.1
      have e2 : b = b' := Fin.ext e.2
      subst e1 e2; rfl
    · omega
    · omega
    · have e1 : i = i' := Fin.ext (by omega)
      have e2 : j = j' := Fin.ext e.2
      subst e1 e2; rfl
  · rintro ⟨⟨a, b⟩, hab, hs⟩
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left j =>
        rw [blockPerm_symm_castAdd, blockPerm_symm_castAdd] at hs
        exact ⟨Sum.inl ⟨(i, j), hab, hs⟩, rfl⟩
      | right j => exfalso; rw [Fin.lt_def] at hab; simp only [Fin.val_natAdd, Fin.val_castAdd] at hab; omega
    | right i =>
      induction b using Fin.addCases with
      | left j => exact ⟨Sum.inr (i, j), rfl⟩
      | right j =>
        exfalso
        rw [blockPerm_symm_natAdd, blockPerm_symm_natAdd, Fin.lt_def] at hs
        rw [Fin.lt_def] at hab
        simp only [Fin.val_natAdd, Fin.val_rev] at hs hab; omega

def lwEquiv (σ : Equiv.Perm (Fin ph)) : U.LW (sigP (n := n) σ) ≃ U.LW σ ⊕ (Fin (n + 1) × Fin ph) :=
  (Equiv.ofBijective _ (lwIn_bij σ)).symm

def utIn : (G.UT ph ⊕ (Fin ph × Fin (n + 1))) ⊕ G.UT (n + 1) → G.UT (ph + (n + 1))
  | Sum.inl (Sum.inl q) => ⟨(Fin.castAdd (n + 1) q.1.1, Fin.castAdd (n + 1) q.1.2), by
      exact q.2⟩
  | Sum.inl (Sum.inr (i, j)) => ⟨(Fin.castAdd (n + 1) i, Fin.natAdd ph j), show i.val < ph + j.val by omega⟩
  | Sum.inr q => ⟨(Fin.natAdd ph q.1.1, Fin.natAdd ph q.1.2), show ph + q.1.1.val < ph + q.1.2.val by
      have : q.1.1.val < q.1.2.val := q.2; omega⟩

theorem utIn_bij : Function.Bijective (utIn (ph := ph) (n := n)) := by
  constructor
  · rintro ((⟨⟨a, b⟩, h⟩ | ⟨i, j⟩) | ⟨⟨a, b⟩, h⟩) ((⟨⟨a', b'⟩, h'⟩ | ⟨i', j'⟩) | ⟨⟨a', b'⟩, h'⟩) e <;>
      simp only [utIn, Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at e
    all_goals first
      | omega
      | (have e1 : a = a' := Fin.ext (by omega)
         have e2 : b = b' := Fin.ext (by omega)
         subst e1 e2; rfl)
      | (have e1 : i = i' := Fin.ext (by omega)
         have e2 : j = j' := Fin.ext (by omega)
         subst e1 e2; rfl)
  · rintro ⟨⟨a, b⟩, hab⟩
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left j => exact ⟨Sum.inl (Sum.inl ⟨(i, j), hab⟩), rfl⟩
      | right j => exact ⟨Sum.inl (Sum.inr (i, j)), rfl⟩
    | right i =>
      induction b using Fin.addCases with
      | left j => exfalso; rw [Fin.lt_def] at hab; simp only [Fin.val_natAdd, Fin.val_castAdd] at hab; omega
      | right j => exact ⟨Sum.inr ⟨(i, j), show i.val < j.val by have : ph + i.val < ph + j.val := hab; omega⟩, rfl⟩

def utEquiv : G.UT (ph + (n + 1)) ≃ (G.UT ph ⊕ (Fin ph × Fin (n + 1))) ⊕ G.UT (n + 1) :=
  (Equiv.ofBijective _ utIn_bij).symm

section blocks
variable {p s : ℕ}

theorem b_cc (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) (i j : Fin p) : U.blk2 A B C D (Fin.castAdd s i) (Fin.castAdd s j) = A i j := by
  simp [U.blk2]
theorem b_cn (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) (i : Fin p) (j : Fin s) : U.blk2 A B C D (Fin.castAdd s i) (Fin.natAdd p j) = B i j := by
  simp [U.blk2]
theorem b_nc (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) (i : Fin s) (j : Fin p) : U.blk2 A B C D (Fin.natAdd p i) (Fin.castAdd s j) = C i j := by
  simp [U.blk2]
theorem b_nn (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) (i j : Fin s) : U.blk2 A B C D (Fin.natAdd p i) (Fin.natAdd p j) = D i j := by
  simp [U.blk2]

theorem one_cn (i : Fin p) (j : Fin s) : (1 : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) (Fin.castAdd s i) (Fin.natAdd p j) = 0 := by
  rw [Matrix.one_apply_ne]; intro h; have := congrArg Fin.val h; simp at this; omega
theorem one_nc (i : Fin s) (j : Fin p) : (1 : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) (Fin.natAdd p i) (Fin.castAdd s j) = 0 := by
  rw [Matrix.one_apply_ne]; intro h; have := congrArg Fin.val h; simp at this; omega
theorem one_cc (i j : Fin p) : (1 : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) (Fin.castAdd s i) (Fin.castAdd s j) =
    (1 : Matrix (Fin p) (Fin p) ℂ) i j := by
  simp [Matrix.one_apply, Fin.ext_iff]
theorem one_nn (i j : Fin s) : (1 : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) (Fin.natAdd p i) (Fin.natAdd p j) =
    (1 : Matrix (Fin s) (Fin s) ℂ) i j := by
  simp [Matrix.one_apply, Fin.ext_iff]

end blocks

theorem permutationMatrix_extend_eq_fromBlocks (σ : Equiv.Perm (Fin ph)) : U.wP (sigP (n := n) σ) = U.blk2 (U.wP σ) 0 0 (G.wMat (n + 1)) := by
  ext a b
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j => rw [b_cc]; simp [U.wP, blockPerm_castAdd, Fin.castAdd_inj]
    | right j =>
      rw [b_cn]; simp only [U.wP, Matrix.of_apply, blockPerm_castAdd, Matrix.zero_apply]
      rw [if_neg]; intro h; have := congrArg Fin.val h; simp at this; omega
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      rw [b_nc]; simp only [U.wP, Matrix.of_apply, blockPerm_natAdd, Matrix.zero_apply]
      rw [if_neg]; intro h; have := congrArg Fin.val h; simp at this; omega
    | right j => rw [b_nn]; simp [U.wP, blockPerm_natAdd, G.wMat, eq_comm]

theorem diag_dP (d : Fin ph → ℂ) (t : ℂ) :
    Matrix.diagonal (dP (n := n) d t) = U.blk2 (Matrix.diagonal d) 0 0 (t • 1) := by
  ext a b
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j => rw [b_cc]; simp [Matrix.diagonal_apply, dP, Fin.castAdd_inj]
    | right j => rw [b_cn, Matrix.diagonal_apply_ne]; · rfl
                 intro h; have := congrArg Fin.val h; simp at this; omega
  | right i =>
    induction b using Fin.addCases with
    | left j => rw [b_nc, Matrix.diagonal_apply_ne]; · rfl
                intro h; have := congrArg Fin.val h; simp at this; omega
    | right j => rw [b_nn]; simp [Matrix.diagonal_apply, dP, Matrix.one_apply, Fin.natAdd_inj]

theorem lowW_sigP (σ : Equiv.Perm (Fin ph)) (v : U.LW (sigP (n := n) σ) → ℂ) :
    U.lowW (sigP σ) v = U.blk2 (U.lowW σ (fun q => v (lwIn σ (Sum.inl q)))) 0
      (Matrix.of fun i j => v (lwIn σ (Sum.inr (i, j)))) 1 := by
  ext a b
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j =>
      rw [b_cc]
      simp only [U.lowW, Matrix.add_apply, Matrix.of_apply, one_cc]
      congr 1
      by_cases h : j < i ∧ σ.symm j < σ.symm i
      · have h' : Fin.castAdd (n + 1) j < Fin.castAdd (n + 1) i ∧
            (sigP σ).symm (Fin.castAdd (n + 1) j) < (sigP σ).symm (Fin.castAdd (n + 1) i) := by
          rw [blockPerm_symm_castAdd, blockPerm_symm_castAdd]; exact h
        rw [dif_pos h, dif_pos h']; rfl
      · have h' : ¬ (Fin.castAdd (n + 1) j < Fin.castAdd (n + 1) i ∧
            (sigP σ).symm (Fin.castAdd (n + 1) j) < (sigP σ).symm (Fin.castAdd (n + 1) i)) := by
          rw [blockPerm_symm_castAdd, blockPerm_symm_castAdd]; exact h
        rw [dif_neg h, dif_neg h']
    | right j =>
      rw [b_cn]
      simp only [U.lowW, Matrix.add_apply, Matrix.of_apply, one_cn, Matrix.zero_apply, zero_add]
      rw [dif_neg]; intro h; have : ph + j.val < i.val := h.1; omega
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      rw [b_nc]
      simp only [U.lowW, Matrix.add_apply, Matrix.of_apply, one_nc, zero_add]
      have h' : Fin.castAdd (n + 1) j < Fin.natAdd ph i ∧
          (sigP σ).symm (Fin.castAdd (n + 1) j) < (sigP σ).symm (Fin.natAdd ph i) := by
        refine ⟨show j.val < ph + i.val by omega, ?_⟩
        rw [blockPerm_symm_castAdd, blockPerm_symm_natAdd]
        show (σ.symm j).val < ph + (Fin.rev i).val
        have := (σ.symm j).isLt; omega
      rw [dif_pos h']; rfl
    | right j =>
      rw [b_nn]
      simp only [U.lowW, Matrix.add_apply, Matrix.of_apply, one_nn]
      rw [dif_neg, add_zero]
      rintro ⟨h1, h2⟩
      rw [blockPerm_symm_natAdd, blockPerm_symm_natAdd] at h2
      have e1 : ph + j.val < ph + i.val := h1
      have e2 : ph + (Fin.rev j).val < ph + (Fin.rev i).val := h2
      simp only [Fin.val_rev] at e2; omega

theorem upper_split (u : G.UT (ph + (n + 1)) → ℂ) :
    G.upper u = U.blk2 (G.upper (fun q => u (utIn (Sum.inl (Sum.inl q)))))
      (Matrix.of fun i j => u (utIn (Sum.inl (Sum.inr (i, j))))) 0 (G.upper (fun q => u (utIn (Sum.inr q)))) := by
  ext a b
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j =>
      rw [b_cc]; simp only [G.upper, Matrix.add_apply, one_cc, G.strictUpper, Matrix.of_apply]
      congr 1
    | right j =>
      rw [b_cn]; simp only [G.upper, Matrix.add_apply, one_cn, G.strictUpper, Matrix.of_apply, zero_add]
      rw [dif_pos (show Fin.castAdd (n + 1) i < Fin.natAdd ph j from show i.val < ph + j.val by omega)]; rfl
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      rw [b_nc]; simp only [G.upper, Matrix.add_apply, one_nc, G.strictUpper, Matrix.of_apply, zero_add,
        Matrix.zero_apply]
      rw [dif_neg]; intro h; have : ph + i.val < j.val := h; omega
    | right j =>
      rw [b_nn]; simp only [G.upper, Matrix.add_apply, one_nn, G.strictUpper, Matrix.of_apply]
      congr 1
      by_cases h : i < j
      · rw [dif_pos h, dif_pos (show Fin.natAdd ph i < Fin.natAdd ph j from show ph + i.val < ph + j.val by
          have : i.val < j.val := h; omega)]; rfl
      · rw [dif_neg h, dif_neg (show ¬ (Fin.natAdd ph i < Fin.natAdd ph j) from fun h' => h (show i.val < j.val by
          have : ph + i.val < ph + j.val := h'; omega))]

section ident
variable (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ)

def v1 (v : U.LW (sigP (n := n) σ) → ℂ) : U.LW σ → ℂ := fun q => v (lwIn σ (Sum.inl q))
def Am (v : U.LW (sigP (n := n) σ) → ℂ) : Matrix (Fin (n + 1)) (Fin ph) ℂ := Matrix.of fun i j => v (lwIn σ (Sum.inr (i, j)))
def u1 (u : G.UT (ph + (n + 1)) → ℂ) : G.UT ph → ℂ := fun q => u (utIn (Sum.inl (Sum.inl q)))
def Bm (u : G.UT (ph + (n + 1)) → ℂ) : Matrix (Fin ph) (Fin (n + 1)) ℂ := Matrix.of fun i j => u (utIn (Sum.inl (Sum.inr (i, j))))
def u2 (u : G.UT (ph + (n + 1)) → ℂ) : G.UT (n + 1) → ℂ := fun q => u (utIn (Sum.inr q))

def aN (v : U.LW (sigP (n := n) σ) → ℂ) : Matrix (Fin (n + 1)) (Fin ph) ℂ :=
  G.wMat (n + 1) * Am σ v * (U.lowW σ (v1 σ v))⁻¹ * (U.wP σ)⁻¹
def bN (u : G.UT (ph + (n + 1)) → ℂ) : Matrix (Fin ph) (Fin (n + 1)) ℂ := (G.upper (u1 u))⁻¹ * Bm u

theorem headH_split (v : U.LW (sigP (n := n) σ) → ℂ) (u : G.UT (ph + (n + 1)) → ℂ) :
    U.headH (sigP σ) (dP d t) v u =
      U.blk2 (U.wP σ * U.lowW σ (v1 σ v) * Matrix.diagonal d * G.upper (u1 u))
        (U.wP σ * U.lowW σ (v1 σ v) * Matrix.diagonal d * Bm u)
        (G.wMat (n + 1) * Am σ v * Matrix.diagonal d * G.upper (u1 u))
        (G.wMat (n + 1) * Am σ v * Matrix.diagonal d * Bm u + t • (G.wMat (n + 1) * G.upper (u2 u))) := by
  unfold U.headH
  rw [permutationMatrix_extend_eq_fromBlocks, lowW_sigP, diag_dP, upper_split]
  simp only [Ux2.symmetricScalarBlockMatrix_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_smul,
    Matrix.smul_mul, smul_zero]
  rfl

theorem isUnit_low (v : U.LW σ → ℂ) : IsUnit (U.lowW σ v).det := by rw [Ux3.det_lowW]; exact isUnit_one
theorem isUnit_up {m : ℕ} (u : G.UT m → ℂ) : IsUnit (G.upper u).det := by rw [Ux3.det_upper]; exact isUnit_one
theorem isUnit_wP {m : ℕ} (τ : Equiv.Perm (Fin m)) : IsUnit (U.wP τ).det :=
  Matrix.isUnit_det_of_right_inverse (Ux2.permutationMatrix_mul_symm τ)

theorem zj_zero {P : ℕ} (a : Fin 0 → Fin P → ℂ) (b : Fin P → Fin 0 → ℂ) (H : Matrix (Fin P) (Fin P) ℂ)
    (Z : Matrix (Fin 0) (Fin 0) ℂ) : U.Zj a b H Z = H := by
  rw [Ux4.ux_zjAffine]
  ext i j
  have hi : i = Fin.castAdd 0 i := Fin.ext rfl
  have hj : j = Fin.castAdd 0 j := Fin.ext rfl
  conv_lhs => rw [hi, hj]
  rw [b_cc]

theorem zj_split (v : U.LW (sigP (n := n) σ) → ℂ) (u : G.UT (ph + (n + 1)) → ℂ) :
    U.headH (sigP σ) (dP d t) v u =
      U.Zj (Matrix.of.symm (aN σ v)) (Matrix.of.symm (bN u)) (U.headH σ d (v1 σ v) (u1 u))
        (t • G.wMat (n + 1) * G.upper (u2 u)) := by
  rw [headH_split, Ux4.ux_zjAffine]
  have hL := Matrix.nonsing_inv_mul _ (isUnit_low σ (v1 σ v))
  have hW := Matrix.nonsing_inv_mul _ (isUnit_wP σ)
  have hU := Matrix.mul_nonsing_inv _ (isUnit_up (u1 u))
  simp only [Matrix.of_symm_apply, Equiv.apply_symm_apply, U.headH, aN, bN]
  congr 1
  · rw [show U.wP σ * U.lowW σ (v1 σ v) * Matrix.diagonal d * G.upper (u1 u) * ((G.upper (u1 u))⁻¹ * Bm u) =
      U.wP σ * U.lowW σ (v1 σ v) * Matrix.diagonal d * (G.upper (u1 u) * (G.upper (u1 u))⁻¹) * Bm u by
        simp only [Matrix.mul_assoc], hU, Matrix.mul_one]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U.wP σ)⁻¹, hW, Matrix.one_mul, ← Matrix.mul_assoc (U.lowW σ (v1 σ v))⁻¹, hL, Matrix.one_mul]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U.wP σ)⁻¹, hW, Matrix.one_mul, ← Matrix.mul_assoc (U.lowW σ (v1 σ v))⁻¹, hL, Matrix.one_mul]
    congr 1
    · rw [← Matrix.mul_assoc (G.upper (u1 u)), hU, Matrix.one_mul]
    · rw [Matrix.smul_mul]

end ident

section chars
variable (σ : Equiv.Perm (Fin ph))

theorem blockPerm_symm₂ : (sigP (n := n) σ).symm = sigP σ.symm := by
  ext x
  induction x using Fin.addCases with
  | left i => rw [blockPerm_symm_castAdd, blockPerm_castAdd]
  | right i => rw [blockPerm_symm_natAdd, blockPerm_natAdd]

theorem psi_add (β x y : ℂ) : G.psi β (x + y) = G.psi β x * G.psi β y := by
  unfold G.psi
  rw [← Complex.exp_add]; congr 1
  rw [mul_add, Complex.add_re]; push_cast; ring

theorem subS_one {m : ℕ} : U.subS (1 : Matrix (Fin m) (Fin m) ℂ) = 0 := by
  unfold U.subS
  apply Finset.sum_eq_zero; intro i _
  split_ifs with h
  · rw [Matrix.one_apply_ne]; intro e; have := congrArg Fin.val e; simp at this
  · rfl

theorem supS_superSum {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) : U.supS M = G.superSum M := by
  unfold U.supS G.superSum
  rw [Fin.sum_univ_castSucc]
  rw [dif_neg (by simp), add_zero]
  apply Finset.sum_congr rfl; intro i _
  rw [dif_pos (by simp)]; rfl

theorem cornerA_zero {P : ℕ} (a : Fin 0 → Fin P → ℂ) : U.cornerA a = 0 := by simp [U.cornerA]
theorem cornerB_zero {P : ℕ} (b : Fin P → Fin 0 → ℂ) : U.cornerB b = 0 := by simp [U.cornerB]

theorem conj_split (v : U.LW (sigP (n := n) σ) → ℂ) :
    U.wP (sigP σ) * U.lowW (sigP σ) v * (U.wP (sigP σ))⁻¹ =
      U.blk2 1 0 (Matrix.of (Matrix.of.symm (aN σ v))) 1 *
        U.blk2 (U.wP σ * U.lowW σ (v1 σ v) * (U.wP σ)⁻¹) 0 0 1 := by
  rw [Ux2.permutationMatrix_inv, blockPerm_symm₂, permutationMatrix_extend_eq_fromBlocks, permutationMatrix_extend_eq_fromBlocks, lowW_sigP, Ux2.permutationMatrix_inv]
  simp only [Ux2.symmetricScalarBlockMatrix_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
    Equiv.apply_symm_apply, Ux3.wMat_mul_self]
  congr 1
  have hL := Matrix.nonsing_inv_mul _ (isUnit_low σ (v1 σ v))
  have hW : U.wP σ.symm * U.wP σ = 1 := Ux2.permutationMatrix_symm_mul σ
  unfold aN
  rw [Ux2.permutationMatrix_inv]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U.wP σ.symm), hW, Matrix.one_mul, ← Matrix.mul_assoc (U.lowW σ (v1 σ v))⁻¹, hL, Matrix.one_mul]
  rfl

theorem upper_fact (u : G.UT (ph + (n + 1)) → ℂ) :
    G.upper u = U.blk2 (G.upper (u1 u)) 0 0 (G.upper (u2 u)) * U.blk2 1 (Matrix.of (Matrix.of.symm (bN u))) 0 1 := by
  rw [upper_split, Ux2.symmetricScalarBlockMatrix_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
    Equiv.apply_symm_apply]
  congr 1
  unfold bN
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_up (u1 u)), Matrix.one_mul]; rfl

theorem psiH_split (β : ℂ) (a0 : Fin 0 → Fin (ph + (n + 1)) → ℂ) (b0 : Fin (ph + (n + 1)) → Fin 0 → ℂ)
    (v : U.LW (sigP (n := n) σ) → ℂ) (u : G.UT (ph + (n + 1)) → ℂ) :
    U.psiH (s := 0) β (sigP σ) ((a0, b0), (v, u)) =
      U.psiH (s := n + 1) β σ ((Matrix.of.symm (aN σ v), Matrix.of.symm (bN u)), (v1 σ v, u1 u)) *
        G.psi β (G.superSum (G.upper (u2 u))) := by
  unfold U.psiH
  simp only
  rw [← psi_add, conj_split, upper_fact, cornerA_zero, cornerB_zero]
  have hlow := ((Formalism.FourierDecayAlt.P.low_weight_specialisation ph σ (U.lowW σ (v1 σ v))).mpr ⟨v1 σ v, rfl⟩)
  have huh : G.IsUpperUni (G.upper (u1 u)) := (Ux2.upper_iff _).mpr (Ux2.upper_uni _)
  have hu2 : G.IsUpperUni (G.upper (u2 u)) := (Ux2.upper_iff _).mpr (Ux2.upper_uni _)
  have h1 : G.IsLowerUni (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    refine ⟨fun i => by simp, fun i j h => ?_⟩
    rw [Matrix.transpose_one, Matrix.one_apply_ne (ne_of_lt h).symm]
  obtain ⟨cA, cB⟩ := Formalism.FourierDecayAlt.P.character_on_blocks ph (n + 1) (Matrix.of.symm (aN σ v)) (Matrix.of.symm (bN u))
    (U.wP σ * U.lowW σ (v1 σ v) * (U.wP σ)⁻¹) (G.upper (u1 u)) 1 (G.upper (u2 u)) hlow.2 h1 huh hu2
  rw [cA, cB, subS_one, supS_superSum]
  congr 1
  ring

end chars

section meas

theorem reindex_mp {ι κ X : Type} [Fintype ι] [Fintype κ] [MeasureSpace X] [SigmaFinite (volume : Measure X)]
    (e : ι ≃ κ) : MeasurePreserving (fun (y : κ → X) (i : ι) => y (e i)) volume volume := by
  refine ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply (e i)), ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))) (MeasurableSet.univ_pi hs)]
  have : (fun (y : κ → X) (i : ι) => y (e i)) ⁻¹' Set.univ.pi s = Set.univ.pi (fun k => s (e.symm k)) := by
    ext y; simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h k; have := h (e.symm k); simpa using this
    · intro h i; have := h (e i); simpa using this
  rw [this, volume_pi, Measure.pi_pi]
  exact Equiv.prod_comp e.symm (fun i => (volume : Measure X) (s i))

theorem row_mp {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ) (hN : Complex.normSq N.det = 1) :
    MeasurePreserving (fun x : Fin m → ℂ => Matrix.vecMul x N) volume volume := by
  let f : (Fin m → ℂ) →ₗ[ℝ] (Fin m → ℂ) := (Matrix.toLin' Nᵀ).restrictScalars ℝ
  have hf : ∀ x, f x = Matrix.vecMul x N := by
    intro x; simp [f, Matrix.toLin'_apply, Matrix.mulVec_transpose]
  have hdet : LinearMap.det f = 1 := by
    simp only [f]
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose, Algebra.norm_complex_apply, hN]
  have hmeas : Measurable f := f.continuous_of_finiteDimensional.measurable
  refine ⟨by simpa [← funext hf] using hmeas, ?_⟩
  rw [show (fun x : Fin m → ℂ => Matrix.vecMul x N) = f from funext fun x => (hf x).symm]
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (f := f) (by rw [hdet]; exact one_ne_zero), hdet]
  simp

end meas

section shear

theorem permutationMatrix_eq_permMatrix'' {m : ℕ} (τ : Equiv.Perm (Fin m)) : U.wP τ = τ.permMatrix ℂ := by
  ext a b
  simp [U.wP, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

theorem normSq_det_wP {m : ℕ} (τ : Equiv.Perm (Fin m)) : Complex.normSq (U.wP τ).det = 1 := by
  rw [permutationMatrix_eq_permMatrix'', Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]

theorem det_inv_low (σ : Equiv.Perm (Fin ph)) (v : U.LW σ → ℂ) : ((U.lowW σ v)⁻¹).det = 1 := by
  rw [Matrix.det_nonsing_inv, Ux3.det_lowW, Ring.inverse_one]
theorem det_inv_up {m : ℕ} (u : G.UT m → ℂ) : ((G.upper u)⁻¹).det = 1 := by
  rw [Matrix.det_nonsing_inv, Ux3.det_upper, Ring.inverse_one]

theorem fa_mp (N : Matrix (Fin ph) (Fin ph) ℂ) (hN : Complex.normSq N.det = 1) :
    MeasurePreserving (fun y : Fin (n + 1) → Fin ph → ℂ => Matrix.of.symm (G.wMat (n + 1) * Matrix.of y * N))
      volume volume := by
  have h1 := reindex_mp (X := Fin ph → ℂ) (Fin.revPerm (n := n + 1))
  have h2 : MeasurePreserving (fun (y : Fin (n + 1) → Fin ph → ℂ) (i : Fin (n + 1)) => Matrix.vecMul (y i) N)
      volume volume :=
    measurePreserving_pi (fun _ => volume) (fun _ => volume) (f := fun _ x => Matrix.vecMul x N) (fun _ => row_mp N hN)
  have e : (fun y : Fin (n + 1) → Fin ph → ℂ => Matrix.of.symm (G.wMat (n + 1) * Matrix.of y * N)) =
      (fun (y : Fin (n + 1) → Fin ph → ℂ) (i : Fin (n + 1)) => Matrix.vecMul (y i) N) ∘
        (fun (y : Fin (n + 1) → Fin ph → ℂ) (i : Fin (n + 1)) => y (Fin.revPerm i)) := by
    funext y i j
    simp only [Function.comp, Matrix.of_symm_apply, Matrix.mul_assoc]
    rw [Ux3.wMat_mul_apply]
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  rw [e]; exact h2.comp h1

theorem swap_mp (a b : ℕ) :
    MeasurePreserving (fun (y : Fin a → Fin b → ℂ) (j : Fin b) (i : Fin a) => y i j) volume volume := by
  have h1 := (curry_mp (Fin a) (Fin b)).symm
  have h2 := reindex_mp (X := ℂ) (Equiv.prodComm (Fin b) (Fin a))
  have h3 := curry_mp (Fin b) (Fin a)
  have e : (fun (y : Fin a → Fin b → ℂ) (j : Fin b) (i : Fin a) => y i j) =
      (MeasurableEquiv.curry (Fin b) (Fin a) ℂ) ∘ (fun (g : Fin a × Fin b → ℂ) (q : Fin b × Fin a) => g (Equiv.prodComm _ _ q)) ∘
        (MeasurableEquiv.curry (Fin a) (Fin b) ℂ).symm := by
    funext y j i; rfl
  rw [e]; exact h3.comp (h2.comp h1)

theorem fb_mp (M : Matrix (Fin ph) (Fin ph) ℂ) (hM : Complex.normSq M.det = 1) :
    MeasurePreserving (fun y : Fin ph → Fin (n + 1) → ℂ => Matrix.of.symm (M * Matrix.of y)) volume volume := by
  have h1 := swap_mp ph (n + 1)
  have h2 : MeasurePreserving (fun (y : Fin (n + 1) → Fin ph → ℂ) (j : Fin (n + 1)) => Matrix.vecMul (y j) Mᵀ)
      volume volume :=
    measurePreserving_pi (fun _ => volume) (fun _ => volume) (f := fun _ x => Matrix.vecMul x Mᵀ)
      (fun _ => row_mp Mᵀ (by rw [Matrix.det_transpose]; exact hM))
  have h3 := swap_mp (n + 1) ph
  have e : (fun y : Fin ph → Fin (n + 1) → ℂ => Matrix.of.symm (M * Matrix.of y)) =
      (fun (y : Fin (n + 1) → Fin ph → ℂ) (i : Fin ph) (j : Fin (n + 1)) => y j i) ∘
        (fun (y : Fin (n + 1) → Fin ph → ℂ) (j : Fin (n + 1)) => Matrix.vecMul (y j) Mᵀ) ∘
          (fun (y : Fin ph → Fin (n + 1) → ℂ) (j : Fin (n + 1)) (i : Fin ph) => y i j) := by
    funext y i j
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, mul_comm]
  rw [e]; exact h3.comp (h2.comp h1)

end shear

section chain

variable {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

theorem assoc_mp (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa] [SFinite μb] [SFinite μc] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (α × β) × γ ≃ᵐ α × β × γ) ((μa.prod μb).prod μc)
      (μa.prod (μb.prod μc)) :=
  ⟨MeasurableEquiv.measurable _, Measure.prodAssoc_prod⟩

def swap4 : (α × β) × (γ × δ) ≃ᵐ (α × γ) × (β × δ) :=
  MeasurableEquiv.prodAssoc.trans <| (MeasurableEquiv.prodCongr (MeasurableEquiv.refl α)
    ((MeasurableEquiv.prodAssoc.symm.trans (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
      (MeasurableEquiv.refl δ))).trans MeasurableEquiv.prodAssoc)).trans MeasurableEquiv.prodAssoc.symm

theorem measurePreserving_prod_middle_swap (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ) [SFinite μa] [SFinite μb]
    [SFinite μc] [SFinite μd] :
    MeasurePreserving (swap4 : (α × β) × (γ × δ) ≃ᵐ (α × γ) × (β × δ)) ((μa.prod μb).prod (μc.prod μd))
      ((μa.prod μc).prod (μb.prod μd)) := by
  have h1 := assoc_mp μa μb (μc.prod μd)
  have h2 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : β × γ × δ ≃ᵐ (β × γ) × δ)
      (μb.prod (μc.prod μd)) ((μb.prod μc).prod μd) := (assoc_mp μb μc μd).symm _
  have h3 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.prodComm : β × γ ≃ᵐ γ × β)
      (MeasurableEquiv.refl δ)) ((μb.prod μc).prod μd) ((μc.prod μb).prod μd) :=
    (Measure.measurePreserving_swap).prod (MeasurePreserving.id μd)
  have h4 := assoc_mp μc μb μd
  have h5 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl α)
      ((MeasurableEquiv.prodAssoc.symm.trans (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
        (MeasurableEquiv.refl δ))).trans MeasurableEquiv.prodAssoc))
      (μa.prod (μb.prod (μc.prod μd))) (μa.prod (μc.prod (μb.prod μd))) :=
    (MeasurePreserving.id μa).prod (h4.comp (h3.comp h2))
  have h6 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : α × γ × β × δ ≃ᵐ (α × γ) × β × δ)
      (μa.prod (μc.prod (μb.prod μd))) ((μa.prod μc).prod (μb.prod μd)) := (assoc_mp μa μc (μb.prod μd)).symm _
  exact h6.comp (h5.comp h1)

def dropE (T Y : Type) [MeasurableSpace T] [MeasurableSpace Y] [Unique T] : T × Y ≃ᵐ Y where
  toFun p := p.2
  invFun y := (default, y)
  left_inv p := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv y := rfl
  measurable_toFun := measurable_snd
  measurable_invFun := measurable_const.prodMk measurable_id

theorem dropE_mp (T Y : Type) [MeasurableSpace T] [MeasurableSpace Y] [Unique T] (μ : Measure T)
    [IsProbabilityMeasure μ] (ν : Measure Y) [SFinite ν] : MeasurePreserving (dropE T Y) (μ.prod ν) ν :=
  measurePreserving_snd

def reE {ι κ X : Type} [MeasurableSpace X] (e : ι ≃ κ) : (κ → X) ≃ᵐ (ι → X) where
  toFun y i := y (e i)
  invFun y k := y (e.symm k)
  left_inv y := by funext k; simp
  right_inv y := by funext i; simp
  measurable_toFun := measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))
  measurable_invFun := measurable_pi_lambda _ (fun k => measurable_pi_apply (e.symm k))

end chain

section shearE
variable (σ : Equiv.Perm (Fin ph))

theorem cont_lowW : Continuous (U.lowW σ) := by
  unfold U.lowW
  refine continuous_const.add ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  show Continuous fun v : U.LW σ → ℂ => if h : b < a ∧ σ.symm b < σ.symm a then v ⟨(a, b), h⟩ else 0
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const

theorem cont_upper {m : ℕ} : Continuous (G.upper (d := m)) := by
  unfold G.upper G.strictUpper
  refine continuous_const.add ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  show Continuous fun v : G.UT m → ℂ => if h : a < b then v ⟨(a, b), h⟩ else 0
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const

theorem inv_adj {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (h : A.det = 1) : A⁻¹ = A.adjugate := by
  rw [Matrix.inv_def, h, Ring.inverse_one, one_smul]

def shF (x : (U.LW σ → ℂ) × (G.UT ph → ℂ)) (y : (Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) :
    (Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ) :=
  (Matrix.of.symm (G.wMat (n + 1) * Matrix.of y.1 * ((U.lowW σ x.1)⁻¹ * (U.wP σ)⁻¹)),
   Matrix.of.symm ((G.upper x.2)⁻¹ * Matrix.of y.2))

def shG (x : (U.LW σ → ℂ) × (G.UT ph → ℂ)) (y : (Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) :
    (Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ) :=
  (Matrix.of.symm (G.wMat (n + 1) * Matrix.of y.1 * (U.wP σ * U.lowW σ x.1)),
   Matrix.of.symm (G.upper x.2 * Matrix.of y.2))

theorem shG_shF (x) (y : (Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) : shG σ x (shF σ x y) = y := by
  have hL := Matrix.nonsing_inv_mul _ (isUnit_low σ x.1)
  have hW := Matrix.nonsing_inv_mul _ (isUnit_wP σ)
  have hU := Matrix.mul_nonsing_inv _ (isUnit_up x.2)
  ext1
  · simp only [shG, shF, Equiv.apply_symm_apply]
    apply (Matrix.of).symm.injective.eq_iff.mpr
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (G.wMat (n + 1)) (G.wMat (n + 1)), Ux3.wMat_mul_self, Matrix.one_mul]
    rw [← Matrix.mul_assoc (U.wP σ)⁻¹ (U.wP σ), hW, Matrix.one_mul, hL, Matrix.mul_one]; rfl
  · simp only [shG, shF, Equiv.apply_symm_apply]
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]; rfl

theorem shF_shG (x) (y : (Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) : shF σ x (shG σ x y) = y := by
  have hL := Matrix.mul_nonsing_inv _ (isUnit_low σ x.1)
  have hW := Matrix.mul_nonsing_inv _ (isUnit_wP σ)
  have hU := Matrix.nonsing_inv_mul _ (isUnit_up x.2)
  ext1
  · simp only [shG, shF, Equiv.apply_symm_apply]
    apply (Matrix.of).symm.injective.eq_iff.mpr
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (G.wMat (n + 1)) (G.wMat (n + 1)), Ux3.wMat_mul_self, Matrix.one_mul]
    rw [← Matrix.mul_assoc (U.lowW σ x.1) (U.lowW σ x.1)⁻¹, hL, Matrix.one_mul, hW, Matrix.mul_one]; rfl
  · simp only [shG, shF, Equiv.apply_symm_apply]
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]; rfl

theorem cont_shF : Continuous (fun p : ((U.LW σ → ℂ) × (G.UT ph → ℂ)) ×
    ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) => shF σ p.1 p.2) := by
  have e : (fun p : ((U.LW σ → ℂ) × (G.UT ph → ℂ)) ×
      ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) => shF σ p.1 p.2) =
      fun p => (Matrix.of.symm (G.wMat (n + 1) * Matrix.of p.2.1 * ((U.lowW σ p.1.1).adjugate * (U.wP σ)⁻¹)),
        Matrix.of.symm ((G.upper p.1.2).adjugate * Matrix.of p.2.2)) := by
    funext p
    simp only [shF, inv_adj _ (Ux3.det_lowW σ p.1.1), inv_adj _ (Ux3.det_upper p.1.2)]
  rw [e]
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_const.matrix_mul (continuous_snd.fst : Continuous fun p : ((U.LW σ → ℂ) × (G.UT ph → ℂ)) ×
      ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) => (Matrix.of p.2.1 : Matrix _ _ ℂ))).matrix_mul
      (((cont_lowW σ).comp continuous_fst.fst).matrix_adjugate.matrix_mul continuous_const)
  · exact ((cont_upper.comp continuous_fst.snd).matrix_adjugate).matrix_mul
      (continuous_snd.snd : Continuous fun p : ((U.LW σ → ℂ) × (G.UT ph → ℂ)) ×
      ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) => (Matrix.of p.2.2 : Matrix _ _ ℂ))

theorem cont_shG : Continuous (fun p : ((U.LW σ → ℂ) × (G.UT ph → ℂ)) ×
    ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) => shG σ p.1 p.2) := by
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_const.matrix_mul (continuous_snd.fst : Continuous fun p : ((U.LW σ → ℂ) × (G.UT ph → ℂ)) ×
      ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) => (Matrix.of p.2.1 : Matrix _ _ ℂ))).matrix_mul
      (continuous_const.matrix_mul ((cont_lowW σ).comp continuous_fst.fst))
  · exact (cont_upper.comp continuous_fst.snd).matrix_mul
      (continuous_snd.snd : Continuous fun p : ((U.LW σ → ℂ) × (G.UT ph → ℂ)) ×
      ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) => (Matrix.of p.2.2 : Matrix _ _ ℂ))

def shearE : ((U.LW σ → ℂ) × (G.UT ph → ℂ)) × ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) ≃ᵐ
    ((U.LW σ → ℂ) × (G.UT ph → ℂ)) × ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) where
  toFun p := (p.1, shF σ p.1 p.2)
  invFun p := (p.1, shG σ p.1 p.2)
  left_inv p := by simp only [shG_shF]
  right_inv p := by simp only [shF_shG]
  measurable_toFun := measurable_fst.prodMk (cont_shF σ).measurable
  measurable_invFun := measurable_fst.prodMk (cont_shG σ).measurable

theorem shearE_mp : MeasurePreserving (shearE (n := n) σ) volume volume := by
  have hx : ∀ x : (U.LW σ → ℂ) × (G.UT ph → ℂ),
      MeasurePreserving (shF (n := n) σ x) volume volume := by
    intro x
    have hN : Complex.normSq (((U.lowW σ x.1)⁻¹ * (U.wP σ)⁻¹)).det = 1 := by
      rw [Matrix.det_mul, det_inv_low, one_mul, Ux2.permutationMatrix_inv, normSq_det_wP]
    have hM : Complex.normSq ((G.upper x.2)⁻¹).det = 1 := by rw [det_inv_up]; simp
    exact (fa_mp _ hN).prod (fb_mp _ hM)
  have s1 : SFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT ph → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have i1 : SigmaFinite (volume : Measure (Fin (n + 1) → Fin ph → ℂ)) := inferInstance
  have i2 : SigmaFinite (volume : Measure (Fin ph → Fin (n + 1) → ℂ)) := inferInstance
  have s2 : SFinite (volume : Measure ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [Measure.volume_eq_prod (α := (U.LW σ → ℂ) × (G.UT ph → ℂ))]
  exact MeasurePreserving.skew_product (f := id) (MeasurePreserving.id _) (cont_shF σ).measurable
    (Filter.Eventually.of_forall fun x => (hx x).map_eq)

end shearE

section split
variable (σ : Equiv.Perm (Fin ph))

def lwSplit : (U.LW (sigP (n := n) σ) → ℂ) ≃ᵐ (U.LW σ → ℂ) × (Fin (n + 1) → Fin ph → ℂ) :=
  (reE (X := ℂ) (lwEquiv (n := n) σ).symm).trans ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.curry (Fin (n + 1)) (Fin ph) ℂ)))

theorem lwSplit_mp : MeasurePreserving (lwSplit (n := n) σ) volume (volume.prod volume) := by
  have h1 := reindex_mp (X := ℂ) (lwEquiv (n := n) σ).symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : U.LW σ ⊕ (Fin (n + 1) × Fin ph) => (volume : Measure ℂ))
  have h3 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (U.LW σ → ℂ))
      (MeasurableEquiv.curry (Fin (n + 1)) (Fin ph) ℂ))
      ((Measure.pi fun _ : U.LW σ => (volume : Measure ℂ)).prod (Measure.pi fun _ : Fin (n + 1) × Fin ph => (volume : Measure ℂ)))
      (volume.prod volume) :=
    (MeasurePreserving.id _).prod (curry_mp (Fin (n + 1)) (Fin ph))
  exact h3.comp (h2.comp h1)

def utSplit : (G.UT (ph + (n + 1)) → ℂ) ≃ᵐ ((G.UT ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) × (G.UT (n + 1) → ℂ) :=
  (reE (X := ℂ) (utEquiv (ph := ph) (n := n)).symm).trans ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ)).trans
    (MeasurableEquiv.prodCongr ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.curry (Fin ph) (Fin (n + 1)) ℂ)))
      (MeasurableEquiv.refl _)))

theorem utSplit_mp : MeasurePreserving (utSplit (ph := ph) (n := n)) volume
    ((volume.prod volume).prod volume) := by
  have h1 := reindex_mp (X := ℂ) (utEquiv (ph := ph) (n := n)).symm
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : (G.UT ph ⊕ (Fin ph × Fin (n + 1))) ⊕ G.UT (n + 1) => (volume : Measure ℂ))
  have h3 := measurePreserving_sumPiEquivProdPi (fun _ : G.UT ph ⊕ (Fin ph × Fin (n + 1)) => (volume : Measure ℂ))
  have h4 : MeasurePreserving (MeasurableEquiv.prodCongr ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.curry (Fin ph) (Fin (n + 1)) ℂ)))
      (MeasurableEquiv.refl (G.UT (n + 1) → ℂ)))
      ((Measure.pi fun _ : G.UT ph ⊕ (Fin ph × Fin (n + 1)) => (volume : Measure ℂ)).prod
        (Measure.pi fun _ : G.UT (n + 1) => (volume : Measure ℂ)))
      ((volume.prod volume).prod volume) :=
    (((MeasurePreserving.id _).prod (curry_mp (Fin ph) (Fin (n + 1)))).comp h3).prod (MeasurePreserving.id _)
  exact h4.comp (h2.comp h1)

end split

section xi
variable (σ : Equiv.Perm (Fin ph))

instance isProbabilityMeasure_pi_fin_zero {X : Type} [MeasureSpace X] : IsProbabilityMeasure (volume : Measure (Fin 0 → X)) := by
  rw [volume_pi, Measure.pi_of_empty]; infer_instance

instance uniqueT (P : ℕ) : Unique ((Fin 0 → Fin P → ℂ) × (Fin P → Fin 0 → ℂ)) where
  default := (fun i => i.elim0, fun _ i => i.elim0)
  uniq p := Prod.ext (funext fun i => i.elim0) (funext fun _ => funext fun i => i.elim0)

theorem probT (P : ℕ) : IsProbabilityMeasure (volume : Measure ((Fin 0 → Fin P → ℂ) × (Fin P → Fin 0 → ℂ))) := by
  have : IsProbabilityMeasure (volume : Measure (Fin P → Fin 0 → ℂ)) := by
    rw [volume_pi]; infer_instance
  rw [Measure.volume_eq_prod]; infer_instance

def xiE : U.XiH (ph + (n + 1)) 0 (sigP σ) ≃ᵐ U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ) :=
  (dropE ((Fin 0 → Fin (ph + (n + 1)) → ℂ) × (Fin (ph + (n + 1)) → Fin 0 → ℂ)) _).trans
    ((MeasurableEquiv.prodCongr (lwSplit σ) utSplit).trans (MeasurableEquiv.prodAssoc.symm.trans
      ((MeasurableEquiv.prodCongr swap4 (MeasurableEquiv.refl _)).trans
        ((MeasurableEquiv.prodCongr (shearE σ) (MeasurableEquiv.refl _)).trans
          (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl _))))))

theorem xiE_apply (η : U.XiH (ph + (n + 1)) 0 (sigP σ)) :
    xiE σ η = (((Matrix.of.symm (aN σ η.2.1), Matrix.of.symm (bN η.2.2)), (v1 σ η.2.1, u1 η.2.2)), u2 η.2.2) := by
  rw [show aN σ η.2.1 = G.wMat (n + 1) * Am σ η.2.1 * ((U.lowW σ (v1 σ η.2.1))⁻¹ * (U.wP σ)⁻¹) from by
    simp only [aN, Matrix.mul_assoc]]
  rfl

theorem xiE_mp : MeasurePreserving (xiE (n := n) σ) volume (volume.prod volume) := by
  have hT := probT (ph + (n + 1))
  have i1 : SigmaFinite (volume : Measure (Fin (n + 1) → Fin ph → ℂ)) := inferInstance
  have i2 : SigmaFinite (volume : Measure (Fin ph → Fin (n + 1) → ℂ)) := inferInstance
  have i3 : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  have i4 : SigmaFinite (volume : Measure (G.UT ph → ℂ)) := inferInstance
  have i5 : SigmaFinite (volume : Measure (G.UT (n + 1) → ℂ)) := inferInstance
  have h1 : MeasurePreserving (dropE ((Fin 0 → Fin (ph + (n + 1)) → ℂ) × (Fin (ph + (n + 1)) → Fin 0 → ℂ))
      ((U.LW (sigP (n := n) σ) → ℂ) × (G.UT (ph + (n + 1)) → ℂ))) volume (volume.prod volume) :=
    dropE_mp _ _ volume _
  have h2 := (lwSplit_mp (n := n) σ).prod (utSplit_mp (ph := ph) (n := n))
  have h3 := (assoc_mp ((volume : Measure (U.LW σ → ℂ)).prod (volume : Measure (Fin (n + 1) → Fin ph → ℂ)))
    ((volume : Measure (G.UT ph → ℂ)).prod (volume : Measure (Fin ph → Fin (n + 1) → ℂ)))
    (volume : Measure (G.UT (n + 1) → ℂ))).symm _
  have h4 := (measurePreserving_prod_middle_swap (volume : Measure (U.LW σ → ℂ)) (volume : Measure (Fin (n + 1) → Fin ph → ℂ))
    (volume : Measure (G.UT ph → ℂ)) (volume : Measure (Fin ph → Fin (n + 1) → ℂ))).prod
    (MeasurePreserving.id (volume : Measure (G.UT (n + 1) → ℂ)))
  have h5 := (shearE_mp (n := n) σ).prod (MeasurePreserving.id (volume : Measure (G.UT (n + 1) → ℂ)))
  have h6 := (Measure.measurePreserving_swap (μ := ((volume : Measure (U.LW σ → ℂ)).prod (volume : Measure (G.UT ph → ℂ))))
    (ν := ((volume : Measure (Fin (n + 1) → Fin ph → ℂ)).prod (volume : Measure (Fin ph → Fin (n + 1) → ℂ))))).prod
    (MeasurePreserving.id (volume : Measure (G.UT (n + 1) → ℂ)))
  exact h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))

end xi

section core

theorem card_UT (m : ℕ) : 2 * Fintype.card (G.UT m) = m * (m - 1) := by
  induction m with
  | zero => simp [Fintype.card_eq_zero_iff]
  | succ m ih =>
    have e := Fintype.card_congr (utEquiv (ph := m) (n := 0))
    have h1 : Fintype.card (G.UT (0 + 1)) = 0 := by
      rw [Fintype.card_eq_zero_iff]; exact ⟨fun q => absurd q.2 (by
        have a := q.1.1.isLt
        have b := q.1.2.isLt
        have e : q.1.1 = q.1.2 := Fin.ext (by omega)
        rw [e]; exact lt_irrefl _)⟩
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, h1, add_zero, mul_one] at e
    rw [show m + (0 + 1) = m + 1 from rfl] at e
    rw [e, mul_add, ih]
    cases m with
    | zero => simp
    | succ m => simp [Nat.succ_sub_one]; ring

theorem card_UT' (n : ℕ) : Fintype.card (G.UT (n + 1)) = (n + 1) * n / 2 := by
  have := card_UT (n + 1)
  simp only [Nat.add_sub_cancel] at this
  omega

theorem pi_const_smul {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (c : NNReal) :
    Measure.pi (fun _ : ι => c • μ) = (c ^ Fintype.card ι) • Measure.pi (fun _ : ι => μ) := by
  have : ∀ _ : ι, SigmaFinite (c • μ) := fun _ => inferInstance
  refine Measure.pi_eq (μ := fun _ : ι => c • μ) fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  simp [ENNReal.coe_pow]

theorem norm_betaU : ‖U.betaU‖ = 2 := by
  simp [U.betaU, cStd]

theorem muPi_betaU (ι : Type) [Fintype ι] :
    G.muPi U.betaU ι = (Real.toNNReal (1 / Real.pi) ^ Fintype.card ι) • (volume : Measure (ι → ℂ)) := by
  unfold G.muPi G.mu
  rw [norm_betaU, show (2 : ℝ) / (2 * Real.pi) = 1 / Real.pi by field_simp, pi_const_smul, volume_pi]

end core

section main

theorem sigma_RC (k j ρ : ℕ) : SigmaFinite (U.muRC k j ρ) := by
  have a1 : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin j → ℂ)) := inferInstance
  have a2 : SigmaFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  have a3 : SigmaFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  have a4 : SigmaFinite (volume : Measure ((G.UT j → ℂ) × (Fin j → ℝ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  unfold U.muRC
  rw [Measure.volume_eq_prod]; infer_instance

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem core (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ)
    (z z' : Fin (2 * (ph + (n + 1) + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + (n + 1) + ρ) → E) (γ : B.Mat k ρ)
    (hint : Integrable (fun ξ : U.Xi k (ph + (n + 1)) 0 ρ (sigP σ) =>
        U.psiStar (p := ph + (n + 1)) (s := 0) k ρ (sigP σ) z z' ξ • F (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (sigP σ) (dP d t) ξ (fun a => a.elim0) γ))
      (U.muXi k (ph + (n + 1)) 0 ρ (sigP σ))) :
    U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (sigP σ) (dP d t) z z' F (fun a => a.elim0) γ =
      ((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) • G.OmLong U.betaU n (fun Z => U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F Z γ) t := by

  set RR := U.RC k (ph + (n + 1)) ρ × U.RC k (ph + (n + 1)) ρ
  have sR := sigma_RC k (ph + (n + 1)) ρ
  set μR : Measure RR := (U.muRC k (ph + (n + 1)) ρ).prod (U.muRC k (ph + (n + 1)) ρ)
  let g : RR × (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)) → E := fun y =>
    G.psi U.betaU (G.superSum (G.upper y.2.2)) •
      (U.psiStar (p := ph) (s := n + 1) k ρ σ z z' (y.1, y.2.1) • F (U.gaXi (p := ph) (s := n + 1) k ρ σ d (y.1, y.2.1)
        (Matrix.of.symm (t • G.wMat (n + 1) * G.upper y.2.2)) γ))
  let Φ : U.Xi k (ph + (n + 1)) 0 ρ (sigP σ) ≃ᵐ RR × (U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ)) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl RR) (xiE σ)
  have sX : SFinite (U.muXiH (ph + (n + 1)) 0 (sigP σ)) := by
    have hT := probT (ph + (n + 1))
    have b1 : SigmaFinite (volume : Measure (U.LW (sigP (n := n) σ) → ℂ)) := inferInstance
    have b2 : SigmaFinite (volume : Measure (G.UT (ph + (n + 1)) → ℂ)) := inferInstance
    have b3 : SigmaFinite (volume : Measure ((U.LW (sigP (n := n) σ) → ℂ) × (G.UT (ph + (n + 1)) → ℂ))) := by
      rw [Measure.volume_eq_prod]; infer_instance
    unfold U.muXiH
    rw [Measure.volume_eq_prod]; infer_instance
  have hΦ : MeasurePreserving Φ (U.muXi k (ph + (n + 1)) 0 ρ (sigP σ)) (μR.prod (volume.prod volume)) :=
    (MeasurePreserving.id μR).prod (xiE_mp σ)
  have hfg : (fun ξ : U.Xi k (ph + (n + 1)) 0 ρ (sigP σ) =>
      U.psiStar (p := ph + (n + 1)) (s := 0) k ρ (sigP σ) z z' ξ • F (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (sigP σ) (dP d t) ξ (fun a => a.elim0) γ)) = g ∘ Φ := by
    funext ξ
    obtain ⟨x, ⟨a0, b0⟩, v, u⟩ := ξ
    rw [Function.comp_apply]
    rw [show Φ (x, ((a0, b0), v, u)) = (x, xiE σ ((a0, b0), v, u)) from rfl, xiE_apply]
    simp only [g, U.psiStar, U.gaXi, U.ZjH, zj_zero, zj_split, Equiv.apply_symm_apply]
    rw [psiH_split, smul_smul]
    congr 1
    have e1 : Formalism.QuantumDeterminants.psi k (ph + (n + 1) + 0 + ρ) z cStd (U.Rn k (ph + (n + 1) + 0) ρ x.1) =
        Formalism.QuantumDeterminants.psi k (ph + (n + 1) + ρ) z cStd (U.Rn k (ph + (n + 1)) ρ x.1) := rfl
    have e2 : Formalism.QuantumDeterminants.psi k (ph + (n + 1) + 0 + ρ) z' cStd (U.Rn k (ph + (n + 1) + 0) ρ x.2) =
        Formalism.QuantumDeterminants.psi k (ph + (n + 1) + ρ) z' cStd (U.Rn k (ph + (n + 1)) ρ x.2) := rfl
    rw [e1, e2]
    ring
  have hg : Integrable g (μR.prod (volume.prod volume)) := by
    have := hint; rw [hfg] at this
    exact (hΦ.integrable_comp_emb Φ.measurableEmbedding).mp this
  have hL : U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (sigP σ) (dP d t) z z' F (fun a => a.elim0) γ =
      ∫ y, g y ∂(μR.prod (volume.prod volume)) := by
    unfold U.PhiFun
    rw [show (fun ξ : U.Xi k (ph + (n + 1)) 0 ρ (sigP σ) =>
      U.psiStar (p := ph + (n + 1)) (s := 0) k ρ (sigP σ) z z' ξ • F (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (sigP σ)
        (dP d t) ξ (fun a => a.elim0) γ)) = g ∘ Φ from hfg]
    exact hΦ.integral_comp' g
  have hvi : SigmaFinite (volume : Measure (G.UT (n + 1) → ℂ)) := inferInstance
  have hxi : SFinite (volume : Measure (U.XiH ph (n + 1) σ)) := by
    have c1 : SigmaFinite (volume : Measure (Fin (n + 1) → Fin ph → ℂ)) := inferInstance
    have c2 : SigmaFinite (volume : Measure (Fin ph → Fin (n + 1) → ℂ)) := inferInstance
    have c3 : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
    have c4 : SigmaFinite (volume : Measure (G.UT ph → ℂ)) := inferInstance
    have c5 : SigmaFinite (volume : Measure ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ))) := by
      rw [Measure.volume_eq_prod]; infer_instance
    have c6 : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT ph → ℂ))) := by
      rw [Measure.volume_eq_prod]; infer_instance
    rw [Measure.volume_eq_prod]; infer_instance
  have hA : MeasurePreserving (MeasurableEquiv.prodAssoc : (RR × U.XiH ph (n + 1) σ) × (G.UT (n + 1) → ℂ) ≃ᵐ _)
      ((μR.prod volume).prod volume) (μR.prod (volume.prod volume)) := assoc_mp μR volume volume
  let g' : (RR × U.XiH ph (n + 1) σ) × (G.UT (n + 1) → ℂ) → E := fun w => g (w.1.1, (w.1.2, w.2))
  have eg : g ∘ (MeasurableEquiv.prodAssoc : (RR × U.XiH ph (n + 1) σ) × (G.UT (n + 1) → ℂ) ≃ᵐ _) = g' := rfl
  have hg' : Integrable g' ((μR.prod volume).prod volume) := by
    rw [← eg]; exact (hA.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).mpr hg
  have hA' : ∫ y, g y ∂(μR.prod (volume.prod volume)) = ∫ w, g' w ∂((μR.prod volume).prod volume) :=
    (hA.integral_comp' g).symm
  rw [hL, hA', MeasureTheory.integral_prod_symm g' hg']

  have hin : ∀ w : G.UT (n + 1) → ℂ, ∫ x, g' (x, w) ∂(μR.prod volume) =
      G.psi U.betaU (G.superSum (G.upper w)) •
        U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F (Matrix.of.symm (t • G.wMat (n + 1) * G.upper w)) γ := by
    intro w
    simp only [g', g]
    rw [integral_smul]
    rfl
  simp_rw [hin]
  unfold G.OmLong
  rw [muPi_betaU, integral_smul_nnreal_measure, card_UT' n]
  rw [NNReal.smul_def, ← Complex.coe_smul, smul_smul]
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  have : ((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) * (((Real.toNNReal (1 / Real.pi) ^ ((n + 1) * n / 2) : NNReal) : ℝ) : ℂ) = 1 := by
    rw [NNReal.coe_pow, Real.coe_toNNReal _ (by positivity)]
    push_cast
    rw [← mul_pow, mul_one_div_cancel (by exact_mod_cast hp.ne'), one_pow]
  rw [this, one_smul]
  rfl

end main

section wrap

theorem ptSize_cons (b : ℕ × ℂ) (h : C.LPt) : D.ptSize (b :: h) = b.1 + D.ptSize h := by
  simp [D.ptSize]

theorem ptSize_append (h : C.LPt) (s : ℕ) (t : ℂ) : D.ptSize (h ++ [(s, t)]) = D.ptSize h + s := by
  simp [D.ptSize]

theorem partner_append (s : ℕ) (t : ℂ) : ∀ (h : C.LPt) (a : ℕ), a < D.ptSize h + s →
    D.ptPartner (h ++ [(s, t)]) a = if a < D.ptSize h then D.ptPartner h a else D.ptSize h + (s - 1 - (a - D.ptSize h))
  | [], a, ha => by
    simp only [List.nil_append, D.ptPartner, D.ptSize, List.map_nil, List.sum_nil] at ha ⊢
    rw [if_pos (by omega)]; simp
  | b :: h, a, ha => by
    rw [ptSize_cons] at ha
    simp only [List.cons_append, D.ptPartner, ptSize_cons]
    by_cases h1 : a < b.1
    · rw [if_pos h1, if_pos (by omega), if_pos h1]
    · rw [if_neg h1, partner_append s t h (a - b.1) (by omega)]
      by_cases h2 : a - b.1 < D.ptSize h
      · rw [if_pos h2, if_pos (by omega), if_neg h1]
      · rw [if_neg h2, if_neg (by omega)]; omega

theorem scal_append (s : ℕ) (t : ℂ) : ∀ (h : C.LPt) (a : ℕ), a < D.ptSize h + s →
    D.ptScal (h ++ [(s, t)]) a = if a < D.ptSize h then D.ptScal h a else t
  | [], a, ha => by
    simp only [List.nil_append, D.ptScal, D.ptSize, List.map_nil, List.sum_nil] at ha ⊢
    rw [if_pos (by omega)]; simp
  | b :: h, a, ha => by
    rw [ptSize_cons] at ha
    simp only [List.cons_append, D.ptScal, ptSize_cons]
    by_cases h1 : a < b.1
    · rw [if_pos h1, if_pos (by omega), if_pos h1]
    · rw [if_neg h1, scal_append s t h (a - b.1) (by omega)]
      by_cases h2 : a - b.1 < D.ptSize h
      · rw [if_pos h2, if_pos (by omega), if_neg h1]
      · rw [if_neg h2, if_neg (by omega)]

theorem isLocPt_head {h : C.LPt} {s : ℕ} {t : ℂ} (hl : D.IsLocPt (h ++ [(s, t)]) (D.ptSize (h ++ [(s, t)]))) :
    D.IsLocPt h (D.ptSize h) :=
  ⟨fun b hb => hl.1 b (List.mem_append_left _ hb), rfl⟩

theorem phi_transport {k ρ P P' : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (e : P = P')
    (σ : Equiv.Perm (Fin P)) (σ' : Equiv.Perm (Fin P')) (hσ : ∀ a : Fin P, (σ' (Fin.cast e a)).val = (σ a).val)
    (dd : Fin P → ℂ) (dd' : Fin P' → ℂ) (hd : ∀ a : Fin P, dd' (Fin.cast e a) = dd a)
    (z z' : Fin (2 * (P + 0 + ρ) + k + 1) → ℂ) (F : B.Mat k (P + 0 + ρ) → E) (γ : B.Mat k ρ) :
    (Integrable (fun ξ : U.Xi k P 0 ρ σ => U.psiStar k ρ σ z z' ξ • F (U.gaXi k ρ σ dd ξ (fun a => a.elim0) γ))
        (U.muXi k P 0 ρ σ) →
      Integrable (fun ξ : U.Xi k P' 0 ρ σ' => U.psiStar k ρ σ' (D.castV (by omega) z) (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k ρ σ' dd' ξ (fun a => a.elim0) γ)) (U.muXi k P' 0 ρ σ')) ∧
    U.PhiFun k ρ σ dd z z' F (fun a => a.elim0) γ =
      U.PhiFun k ρ σ' dd' (D.castV (by omega) z) (D.castV (by omega) z') (D.castF (by omega) F) (fun a => a.elim0) γ := by
  subst e
  have h1 : σ' = σ := Equiv.ext fun a => Fin.ext (hσ a)
  have h2 : dd' = dd := funext fun a => hd a
  subst h1 h2
  have e1 : D.castV (k := k) (a := P + 0 + ρ) (b := P + 0 + ρ) (by omega) z = z := by
    funext i; simp [D.castV]
  have e2 : D.castV (k := k) (a := P + 0 + ρ) (b := P + 0 + ρ) (by omega) z' = z' := by
    funext i; simp [D.castV]
  have e3 : D.castF (k := k) (a := P + 0 + ρ) (b := P + 0 + ρ) (by omega) F = F := by
    funext g; simp [D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rw [e1, e2, e3]
  exact ⟨id, rfl⟩

end wrap

section final

theorem castV_castV {k a b c : ℕ} (h1 : a = b) (h2 : b = c) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h2 (D.castV h1 v) = D.castV (h1.trans h2) v := by
  subst h1 h2; rfl

theorem castF_castF {k a b c : ℕ} {E : Type} (h1 : a = b) (h2 : b = c) (F : B.Mat k c → E) :
    D.castF h1 (D.castF h2 F) = D.castF (h1.trans h2) F := by
  subst h1 h2; rfl

theorem sliceOm : D.SliceOm := by
  intro k r E _ _ _ z z' F h p n t hp hle γ hloc hint
  subst hp
  have hP : D.ptSize (h ++ [(n + 1, t)]) = D.ptSize h + (n + 1) := ptSize_append h (n + 1) t
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ (isLocPt_head hloc)).1
  have hσ : ∀ a : Fin (D.ptSize (h ++ [(n + 1, t)])),
      ((sigP (n := n) (D.ptPerm h)) (Fin.cast hP a)).val = (D.ptPerm (h ++ [(n + 1, t)]) a).val := by
    intro a
    rw [hspec a, partner_append (n + 1) t h a.val (by have := a.isLt; omega)]
    by_cases h1 : a.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (n + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, blockPerm_castAdd]
      exact hspec' ⟨a.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd (D.ptSize h) ⟨a.val - D.ptSize h, by have := a.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ a : Fin (D.ptSize (h ++ [(n + 1, t)])),
      dP (n := n) (D.ptDiag h) t (Fin.cast hP a) = D.ptDiag (h ++ [(n + 1, t)]) a := by
    intro a
    simp only [D.ptDiag]
    rw [scal_append (n + 1) t h a.val (by have := a.isLt; omega)]
    by_cases h1 : a.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (n + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd (D.ptSize h) ⟨a.val - D.ptSize h, by have := a.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, dP, Fin.addCases_right]
  obtain ⟨hT1, hT2⟩ := phi_transport (k := k) (ρ := r - D.ptSize (h ++ [(n + 1, t)])) hP _ _ hσ _ _ hd
    (D.castV (by omega) z) (D.castV (by omega) z') (D.castF (by omega) F) γ
  have hc := core (k := k) (ρ := r - D.ptSize (h ++ [(n + 1, t)])) (D.ptPerm h) (D.ptDiag h) t _ _ _ γ (hT1 hint)
  unfold D.sliceAt
  rw [dif_pos hle, hT2, hc]
  simp only [castV_castV, castF_castF]

end final

end Formalism.FourierDecayAlt.P.Dx2.SL

end

namespace Formalism.FourierDecayAlt.P

theorem nilpotent_measure_is_haar : Formalism.FourierDecayAlt.D.MuNHaar := fun k r => Dx2.MN.haar (k := k) r

theorem unipotent_dual_lattice_covolume : Formalism.FourierDecayAlt.D.NhatCovol := Dx2.NH.nhat

theorem exists_level_tower : Formalism.FourierDecayAlt.D.TowerExists := Dx2.Tower.towerExists

theorem exists_isotropic_frame : Formalism.FourierDecayAlt.D.DFrameExists := Dx2.dFrameExists

theorem radial_measure_is_haar : Formalism.FourierDecayAlt.D.MuRHaar := Dx2.Rad.muRHaar

theorem slice_measure_identity : Formalism.FourierDecayAlt.D.SliceOm := Dx2.SL.sliceOm

end Formalism.FourierDecayAlt.P
