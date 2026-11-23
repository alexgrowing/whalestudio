import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtAeEqContRep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvolutionOperatorAeEqIntegralAdelic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsAutIdemElementary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Reproducing

theorem two_mul_rank_le {n : ℕ} (ε : Fin n → Bool) : 2 * rkR ε ≤ n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun a => ε a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  unfold rkR
  omega

theorem weight_condition (B : RowsAut) (h s : ℝ) (hn : 1 ≤ B.I.n) (hb : HBig B 40 h)
    (hs : s ≤ 2 * (B.I.n : ℝ) ^ 2) (v : InfinitePlace B.I.F) :
    rkR (B.I.ε v) = 0 ∨ 8 * Real.sqrt (rkR (B.I.ε v)) * (s + 4 * B.I.n * rkR (B.I.ε v)) < h := by
  rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with h0 | h0
  · exact Or.inl h0
  right
  have h1 : (2 : ℝ) * rkR (B.I.ε v) ≤ B.I.n := by exact_mod_cast two_mul_rank_le _
  have h2 : 0 < Real.sqrt (rkR (B.I.ε v)) := Real.sqrt_pos.2 (by exact_mod_cast h0)
  have h3 : (1 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have h4 := hb v
  have h5 : s + 4 * B.I.n * rkR (B.I.ε v) ≤ 4 * (B.I.n : ℝ) ^ 2 := by nlinarith
  have h6 := mul_le_mul_of_nonneg_left h5 h2.le
  have h7 : 0 < Real.sqrt (rkR (B.I.ε v)) * (B.I.n : ℝ) ^ 2 := by positivity
  nlinarith

theorem inv_tau_pow_le (I : AutInst) (hn : 1 ≤ I.n) (x g : I.GA) (hg : g.2 ∈ I.Kset) :
    (tau1 I (x * g))⁻¹ ^ (2 * I.n ^ 2 * I.f) ≤
      (tau1 I x)⁻¹ ^ (2 * I.n ^ 2 * I.f) * Real.exp (2 * (I.n : ℝ) ^ 2 * dSum I g.1) := by
  obtain ⟨hp, -, -, hl⟩ := GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties I hn
  have hf : (0 : ℝ) < I.f := by
    have : 0 < I.f := Module.finrank_pos
    exact_mod_cast this
  have h1 := (abs_le.1 (hl x g hg)).1
  have h2 : (tau1 I (x * g))⁻¹ ≤ (tau1 I x)⁻¹ * Real.exp (dSum I g.1 / I.f) := by
    rw [← Real.exp_log (inv_pos.2 (hp (x * g))), ← Real.exp_log (inv_pos.2 (hp x)), ← Real.exp_add,
      Real.log_inv, Real.log_inv]
    exact Real.exp_le_exp.2 (by linarith)
  refine (pow_le_pow_left₀ (inv_pos.2 (hp _)).le h2 _).trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  field_simp

theorem isContRep_sum (B : RowsAut) {m : ℕ} (y : Fin m → B.I.L2 B.μf B.fund) (F : Fin m → B.I.GA → ℂ)
    (hF : ∀ i, IsContRep B (y i) (F i)) (c : Fin m → ℂ) :
    IsContRep B (∑ i, c i • y i) (fun x => ∑ i, c i * F i x) := by
  refine ⟨continuous_finset_sum _ fun i _ => continuous_const.mul (hF i).1, fun γ hγ x => ?_, ?_⟩
  · exact Finset.sum_congr rfl fun i _ => by rw [(hF i).2.1 γ hγ]
  · have h1 := Lp.coeFn_finsetSum (univ : Finset (Fin m)) (fun i => c i • y i)
    have h2 : ∀ᵐ x ∂((B.I.muA B.μf).restrict B.fund), ∀ i, (c i • y i : B.I.L2 B.μf B.fund) x = c i * F i x :=
      ae_all_iff.2 fun i => by
        filter_upwards [Lp.coeFn_smul (c i) (y i), (hF i).2.2] with x hx hx'
        rw [hx, Pi.smul_apply, hx', smul_eq_mul]
    filter_upwards [h1, h2] with x hx hx'
    rw [hx, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => hx' i

theorem reproducing_formula : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ), IsContRep B (T y) f → (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) ∧ (∃ Φ : B.I.GA → ℝ, Integrable Φ (B.I.muA B.μf) ∧ ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g) ∧ ∀ x, f x = ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
  intro B d h hd hn hdec hb hfin T hT y f hf
  obtain ⟨hT2, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨hl, -⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular B.I B.μf
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  obtain ⟨hp, htc, -, -⟩ := GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties B.I hn
  obtain ⟨hphc, hphb, hphi⟩ := GlobalTheory.T.discrete_series_coefficient_integrable_majorant B d h hd hdec
  have hec : Continuous B.e := (GlobalTheory.rowsAut_idem_elementary B).2.2.2
  have hb' : HBig B 32 h := fun v => le_trans (by
    have : 0 ≤ (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by positivity
    nlinarith) (hb v)
  obtain ⟨u, F, -, hsp, hF, -, -, -, hbd⟩ := GlobalTheory.T.kernelB' B d h hd hn hdec hb' hfin T hT
  have hmem : T y ∈ Submodule.span ℂ (Set.range u) := by rw [hsp]; exact ⟨y, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  obtain ⟨hext, huniq, -⟩ := GlobalTheory.ExtContRep.ext_ae_eq_contRep B (T y) f hf
  have hfe : (fun x => ∑ i, c i * F i x) = f := huniq _ (hc ▸ isContRep_sum B u F hF c)
  set N := 2 * B.I.n ^ 2 * B.I.f with hN
  have hτ : ∀ x, 0 ≤ (tau1 B.I x)⁻¹ ^ N := fun x => pow_nonneg (inv_pos.2 (hp x)).le _
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ N := by
    refine ⟨Real.sqrt ((∑ i, ‖c i‖ ^ 2) * kerC B d), Real.sqrt_nonneg _, fun x => ?_⟩
    have h1 := hbd c x
    rw [congrFun hfe x, show 4 * B.I.n ^ 2 * B.I.f = N * 2 by rw [hN]; ring, pow_mul, ← mul_assoc] at h1
    have h2 := Real.le_sqrt_of_sq_le h1
    rwa [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (hτ x)] at h2
  let Φ : B.I.GA → ℝ := fun g =>
    C * (majPh B d h g.1 * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1) * ‖B.e g.2‖)
  have hm0 : ∀ g, 0 ≤ majPh B d h g := fun g => (norm_nonneg _).trans (hphb g)
  have hΦ0 : ∀ g, 0 ≤ Φ g := fun g =>
    mul_nonneg hC0 (mul_nonneg (mul_nonneg (hm0 _) (Real.exp_pos _).le) (norm_nonneg _))
  have hΦi : Integrable Φ (B.I.muA B.μf) :=
    (Integrable.mul_prod (hphi _ (by positivity) (weight_condition B h _ hn hb le_rfl))
      B.Re_spec.1.norm).const_mul C
  have hΦ : ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ N * Φ g := by
    intro x g
    by_cases he : B.e g.2 = 0
    · rw [phe, he, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg (hτ x) (hΦ0 g)
    have hg : g.2 ∈ B.I.Kset := B.e_adm.2.2.2.2.1 _ he
    have h1 := (hC (x * g)).trans (mul_le_mul_of_nonneg_left (inv_tau_pow_le B.I hn x g hg) hC0)
    rw [norm_mul, phe, norm_mul]
    calc _ ≤ (majPh B d h g.1 * ‖B.e g.2‖) *
          (C * ((tau1 B.I x)⁻¹ ^ N * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hphb _) (norm_nonneg _)) h1 (norm_nonneg _)
            (mul_nonneg (hm0 _) (norm_nonneg _))
      _ = _ := by simp only [Φ]; ring
  refine ⟨⟨C, hC⟩, ⟨Φ, hΦi, hΦ⟩, fun x => (congrFun (huniq (fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf))
    ⟨?_, fun γ hγ x => ?_, ?_⟩) x).symm⟩
  · have hpc : Continuous (phe B d) := (hphc.comp continuous_fst).mul (hec.comp continuous_snd)
    have htN : Continuous fun x => (tau1 B.I x)⁻¹ ^ N := (htc.inv₀ fun x => (hp x).ne').pow _
    refine continuous_iff_continuousAt.2 fun x₀ => ?_
    refine continuousAt_of_dominated (bound := fun g => ((tau1 B.I x₀)⁻¹ ^ N + 1) * Φ g)
      (Filter.Eventually.of_forall fun x => ?_) ?_ (hΦi.const_mul _) (Filter.Eventually.of_forall fun g => ?_)
    · exact (hpc.mul (hf.1.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    · filter_upwards [htN.continuousAt.eventually_lt continuousAt_const (lt_add_one ((tau1 B.I x₀)⁻¹ ^ N))]
        with x hx
      exact Filter.Eventually.of_forall fun g => (hΦ x g).trans (mul_le_mul_of_nonneg_right hx.le (hΦ0 g))
    · exact (continuous_const.mul (hf.1.comp (continuous_id.mul continuous_const))).continuousAt
  · simp only [mul_assoc, hf.2.1 γ hγ]
  · have hi : Integrable (ph B d) (muInf B.I) := by
      refine (hphi 0 le_rfl (weight_condition B h _ hn hb (by positivity))).mono' hphc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun g => ?_)
      simpa using hphb g
    have hproj := ((GlobalTheory.T.globalConvolutionOrthogonalProjector_proof B d hd hi).2.2.2 T hT).1
    have hTT : T (T y) = T y := congrArg (fun A : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => A y) hproj.1
    have h1 := (GlobalTheory.ConvKernel.rconv_eq_integral B _ T hT (T y)).2
    rw [hTT] at h1
    refine h1.trans (Filter.Eventually.of_forall fun x => integral_congr_ae ?_)
    filter_upwards [(measurePreserving_mul_left (B.I.muA B.μf) x).quasiMeasurePreserving.ae hext] with g hg
    rw [hg]

end GlobalTheory.Reproducing
