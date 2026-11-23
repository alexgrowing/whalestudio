import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.GeoRatio
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.FarSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.RootDecay
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.ContinuousLeviUnipotentPath
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.CtVanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.UnipMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.BlkCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LocFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PolyBdAll
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem pow_arith (c : ℝ) (hc : 0 < c) (A B : ℕ) :
    ∃ k : ℕ, ∀ y u : ℝ, 1 ≤ y → 0 ≤ u → u ≤ (y ^ c)⁻¹ → u ^ k * y ^ A ≤ (y ^ B)⁻¹ := by
  obtain ⟨k, hk⟩ := exists_nat_ge (((A : ℝ) + B) / c)
  refine ⟨k, fun y u hy hu huy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hk' : (A : ℝ) + B ≤ c * k := by
    rw [div_le_iff₀ hc] at hk
    linarith
  have h1 : u ^ k ≤ ((y ^ c)⁻¹) ^ k := pow_le_pow_left₀ hu huy k
  have h2 : ((y ^ c)⁻¹) ^ k = (y ^ (c * k))⁻¹ := by
    rw [inv_pow, ← Real.rpow_natCast (y ^ c), ← Real.rpow_mul hy0.le]
  have h3 : y ^ ((A : ℝ) + B) ≤ y ^ (c * k) := Real.rpow_le_rpow_of_exponent_le hy hk'
  have h4 : y ^ ((A : ℝ) + B) = y ^ A * y ^ B := by
    rw [Real.rpow_add hy0, Real.rpow_natCast, Real.rpow_natCast]
  have hyA : 0 < y ^ A := pow_pos hy0 A
  have hyB : 0 < y ^ B := pow_pos hy0 B
  have h5 : (y ^ (c * k))⁻¹ ≤ (y ^ A * y ^ B)⁻¹ := by
    rw [← h4]
    exact inv_anti₀ (Real.rpow_pos_of_pos hy0 _) h3
  calc u ^ k * y ^ A ≤ (y ^ A * y ^ B)⁻¹ * y ^ A :=
        mul_le_mul_of_nonneg_right ((h2 ▸ h1).trans h5) hyA.le
    _ = (y ^ B)⁻¹ := by field_simp

private theorem pow_arith2 (c : ℝ) (hc : 0 < c) (N N' : ℕ) :
    ∃ k : ℕ, ∀ y R u : ℝ, 1 ≤ y → 1 ≤ R → y ^ c ≤ R → 0 ≤ u → u ≤ (R ^ c)⁻¹ →
      u ^ k * R ^ N ≤ (y ^ N')⁻¹ := by
  obtain ⟨B, hB⟩ := exists_nat_ge ((N' : ℝ) / c)
  obtain ⟨k, hk⟩ := pow_arith c hc N B
  refine ⟨k, fun y R u hy hR hyR hu huR => (hk R u hR hu huR).trans ?_⟩
  have hy0 : 0 < y := by linarith
  have hB' : (N' : ℝ) ≤ c * B := by
    rw [div_le_iff₀ hc] at hB
    linarith
  have h1 : y ^ N' ≤ (y ^ c) ^ B := by
    rw [← Real.rpow_natCast y N', ← Real.rpow_natCast (y ^ c) B, ← Real.rpow_mul hy0.le]
    exact Real.rpow_le_rpow_of_exponent_le hy hB'
  have h2 : (y ^ c) ^ B ≤ R ^ B := pow_le_pow_left₀ (Real.rpow_nonneg hy0.le _) hyR B
  exact inv_anti₀ (pow_pos hy0 _) (h1.trans h2)

section

variable {K : Type} [Field K] [NumberField K]

private theorem sec_norm_le {d : ℕ} (sec : Eu d →ₗ[ℂ] (G1 K (2 + 2) → ℂ)) (U : ℝ → Eu d) (B : ℝ)
    (hU : ∀ s, ‖U s‖ ≤ B) (z : G1 K (2 + 2)) :
    ‖secF sec U z‖ ≤ B * ∑ i, Real.exp (2 * HH z) * ‖sec (EuclideanSpace.basisFun (Fin d) ℂ i) z‖ := by
  set b := EuclideanSpace.basisFun (Fin d) ℂ with hb
  set v := U (HH z) with hv
  have hsum : sec v z = ∑ i, b.repr v i * sec (b i) z := by
    conv_lhs => rw [← b.sum_repr v]
    simp [map_sum, Finset.sum_apply]
  have hc : ∀ i, ‖b.repr v i‖ ≤ B := fun i =>
    (PiLp.norm_apply_le (b.repr v) i).trans ((b.repr.norm_map v).le.trans (hU _))
  have hexp : ‖Complex.exp (2 * (HH z : ℂ))‖ = Real.exp (2 * HH z) := by
    rw [Complex.norm_exp]
    simp
  unfold secF
  rw [norm_mul, hexp, hsum]
  have h : ‖∑ i, b.repr v i * sec (b i) z‖ ≤ ∑ i, B * ‖sec (b i) z‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _))
  calc Real.exp (2 * HH z) * ‖∑ i, b.repr v i * sec (b i) z‖
      ≤ Real.exp (2 * HH z) * ∑ i, B * ‖sec (b i) z‖ :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = B * ∑ i, Real.exp (2 * HH z) * ‖sec (b i) z‖ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring

private theorem far_fam {ι : Type} [Fintype ι] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ) (hR : Red ω t)
    (f : ι → G1 K (2 + 2) → ℂ) (hf : ∀ i, SFun (f i)) :
    (∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)), (∀ q ∈ S, 0 ≤ HH (qx q x)) →
        ∑ q ∈ S, ∑ i, Real.exp (2 * HH (qx q x)) * ‖f i (qx q x)‖ ≤ C * qht x ^ N) ∧
      ∀ (ε : ℝ) (N' : ℕ), 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)),
        (∀ q ∈ S, 0 ≤ HH (qx q x) ∧ Far ω t ε (qx q x)) →
        ∑ q ∈ S, ∑ i, Real.exp (2 * HH (qx q x)) * ‖f i (qx q x)‖ ≤ C * (qht x ^ N')⁻¹ := by
  have hq1 : ∀ x : G1 K (2 + 2), 1 ≤ qht x := (qhtBasic K (2 + 2)).1
  constructor
  · choose C N hC using fun i => (farSum ω t hR (f i) (hf i)).1
    refine ⟨∑ i, |C i|, ∑ i, N i, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun x S hS => ?_⟩
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => (hC i x S hS).trans ?_
    have h0 : (0 : ℝ) < qht x ^ N i := pow_pos (by linarith [hq1 x]) _
    have h1 : qht x ^ N i ≤ qht x ^ ∑ i, N i :=
      pow_le_pow_right₀ (hq1 x) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) h0.le).trans
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
  · intro ε N' hε
    choose C hC using fun i => (farSum ω t hR (f i) (hf i)).2 ε N' hε
    refine ⟨∑ i, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun x S hS => ?_⟩
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => (hC i x S hS).trans ?_
    have h0 : (0 : ℝ) ≤ (qht x ^ N')⁻¹ := inv_nonneg.2 (pow_nonneg (by linarith [hq1 x]) _)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) h0

private theorem th_hi_eq (T : ℝ) (F : G1 K (2 + 2) → ℂ) (x : G1 K (2 + 2)) :
    ∃ S : Finset (Cos K), (∀ q, q ∈ S ↔ T < HH (qx q x)) ∧ th (hi T F) x = ∑ q ∈ S, F (qx q x) := by
  have hfin : {q : Cos K | T < HH (qx q x)}.Finite :=
    (locFin {x} T isCompact_singleton).subset fun q hq => ⟨x, rfl, le_of_lt hq⟩
  refine ⟨hfin.toFinset, fun q => by simp, ?_⟩
  unfold th
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · refine Finset.sum_congr rfl fun q hq => ?_
    have : T < HH (qx q x) := by simpa using hq
    exact Set.indicator_of_mem (s := {z : G1 K (2 + 2) | T < HH z}) this F
  · intro q hq
    by_contra hn
    have hn' : ¬ T < HH (qx q x) := by simpa using hn
    exact hq (Set.indicator_of_notMem (s := {z : G1 K (2 + 2) | T < HH z}) hn' F)

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.mainBd :
    ForAllC fun K _ _ μ _ _ _ _ _ D _ _ A A' => ∀ (a : CC K (2 + 2)) (P : L2 μ →L[ℂ] L2 μ), IsOrthogonalProjectionTwoLines A.J A'.J P → IsLeftSmooth a → D.Hecke a → ∀ N' : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : ℝ) (x : G1 K (2 + 2)) (φ : L2 μ), 0 ≤ T → P φ = φ → ¬ Om T x → ‖lam T (rc μ a φ) x‖ ≤ C * (qht x ^ N')⁻¹ * ‖φ‖ := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' a P hP ha hD N'
  classical
  obtain ⟨ω, t, hR⟩ := redEx (K := K)
  have hq1 : ∀ x : G1 K (2 + 2), 1 ≤ qht x := (qhtBasic K (2 + 2)).1
  have hfA : ∀ i, SFun (A.sec (EuclideanSpace.basisFun (Fin d) ℂ i)) := fun i => by
    have h := (A.onto (A.sec (EuclideanSpace.basisFun (Fin d) ℂ i))).1 ⟨_, rfl⟩
    exact secFun μ₂ τ₁ τ₂ D hp.irr₁ hp.irr₂ _ h.1 h.2
  have hfB : ∀ i, SFun (A'.sec (EuclideanSpace.basisFun (Fin d') ℂ i)) := fun i => by
    have h := (A'.onto (A'.sec (EuclideanSpace.basisFun (Fin d') ℂ i))).1 ⟨_, rfl⟩
    exact secFun μ₂ τ₂ τ₁ D hp.irr₂ hp.irr₁ _ h.1 h.2
  obtain ⟨⟨Ca, Na, hCa, hNa⟩, hFarA⟩ := far_fam ω t hR _ hfA
  obtain ⟨⟨Cb, Nb, hCb, hNb⟩, hFarB⟩ := far_fam ω t hR _ hfB
  obtain ⟨C₀, hC₀⟩ := ctRep K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP hD

  set G : G1 K (2 + 2) → ℝ := fun z =>
    (∑ i, Real.exp (2 * HH z) * ‖A.sec (EuclideanSpace.basisFun (Fin d) ℂ i) z‖) +
      ∑ i, Real.exp (2 * HH z) * ‖A'.sec (EuclideanSpace.basisFun (Fin d') ℂ i) z‖ with hG
  have hct : ∀ φ, P φ = φ → ∀ z, ‖ct 2 (rc μ a φ) z‖ ≤ |C₀| * ‖φ‖ * G z := by
    intro φ hφ z
    obtain ⟨U, U', -, -, hU, -, -, hrep⟩ := hC₀ φ hφ
    have hB : ∀ s, ‖U s‖ ≤ |C₀| * ‖φ‖ ∧ ‖U' s‖ ≤ |C₀| * ‖φ‖ := fun s =>
      ⟨(hU s).1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)),
        (hU s).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))⟩
    rw [hrep z, hG]
    simp only [mul_add]
    exact (norm_add_le _ _).trans (add_le_add (sec_norm_le _ U _ (fun s => (hB s).1) z)
      (sec_norm_le _ U' _ (fun s => (hB s).2) z))
  have hsum : ∀ φ, P φ = φ → ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)),
      ‖∑ q ∈ S, ct 2 (rc μ a φ) (qx q x)‖ ≤ |C₀| * ‖φ‖ * ∑ q ∈ S, G (qx q x) := by
    intro φ hφ x S
    rw [Finset.mul_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => hct φ hφ _)
  obtain ⟨ε, c, Q, M, hε, hc, hgeo⟩ := geo ω t hR
  obtain ⟨CA, hCA, hA⟩ := hFarA ε N' hε
  obtain ⟨CB, hCB, hB⟩ := hFarB ε N' hε
  obtain ⟨Cp, Np, hpoly⟩ := polyBdAll K (2 + 2) μ a
  obtain ⟨N₂, h₂⟩ := rootDecay μ a ha ω t hR.bor hR.pos 2 (by norm_num) (by norm_num)
  obtain ⟨N₁, h₁⟩ := rootDecay μ a ha ω t hR.bor hR.pos 1 (by norm_num) (by norm_num)
  obtain ⟨N₃, h₃⟩ := rootDecay μ a ha ω t hR.bor hR.pos 3 (by norm_num) (by norm_num)
  obtain ⟨k₂, hk₂⟩ := pow_arith c hc (M * N₂) N'
  obtain ⟨k₁, hk₁⟩ := pow_arith2 c hc N₁ N'
  obtain ⟨k₃, hk₃⟩ := pow_arith2 c hc N₃ N'
  obtain ⟨D₂, hD₂⟩ := h₂ k₂
  obtain ⟨D₁, hD₁⟩ := h₁ k₁
  obtain ⟨D₃, hD₃⟩ := h₃ k₃
  have hvan := (ctVanish K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP).1

  set E : ℝ := |C₀| * (CA + CB) with hE
  have hE0 : 0 ≤ E := mul_nonneg (abs_nonneg _) (add_nonneg hCA hCB)
  have hfar : ∀ φ, P φ = φ → ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)),
      (∀ q ∈ S, 0 ≤ HH (qx q x) ∧ Far ω t ε (qx q x)) →
      ‖∑ q ∈ S, ct 2 (rc μ a φ) (qx q x)‖ ≤ E * (qht x ^ N')⁻¹ * ‖φ‖ := by
    intro φ hφ x S hS
    refine (hsum φ hφ x S).trans ?_
    have h : ∑ q ∈ S, G (qx q x) ≤ (CA + CB) * (qht x ^ N')⁻¹ := by
      rw [hG]
      simp only [Finset.sum_add_distrib, add_mul]
      exact add_le_add (hA x S hS) (hB x S hS)
    calc |C₀| * ‖φ‖ * ∑ q ∈ S, G (qx q x) ≤ |C₀| * ‖φ‖ * ((CA + CB) * (qht x ^ N')⁻¹) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg _) (norm_nonneg _))
      _ = E * (qht x ^ N')⁻¹ * ‖φ‖ := by rw [hE]; ring

  set Q' : ℝ := max Q 1 with hQ'
  have hQ1 : 1 ≤ Q' := le_max_right _ _
  set Cs : ℝ := (|Cp| * Q' ^ Np + |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb)) * Q' ^ N' with hCs
  have hCs0 : 0 ≤ Cs := by
    have : (0 : ℝ) ≤ Q' := by linarith
    positivity
  refine ⟨Cs + (|D₁| + |D₂| + |D₃|) + E, by positivity, fun T x φ hT hφ hOm => ?_⟩
  set y := qht x with hy
  have hy1 : 1 ≤ y := hq1 x
  have hy0 : 0 < y := by linarith
  have hyi : 0 < (y ^ N')⁻¹ := inv_pos.2 (pow_pos hy0 _)
  have hn0 : 0 ≤ ‖φ‖ := norm_nonneg _
  set ψ := rc μ a φ with hψ
  obtain ⟨S, hS, hth⟩ := th_hi_eq T (ct 2 ψ) x
  obtain ⟨-, -, hGam₀, hPK₀, -⟩ := (ctKv μ a).2 φ
  have hGam : ∀ γ ∈ Gam K (2 + 2), ∀ x, ψ (γ * x) = ψ x := hGam₀
  have hPK : ∀ γ ∈ PK K, ∀ z, ct 2 ψ (γ * z) = ct 2 ψ z := hPK₀
  have hlam : lam T ψ x = ψ x - ∑ q ∈ S, ct 2 ψ (qx q x) := by
    rw [lam, hth]
  rw [hlam]
  have hHH : ∀ q ∈ S, 0 ≤ HH (qx q x) := fun q hq => hT.trans ((hS q).1 hq).le
  by_cases hQ : y < Q
  ·
    have hyQ : y ≤ Q' := hQ.le.trans (le_max_left _ _)
    have hpw : ∀ n : ℕ, y ^ n ≤ Q' ^ n := fun n => pow_le_pow_left₀ hy0.le hyQ n
    have h1 : ‖ψ x‖ ≤ |Cp| * Q' ^ Np * ‖φ‖ := by
      refine (hpoly φ x).trans (mul_le_mul_of_nonneg_right ?_ hn0)
      exact (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_pos hy0 _).le).trans
        (mul_le_mul_of_nonneg_left (hpw _) (abs_nonneg _))
    have h2 : ‖∑ q ∈ S, ct 2 ψ (qx q x)‖ ≤ |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb) * ‖φ‖ := by
      refine (hsum φ hφ x S).trans ?_
      have h : ∑ q ∈ S, G (qx q x) ≤ Ca * Q' ^ Na + Cb * Q' ^ Nb := by
        rw [hG]
        simp only [Finset.sum_add_distrib]
        exact add_le_add ((hNa x S hHH).trans (mul_le_mul_of_nonneg_left (hpw _) hCa))
          ((hNb x S hHH).trans (mul_le_mul_of_nonneg_left (hpw _) hCb))
      calc |C₀| * ‖φ‖ * ∑ q ∈ S, G (qx q x) ≤ |C₀| * ‖φ‖ * (Ca * Q' ^ Na + Cb * Q' ^ Nb) :=
            mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg _) hn0)
        _ = _ := by ring
    have h3 : 1 ≤ Q' ^ N' * (y ^ N')⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div (pow_pos hy0 _)]
      exact hpw _
    have hB0 : 0 ≤ |Cp| * Q' ^ Np + |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb) := by
      have : (0 : ℝ) ≤ Q' := by linarith
      positivity
    calc ‖ψ x - ∑ q ∈ S, ct 2 ψ (qx q x)‖
        ≤ (|Cp| * Q' ^ Np + |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb)) * ‖φ‖ := by
          rw [add_mul]
          exact (norm_sub_le _ _).trans (add_le_add h1 h2)
      _ ≤ (|Cp| * Q' ^ Np + |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb)) * (Q' ^ N' * (y ^ N')⁻¹) * ‖φ‖ :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hB0 h3) hn0
      _ = Cs * (y ^ N')⁻¹ * ‖φ‖ := by rw [hCs]; ring
      _ ≤ (Cs + (|D₁| + |D₂| + |D₃|) + E) * (y ^ N')⁻¹ * ‖φ‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hyi.le) hn0
          have := abs_nonneg D₁
          have := abs_nonneg D₂
          have := abs_nonneg D₃
          linarith
  · have hQy : Q ≤ y := not_lt.1 hQ

    have fin : ∀ (Dc : ℝ) (w : ℂ) (S' : Finset (Cos K)), |Dc| ≤ |D₁| + |D₂| + |D₃| →
        ‖w‖ ≤ |Dc| * (y ^ N')⁻¹ * ‖φ‖ → ‖∑ q ∈ S', ct 2 ψ (qx q x)‖ ≤ E * (y ^ N')⁻¹ * ‖φ‖ →
        ‖w‖ + ‖∑ q ∈ S', ct 2 ψ (qx q x)‖ ≤ (Cs + (|D₁| + |D₂| + |D₃|) + E) * (y ^ N')⁻¹ * ‖φ‖ := by
      intro Dc w S' hDc h1 h2
      have h3 : (|Dc| + E) * (y ^ N')⁻¹ * ‖φ‖ ≤ (Cs + (|D₁| + |D₂| + |D₃|) + E) * (y ^ N')⁻¹ * ‖φ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hyi.le) hn0
      have h4 : (|Dc| + E) * (y ^ N')⁻¹ * ‖φ‖ = |Dc| * (y ^ N')⁻¹ * ‖φ‖ + E * (y ^ N')⁻¹ * ‖φ‖ := by ring
      linarith
    have scale : ∀ Dc v : ℝ, 0 ≤ v → v ≤ (y ^ N')⁻¹ → Dc * v * ‖φ‖ ≤ |Dc| * (y ^ N')⁻¹ * ‖φ‖ := by
      intro Dc v hv0 hv
      refine mul_le_mul_of_nonneg_right ?_ hn0
      exact (mul_le_mul_of_nonneg_right (le_abs_self _) hv0).trans
        (mul_le_mul_of_nonneg_left hv (abs_nonneg _))
    have hd1 : |D₁| ≤ |D₁| + |D₂| + |D₃| := by
      have := abs_nonneg D₂
      have := abs_nonneg D₃
      linarith
    have hd2 : |D₂| ≤ |D₁| + |D₂| + |D₃| := by
      have := abs_nonneg D₁
      have := abs_nonneg D₃
      linarith
    have hd3 : |D₃| ≤ |D₁| + |D₂| + |D₃| := by
      have := abs_nonneg D₁
      have := abs_nonneg D₂
      linarith
    rcases hgeo T x hT hQy hOm with ⟨q₀, δ, hδ, ρ, hSg, hFull, hTq, hratio, hRat, hoth⟩ | ⟨γ, hγ, ρ, R, hSg, hFull, hR1, hRat, hyR, hcase, hoth⟩
    ·
      obtain ⟨hρ, -⟩ := id hSg
      have hq₀ : q₀ ∈ S := (hS q₀).2 hTq
      rw [← Finset.add_sum_erase S _ hq₀]
      have hδG : δ ∈ Gam K (2 + 2) := by
        obtain ⟨p, -, rfl⟩ := hδ
        exact p.2
      have e1 : ψ x = ψ (δ * qx q₀ x) := by
        rw [hGam δ hδG, hGam _ q₀.out.2]
      have e2 : ct 2 ψ (qx q₀ x) = ct 2 ψ (δ * qx q₀ x) := (hPK δ hδ _).symm
      have hb : ‖ψ (δ * qx q₀ x) - ct 2 ψ (δ * qx q₀ x)‖ ≤
          D₂ * (ρ 2 / ρ 1) ^ k₂ * (y ^ M) ^ N₂ * ‖φ‖ :=
        hD₂ φ ρ _ (y ^ M) hSg hFull (one_le_pow₀ hy1) hRat
      have hu0 : 0 ≤ ρ 2 / ρ 1 := (div_pos (hρ 2) (hρ 1)).le
      have hu : ρ 2 / ρ 1 ≤ (y ^ c)⁻¹ := by
        rw [← inv_div (ρ 1) (ρ 2)]
        exact inv_anti₀ (Real.rpow_pos_of_pos hy0 _) hratio
      have hv := hk₂ y _ hy1 hu0 hu
      rw [pow_mul y M N₂] at hv
      have hb' : ‖ψ (δ * qx q₀ x) - ct 2 ψ (δ * qx q₀ x)‖ ≤ |D₂| * (y ^ N')⁻¹ * ‖φ‖ := by
        refine hb.trans ?_
        rw [mul_assoc D₂]
        exact scale _ _ (mul_nonneg (pow_nonneg hu0 _) (pow_pos (pow_pos hy0 _) _).le) hv
      have hd : ‖ψ x - (ct 2 ψ (qx q₀ x) + ∑ q ∈ S.erase q₀, ct 2 ψ (qx q x))‖ ≤
          ‖ψ (δ * qx q₀ x) - ct 2 ψ (δ * qx q₀ x)‖ + ‖∑ q ∈ S.erase q₀, ct 2 ψ (qx q x)‖ := by
        rw [e2, ← sub_sub, ← e1]
        exact norm_sub_le _ _
      exact hd.trans (fin D₂ _ _ hd2 hb' (hfar φ hφ x _ fun q hq =>
        ⟨hHH q (Finset.mem_of_mem_erase hq),
          hoth q (Finset.ne_of_mem_erase hq) ((hS q).1 (Finset.mem_of_mem_erase hq))⟩))
    ·
      obtain ⟨hρ, -⟩ := id hSg
      have e1 : ψ x = ψ (γ * x) := (hGam γ hγ x).symm
      have htail := hfar φ hφ x S fun q hq => ⟨hHH q hq, hoth q ((hS q).1 hq)⟩
      rw [e1]
      rcases hcase with hc1 | hc3
      · have hb : ‖ψ (γ * x) - ct 1 ψ (γ * x)‖ ≤ D₁ * (ρ 1 / ρ 0) ^ k₁ * R ^ N₁ * ‖φ‖ :=
          hD₁ φ ρ _ R hSg hFull hR1 hRat
        rw [(hvan φ hφ _).1, sub_zero] at hb
        have hu0 : 0 ≤ ρ 1 / ρ 0 := (div_pos (hρ 1) (hρ 0)).le
        have hu : ρ 1 / ρ 0 ≤ (R ^ c)⁻¹ := by
          rw [← inv_div (ρ 0) (ρ 1)]
          exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _) hc1
        have hv := hk₁ y R _ hy1 hR1 hyR hu0 hu
        have hb' : ‖ψ (γ * x)‖ ≤ |D₁| * (y ^ N')⁻¹ * ‖φ‖ := by
          refine hb.trans ?_
          rw [mul_assoc D₁]
          exact scale _ _ (mul_nonneg (pow_nonneg hu0 _) (pow_nonneg (by linarith) _)) hv
        exact (norm_sub_le _ _).trans (fin D₁ _ _ hd1 hb' htail)
      · have hb : ‖ψ (γ * x) - ct 3 ψ (γ * x)‖ ≤ D₃ * (ρ 3 / ρ 2) ^ k₃ * R ^ N₃ * ‖φ‖ :=
          hD₃ φ ρ _ R hSg hFull hR1 hRat
        rw [(hvan φ hφ _).2, sub_zero] at hb
        have hu0 : 0 ≤ ρ 3 / ρ 2 := (div_pos (hρ 3) (hρ 2)).le
        have hu : ρ 3 / ρ 2 ≤ (R ^ c)⁻¹ := by
          rw [← inv_div (ρ 2) (ρ 3)]
          exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _) hc3
        have hv := hk₃ y R _ hy1 hR1 hyR hu0 hu
        have hb' : ‖ψ (γ * x)‖ ≤ |D₃| * (y ^ N')⁻¹ * ‖φ‖ := by
          refine hb.trans ?_
          rw [mul_assoc D₃]
          exact scale _ _ (mul_nonneg (pow_nonneg hu0 _) (pow_nonneg (by linarith) _)) hv
        exact (norm_sub_le _ _).trans (fin D₃ _ _ hd3 hb' htail)
