import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IteratedFDerivCombMem
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MeasureOfProducts
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSumProdLeOfCoord
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DifferentiableU1
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLawsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeHeisenbergRelationsOneVariableStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaVectorsSetupExistsEqSmulStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HeisenbergOperatorsOrthogonalFrameCoordsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsOrthogonalFrameNormsCoprimeOfUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmThetaOperatorInvariantOfLiftCongrOneStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPadicIntFrameChangeEtaleBasisStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmThetaEqSumProdTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorsionLiftPairingInOrthogonalFrameStatement

open PowerSeries GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators Topology

noncomputable section
namespace GlobalTheory.MomOne.Translates

theorem eq_zero_of_jets {g : ℕ} (Φ : (Fin g → ℂ) → ℂ) (hΦ : ContDiff ℂ ⊤ Φ) (δ : ℂ) (hδ : δ ≠ 0)
    (h : ∀ (k : ℕ) (σ : Fin k → Fin g),
      iteratedFDeriv ℂ k Φ 0 (fun l => δ⁻¹ • (Pi.single (σ l) 1 : Fin g → ℂ)) = 0) : Φ = 0 := by
  have hz : ∀ k, iteratedFDeriv ℂ k Φ 0 = 0 := by
    intro k
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    refine Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ (Fin g)) fun σ => ?_
    have := h k σ
    rw [ContinuousMultilinearMap.map_smul_univ] at this
    simp only [smul_eq_mul, mul_eq_zero, Finset.prod_eq_zero_iff, _root_.inv_eq_zero, hδ, and_false, exists_false,
      false_or] at this
    simpa using this
  have ha : AnalyticOnNhd ℂ Φ Set.univ := fun x _ => hΦ.contDiffAt.analyticAt
  obtain ⟨p, r, hp⟩ := ha 0 trivial
  have hev : Φ =ᶠ[𝓝 0] 0 := by
    filter_upwards [Metric.eball_mem_nhds (0 : Fin g → ℂ) hp.r_pos] with y hy
    have := hp.hasSum_iteratedFDeriv hy
    simp only [hz, zero_apply, smul_zero, zero_add] at this
    exact this.unique hasSum_zero
  exact ha.eq_of_eventuallyEq analyticOnNhd_const hev

def compIso {X Y K : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y]
    [NormedField K] (T : X ≃ₜ Y) : C(X, K) ≃ₗᵢ[K] C(Y, K) where
  toFun f := f.comp (T.symm : C(Y, X))
  invFun f := f.comp (T : C(X, Y))
  map_add' f g := rfl
  map_smul' c f := rfl
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  norm_map' f := by
    apply le_antisymm
    · exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun y => f.norm_coe_le_norm _
    · refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
      have := (f.comp (T.symm : C(Y, X))).norm_coe_le_norm (T x)
      simpa using this

theorem inOK_add {d : ℕ} {α β : ℂ} (h : InOK d α) (h' : InOK d β) : InOK d (α + β) := by
  obtain ⟨u, v, rfl⟩ := h
  obtain ⟨u', v', rfl⟩ := h'
  exact ⟨u + u', v + v', by push_cast; ring⟩

theorem inOK_nat_mul {d : ℕ} {α : ℂ} (n : ℕ) (h : InOK d α) : InOK d (n * α) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨n * u, n * v, by push_cast; ring⟩

theorem primeTo_add {d q : ℕ} {α β : ℂ} (h : PrimeTo d q α) (h' : PrimeTo d q β) : PrimeTo d q (α + β) := by
  obtain ⟨s, hs, hc, h⟩ := h
  obtain ⟨s', hs', hc', h'⟩ := h'
  refine ⟨s * s', by positivity, Nat.Coprime.mul_left hc hc', ?_⟩
  have := inOK_add (inOK_nat_mul s' h) (inOK_nat_mul s h')
  convert this using 1
  push_cast; ring

theorem primeTo_neg {d q : ℕ} {α : ℂ} (h : PrimeTo d q α) : PrimeTo d q (-α) := by
  obtain ⟨s, hs, hc, u, v, h⟩ := h
  exact ⟨s, hs, hc, -u, -v, by push_cast; linear_combination -h⟩

theorem primeTo_common {d q : ℕ} {I : Type} [Fintype I] (t : I → ℂ) (h : ∀ i, PrimeTo d q (t i)) :
    ∃ s : ℕ, Nat.Coprime s q ∧ ∀ i, InOK d ((s : ℂ) * t i) := by
  classical
  choose s hs hc h using h
  refine ⟨∏ i, s i, Nat.Coprime.prod_left fun i _ => hc i, fun i => ?_⟩
  obtain ⟨k, hk⟩ : s i ∣ ∏ i, s i := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have := inOK_nat_mul k (h i)
  rw [hk]
  convert this using 1
  push_cast; ring

def rho (d : ℕ) (x y : ℂ) : ℂ := Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d x y).im : ℝ) : ℂ))

theorem rho_mem {d q : ℕ} (hOK : ∀ x y, InOK d x → InOK d y → ∃ k : ℤ, (h1 d x y).im = k) {x y : ℂ}
    (hx : PrimeTo d q x) (hy : PrimeTo d q y) : rho d x y ∈ algebraicClosure ℚ ℂ := by
  obtain ⟨s, hs, -, hx⟩ := hx
  obtain ⟨s', hs', -, hy⟩ := hy
  obtain ⟨k, hk⟩ := hOK _ _ hx hy
  have e : h1 d (s * x) (s' * y) = ((s * s' : ℝ) : ℂ) * h1 d x y := by
    simp only [h1, map_mul, Complex.conj_natCast]; push_cast; ring
  rw [e, Complex.im_ofReal_mul] at hk
  have hk' : ((s : ℂ) * s') * (((h1 d x y).im : ℝ) : ℂ) = k := by exact_mod_cast hk
  have hp : rho d x y ^ (2 * s * s') = 1 := by
    rw [rho, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨-k, ?_⟩
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * Complex.I) * hk'
  rw [mem_algebraicClosure_iff]
  refine IsAlgebraic.of_pow (n := 2 * s * s') (by positivity) ?_
  rw [hp]; exact isAlgebraic_one

theorem thetaTranslation_comp_eq_cocycle_mul {d : ℕ} (hd : 0 < d) (x y : ℂ) (F : ℂ → ℂ) :
    U1 d x (U1 d y F) = fun z => rho d x y * U1 d (x + y) F z := (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd).1 x y F

theorem cmLatticeTranslationOperator_eq_phase_mul_neg_comp {d : ℕ} (hd : 0 < d) (x y : ℂ) (F : ℂ → ℂ) :
    U1 d y F = fun z => rho d x y * U1 d (-x) (U1 d (x + y) F) z := by
  have e1 : U1 d (-x) (U1 d x (U1 d y F)) = U1 d y F := by
    rw [thetaTranslation_comp_eq_cocycle_mul hd (-x) x, neg_add_cancel, (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd).2.1]
    have : (h1 d (-x) x).im = 0 := by
      rw [h1, Complex.im_ofReal_mul]; simp [mul_comm]
    simp [rho, this]
  rw [← e1, thetaTranslation_comp_eq_cocycle_mul hd x y]
  funext z
  simp only [U1]; ring

theorem cmLatticeWeylOperator_const_mul (d : ℕ) (y c : ℂ) (F : ℂ → ℂ) :
    W1 d y (fun z => c * F z) = fun z => c * W1 d y F z := by
  funext z; simp only [W1, U1]; ring

variable {q : ℕ} [Fact q.Prime]

theorem family_scale (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) {g m : ℕ} (a : Fin g → ℕ) (c : Fin m → ℂ)
    (ρ : Fin m → Fin g → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (hf : ∀ j i, Differentiable ℂ (f j i)) (ν : Fin g → ℕ) :
    ∑ j, ι (c j) * ∏ i, coeff (ν i) (hat ι (C ω * logS) (fun z => ρ j i * f j i z) ^ a i) =
      ∑ j, ι (c j * ∏ i, ρ j i ^ a i) * ∏ i, coeff (ν i) (hat ι (C ω * logS) (f j i) ^ a i) := by
  have h0 : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [map_mul, ← coeff_zero_eq_constantCoeff_apply logS]; simp [logS]
  obtain ⟨H1, H2, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ h0
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_prod, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(H1 (fun _ => ρ j i) (f j i) analyticAt_const ((hf j i).analyticAt 0)).2.1, H2, mul_pow,
    ← map_pow (C : ℂ_[q] →+* ℂ_[q]⟦X⟧), coeff_C_mul, map_pow ι]

theorem comb_translate {d : ℕ} (hd : 0 < d) {g m : ℕ} (a : Fin g → ℕ) (c : Fin m → ℂ) (t : Fin m → Fin g → ℂ)
    (τ y : Fin g → ℂ) (θ : ℂ → ℂ) :
    (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, W1 d (y i) (U1 d (τ i) (U1 d (t j i) θ)) (z i) ^ a i) =
      fun z => ∑ j, (c j * ∏ i, rho d (τ i) (t j i) ^ a i) * ∏ i, W1 d (y i) (U1 d (τ i + t j i) θ) (z i) ^ a i := by
  funext z
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [thetaTranslation_comp_eq_cocycle_mul hd, cmLatticeWeylOperator_const_mul, mul_pow]

theorem product_measures (d : ℕ) (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (Ω : ℂ_[q]) (θ : ℂ → ℂ) (hd : 0 < d) (hδ : δ ≠ 0)
    (hΩ : Ω ≠ 0) (hθ : Differentiable ℂ θ) (hL : ThetaLaws ι d (Ω / ι δ) θ) {g m : ℕ} (a : Fin g → ℕ)
    (c : Fin m → ℂ) (t : Fin m → Fin g → ℂ) (ht : ∀ j i, PrimeTo d q (t j i)) :
    ∃ N : ℝ, ∀ τ : Fin g → ℂ, (∀ i, PrimeTo d q (τ i)) →
      ∃ μ : C(Fin g → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q], ‖μ‖ = N ∧
        ∀ (n s : ℕ) (y : Fin g → ℂ), Nat.Coprime s q → (∀ j i, InOK d ((s : ℂ) * (τ i + t j i))) →
          (∀ i, Good ι d n s (y i)) → ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ) (F : C(Fin g → ℤ_[q], ℂ_[q])),
          (∀ A, F A = (∏ i, ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n (A i)).val) *
            ∏ l, (Ω⁻¹ * ∑ i, ι (ys l i) * GlobalTheory.MomOne.zc (A i))) →
          ι (iteratedFDeriv ℂ k (fun z : Fin g → ℂ =>
            ∑ j, c j * ∏ i, W1 d (y i) (U1 d (τ i) (U1 d (t j i) θ)) (z i) ^ a i) 0 (fun l => δ⁻¹ • ys l)) = μ F := by
  have hU : ∀ x F, Differentiable ℂ F → Differentiable ℂ (U1 d x F) := fun x F h =>
    ((GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd).2.2.1 x F h).1
  obtain ⟨μ₀, h₀, -⟩ := ProdMeasure.measure_of_products d q ι δ Ω θ hd hδ hΩ hθ hL g m a c t ht
  refine ⟨‖μ₀‖, fun τ hτ => ?_⟩
  have ht' : ∀ j i, PrimeTo d q (τ i + t j i) := fun j i => primeTo_add (hτ i) (ht j i)
  obtain ⟨μ, h₁, h₂⟩ := ProdMeasure.measure_of_products d q ι δ Ω θ hd hδ hΩ hθ hL g m a
    (fun j => c j * ∏ i, rho d (τ i) (t j i) ^ a i) (fun j i => τ i + t j i) ht'
  refine ⟨μ, le_antisymm ?_ ?_, fun n s y hs hst hy k ys F hF => ?_⟩
  · refine (h₁ _ (norm_nonneg _)).2 fun ν => ?_
    have := translate_norm_prod_le d q ι _ θ hL g m a (fun j => ι (c j)) t τ _ ht hτ
      ((h₀ _ (norm_nonneg _)).1 le_rfl) ν
    simp only [thetaTranslation_comp_eq_cocycle_mul hd] at this
    rwa [family_scale ι _ a c (fun j i => rho d (τ i) (t j i)) (fun j i => U1 d (τ i + t j i) θ)
      (fun j i => hU _ _ hθ)] at this
  · refine (h₀ _ (norm_nonneg _)).2 fun ν => ?_
    have := translate_norm_prod_le d q ι _ θ hL g m a _ (fun j i => τ i + t j i) (fun i => -τ i) _ ht'
      (fun i => primeTo_neg (hτ i)) ((h₁ _ (norm_nonneg _)).1 le_rfl) ν
    rw [← family_scale ι _ a c (fun j i => rho d (τ i) (t j i)) (fun j i => U1 d (-τ i) (U1 d (τ i + t j i) θ))
      (fun j i => hU _ _ (hU _ _ hθ))] at this
    simpa only [← cmLatticeTranslationOperator_eq_phase_mul_neg_comp hd] using this
  · rw [comb_translate hd]
    exact h₂ n s y hs hst hy k ys F hF

theorem product_algebraic (d : ℕ) (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (θ : ℂ → ℂ) (hp : d.Prime) (h7 : d % 16 = 7)
    (hS : Split d q) (hθ : IsTh d θ) (hδ : δ ≠ 0)
    (hL : ∀ ι' : ℂ ≃+* ℂ_[q], ∃ Ω' : ℂ_[q], ‖Ω'‖ = 1 ∧ ThetaLaws ι' d (Ω' / ι' δ) θ) {g m : ℕ} (a : Fin g → ℕ)
    (c : Fin m → ℂ) (hc : ∀ j, c j ∈ algebraicClosure ℚ ℂ) (t : Fin m → Fin g → ℂ) (ht : ∀ j i, PrimeTo d q (t j i))
    (τ : Fin g → ℂ) (hτ : ∀ i, PrimeTo d q (τ i)) (n s : ℕ) (y : Fin g → ℂ) (hs : Nat.Coprime s q)
    (hst : ∀ j i, InOK d ((s : ℂ) * (τ i + t j i))) (hy : ∀ i, Good ι d n s (y i)) (k : ℕ)
    (ys : Fin k → Fin g → ℂ) (hys : ∀ l i, ys l i ∈ algebraicClosure ℚ ℂ) :
    iteratedFDeriv ℂ k (fun z : Fin g → ℂ =>
      ∑ j, c j * ∏ i, W1 d (y i) (U1 d (τ i) (U1 d (t j i) θ)) (z i) ^ a i) 0 (fun l => δ⁻¹ • ys l)
      ∈ algebraicClosure ℚ ℂ := by
  have hd := hp.pos
  have H := (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd).2.2.1
  rw [comb_translate hd]
  refine GlobalTheory.AlgJetComb.iteratedFDeriv_comb_mem g m k δ a _ (fun j i => W1 d (y i) (U1 d (τ i + t j i) θ)) ys
    (fun j i => (H _ _ (H _ _ hθ.1).1).2)
    (fun j i k' => jets_algebraic d q δ θ hp h7 hS hθ hδ hL ι _ _ n s k' hs (hst j i) (hy i)) (fun j => ?_) hys
  refine mul_mem (hc j) (prod_mem fun i _ => pow_mem ?_ _)
  exact rho_mem (GlobalTheory.T.imagQuadraticMaximalOrder_arithmetic_at_split_prime d q ι hp h7 hS).2.2.2.2.2.1 (hτ i) (ht j i)

theorem beta_sum_left {g : ℕ} (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) {I : Type} [Fintype I] (c : I → ℂ)
    (u : I → Fin g → ℂ) (w : Fin g → ℂ) : beta d Hm (∑ k, c k • u k) w = ∑ k, c k * beta d Hm (u k) w := by
  simp only [beta, hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem beta_smul_left {g : ℕ} (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ)
    (u w : Fin g → ℂ) : beta d Hm (c • u) w = c * beta d Hm u w := by
  simp only [beta, hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem good_zero (ι : ℂ ≃+* ℂ_[q]) (d s : ℕ) : Good ι d 0 s 0 :=
  ⟨0, ⟨0, 0, by simp⟩, by simp, by simp⟩

theorem cmLatticeWeylOperator_zero {d : ℕ} (hd : 0 < d) (F : ℂ → ℂ) : W1 d 0 F = F := by
  funext z; simp [W1, (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd).2.1]

theorem lamA_eq (lam : Qbar →+* ℂ_[q]) (ι : ℂ ≃+* ℂ_[q]) (h : ∀ z : Qbar, ι (z : ℂ) = lam z) {z : ℂ}
    (hz : z ∈ Qbar) : lamA lam z = ι z := by
  rw [lamA, dif_pos hz]; exact (h ⟨z, hz⟩).symm

theorem contDiff_opU {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℂ) {F : (Fin g → ℂ) → ℂ}
    (hF : ContDiff ℂ ⊤ F) : ContDiff ℂ ⊤ (opU Hm x F) := by
  unfold opU hf
  fun_prop

theorem contDiff_opW {g : ℕ} (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℂ) {F : (Fin g → ℂ) → ℂ}
    (hF : ContDiff ℂ ⊤ F) : ContDiff ℂ ⊤ (opW d Hm x F) := by
  have := contDiff_opU Hm x hF
  unfold opW
  fun_prop

theorem theta_in_frame (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (θ : ℂ → ℂ) {g : ℕ} (S : Setup g) (hO : S.Ok)
    (hS : Split S.d q) (hθ : IsTh S.d θ) (hδ : δ ≠ 0)
    (hL : ∀ ι' : ℂ ≃+* ℂ_[q], ∃ Ω' : ℂ_[q], ‖Ω'‖ = 1 ∧ ThetaLaws ι' S.d (Ω' / ι' δ) θ)
    (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (hx : ∀ i, x i ∈ S.La)
    (hxx : ∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    (ha : ∀ i, 0 < a i ∧ Nat.Coprime (a i) q) (e : (Fin g → ℂ) → ℂ) (he : S.IsTheta e) (hj : S.AlgJets δ e) :
    ∃ (m : ℕ) (r : Fin m → ℂ) (t : Fin m → Fin g → ℂ), (∀ j, r j ∈ Qbar) ∧ (∀ j i, PrimeTo S.d q (t j i)) ∧
      ∀ z : Fin g → ℂ, e (∑ i, z i • x i) = ∑ j, r j * ∏ i, U1 S.d (t j i) θ (z i) ^ a i := by
  have hd := hO.1.pos
  obtain ⟨m, r, t, Θ, hΘ, hne, hr, ht, hz⟩ := GlobalTheory.T.exists_cmTheta_eq_sum_prod_translates q g S x a θ Fact.out hO hx hxx ha hθ
  obtain ⟨c, rfl⟩ := GlobalTheory.T.theta_vectors_setup_exists_eq_smul g S e Θ hO he hΘ hne
  obtain ⟨C1, -, -, C4⟩ := GlobalTheory.T.heisenbergOperators_orthogonalFrame_coords g S x a hd hxx fun i => (ha i).1
  have hc : c ∈ Qbar := by
    by_contra hc
    have hΦ : ContDiff ℂ ⊤ (fun z : Fin g → ℂ => Θ (∑ i, z i • x i)) := hΘ.1.comp (by fun_prop)
    have h0 := eq_zero_of_jets _ hΦ δ hδ fun k σ => by
      obtain ⟨s, hs, hst⟩ := primeTo_common (d := S.d) (q := q) (fun p : Fin m × Fin g => t p.1 p.2)
        fun p => ht _ _
      have h1 := product_algebraic S.d ι δ θ hO.1 hO.2.1 hS hθ hδ hL a r hr t ht 0
        (fun i => ⟨1, one_pos, Nat.coprime_one_left _, 0, 0, by simp⟩) 0 s 0 hs
        (fun j i => by simpa using hst (j, i)) (fun i => good_zero ι _ _) k (fun l => Pi.single (σ l) 1)
        (fun l i => by
          rw [Pi.single_apply]; split_ifs
          exacts [one_mem _, zero_mem _])
      simp only [Pi.zero_apply, cmLatticeWeylOperator_zero hd, (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable S.d hd).2.1, ← hz] at h1
      have h2 := hj k (fun l => x (σ l)) fun l => ⟨1, one_pos, by simpa using hx _⟩
      have e1 : (fun l => δ⁻¹ • x (σ l)) =
          fun l => ∑ i, (δ⁻¹ • (Pi.single (σ l) 1 : Fin g → ℂ)) i • x i := by
        funext l; simp [Pi.single_apply, ite_smul]
      rw [e1, C4 _ he.1] at h2
      have e2 : (fun z : Fin g → ℂ => (c • Θ) (∑ i, z i • x i)) = c • fun z : Fin g → ℂ => Θ (∑ i, z i • x i) := rfl
      rw [e2, iteratedFDeriv_const_smul_apply (hΦ.of_le le_top).contDiffAt, smul_apply, smul_eq_mul] at h2
      by_contra hn
      apply hc
      have := div_mem h2 h1
      rwa [mul_div_cancel_right₀ _ hn] at this
    apply hne
    funext v
    have := congrFun h0 fun i => beta S.d S.Hm v (x i) / (a i : ℂ)
    rw [C1 v]; exact this
  refine ⟨m, fun j => c * r j, t, fun j => mul_mem hc (hr j), ht, fun z => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hz, Finset.mul_sum, mul_assoc]

theorem moments_of_translates : ∀ (d q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (δ : ℂ) (θ : ℂ → ℂ) (ι : ℂ ≃+* ℂ_[q]) (Ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsTh d θ → δ ≠ 0 → (∀ ι' : ℂ ≃+* ℂ_[q], ∃ Ω' : ℂ_[q], ‖Ω'‖ = 1 ∧ ThetaLaws ι' d (Ω' / ι' δ) θ) → (∀ z : Qbar, ι (z : ℂ) = lam z) → ‖Ω‖ = 1 → ThetaLaws ι d (Ω / ι δ) θ → ∀ (g : ℕ) (S : Setup g), S.d = d → S.Ok → ∀ (r : ℕ) (b : Fin r → Fin g → ℂ), S.NNBasis q b → ∀ e : (Fin g → ℂ) → ℂ, S.IsTheta e → S.AlgJets δ e → ∃ N : ℝ, ∀ t : Fin g → ℂ, S.PrimeTo q t → ∃ μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q], ‖μ‖ = N ∧ MomentProperty lam Ω δ S b (fun _ : Fin 1 => t) μ (opU S.Hm t e) := by
  intro d q _ lam δ θ ι Ω hp h7 hS hθ hδ hL hlam hΩ hL0 g S hSd hO r b hb e he hj
  subst hSd
  have hd := hp.pos
  have hq : q.Prime := Fact.out
  obtain ⟨-, K2, -, -, -, -, K7⟩ := GlobalTheory.T.imagQuadraticMaximalOrder_arithmetic_at_split_prime S.d q ι hp h7 hS
  obtain ⟨x, a, hx, hxx, ha⟩ := GlobalTheory.T.exists_orthogonal_frame_norms_coprime_of_unimodular q g S hq hO K7
  obtain ⟨m, c, t, hc, ht, hz⟩ := theta_in_frame ι δ θ S hO hS hθ hδ hL x a hx hxx ha e he hj
  obtain ⟨C1, -, C3, C4⟩ := GlobalTheory.T.heisenbergOperators_orthogonalFrame_coords g S x a hd hxx fun i => (ha i).1
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_padicInt_frame_change_etale_basis q ι g S x a r b hO hS hx hxx ha hb
  have hΩ0 : Ω ≠ 0 := by rintro rfl; simp at hΩ
  obtain ⟨N, hN⟩ := product_measures S.d ι δ Ω θ hd hδ hΩ0 hθ.1 hL0 a c t ht
  have hβ : ∀ u ∈ S.La, ∀ v ∈ S.La, InOK S.d (beta S.d S.Hm u v) := hO.2.2.2.2.2.2.1
  have hβ' : ∀ v, S.AlgDir v → ∀ w ∈ S.La, beta S.d S.Hm v w ∈ Qbar := by
    rintro v ⟨s, cc, u, hcc, hu, rfl⟩ w hw
    rw [beta_sum_left]
    exact sum_mem fun k _ => mul_mem (hcc k) (K2 _ (hβ _ (hu k) _ hw)).2.2
  refine ⟨N, fun t₀ ht₀ => ?_⟩
  set τ : Fin g → ℂ := fun i => beta S.d S.Hm t₀ (x i) / (a i : ℂ) with hτd
  have hτ : ∀ i, PrimeTo S.d q (τ i) := by
    obtain ⟨s, hs, hsq, hst⟩ := ht₀
    intro i
    have h1 := hβ _ hst _ (hx i)
    have h2 : (a i : ℂ) ≠ 0 := by exact_mod_cast (ha i).1.ne'
    refine ⟨s * a i, Nat.mul_pos hs (ha i).1, Nat.Coprime.mul_left hsq (ha i).2, ?_⟩
    rw [beta_smul_left] at h1
    convert h1 using 1
    simp only [hτd]; push_cast; field_simp
  obtain ⟨μ, hμ, hM⟩ := hN τ hτ
  refine ⟨μ.comp (compIso (K := ℂ_[q]) T).toLinearIsometry.toContinuousLinearMap, ?_, ?_⟩
  · rw [← hμ]; exact μ.opNorm_comp_linearIsometryEquiv (compIso T)
  intro n m' eps hI hnm hint y k ys hys f hf
  obtain ⟨s₀, hs₀, hst⟩ := primeTo_common (d := S.d) (q := q) (fun p : Fin m × Fin g => τ p.2 + t p.1 p.2)
    fun p => primeTo_add (hτ _) (ht _ _)
  have hcop : Nat.Coprime (s₀ * ∏ i, a i) (q ^ n) :=
    (Nat.Coprime.mul_left hs₀ (Nat.Coprime.prod_left fun i _ => (ha i).2)).pow_right n
  set s := (s₀ * ∏ i, a i) ^ Nat.totient (q ^ n) with hsd
  have hs1 : s ≡ 1 [MOD q ^ n] := Nat.ModEq.pow_totient hcop
  have hs2 : (s₀ * ∏ i, a i) ∣ s := dvd_pow_self _ (Nat.totient_pos.2 (pow_pos hq.pos n)).ne'
  obtain ⟨L1, L2⟩ := GlobalTheory.T.cmThetaOperator_invariant_of_lift_congr_one q lam g S r b e t₀ n m' s eps y hO hb.1 he hI hnm (hint 0) hs1
  obtain ⟨G1, G2⟩ := GlobalTheory.T.torsion_lift_pairing_in_orthogonal_frame q lam ι g S x a r b n m' s s₀ eps y hlam hO hS hx hxx ha hb.1 hI hnm hs2
  set y' : Fin g → ℂ := fun i => beta S.d S.Hm ((s : ℂ) • liftY q n eps b y) (x i) / (a i : ℂ) with hy'
  set yc : Fin k → Fin g → ℂ := fun l i => beta S.d S.Hm (ys l) (x i) / (a i : ℂ) with hyc
  have hyc' : ∀ l i, yc l i ∈ Qbar := fun l i => div_mem (hβ' _ (hys l) _ (hx i)) (natCast_mem _ _)
  have e1 : (fun l => δ⁻¹ • ys l) = fun l => ∑ i, (δ⁻¹ • yc l) i • x i := by
    funext l
    conv_lhs => rw [C1 (ys l)]
    simp only [Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul, hyc]
  have e2 : (fun z : Fin g → ℂ => opW S.d S.Hm ((s : ℂ) • liftY q n eps b y) (opU S.Hm t₀ e) (∑ i, z i • x i)) =
      fun z => ∑ j, c j * ∏ i, W1 S.d (y' i) (U1 S.d (τ i) (U1 S.d (t j i) θ)) (z i) ^ a i := by
    funext z
    rw [C1 ((s : ℂ) • liftY q n eps b y), C1 t₀]
    exact (C3 m c (fun j i => U1 S.d (τ i) (U1 S.d (t j i) θ)) _
      (fun z => (C3 m c (fun j i => U1 S.d (t j i) θ) e hz τ z).1) y' z).2
  rw [← L1, e1, C4 _ (contDiff_opW _ _ _ (contDiff_opU _ _ he.1)), e2]
  have halg := product_algebraic S.d ι δ θ hp h7 hS hθ hδ hL a c hc t ht τ hτ n s₀ y' hs₀
    (fun j i => hst (j, i)) G1 k yc hyc'
  refine ⟨halg, ?_⟩
  rw [lamA_eq lam ι hlam halg]
  refine hM n s₀ y' hs₀ (fun j i => hst (j, i)) G1 k yc (compIso T f) fun A' => ?_
  obtain ⟨A, rfl⟩ := T.surjective A'
  have e3 : compIso (K := ℂ_[q]) T f (T A) = f A := by
    show f (T.symm (T A)) = f A
    rw [T.symm_apply_apply]
  have hv : vecA n b A ∈ S.La := sum_mem fun i _ => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hb.1 i) _
  obtain ⟨G3, G4⟩ := G2 A (T A) (hT A)
  rw [e3, hf, ← L2 _ hv, lamA_eq lam ι hlam G3, G4]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [pairD]
  congr 1
  simp only [hT, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lamA_eq lam ι hlam (hβ' _ (hys l) _ (hb.1 j))]
  conv_lhs => rw [C1 (ys l), beta_sum_left, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  show GlobalTheory.MomOne.zc (A j) * (ι (yc l i) * _) = _
  ring

end GlobalTheory.MomOne.Translates
