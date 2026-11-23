import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixBoundaryExtensionMonodromyPosSemidefStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstIntegralCoordsLatticeSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscUniversalCoverOpenConvexExpAnalytic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfImHermFormIntegralRealBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatLinearIndependentCoordsOfRealIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoisotropicSublatticeOfTorsionCount
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscCoverLatticeBasisRealHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexMatrixEqOfHermFormImEqRealSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntMatrixTransposeNegStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntCombinationEqConjMulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntCombinationDotProductStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffMatrixMulEqOfSameIntCombinationsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalSymplecticBasisAdaptedCoisotropicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntIsometryFixingRowSpaceSymplecticShiftStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorRatMatricesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsRationalCombinationFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOnRationalFramePeriodMatrixLogCoveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetRationalCombinationFrameClosedBallStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefImPartOnPolydiscOfPuncturedCoverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotPeriodMatrixIntVecContinuousBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonIntKernelPsdBlockNotPosDefStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOnBallOfEqOnPunctPolydiscCoveringExpImageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodChartRescaleBallToUnitPolydiscStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.PerChartKer

theorem exists_nat_mul_int {g r : ℕ} (ε : Matrix (Fin g) (Fin r) ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ e : Matrix (Fin g) (Fin r) ℤ, ∀ i m, (e i m : ℚ) = N * ε i m := by
  refine ⟨∏ i, ∏ m, (ε i m).den, Finset.prod_pos fun i _ => Finset.prod_pos fun m _ => (ε i m).den_pos,
    fun i m => (((∏ i, ∏ m, (ε i m).den) / (ε i m).den : ℕ) : ℤ) * (ε i m).num, fun i m => ?_⟩
  have hd : (ε i m).den ∣ ∏ i, ∏ m, (ε i m).den :=
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ m)).trans (Finset.dvd_prod_of_mem (fun i => ∏ m, (ε i m).den) (Finset.mem_univ i))
  obtain ⟨q, hq⟩ := hd
  dsimp only
  rw [hq, Nat.mul_div_cancel_left _ (ε i m).den_pos]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

theorem combMat_mulVec_intCast {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ) (N : ℕ)
    (e : Matrix (Fin g) (Fin r) ℤ) (he : ∀ i m, (e i m : ℚ) = N * ε i m) (v : Fin g → ℤ) :
    (N : ℂ) • (GlobalTheory.PeriodFrame.combMat l ε *ᵥ fun i => (v i : ℂ)) = ∑ m, (∑ i, e i m * v i) • l m := by
  ext k
  simp only [Finset.sum_apply, Pi.smul_apply]
  simp only [GlobalTheory.PeriodFrame.combMat, Matrix.mulVec, dotProduct, Matrix.of_apply, smul_eq_mul, zsmul_eq_mul]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
  have h := congrArg (Rat.cast : ℚ → ℂ) (he i m)
  push_cast at h
  rw [h]
  ring

theorem mulVec_smul_add_inv {g : ℕ} (P Q : Matrix (Fin g) (Fin g) ℂ) (hP : IsUnit P.det) (N D : ℕ)
    (x y : Fin g → ℂ) :
    P *ᵥ ((N : ℂ) • (x + ((D : ℂ) • (P⁻¹ * Q)) *ᵥ y)) = (N : ℂ) • (P *ᵥ x) + (N : ℂ) • ((D : ℂ) • (Q *ᵥ y)) := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.one_mul, smul_add]

section
variable {g r : ℕ} {S : Set (Fin g → ℂ)} {l : Fin r → Fin g → ℂ}

theorem mem_add (hS : ∀ w, w ∈ S ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • l j) {x y : Fin g → ℂ} (hx : x ∈ S)
    (hy : y ∈ S) : x + y ∈ S := by
  obtain ⟨m, rfl⟩ := (hS x).1 hx
  obtain ⟨m', rfl⟩ := (hS y).1 hy
  exact (hS _).2 ⟨m + m', by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩

theorem mem_smul (hS : ∀ w, w ∈ S ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • l j) (k : ℕ) {x : Fin g → ℂ} (hx : x ∈ S) :
    (k : ℂ) • x ∈ S := by
  obtain ⟨m, rfl⟩ := (hS x).1 hx
  refine (hS _).2 ⟨fun j => (k : ℤ) * m j, ?_⟩
  ext t
  simp only [Finset.sum_apply, Pi.smul_apply]
  simp only [smul_eq_mul, zsmul_eq_mul, Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by ring

end

theorem frame_ker : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m) → ∃ (rk : ℕ) (d ρ₁ : ℝ) (P τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (Δ : (Fin n → ℂ) → Matrix {j : Fin g // rk ≤ j.val} {j : Fin g // rk ≤ j.val} ℂ), 0 < ρ₁ ∧ ρ₁ ≤ 1 ∧ 0 < d ∧ rk ≤ g ∧ (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ₁)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, IsUnit (P z).det) ∧ (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) ∧ (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (P (logExp a s))ᵀ * Hm * (P (logExp a s))ᵀᴴ = ((d : ℝ) : ℂ) • (((τ s).map Complex.im).map Complex.ofReal)⁻¹) ∧ ContinuousOn Δ (Metric.ball 0 ρ₁) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, ((Δ z).map Complex.im).PosDef) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).submatrix Subtype.val Subtype.val = Δ (logExp a s)) ∧ (∀ v : Fin g → ℤ, v ≠ 0 → (∀ j : Fin g, rk ≤ j.val → v j = 0) → ∀ F : (Fin n → ℂ) → Fin g → ℂ, ContinuousOn F (Metric.ball 0 ρ₁) → ¬ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).mulVec (fun j => (v j : ℂ)) = F (logExp a s)) ∧ ∃ Dn : ℕ, 0 < Dn ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ m m' : Fin g → ℤ, P (logExp a s) *ᵥ ((Dn : ℂ) • ((fun i => (m i : ℂ)) + τ s *ᵥ fun i => (m' i : ℂ))) ∈ K (logExp a s) := by
  intro n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlamc hlam hH htor
  obtain ⟨hDo, hDc, hDan, hDmaps⟩ := GlobalTheory.logDom_chart_props n a
  have hlogc : Continuous (logExp a : (Fin n → ℂ) → Fin n → ℂ) :=
    continuous_iff_continuousAt.2 fun s => (hDan s).continuousAt
  set s₀ : Fin n → ℂ := fun k => if (k : ℕ) < a then -1 else 0 with hs₀def
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_setOf_eq]
    intro k
    by_cases h : (k : ℕ) < a <;> simp [s₀, h]
  obtain ⟨hr, hlamR, hlamD⟩ := GlobalTheory.T.punctPolydiscCover_latticeBasis_real_holomorphic n a g r K lam hK hlamc hlam
  have hlB : ∀ b ∈ logDom n a, IsLatBasis (K (logExp a b)) (lam b) := fun b hb => ⟨hlamR b hb, (hlam b hb).2.2⟩
  have hmemL : ∀ b ∈ logDom n a, ∀ i, lam b i ∈ K (logExp a b) := fun b hb i =>
    ((hlam b hb).2.2 _).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
  have hpre : _root_.IsPreconnected (logDom n a) := hDc.isPreconnected
  have hζc : ContinuousOn (fun s => ζ (logExp a s)) (logDom n a) := hζ.continuousOn.comp hlogc.continuousOn hDmaps
  have hcex' : ∀ i : Fin r₀, ∃ m : Fin r → ℤ, ∀ b ∈ logDom n a, ζ (logExp a b) i = ∑ j, m j • lam b j := fun i =>
    GlobalTheory.ShFam.Hor.LogCh.exists_const_coords n g r (logDom n a) (fun b => K (logExp a b)) lam
      (fun b => ζ (logExp a b) i) s₀ hpre hlamc ((continuous_apply i).comp_continuousOn hζc) hlB
      (fun b hb => hζK _ (hDmaps hb) i) hs₀
  have hcex : ∃ c : Matrix (Fin r₀) (Fin r) ℤ, ∀ i, ∀ b ∈ logDom n a, ζ (logExp a b) i = ∑ j, c i j • lam b j := by
    choose c hc using hcex'
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hcex
  have hsh := fun (k : Fin a) (s : Fin n → ℂ) (hs : s ∈ logDom n a) => GlobalTheory.PeriodFrame.shift_mem ha k hs
  have hTex' : ∀ (k : Fin a) (i : Fin r), ∃ m : Fin r → ℤ, ∀ b ∈ logDom n a,
      lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i = ∑ j, m j • lam b j := fun k i =>
    GlobalTheory.ShFam.Hor.LogCh.exists_const_coords n g r (logDom n a) (fun b => K (logExp a b)) lam
      (fun b => lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i) s₀ hpre hlamc
      ((continuous_apply i).comp_continuousOn
        (hlamc.comp (continuous_add_right _).continuousOn fun b hb => (hsh k b hb).1))
      hlB (fun b hb => by rw [← (hsh k b hb).2]; exact hmemL _ (hsh k b hb).1 i) hs₀
  have hTex : ∃ T : Fin a → Matrix (Fin r) (Fin r) ℤ, ∀ k i, ∀ b ∈ logDom n a,
      lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i = ∑ j, T k i j • lam b j := by
    choose T hT using hTex'
    exact ⟨T, hT⟩
  obtain ⟨T, hT⟩ := hTex
  obtain ⟨Hm₀, hH₀h, hH₀p, hH₀l⟩ := hH s₀ hs₀
  have hM₀ := hH₀l s₀ hs₀ rfl
  have hMa : Mᵀ = -M := GlobalTheory.T.hermForm_im_intMatrix_transpose_neg g r Hm₀ (lam s₀) M hH₀h hM₀
  have hMd : M.det ≠ 0 :=
    GlobalTheory.det_ne_zero_of_im_hermForm_eq_int g r Hm₀ (lam s₀) M hH₀p (hlamR s₀ hs₀) (hlam s₀ hs₀).2.1 hM₀
  have hTM : ∀ k, T k * M * (T k)ᵀ = M := by
    intro k
    have h1 := GlobalTheory.T.hermForm_im_intCombination_eq_conj_mul g r r Hm₀ (lam s₀) (lam (s₀ + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)))
      (T k) M (fun i => hT k i s₀ hs₀) hM₀
    have h2 := hH₀l _ (hsh k s₀ hs₀).1 (hsh k s₀ hs₀).2
    ext i j
    have h3 := (h1 i j).symm.trans (h2 i j)
    exact_mod_cast h3
  have hcT : ∀ k, c * T k = c := fun k =>
    GlobalTheory.T.coeffMatrix_mul_eq_of_same_intCombinations g r r₀ (lam s₀) (lam (s₀ + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)))
      (ζ (logExp a s₀)) c (T k) (hlam s₀ hs₀).1 (fun i => hT k i s₀ hs₀) (fun i => hc i s₀ hs₀)
      (fun i => by rw [← (hsh k s₀ hs₀).2]; exact hc i _ (hsh k s₀ hs₀).1)
  have hcLI : LinearIndependent ℚ (fun i j => (c i j : ℚ)) :=
    GlobalTheory.rowsInd_rat_of_real g r r₀ (lam s₀) (ζ (logExp a s₀)) c (hζi _ (hDmaps hs₀)) (fun i => hc i s₀ hs₀)
  have hco := GlobalTheory.CoisoCount.coisotropic_of_torsion_count r r₀ M c hMd hcLI (by
    intro N hN
    obtain ⟨S, hcard, hS⟩ := htor N hN
    refine ⟨S, by rw [hr]; exact hcard, fun u u' hu => ?_⟩
    obtain ⟨m, hm⟩ := hS u u' hu s₀ hs₀ Hm₀ hM₀
    rw [GlobalTheory.T.hermForm_im_intCombination_dotProduct g r r₀ Hm₀ (lam s₀) (ζ (logExp a s₀)) c M (fun i => hc i s₀ hs₀) hM₀ u u'] at hm
    exact ⟨m, by exact_mod_cast hm⟩)
  obtain ⟨rk, α, φ, β, gm, dl, hrk, hN1, hN2, hN3, hN4, hN5, hN6, hN7⟩ := GlobalTheory.T.exists_rational_symplecticBasis_adapted_coisotropic g r r₀ M c hr hMa hMd hcLI hco
  choose b hb using fun k => GlobalTheory.T.intIsometry_fixing_rowSpace_symplectic_shift g r r₀ rk M (T k) c α φ β hr hMa (hTM k) (hcT k) hN1 hN2 hN3 hN5
  obtain ⟨D, Bz, hD, hBz⟩ := GlobalTheory.T.exists_common_denominator_rat_matrices a g b
  have hBzs : ∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → Bz k j l = 0 := by
    intro k j l h
    have h1 := hBz k j l
    rw [(hb k).1 j l h, mul_zero] at h1
    exact_mod_cast h1
  have hPeq : ∀ s ∈ logDom n a, GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α =
      GlobalTheory.PeriodFrame.combMat (lam s) (α * c.map (Int.cast : ℤ → ℚ)) :=
    fun s hs => GlobalTheory.PeriodFrame.combMat_comb _ _ c α (fun i => hc i s hs)
  have hRie : ∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ,
      (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) ∧
      IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det ∧ (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).IsSymm ∧
      ((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).PosDef ∧
      (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α)ᵀ * Hm * (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α)ᵀᴴ =
        ((D : ℝ) : ℂ) • (((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).map Complex.ofReal)⁻¹ := by
    intro s hs
    obtain ⟨Hm, h1, h2, h3⟩ := hH s hs
    refine ⟨Hm, h3 s hs rfl, ?_⟩
    unfold GlobalTheory.PeriodFrame.perTau
    rw [hPeq s hs]
    exact GlobalTheory.T.riemannRelations_rationalCombinationFrame g r Hm M (lam s) _ φ D hD h1 h2 (hlamR s hs) (h3 s hs rfl) hN1 hN2 hN3
  have hdet : ∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det := fun s hs => by
    obtain ⟨_, _, h, _⟩ := hRie s hs
    exact h
  obtain ⟨hPd, hτd⟩ := GlobalTheory.T.differentiableOn_rationalFrame_periodMatrix_logCover n a g r₀ r ζ lam α φ D hζ hlamD hdet
  have hτsm : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 →
      (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).IsSymm ∧
      ((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).PosDef := fun s hs _ => by
    obtain ⟨_, _, _, h1, h2, _⟩ := hRie s hs
    exact ⟨h1, h2⟩
  have hmono : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → ∀ k : Fin a,
      GlobalTheory.PeriodFrame.perTau a ζ lam α φ D (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) =
        GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s + (Bz k).map (Int.cast : ℤ → ℂ) := by
    intro s hs _ k
    unfold GlobalTheory.PeriodFrame.perTau
    rw [(hsh k s hs).2, hPeq s hs,
      GlobalTheory.PeriodFrame.combMat_comb (lam (s + _)) (lam s) (T k) φ (fun i => hT k i s hs), (hb k).2]
    exact GlobalTheory.PeriodFrame.combMat_shift (lam s) _ φ (b k) D (Bz k) (hPeq s hs ▸ hdet s hs) (hBz k)
  obtain ⟨hpsd, τ₀, hτ₀d, hτ₀s, hτ₀e⟩ :=
    GlobalTheory.T.periodMatrix_boundaryExtension_monodromy_posSemidef n a g ha 1 (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D) Bz one_pos le_rfl hτd hτsm hmono
  have hPu : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ z) α).det :=
    GlobalTheory.T.isUnit_det_rational_combination_frame_closed_ball n a g r₀ r ha ζ lam c α φ gm dl rk D τ₀ Bz hD hζ hstd (fun s hs i => hc i s hs) hN7 hN6 hdet hτ₀d
      hBzs hτ₀e
  have hcont : ∀ j l, ContinuousOn (fun z => τ₀ z j l) (Metric.ball 0 1) := fun j l => (hτ₀d j l).continuousOn
  have hagree : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 →
      (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
        (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) =
        (τ₀ (logExp a s)).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
          (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) := by
    intro s hs hz
    rw [hτ₀e s hs hz]
    ext ⟨j, hj⟩ ⟨l, hl⟩
    simp [Matrix.sum_apply, hBzs _ j l (Or.inl hj)]
  refine ⟨rk, (D : ℝ), 1, fun z => GlobalTheory.PeriodFrame.combMat (ζ z) α, GlobalTheory.PeriodFrame.perTau a ζ lam α φ D, Bz,
    fun z => (τ₀ z).submatrix Subtype.val Subtype.val, one_pos, le_rfl, by exact_mod_cast hD, hrk, hPd, hPu, hτd,
    hτsm, hmono, hBzs, ?_, ?_, ?_, hagree, ?_, ?_⟩
  · intro s hs hz Hm hHm
    obtain ⟨Hm', h1, _, _, _, h5⟩ := hRie s hs
    have hHH : Hm = Hm' :=
      GlobalTheory.T.complexMatrix_eq_of_hermForm_im_eq_real_span g r Hm Hm' (lam s) (hlam s hs).2.1 (fun i j => (hHm i j).trans (h1 i j).symm)
    subst hHH
    exact h5
  · exact continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j.1 l.1
  · refine GlobalTheory.T.posDef_imPart_on_polydisc_of_punctured_cover n a {j : Fin g // rk ≤ j.val} (fun z => (τ₀ z).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
      (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g))
      (fun j l => hτ₀d j.1 l.1) ?_
    intro s hs
    rw [← hagree s hs (hDmaps hs)]
    exact (hτsm s hs (hDmaps hs)).2.submatrix Subtype.val_injective
  · exact GlobalTheory.T.not_periodMatrix_intVec_continuous_boundary n a g r₀ r K ζ lam M c α φ rk D hK hζ hζK hζ0 (fun s hs => ⟨hlamR s hs, (hlam s hs).2.2⟩)
      (fun s hs i => hc i s hs) hMa hN3 hN4 hD hdet
  · obtain ⟨N₁, hN₁, e₁, he₁⟩ := exists_nat_mul_int (α * c.map (Int.cast : ℤ → ℚ))
    obtain ⟨N₂, hN₂, e₂, he₂⟩ := exists_nat_mul_int φ
    refine ⟨N₁ * N₂, Nat.mul_pos hN₁ hN₂, fun s hs _ m m' => ?_⟩
    show GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α *ᵥ ((((N₁ * N₂ : ℕ) : ℂ)) • ((fun i => (m i : ℂ)) +
      GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s *ᵥ fun i => (m' i : ℂ))) ∈ K (logExp a s)
    unfold GlobalTheory.PeriodFrame.perTau
    rw [mulVec_smul_add_inv _ _ (hdet s hs), hPeq s hs]
    have hK' := (hlam s hs).2.2
    refine mem_add hK' ?_ ?_
    · rw [Nat.cast_mul, mul_comm (N₁ : ℂ), mul_smul, combMat_mulVec_intCast _ _ N₁ e₁ he₁]
      exact mem_smul hK' _ ((hK' _).2 ⟨_, rfl⟩)
    · rw [smul_comm, Nat.cast_mul, mul_smul, combMat_mulVec_intCast _ _ N₂ e₂ he₂]
      exact mem_smul hK' _ (mem_smul hK' _ ((hK' _).2 ⟨_, rfl⟩))

theorem periodChart_ker : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m) → ∃ (rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (P : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (ρ d : ℝ), 0 < ρ ∧ ρ ≤ 1 ∧ 0 < d ∧ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (P z).det) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (P (logExp a s))ᵀ * Hm * (P (logExp a s))ᵀᴴ = ((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ρ⁻¹ • logExp a s))⁻¹) ∧ ∃ Dn : ℕ, 0 < Dn ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ large₂ : Fin a → ℂ, (∀ k, s (Fin.castLE ha k) = large₂ k + ((Real.log ρ : ℝ) : ℂ)) → ∀ m m' : Fin g → ℤ, P (logExp a s) *ᵥ ((Dn : ℂ) • ((fun i => (m i : ℂ)) + GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period τ₀ B (ρ⁻¹ • logExp a s) large₂ *ᵥ fun i => (m' i : ℂ))) ∈ K (logExp a s) := by
  intro n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlam hlamB hH htor
  obtain ⟨rk, d, ρ, P, τ, B, Δ, hρ, hρ1, hd, hrk, hP, hPdet, hτd, hτs, hτm, hB, hPH, hΔc, hΔp, hτΔ, hcl, hker⟩ :=
    frame_ker n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlam hlamB hH htor
  obtain ⟨hpsd, τ₀, hτ₀d, hτ₀s, hτ₀e⟩ := GlobalTheory.T.periodMatrix_boundaryExtension_monodromy_posSemidef n a g ha ρ τ B hρ hρ1 hτd hτs hτm
  have hcont : ∀ j l, ContinuousOn (fun z => τ₀ z j l) (Metric.ball 0 ρ) := fun j l => (hτ₀d j l).continuousOn
  have hmv : ∀ (k : Fin a) (v : Fin g → ℤ), ((B k).map (Int.cast : ℤ → ℂ)).mulVec (fun j => (v j : ℂ)) =
      fun i => (((B k).mulVec v i : ℤ) : ℂ) := by
    intro k v; ext i; simp [Matrix.mulVec, dotProduct]
  have htoric : (((∑ k, B k).map (Int.cast : ℤ → ℝ)).submatrix
      (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef := by
    by_contra hnot
    obtain ⟨v, hv0, hvs, hBv⟩ := GlobalTheory.T.exists_common_int_kernel_psd_block_not_posDef a g rk B hpsd hB hnot
    refine hcl v hv0 hvs (fun z => (τ₀ z).mulVec (fun j => (v j : ℂ))) ?_ ?_
    · refine continuousOn_pi.2 fun j => ?_
      simp only [Matrix.mulVec, dotProduct]
      exact continuousOn_finset_sum _ fun l _ => (hcont j l).mul continuousOn_const
    · intro s hs hz
      rw [hτ₀e s hs hz, Matrix.add_mulVec]
      have h0 : (∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)).mulVec
          (fun j => (v j : ℂ)) = 0 := by
        rw [Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [Matrix.smul_mulVec, hmv, hBv k]
        ext i; simp
      rw [h0, add_zero]
  have hagree : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ →
      (τ₀ (logExp a s)).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val = Δ (logExp a s) := by
    intro s hs hz
    rw [← hτΔ s hs hz, hτ₀e s hs hz]
    ext ⟨j, hj⟩ ⟨l, hl⟩
    simp [Matrix.sum_apply, hB _ j l (Or.inl hj)]
  have heq := GlobalTheory.T.eqOn_ball_of_eqOn_punctPolydiscCoveringExp_image n a ρ _
    (fun z => (τ₀ z).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val) Δ hρ1
    (continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j.1 l.1) hΔc hagree
  have habel : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (((τ₀ z).map Complex.im).submatrix
      (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef := by
    intro z hz
    have h1 := hΔp z hz
    rw [← heq z hz] at h1
    exact h1
  obtain ⟨hPC, hY⟩ := GlobalTheory.T.periodChart_rescale_ball_to_unitPolydisc n a g rk ha ρ τ₀ B hρ hρ1 hrk hτ₀d hτ₀s hpsd hB htoric habel
  refine ⟨rk, _, B, P, ρ, d, hρ, hρ1, hd, hPC, hP, hPdet, ?_, ?_⟩
  swap
  · obtain ⟨Dn, hDn, hk⟩ := hker
    refine ⟨Dn, hDn, fun s hs hz large₂ hL m m' => ?_⟩
    have hτ : GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B (ρ⁻¹ • logExp a s) large₂ = τ s := by
      rw [hτ₀e s hs hz]
      unfold GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period
      simp only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
      rw [add_assoc, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← add_smul, hL k, ← add_div, add_comm (large₂ k)]
    rw [hτ]
    exact hk s hs hz m m'
  intro s hs hz Hm hHm
  have hnz : ∀ i : Fin a, logExp a s (Fin.castLE ha i) ≠ 0 := by
    intro i
    simp only [logExp, Fin.coe_castLE, i.isLt, if_true]
    exact Complex.exp_ne_zero _
  rw [hPH s hs hz Hm hHm, hY _ hnz]
  congr 2
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram
  congr 1
  rw [← GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.im_period ha τ₀ B (logExp a s) (fun k => s (Fin.castLE ha k)) ?_]
  · rw [hτ₀e s hs hz]; rfl
  · intro i
    simp only [logExp, Fin.coe_castLE, i.isLt, if_true]

end GlobalTheory.ShFam.Hor.LogCh.PerChartKer
