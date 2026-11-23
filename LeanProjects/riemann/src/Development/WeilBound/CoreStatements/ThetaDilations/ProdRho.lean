import Development.WeilBound.CoreStatements.ThetaDilations.SqPosOfNe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScalingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChangeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilRepresentationQuadraticDatumStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MobiusActionUpperHalfPlaneStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SL2BruhatDecompositionIdentitiesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanGaussianFourierStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

variable {F : Type} [Field F] [NumberField F]

theorem prod_rho {ρ : InfinitePlace F → (F →+* ℝ)} (hF : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (a : F) : ∏ w, |ρ w a| = |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  have h := InfinitePlace.prod_eq_abs_norm a
  rw [← Rat.cast_abs, ← h]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [IsTotallyReal.mult_eq, pow_one, ← w.norm_embedding_eq, ← hρ, Complex.norm_real, Real.norm_eq_abs]

theorem map_nMat {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (b : R) :
    Matrix.SpecialLinearGroup.map f (nMat b) = nMat (f b) :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    show f (nMat b i j) = _
    fin_cases i <;> fin_cases j <;> simp [nMat]

theorem map_wMat {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : Matrix.SpecialLinearGroup.map f wMat = wMat :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    show f ((wMat : SL(2, R)) i j) = _
    fin_cases i <;> fin_cases j <;> simp [wMat]

theorem map_mMat {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : Rˣ) :
    Matrix.SpecialLinearGroup.map f (mMat a) = mMat (Units.map (f : R →* S) a) :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    show f (mMat a i j) = _
    fin_cases i <;> fin_cases j <;> simp [mMat]

def uA (a : Fˣ) : (A F)ˣ := Units.map (algebraMap F (A F) : F →* A F) a

theorem mod_rat [MeasurableSpace (A F)] [BorelSpace (A F)] {lf : Measure (A F)} (hlf : lf.IsAddHaarMeasure)
    (h1 : lf (Oh F) = 1) {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ} (hc : Fintype.card ι = 2 * M)
    (B : Matrix ι ι F) (a : Fˣ) (s : Set (ι → A F)) (hs : MeasurableSet s) :
    muF B lf ((fun u => (uA a : A F) • u) '' s) =
      ENNReal.ofReal ((|((Algebra.norm ℚ (a : F) : ℚ) : ℝ)|⁻¹ ^ M) ^ 2) * muF B lf s := by
  have h2 := (GlobalTheory.T.adelic_haar_measure_linear_change F lf hlf h1 ι).2 (uA a) s hs
  have h3 := (GlobalTheory.T.adelic_haar_measure_scaling F lf hlf h1).1 a a.ne_zero _ (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.1.measurableSet
  rw [h1, mul_one] at h3
  rw [muF, Measure.smul_apply, Measure.smul_apply, h2, smul_eq_mul, smul_eq_mul, mul_left_comm, ← pow_mul,
    ENNReal.ofReal_pow (by positivity), hc, mul_comm M 2]
  exact congrArg (fun t => t ^ (2 * M) * _) h3

theorem good_ex [MeasurableSpace (A F)] [BorelSpace (A F)] {lf : Measure (A F)} (hlf : lf.IsAddHaarMeasure)
    (h1 : lf (Oh F) = 1) {ψ : AddChar (A F) ℂ} (hψ : IsStdChar F ψ) {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ}
    {B : Matrix ι ι F} {ρ : InfinitePlace F → (F →+* ℝ)} {P : InfinitePlace F → Matrix ι ι ℝ} (hQ : QSetup M B ρ P)
    {𝒟 : ((ι → A F) → ℂ) → (InfinitePlace F → ℂ) → ℂ}
    (hD : ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) →
      (∀ b : F, 𝒟 (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = 𝒟 φ τ) ∧
      (∀ a : F, a ≠ 0 → 𝒟 (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = 𝒟 φ τ) ∧
      (cG B ρ P τ * 𝒟 (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) = 𝒟 φ τ) ∧
      ∀ c : ℂ, 𝒟 (c • φ) τ = c * 𝒟 φ τ) (γ : SL(2, F)) :
    ∃ T, Impl ψ (hf F) (Bf B) (muF B lf) (Matrix.SpecialLinearGroup.map (algebraMap F (A F)) γ) T ∧
      ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → wt M (mob ρ γ τ) * ‖𝒟 (T φ) (mob ρ γ τ)‖ = wt M τ * ‖𝒟 φ τ‖ := by
  have H := GlobalTheory.T.weil_representation_quadratic_datum F lf hlf h1 ψ hψ ι B hQ.2.2.1 hQ.2.2.2.1
  have hmob := GlobalTheory.T.mobius_action_upper_half_plane F ρ
  set G : SL(2, F) → Prop := fun γ => ∃ T,
    Impl ψ (hf F) (Bf B) (muF B lf) (Matrix.SpecialLinearGroup.map (algebraMap F (A F)) γ) T ∧
      ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → wt M (mob ρ γ τ) * ‖𝒟 (T φ) (mob ρ γ τ)‖ = wt M τ * ‖𝒟 φ τ‖ with hG
  have gmul : ∀ g g', G g → G g' → G (g * g') := by
    rintro g g' ⟨T, a1, a2⟩ ⟨T', b1, b2⟩
    refine ⟨T ∘ T', by rw [map_mul]; exact impl_mul a1 b1, fun φ τ hφ hτ => ?_⟩
    rw [(hmob τ hτ).2.1, ← b2 φ τ hφ hτ]
    exact a2 _ _ (b1.1 φ hφ) fun w => ((hmob τ hτ).1 g' w).2
  have gU : ∀ b, G (nMat b) := fun b => by
    have e : Matrix.SpecialLinearGroup.map (algebraMap F (A F)) (nMat b) = nMat (algebraMap F (A F) b) := map_nMat _ _
    refine ⟨_, e ▸ impl_U H _, fun φ τ hφ hτ => ?_⟩
    rw [(hmob τ hτ).2.2.1, (hD φ τ hφ hτ).1]
    simp [wt]
  have gW : G wMat := by
    have e : Matrix.SpecialLinearGroup.map (algebraMap F (A F)) wMat = wMat := map_wMat _
    refine ⟨_, e ▸ impl_fou_chiB H, fun φ τ hφ hτ => ?_⟩
    rw [(hmob τ hτ).2.2.2.2, ← (hD φ τ hφ hτ).2.2.1, norm_mul, (GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P hQ τ hτ).2.1,
      ← mul_assoc, wt, wt, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg, Real.sqrt_div (hτ w).le, ← Complex.norm_def, div_pow,
      div_eq_mul_inv]
  have gD : ∀ a : Fˣ, G (mMat a) := fun a => by
    have e : Matrix.SpecialLinearGroup.map (algebraMap F (A F)) (mMat a) = mMat (uA a) := map_mMat _ _
    have hn : (0 : ℝ) < |((Algebra.norm ℚ (a : F) : ℚ) : ℝ)| :=
      abs_pos.2 (by exact_mod_cast Algebra.norm_ne_zero_iff.2 a.ne_zero)
    refine ⟨_, e ▸ impl_D H (uA a) (by positivity) (mod_rat hlf h1 hQ.2.1 B a), fun φ τ hφ hτ => ?_⟩
    have e2 : opD (|((Algebra.norm ℚ (a : F) : ℚ) : ℝ)|⁻¹ ^ M) (uA a : A F) φ =
        ((|((Algebra.norm ℚ (a : F) : ℚ) : ℝ)|⁻¹ ^ M : ℝ) : ℂ) • opD 1 (algebraMap F (A F) a) φ := by
      funext u; simp [opD, uA]
    have hτ' := fun w => ((hmob τ hτ).1 (mMat a) w).2
    have hs : SB (opD 1 (algebraMap F (A F) a) φ) := sb_opD H 1 (uA a) hφ
    rw [e2, (hD _ _ hs hτ').2.2.2, (hmob τ hτ).2.2.2.1, (hD φ τ hφ hτ).2.1 a a.ne_zero, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), ← mul_assoc]
    congr 1
    rw [inv_pow, ← div_eq_mul_inv, div_eq_iff (by positivity), ← prod_rho hQ.1 hQ.2.2.2.2.1, wt, wt,
      ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← Complex.ofReal_pow, Complex.im_ofReal_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, mul_pow, mul_comm]
  show G γ
  obtain ⟨d1, -, d3, -⟩ := GlobalTheory.T.SL2_bruhat_decompositions_and_w_inv F γ
  by_cases hc : γ 1 0 = 0
  · have ha : γ 0 0 ≠ 0 := fun h0 => by
      have := γ.det_coe
      rw [Matrix.det_fin_two, h0, hc] at this
      simp at this
    rw [d3 (Units.mk0 _ ha) rfl hc]
    exact gmul _ _ (gU _) (gD _)
  · rw [d1 (Units.mk0 _ hc) rfl]
    exact gmul _ _ (gmul _ _ (gmul _ _ (gU _) (gD _)) gW) (gU _)

theorem inv_all : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ 𝒟 : ((ι → A F) → ℂ) → (InfinitePlace F → ℂ) → ℂ, (∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → (∀ b : F, 𝒟 (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = 𝒟 φ τ) ∧ (∀ a : F, a ≠ 0 → 𝒟 (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = 𝒟 φ τ) ∧ (cG B ρ P τ * 𝒟 (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) = 𝒟 φ τ) ∧ ∀ c : ℂ, 𝒟 (c • φ) τ = c * 𝒟 φ τ) → ∀ (γ : SL(2, F)) T, Impl ψ (hf F) (Bf B) (muF B lf) (Matrix.SpecialLinearGroup.map (algebraMap F (A F)) γ) T → ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → wt M (mob ρ γ τ) * ‖𝒟 (T φ) (mob ρ γ τ)‖ = wt M τ * ‖𝒟 φ τ‖ := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ 𝒟 hD γ T hT φ τ hφ hτ
  have H := GlobalTheory.T.weil_representation_quadratic_datum F lf hlf h1 ψ hψ ι B hQ.2.2.1 hQ.2.2.2.1
  obtain ⟨T₀, a1, a2⟩ := good_ex hlf h1 hψ hQ hD γ
  obtain ⟨c, hc, e⟩ := impl_uniq H a1 hT
  rw [e φ hφ, (hD _ _ (a1.1 φ hφ) fun w => ((GlobalTheory.T.mobius_action_upper_half_plane F ρ τ hτ).1 γ w).2).2.2.2, norm_mul, hc, one_mul]
  exact a2 φ τ hφ hτ

end PositivityTheory.PlacePermOperatorBicommutantSpan
