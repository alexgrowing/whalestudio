import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.FComb
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
import GroundTheory.AutomorphicForms.GL2.InnerProductParamHolo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergMeromorphicContinuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalTorusIntegralIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFourierTransformIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionGlTwoHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCoordinatesBoundedRegion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaRegionMeasureBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnramifiedShellFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerIwasawaGrowthBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeometricSumBelowThreshold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableZFOfBound

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Filter Topology
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.LFHolP

open Ad3 Ad3.LFS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def Jf (W' : GL (Fin 2) F → ℂ) (c : Fˣ →* ℂˣ) (s : ℂ) (k : GL (Fin 2) F) : ℂ :=
  ∫ a, W' (dg2 a 1 * k⁻¹) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F

def dk (k : GL (Fin 2) F) : ℝ := (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ)

theorem dk_pos (k : GL (Fin 2) F) : 0 < dk k := by
  unfold dk
  exact_mod_cast modulus_pos (Units.ne_zero _)

theorem continuous_dk : Continuous (dk : GL (Fin 2) F → ℝ) := by
  have hval : Continuous fun k : GL (Fin 2) F => (k : Matrix (Fin 2) (Fin 2) F) := Units.continuous_val
  have hmod : Continuous fun x : F => (modulus x : ℝ) := NNReal.continuous_coe.comp continuous_modulus
  have : Continuous fun k : GL (Fin 2) F => ((GeneralLinearGroup.det k : Fˣ) : F) := by
    simpa using hval.matrix_det
  exact hmod.comp this

theorem norm_mp_det (k : GL (Fin 2) F) (z : ℂ) : ‖mp (GeneralLinearGroup.det k) z‖ = dk k ^ z.re :=
  GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.norm_mp _ z

theorem continuous_mp_det (z : ℂ) : Continuous fun k : GL (Fin 2) F => mp (GeneralLinearGroup.det k) z := by
  have h : Continuous fun k : GL (Fin 2) F => ((dk k : ℝ) : ℂ) := Complex.continuous_ofReal.comp continuous_dk
  exact h.cpow continuous_const fun k => Complex.ofReal_mem_slitPlane.2 (dk_pos k)

theorem inn_bound {ψ : AddChar F Circle} (hψ : IsStd ψ) {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} (hΦ : Φ ∈ SB F) :
    ∃ C R : ℝ, ∀ k : GL (Fin 2) F, ‖inn ψ Φ k 1‖ * dk k ≤ C ∧ (inn ψ Φ k 1 ≠ 0 → k ∈ om R (1 : Fˣ)) := by
  obtain ⟨C, R, h⟩ := GlobalTheory.CompanionTheory.LFFour.gFour F ψ hψ Φ hΦ
  have e1 : dg (1 : Fˣ) 1 1 = (1 : GL (Fin 3) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg]
  have e2 : dg2 (1 : Fˣ) 1 = (1 : GL (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2]
  have key : ∀ k : GL (Fin 2) F, inn ψ Φ k 1 = mp (GeneralLinearGroup.det k) (-1) *
      pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F) (fun j => ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) := by
    intro k
    have := GlobalTheory.CompanionTheory.LFGTorus.inn_dg ψ Φ k 1 1
    simpa [e1, e2] using this
  refine ⟨C, R, fun k => ⟨?_, fun hne => ?_⟩⟩
  · have hd := dk_pos k
    rw [key, norm_mul, norm_mp_det]
    have : dk k ^ (-1 : ℂ).re * dk k = 1 := by
      simp only [Complex.neg_re, Complex.one_re, Real.rpow_neg_one]
      exact inv_mul_cancel₀ hd.ne'
    calc _ = (dk k ^ (-1 : ℂ).re * dk k) * ‖pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F) (fun j => ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j)‖ := by ring
      _ ≤ C := by rw [this, one_mul]; exact (h _ _).1
  · have hp : pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F) (fun j => ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) ≠ 0 := by
      intro h0
      exact hne (by rw [key, h0, mul_zero])
    obtain ⟨h1, h2⟩ := (h _ _).2 hp
    exact ⟨h1, fun j => by simpa using h2 j⟩

theorem continuous_Jf {W' : GL (Fin 2) F → ℂ}
    (hU : ∃ U : OpenSubgroup (GL (Fin 2) F), ∀ g, ∀ u ∈ U, W' (g * u) = W' g) (c : Fˣ →* ℂˣ) (s : ℂ) :
    Continuous (Jf W' c s) := by
  obtain ⟨U, hU⟩ := hU
  have hl : IsLocallyConstant fun g : GL (Fin 2) F => Jf W' c s g⁻¹ := by
    refine GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.isLocallyConstant_of_invariant _ U.toSubgroup U.isOpen fun g u hu => ?_
    simp only [Jf, inv_inv, ← mul_assoc, hU _ u hu]
  have := hl.continuous.comp (continuous_inv (G := GL (Fin 2) F))
  simpa [Function.comp_def] using this

theorem dk_iwasawa_inv (x : F) (a b : Fˣ) (κ : GL (Fin 2) F) (hκ : κ ∈ GLnLocal.integralGL F 2) :
    dk (Ad3.uni2 x * Ad3.dg2 a b * κ)⁻¹ = ((modulus (a : F) : ℝ) * (modulus (b : F) : ℝ))⁻¹ := by
  unfold dk
  have hκ1 : modulus ((Matrix.GeneralLinearGroup.det κ : Fˣ) : F) = 1 := by
    obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hκ
    have key : ∀ g : GL (Fin 2) F, (∀ i j, g i j ∈ 𝒪[F]) →
        modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ≤ 1 := by
      intro g hg
      rw [modulus_le_one_iff, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      exact sub_mem (mul_mem (hg 0 0) (hg 1 1)) (mul_mem (hg 0 1) (hg 1 0))
    have a' := key κ h1
    have b' := key κ⁻¹ h2
    rw [map_inv, Units.val_inv_eq_inv_val, modulus_inv] at b'
    have hpos := modulus_pos (Matrix.GeneralLinearGroup.det κ : Fˣ).ne_zero
    exact le_antisymm a' ((inv_le_one₀ hpos).1 b')
  have hd1 : Matrix.GeneralLinearGroup.det (Ad3.uni2 x) = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Ad3.uni2, Matrix.det_fin_two]
  have hd2 : Matrix.GeneralLinearGroup.det (Ad3.dg2 a b) = a * b := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Ad3.dg2, Matrix.det_fin_two]
  rw [map_inv, map_mul, map_mul, hd1, hd2, one_mul, Units.val_inv_eq_inv_val, modulus_inv, Units.val_mul,
    modulus_mul, hκ1, mul_one, Units.val_mul, modulus_mul]
  push_cast
  rfl

theorem exists_left_invariant {Φ : Matrix (Fin 2) (Fin 3) F → ℂ}
    (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) :
    ∃ U : OpenSubgroup (GL (Fin 2) F), ∀ u ∈ U, ∀ X : Matrix (Fin 2) (Fin 3) F,
        Φ ((u : Matrix (Fin 2) (Fin 2) F) * X) = Φ X := by
  have hcont : Continuous fun p : Matrix (Fin 2) (Fin 3) F × GL (Fin 2) F =>
      (p.2 : Matrix (Fin 2) (Fin 2) F) * p.1 :=
    (Units.continuous_val.comp continuous_snd).matrix_mul continuous_fst
  have hlc : IsLocallyConstant fun p : Matrix (Fin 2) (Fin 3) F × GL (Fin 2) F =>
      Φ ((p.2 : Matrix (Fin 2) (Fin 2) F) * p.1) - Φ p.1 :=
    (hl.comp_continuous hcont).sub (hl.comp_continuous continuous_fst)
  have hopen := hlc.isOpen_fiber 0
  have hsub : tsupport Φ ×ˢ ({1} : Set (GL (Fin 2) F)) ⊆
      (fun p : Matrix (Fin 2) (Fin 3) F × GL (Fin 2) F =>
        Φ ((p.2 : Matrix (Fin 2) (Fin 2) F) * p.1) - Φ p.1) ⁻¹' {0} := by
    rintro ⟨X, u⟩ ⟨-, hu⟩
    obtain rfl : u = 1 := hu
    simp
  obtain ⟨A, B, -, hB, hA, h1, hAB⟩ :=
    generalized_tube_lemma hc isCompact_singleton hopen hsub
  obtain ⟨m, -, hm⟩ :=
    (GLnLocal.hasBasis_nhds_one F 2).mem_iff.1 (hB.mem_nhds (h1 rfl))
  have hfix : ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, ∀ X, Φ X ≠ 0 →
      Φ ((u : Matrix (Fin 2) (Fin 2) F) * X) = Φ X := by
    intro u hu X hX
    have : (X, u) ∈ A ×ˢ B := ⟨hA (subset_tsupport _ hX), hm hu⟩
    exact sub_eq_zero.1 (hAB this)
  refine ⟨⟨GLnLocal.congruenceSubgroup F 2 m, GLnLocal.isOpen_congruenceSubgroup F 2 m⟩,
    fun u hu X => ?_⟩
  have hu' : u ∈ GLnLocal.congruenceSubgroup F 2 m := hu
  by_cases hX : Φ X = 0
  · by_cases hY : Φ ((u : Matrix (Fin 2) (Fin 2) F) * X) = 0
    · rw [hX, hY]
    · have h := hfix u⁻¹ (inv_mem hu') _ hY
      rw [← Matrix.mul_assoc, Units.inv_mul_of_eq rfl, Matrix.one_mul] at h
      exact h.symm
  · exact hfix u hu' X hX

theorem cont_inn (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (hΦ : Φ ∈ SB F) :
    Continuous fun k : GL (Fin 2) F => inn ψ Φ k 1 := by
  obtain ⟨U, hU⟩ := exists_left_invariant hΦ.1 hΦ.2
  have hl : IsLocallyConstant fun g : GL (Fin 2) F => inn ψ Φ g⁻¹ 1 := by
    refine GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.isLocallyConstant_of_invariant _ U.toSubgroup U.isOpen fun g u hu => ?_
    have hu' : u⁻¹ ∈ U := inv_mem hu
    simp only [inn, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, hU _ hu']
  have := hl.continuous.comp (continuous_inv (G := GL (Fin 2) F))
  simpa [Function.comp_def] using this

theorem shell_fin {X : Type} [MeasurableSpace X] (μ : Measure X) (q A α β : ℝ) (L : ℤ) (c : ℝ≥0∞)
    (S : ℤ → ℤ → Set X) (Φ : X → ℝ≥0∞) (hq : 1 < q) (hA : 0 ≤ A) (hα : 0 < α) (hc : c ≠ ∞)
    (hS : ∀ m n, MeasurableSet (S m n)) (hμ : ∀ m n, n ≤ L → μ (S m n) ≤ ENNReal.ofReal (q ^ (L - n)) * c)
    (hcov : ∀ y, Φ y ≠ 0 → ∃ m n : ℤ, m ≤ L ∧ -L ≤ n ∧ n ≤ L ∧ y ∈ S m n ∧
      Φ y ≤ ENNReal.ofReal (A * q ^ (α * (m : ℝ)) * q ^ (β * (n : ℝ)))) :
    ∫⁻ y, Φ y ∂μ < ∞ := by
  classical
  have hq0 : 0 < q := by linarith
  set w : ℤ × ℤ → ℝ≥0∞ := fun p => if p.1 ≤ L ∧ -L ≤ p.2 ∧ p.2 ≤ L then
    ENNReal.ofReal (A * q ^ (α * (p.1 : ℝ)) * q ^ (β * (p.2 : ℝ))) else 0 with hw
  set a : ℤ → ℝ≥0∞ := fun m => if q ^ m ≤ q ^ L then ENNReal.ofReal (q ^ (α * (m : ℝ))) else 0 with ha
  set b : ℤ → ℝ≥0∞ := fun n => if n ∈ Finset.Icc (-L) L then
    ENNReal.ofReal (A * q ^ (β * (n : ℝ))) * ENNReal.ofReal (q ^ (L - n)) else 0 with hb
  have hpt : ∀ y, Φ y ≤ ∑' p : ℤ × ℤ, (S p.1 p.2).indicator (fun _ => w p) y := by
    intro y
    by_cases h0 : Φ y = 0
    · rw [h0]; exact zero_le
    obtain ⟨m, n, h1, h2, h3, h4, h5⟩ := hcov y h0
    refine le_trans ?_ (ENNReal.le_tsum (m, n))
    simp only [Set.indicator_of_mem h4, hw, h1, h2, h3, and_self, if_true]
    exact h5
  have hterm : ∀ p : ℤ × ℤ, w p * μ (S p.1 p.2) ≤ a p.1 * b p.2 * c := by
    rintro ⟨m, n⟩
    by_cases h : m ≤ L ∧ -L ≤ n ∧ n ≤ L
    · obtain ⟨h1, h2, h3⟩ := h
      have h1' : q ^ m ≤ q ^ L := zpow_le_zpow_right₀ hq.le h1
      have hmem : n ∈ Finset.Icc (-L) L := Finset.mem_Icc.2 ⟨h2, h3⟩
      simp only [hw, ha, hb, h1, h1', h2, h3, hmem, and_self, if_true]
      calc _ ≤ ENNReal.ofReal (A * q ^ (α * (m : ℝ)) * q ^ (β * (n : ℝ))) * (ENNReal.ofReal (q ^ (L - n)) * c) :=
            mul_le_mul_right (hμ m n h3) _
        _ = _ := by
            rw [show A * q ^ (α * (m : ℝ)) * q ^ (β * (n : ℝ)) = q ^ (α * (m : ℝ)) * (A * q ^ (β * (n : ℝ))) by ring,
              ENNReal.ofReal_mul (by positivity)]
            ring
    · have : w (m, n) = 0 := by simp only [hw]; rw [if_neg h]
      rw [this, zero_mul]
      exact zero_le
  have hTa : ∑' m, a m < ∞ :=
    (GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div q α (q ^ L) hq hα (zpow_pos hq0 L)).trans_lt ENNReal.ofReal_lt_top
  have hTb : ∑' n, b n < ∞ := by
    rw [tsum_eq_sum (s := Finset.Icc (-L) L) (fun n hn => by simp only [hb]; rw [if_neg hn])]
    refine ENNReal.sum_lt_top.2 fun n hn => ?_
    simp only [hb]
    rw [if_pos hn]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  calc ∫⁻ y, Φ y ∂μ ≤ ∫⁻ y, ∑' p : ℤ × ℤ, (S p.1 p.2).indicator (fun _ => w p) y ∂μ := lintegral_mono hpt
    _ = ∑' p : ℤ × ℤ, ∫⁻ y, (S p.1 p.2).indicator (fun _ => w p) y ∂μ :=
        lintegral_tsum fun p => (measurable_const.indicator (hS _ _)).aemeasurable
    _ = ∑' p : ℤ × ℤ, w p * μ (S p.1 p.2) := by
        refine tsum_congr fun p => ?_
        exact lintegral_indicator_const (hS _ _) _
    _ ≤ ∑' p : ℤ × ℤ, a p.1 * b p.2 * c := ENNReal.tsum_le_tsum hterm
    _ = (∑' m, a m) * (∑' n, b n) * c := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_prod']
        congr 1
        simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hTa hTb) hc.lt_top

theorem continuous_diag_unit_one : Continuous fun a : Fˣ => (dg2 a 1 : GL (Fin 2) F) := by
  have hinv : Continuous fun a : Fˣ => ((a⁻¹ : Fˣ) : F) := Units.continuous_val.comp continuous_inv
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> first | exact Units.continuous_val | exact continuous_const
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> first | exact hinv | exact continuous_const

theorem whit_int : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (V' : Submodule ℂ (GL (Fin 2) F → ℂ)), Ad3.WhittakerModelGL2 ψ ν ν⁻¹ V' → ∀ W' ∈ V', ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : F) (b₁ b₂ : Fˣ), ∀ κ ∈ GLnLocal.integralGL F 2, Integrable (fun a : Fˣ => ‖W' (Ad3.dg2 a 1 * (Ad3.uni2 x * Ad3.dg2 b₁ b₂ * κ))‖ * (modulus (a : F) : ℝ) ^ (σ - 1 / 2)) (multHaar F) ∧ ∫ a : Fˣ, ‖W' (Ad3.dg2 a 1 * (Ad3.uni2 x * Ad3.dg2 b₁ b₂ * κ))‖ * (modulus (a : F) : ℝ) ^ (σ - 1 / 2) ∂multHaar F ≤ C * ((modulus (b₁ : F) : ℝ) / (modulus (b₂ : F) : ℝ)) ^ (1 / 2 - σ) := by
  intro F _ _ _ _ _ _ ψ ν V' H W' hW' σ hσ
  obtain ⟨C, B, hCB⟩ := H.bound W' hW' (σ / 2) (by positivity)
  have hq : (1 : ℝ) < residueCard F := by exact_mod_cast one_lt_residueCard (K := F)
  have hq0 : (0 : ℝ) < residueCard F := by linarith
  set p : ℝ := (residueCard F : ℝ) ^ (-(1 : ℝ)) with hp
  set r : ℝ := (residueCard F : ℝ) ^ (-(σ / 2)) with hr
  have hp0 : 0 < p := Real.rpow_pos_of_pos hq0 _
  have hr0 : 0 < r := Real.rpow_pos_of_pos hq0 _
  have hp1 : p < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num)
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  set g : ℤ → ℂ := fun k => (((if p ^ k ≤ B then C * r ^ k else 0 : ℝ) : ℂ)) with hg
  have hI := (GlobalTheory.CompanionTheory.LU.sShell F g (GlobalTheory.CompanionTheory.LFGInt.summable_cut hp0 hp1 hr0 hr1)).1
  set M : Fˣ → ℝ := fun a => ‖g (ord (a : F))‖ with hM
  have hMi : Integrable M (multHaar F) := hI.norm
  have hmaj : ∀ κ ∈ GLnLocal.integralGL F 2, ∀ a : Fˣ,
      ‖W' (dg2 a 1 * κ)‖ * (modulus (a : F) : ℝ) ^ (σ - 1 / 2) ≤ M a := by
    intro κ hκ a
    have hm := GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.modulus_pos' a
    by_cases h0 : W' (dg2 a 1 * κ) = 0
    · simp only [h0, norm_zero, zero_mul, hM]
      exact norm_nonneg _
    have hB := (hCB a κ hκ).2 h0
    have h1 : p ^ ord (a : F) ≤ B := by
      have := GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.modulus_rpow a 1
      rw [Real.rpow_one] at this
      rwa [← this]
    have hgv : g (ord (a : F)) = ((C * r ^ ord (a : F) : ℝ) : ℂ) := by simp [hg, h1]
    simp only [hM]
    rw [hgv, Complex.norm_real, Real.norm_eq_abs]
    refine le_trans ?_ (le_abs_self _)
    rw [← GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.modulus_rpow a (σ / 2)]
    calc ‖W' (dg2 a 1 * κ)‖ * (modulus (a : F) : ℝ) ^ (σ - 1 / 2)
        ≤ (C * (modulus (a : F) : ℝ) ^ (1 / 2 - σ / 2)) * (modulus (a : F) : ℝ) ^ (σ - 1 / 2) :=
          mul_le_mul_of_nonneg_right (hCB a κ hκ).1 (Real.rpow_nonneg hm.le _)
      _ = C * (modulus (a : F) : ℝ) ^ (σ / 2) := by
          rw [mul_assoc, ← Real.rpow_add hm]
          congr 2
          ring
  obtain ⟨U, hU⟩ := H.smooth W' hW'
  have hWc : Continuous W' :=
    (GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.isLocallyConstant_of_invariant W' U.toSubgroup U.isOpen hU).continuous
  have hmodc : Continuous fun a : Fˣ => (modulus (a : F) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val)
  refine ⟨∫ a, M a ∂multHaar F, integral_nonneg fun _ => norm_nonneg _, fun x b₁ b₂ κ hκ => ?_⟩
  set G : Fˣ → ℝ := fun a => ‖W' (dg2 a 1 * κ)‖ * (modulus (a : F) : ℝ) ^ (σ - 1 / 2) with hG'
  have hGc : Continuous G :=
    (hWc.comp (continuous_diag_unit_one.mul continuous_const)).norm.mul
      (hmodc.rpow_const fun a => Or.inl (GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.modulus_pos' a).ne')
  have hGi : Integrable G (multHaar F) :=
    hMi.mono' hGc.aestronglyMeasurable (Eventually.of_forall (fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.modulus_pos' a).le _))]
      exact hmaj κ hκ a))
  have hGle : ∫ a, G a ∂multHaar F ≤ ∫ a, M a ∂multHaar F := integral_mono hGi hMi (hmaj κ hκ)
  set u : Fˣ := b₁ * b₂⁻¹ with hu
  set T : ℝ := ((modulus (b₁ : F) : ℝ) / (modulus (b₂ : F) : ℝ)) ^ (1 / 2 - σ) with hT
  have hb₁ := GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.modulus_pos' b₁
  have hb₂ := GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.modulus_pos' b₂
  have hT0 : 0 ≤ T := by positivity
  have hmu : (modulus (u : F) : ℝ) = (modulus (b₁ : F) : ℝ) / (modulus (b₂ : F) : ℝ) := by
    rw [hu, Units.val_mul, modulus_mul, Units.val_inv_eq_inv_val, modulus_inv]
    simp [div_eq_mul_inv]
  have hpt : ∀ a : Fˣ, ‖W' (dg2 a 1 * (uni2 x * dg2 b₁ b₂ * κ))‖ * (modulus (a : F) : ℝ) ^ (σ - 1 / 2) =
      T * G (a * u) := by
    intro a
    have hm := GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.modulus_pos' a
    have e : dg2 a 1 * (uni2 x * dg2 b₁ b₂ * κ) =
        uni2 ((a : F) * x * (((1 : Fˣ)⁻¹ : Fˣ) : F)) * (dg2 (1 * b₂) (1 * b₂) *
          (dg2 (a * b₁ * (1 * b₂)⁻¹) 1 * κ)) := by
      rw [← mul_assoc (dg2 (1 * b₂) (1 * b₂)), ← GlobalTheory.CompanionTheory.WhittakerIwasawa.diagonal_mul_diagonal_alt, ← mul_assoc, ← mul_assoc,
        ← mul_assoc, GlobalTheory.CompanionTheory.WhittakerIwasawa.diagonal_mul_unipotent]
      simp only [mul_assoc]
    have e2 : a * b₁ * (1 * b₂)⁻¹ = a * u := by rw [hu, one_mul, mul_assoc]
    have hcen : ∀ (a : Fˣ) g, W' (dg2 a a * g) = W' g := by
      intro a g
      rw [H.cen W' hW']
      simp
    rw [e, H.psi W' hW', hcen, norm_mul, Circle.norm_coe, one_mul, e2]
    simp only [hG']
    rw [Units.val_mul, modulus_mul, NNReal.coe_mul, hmu, Real.mul_rpow hm.le (by positivity), hT]
    have hc : ((modulus (b₁ : F) : ℝ) / (modulus (b₂ : F) : ℝ)) ^ (1 / 2 - σ) *
        ((modulus (b₁ : F) : ℝ) / (modulus (b₂ : F) : ℝ)) ^ (σ - 1 / 2) = 1 := by
      rw [← Real.rpow_add (by positivity)]
      simp
    linear_combination (-(‖W' (dg2 (a * u) 1 * κ)‖ * (modulus (a : F) : ℝ) ^ (σ - 1 / 2))) * hc
  simp only [hpt]
  refine ⟨(hGi.comp_mul_right u).const_mul T, ?_⟩
  rw [integral_const_mul, integral_mul_right_eq_self G u, mul_comm]
  exact mul_le_mul_of_nonneg_right hGle hT0

theorem integrable_major {ψ : AddChar F Circle} {ν : Fˣ →* ℂˣ} {W' : GL (Fin 2) F → ℂ}
    {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} (hyp : Hyp ψ ν W' Φ) {c : Fˣ →* ℂˣ} (hc : IsUnit1 c) {s : ℂ}
    (hs : 1 / 4 < s.re) {r : ℝ} (hr : -(1 / 16) < r) :
    Integrable (fun k : GL (Fin 2) F => ‖inn ψ Φ k 1‖ * dk k ^ (3 / 2 + r) * ‖Jf W' c s k‖) (hG ψ) := by
  obtain ⟨hψ, hν, ⟨V', hV, hW'⟩, hΦ⟩ := hyp
  classical
  obtain ⟨C₁, R, hCR⟩ := inn_bound hψ hΦ
  obtain ⟨C₂, hC₂0, hC₂⟩ := whit_int F ψ ν V' hV W' hW' s.re (by linarith)
  set q : ℝ := (residueCard F : ℝ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast (one_lt_residueCard (K := F))
  have hq0 : 0 < q := by linarith
  obtain ⟨L₀, hL₀⟩ := pow_unbounded_of_one_lt R hq
  set L : ℤ := (L₀ : ℤ) with hLdef
  have hRL : R ≤ q ^ L := by rw [hLdef, zpow_natCast]; exact hL₀.le
  haveI hμ : (hG ψ).IsHaarMeasure := by unfold hG; infer_instance
  haveI hinv : (hG ψ).IsInvInvariant := ⟨Measures.inv_eq_self_GL F 2 (hG ψ)⟩
  set Kμ : ℝ≥0∞ := hG ψ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) with hKμ
  have hKfin : Kμ ≠ ∞ := (GLnLocal.isCompact_integralGL F 2).measure_lt_top.ne
  set f : GL (Fin 2) F → ℝ := fun k => ‖inn ψ Φ k 1‖ * dk k ^ (3 / 2 + r) * ‖Jf W' c s k‖ with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => mul_nonneg (mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (dk_pos k).le _)) (norm_nonneg _)
  have hfc : Continuous f :=
    ((cont_inn ψ Φ hΦ).norm.mul (continuous_dk.rpow_const fun k => Or.inl (dk_pos k).ne')).mul
      (continuous_Jf (hV.smooth W' hW') c s).norm
  set C₁' : ℝ := max C₁ 0 with hC₁'
  have hC₁0 : 0 ≤ C₁' := le_max_right _ _
  set A : ℝ := C₁' * C₂ with hA
  have hA0 : 0 ≤ A := mul_nonneg hC₁0 hC₂0
  set S : ℤ → ℤ → Set (GL (Fin 2) F) := fun m n => {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ q ^ (L - m) ∧
    ∃ κ ∈ GLnLocal.integralGL F 2, g = uni2 x * dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} with hS
  set Ψ : GL (Fin 2) F → ℝ≥0∞ := fun g => ENNReal.ofReal (f g⁻¹) with hΨ
  have hu : ∀ k : ℤ, (modulus (((unifUnit F ^ k : Fˣ)) : F) : ℝ) = q ^ (-(k : ℝ)) := by
    intro k
    rw [modulus_of_ne_zero (Units.ne_zero _), ord_unifUnit_zpow, NNReal.coe_zpow, NNReal.coe_natCast,
      ← Real.rpow_intCast]
    push_cast
    rfl
  have hcov : ∀ y, Ψ y ≠ 0 → ∃ m n : ℤ, m ≤ L ∧ -L ≤ n ∧ n ≤ L ∧ y ∈ S m n ∧
      Ψ y ≤ ENNReal.ofReal (A * q ^ ((r + s.re) * (m : ℝ)) * q ^ ((1 + r - s.re) * (n : ℝ))) := by
    intro g hg
    have hinn : inn ψ Φ g⁻¹ 1 ≠ 0 := by
      intro h
      exact hg (by simp [hΨ, hf, h])
    have hom := (hCR g⁻¹).2 hinn
    obtain ⟨x, m, n, κ, hκ, rfl⟩ := GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two F g
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.CompanionTheory.LFCoords.coords F x m n L κ R 1 hκ hRL hom
    have hn : -L ≤ n := by
      have h5 : q ^ (-n) ≤ q ^ L := by simpa using h4
      have := (zpow_le_zpow_iff_right₀ hq).1 h5
      omega
    refine ⟨m, n, h1, hn, h2, ⟨x, h3, κ, hκ, rfl⟩, ENNReal.ofReal_le_ofReal ?_⟩
    set g : GL (Fin 2) F := uni2 x * dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ with hgdef
    have hd : dk g⁻¹ = q ^ ((m : ℝ) + n) := by
      rw [hgdef, dk_iwasawa_inv x _ _ κ hκ, hu, hu, ← Real.rpow_add hq0, ← Real.rpow_neg hq0.le]
      congr 1
      ring
    have hdpos := dk_pos g⁻¹
    have hJ : ‖Jf W' c s g⁻¹‖ ≤ C₂ * q ^ (((n : ℝ) - m) * (1 / 2 - s.re)) := by
      have hb := (hC₂ x (unifUnit F ^ m) (unifUnit F ^ n) κ hκ).2
      rw [hu, hu, ← Real.rpow_sub hq0, ← Real.rpow_mul hq0.le,
        show (-(m : ℝ) - -(n : ℝ)) = (n : ℝ) - m by ring] at hb
      refine le_trans (norm_integral_le_integral_norm _) (le_trans (le_of_eq ?_) hb)
      refine integral_congr_ae (Eventually.of_forall fun a => ?_)
      have hca : ‖((c a : ℂˣ) : ℂ)‖ = 1 := hc.2 a
      simp only [norm_mul, inv_inv, hca, mul_one, GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.norm_mp]
      congr 2
      simp
    have hi : ‖inn ψ Φ g⁻¹ 1‖ * dk g⁻¹ ≤ C₁' := ((hCR g⁻¹).1).trans (le_max_left _ _)
    have hsplit : f g⁻¹ = (‖inn ψ Φ g⁻¹ 1‖ * dk g⁻¹) * dk g⁻¹ ^ (1 / 2 + r) * ‖Jf W' c s g⁻¹‖ := by
      simp only [hf]
      rw [show (3 / 2 + r : ℝ) = 1 + (1 / 2 + r) by ring, Real.rpow_add hdpos, Real.rpow_one]
      ring
    rw [hsplit]
    calc (‖inn ψ Φ g⁻¹ 1‖ * dk g⁻¹) * dk g⁻¹ ^ (1 / 2 + r) * ‖Jf W' c s g⁻¹‖
        ≤ C₁' * dk g⁻¹ ^ (1 / 2 + r) * (C₂ * q ^ (((n : ℝ) - m) * (1 / 2 - s.re))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hi (Real.rpow_nonneg hdpos.le _)) hJ (norm_nonneg _) ?_
          exact mul_nonneg hC₁0 (Real.rpow_nonneg hdpos.le _)
      _ = A * q ^ ((r + s.re) * (m : ℝ)) * q ^ ((1 + r - s.re) * (n : ℝ)) := by
          rw [hd, ← Real.rpow_mul hq0.le, hA]
          have e : ((r + s.re) * (m : ℝ)) + ((1 + r - s.re) * (n : ℝ)) =
              ((m : ℝ) + n) * (1 / 2 + r) + ((n : ℝ) - m) * (1 / 2 - s.re) := by ring
          rw [mul_assoc (C₁' * C₂), ← Real.rpow_add hq0, e, Real.rpow_add hq0]
          ring
  have hmain := shell_fin (hG ψ) q A (r + s.re) (1 + r - s.re) L Kμ S Ψ hq hA0 (by linarith) hKfin
    (fun m n => (GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume F (hG ψ) m n L).1.measurableSet)
    (fun m n hn => (GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume F (hG ψ) m n L).2 hn) hcov
  have hfm : Measurable f := hfc.measurable
  have hinvl : ∫⁻ k, ENNReal.ofReal (f k) ∂hG ψ = ∫⁻ g, Ψ g ∂hG ψ :=
    ((Measure.measurePreserving_inv (hG ψ)).lintegral_comp hfm.ennreal_ofReal).symm
  refine ⟨hfc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0), hinvl]
  exact hmain

theorem fHolP : Ad3.LFS.FHolP := by
  intro F _ _ _ _ _ _ ψ ν W' Φ hyp c hc s hs
  have hU : IsOpen {lam : ℂ | -(1 / 16) < lam.re} := isOpen_lt continuous_const Complex.continuous_re
  have hV := hyp.2.2.1
  obtain ⟨V', hV, hW'⟩ := hV
  have hci : Continuous fun k : GL (Fin 2) F => inn ψ Φ k 1 := cont_inn ψ Φ hyp.2.2.2
  have hcJ : Continuous (Jf W' c s) := continuous_Jf (hV.smooth W' hW') c s
  have key := GroundTheory.Automorphic.PseudoEisenstein.differentiableOn_integral_of_bound (μ := hG ψ)
    (F := fun lam k => inn ψ Φ k 1 * mp (GeneralLinearGroup.det k) (3 / 2 + lam) * Jf W' c s k) hU ?_ ?_ ?_
  · exact key
  · intro k lam _
    refine DifferentiableAt.differentiableWithinAt ?_
    have hb : ((modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) : ℂ) ≠ 0 := by
      have := dk_pos k
      unfold dk at this
      exact_mod_cast this.ne'
    have h1 : DifferentiableAt ℂ (fun lam : ℂ => mp (GeneralLinearGroup.det k) (3 / 2 + lam)) lam := by
      unfold mp
      exact ((differentiableAt_const _).add differentiableAt_id).const_cpow (Or.inl hb)
    exact ((differentiableAt_const _).mul h1).mul (differentiableAt_const _)
  · intro lam _
    exact ((hci.mul (continuous_mp_det _)).mul hcJ).aestronglyMeasurable
  · intro s₀ hs₀
    have hs₀' : -(1 / 16) < s₀.re := hs₀
    set ε : ℝ := (s₀.re + 1 / 16) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hre : ∀ lam ∈ Metric.closedBall s₀ ε, s₀.re - ε ≤ lam.re ∧ lam.re ≤ s₀.re + ε := by
      intro lam hl
      have h1 : |(lam - s₀).re| ≤ ‖lam - s₀‖ := Complex.abs_re_le_norm _
      have h2 : ‖lam - s₀‖ ≤ ε := by simpa [dist_eq_norm] using hl
      have h3 := abs_le.1 (h1.trans h2)
      simp only [Complex.sub_re] at h3
      constructor <;> linarith [h3.1, h3.2]
    refine ⟨ε, hε0, fun lam hl => ?_, ?_⟩
    · have := (hre lam hl).1
      show -(1 / 16) < lam.re
      rw [hε] at this
      linarith
    · have i1 := integrable_major hyp hc hs (r := s₀.re - ε) (by rw [hε]; linarith)
      have i2 := integrable_major hyp hc hs (r := s₀.re + ε) (by rw [hε]; linarith)
      refine ⟨_, i1.add i2, fun lam hl k => ?_⟩
      obtain ⟨h1, h2⟩ := hre lam hl
      have hd := dk_pos k
      have hle : dk k ^ (3 / 2 + lam.re) ≤ dk k ^ (3 / 2 + (s₀.re - ε)) + dk k ^ (3 / 2 + (s₀.re + ε)) := by
        rcases le_total 1 (dk k) with h | h
        · have := Real.rpow_le_rpow_of_exponent_le h (show 3 / 2 + lam.re ≤ 3 / 2 + (s₀.re + ε) by linarith)
          linarith [Real.rpow_nonneg hd.le (3 / 2 + (s₀.re - ε))]
        · have := Real.rpow_le_rpow_of_exponent_ge hd h (show 3 / 2 + (s₀.re - ε) ≤ 3 / 2 + lam.re by linarith)
          linarith [Real.rpow_nonneg hd.le (3 / 2 + (s₀.re + ε))]
      have hn : ‖mp (GeneralLinearGroup.det k) (3 / 2 + lam)‖ = dk k ^ (3 / 2 + lam.re) := by
        rw [norm_mp_det]
        congr 1
        simp
      simp only [norm_mul, hn, Pi.add_apply]
      have : ‖inn ψ Φ k 1‖ * dk k ^ (3 / 2 + lam.re) * ‖Jf W' c s k‖ ≤
          ‖inn ψ Φ k 1‖ * (dk k ^ (3 / 2 + (s₀.re - ε)) + dk k ^ (3 / 2 + (s₀.re + ε))) * ‖Jf W' c s k‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (norm_nonneg _)) (norm_nonneg _)
      linarith

end GlobalTheory.CompanionTheory.LFHolP
