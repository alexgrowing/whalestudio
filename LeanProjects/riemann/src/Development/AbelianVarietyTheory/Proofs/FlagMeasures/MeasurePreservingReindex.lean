import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureLeCardMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevIteratedOneParameterSubgroups
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralProductExpChartAllRealPlacesLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousRepresentativePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTranslateLeMultiplicityFundamentalStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.SobolevBound

theorem prod_ofFn_single {M : Type*} [Monoid M] : ∀ {m : ℕ} (g : Fin m → M) (a : Fin m),
    (∀ i, i ≠ a → g i = 1) → (List.ofFn g).prod = g a
  | 0, _, a, _ => a.elim0
  | m + 1, g, a, h => by
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases (fun h => ?_) (fun a h => ?_) a h
    · rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact h _ (Fin.succ_ne_zero i)
    · rw [h 0 (Fin.succ_ne_zero a).symm, one_mul]
      exact prod_ofFn_single (fun i => g i.succ) a fun i hi => h _ fun e => hi (Fin.succ_injective _ e)

theorem prod_ofFn_block {M : Type*} [Monoid M] {m k : ℕ} (g : Fin m → Fin k → M) (a : Fin m)
    (h : ∀ i, i ≠ a → ∀ j, g i j = 1) :
    (List.ofFn fun l : Fin (m * k) => g l.divNat l.modNat).prod = (List.ofFn (g a)).prod := by
  rw [List.ofFn_mul, List.prod_flatten, List.map_ofFn]
  have e : ∀ (i : Fin m) (j : Fin k) (p : i.val * k + j.val < m * k),
      g (Fin.divNat ⟨i.val * k + j.val, p⟩) (Fin.modNat ⟨i.val * k + j.val, p⟩) = g i j := by
    intro i j p
    have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) j.2
    congr 1
    · ext
      simp only [Fin.divNat]
      rw [mul_comm, Nat.mul_add_div hk, Nat.div_eq_of_lt j.2, add_zero]
    · ext
      simp only [Fin.modNat]
      rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt j.2]
  simp only [e]
  rw [prod_ofFn_single _ a]
  · rfl
  · intro i hi
    apply List.prod_eq_one
    intro x hx
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact h i hi j

theorem measurePreserving_reindex {ι κ L : Type} [Fintype ι] [Fintype κ] [Fintype L] (e : L ≃ ι × κ) :
    MeasurePreserving (fun (t : ι → κ → ℝ) (l : L) => t (e l).1 (e l).2) volume volume := by
  have hm : Measurable (fun (t : ι → κ → ℝ) (l : L) => t (e l).1 (e l).2) := by fun_prop
  refine ⟨hm, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun (t : ι → κ → ℝ) (l : L) => t (e l).1 (e l).2) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun v => Set.pi Set.univ fun j => s (e.symm (v, j)) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
    constructor
    · intro h v j
      simpa using h (e.symm (v, j))
    · intro h l
      simpa using h (e l).1 (e l).2
  rw [this, volume_pi_pi]
  simp only [volume_pi_pi]
  rw [← Fintype.prod_prod_type' (f := fun v j => volume (s (e.symm (v, j))))]
  exact Fintype.prod_equiv e.symm _ _ fun _ => rfl

theorem gauge_pos {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) : 0 < c := by
  have h0 : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  obtain ⟨r, h1, h2⟩ := ((h.eventually (lt_mem_nhds h0)).and self_mem_nhdsWithin).exists
  by_contra hc
  have h3 : (0 : ℝ) < r ^ (n ^ 2) := pow_pos h2 _
  exact absurd h1 (not_lt.2 (div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) ENNReal.toReal_nonneg) h3.le))

theorem card_places (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  haveI := I.cm.totReal
  rw [AutInst.f, IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]

theorem expU_zero {n : ℕ} {ε : Fin n → Bool} : expU (0 : gLie ε) = 1 :=
  Subtype.ext (Units.ext (by
    show NormedSpace.exp ((0 : gLie ε) : Matrix (Fin n) (Fin n) ℂ) = 1
    simp))

theorem expU_add {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (a b : ℝ) :
    expU ((a + b) • X) = expU (a • X) * expU (b • X) :=
  Subtype.ext (Units.ext (by
    show NormedSpace.exp ((a + b) • (X : Matrix (Fin n) (Fin n) ℂ)) =
      NormedSpace.exp (a • (X : Matrix (Fin n) (Fin n) ℂ)) * NormedSpace.exp (b • (X : Matrix (Fin n) (Fin n) ℂ))
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left a).smul_right b)))

theorem continuous_expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : Continuous fun t : ℝ => expU (t • X) := by
  have hc : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Continuous fun t : ℝ => NormedSpace.exp (t • Y) := by
    intro Y
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨hc X.1, ?_⟩) _
  have : ∀ t : ℝ, (expU (t • X))⁻¹ = expU ((-t) • X) := fun t => by
    rw [inv_eq_iff_mul_eq_one, ← expU_add, add_neg_cancel, zero_smul, expU_zero]
  have h2 : Continuous fun t : ℝ => uMat (expU ((-t) • X)) := (hc X.1).comp continuous_neg
  simp only [← this] at h2
  exact h2

theorem hs_eq_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : hs X = ((X * Xᴴ).trace).re := by
  simp [hs, Matrix.trace, Matrix.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]

noncomputable def onePar (B : RowsAut) (E : gInf B) (t : ℝ) : B.I.GA := ((fun v => expU (t • E v)), 1)

theorem onePar_spec (B : RowsAut) (E : gInf B) :
    Continuous (onePar B E) ∧ onePar B E 0 = 1 ∧ ∀ a b, onePar B E (a + b) = onePar B E a * onePar B E b := by
  refine ⟨(continuous_pi fun v => continuous_expU (E v)).prodMk continuous_const, ?_, fun a b => ?_⟩
  · refine Prod.ext (funext fun v => ?_) rfl
    simp [onePar, expU_zero]
  · refine Prod.ext (funext fun v => ?_) (by simp [onePar])
    simp [onePar, expU_add]

noncomputable def matAt (I : AutInst) (v : InfinitePlace I.F) : I.GA →* Matrix (Fin I.n) (Fin I.n) ℂ where
  toFun x := uMat (x.1 v)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem cube_bound (B : RowsAut) (c : InfinitePlace B.I.F → ℝ) (s : ℝ) {m : ℕ} (e : Fin m ≃ InfinitePlace B.I.F)
    (E : ∀ v, Fin (B.I.n ^ 2) → gLie (B.I.ε v)) (hn : 1 ≤ B.I.n) (hg : 1 ≤ B.g)
    (hc : ∀ v, IsGauge (B.I.ε v) (c v))
    (hE : ∀ v i j, (((E v i).1 * (E v j).1ᴴ).trace).re = if i = j then 1 else 0)
    (hs : 0 < s) (h3 : 12 * (B.I.n : ℝ) ^ 3 * s ≤ 1) (h5 : 8 * (B.I.n : ℝ) ^ 5 * s ≤ 1)
    (F : B.I.L2 B.μf B.fund) (φ : B.I.GA → ℂ) (hφ : IsContRep B F φ)
    (hk : ∀ k ∈ B.I.Kg B.g, ∀ y, φ (y * (1, k)) = φ y) (y : B.I.GA) :
    ∫ t in Set.pi Set.univ (fun _ : Fin (m * B.I.n ^ 2) => Set.Icc (0 : ℝ) s),
      ‖φ (y * (List.ofFn fun l => onePar B (atPlace B (e l.divNat) (E _ l.modNat)) (t l)).prod)‖ ^ 2 ≤
      (Real.exp B.I.f * (1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) * (∏ v, c v) /
        (B.μf (B.I.Kg B.g)).toReal) * ‖F‖ ^ 2 := by
  classical
  set Pr : (Fin (m * B.I.n ^ 2) → ℝ) → B.I.GA := fun t =>
    (List.ofFn fun l => onePar B (atPlace B (e l.divNat) (E _ l.modNat)) (t l)).prod with hPr
  have hPc : Continuous Pr := by
    simp only [hPr, List.ofFn_eq_map]
    exact continuous_list_prod _ fun l _ => (onePar_spec B _).1.comp (continuous_apply l)
  have hP2 : ∀ t, (Pr t).2 = 1 := by
    intro t
    have := map_list_prod (MonoidHom.snd B.I.Ginf B.I.Gf)
      (List.ofFn fun l => onePar B (atPlace B (e l.divNat) (E _ l.modNat)) (t l))
    refine this.trans (List.prod_eq_one fun x hx => ?_)
    rw [List.map_ofFn] at hx
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    rfl
  let ee : Fin (m * B.I.n ^ 2) ≃ InfinitePlace B.I.F × Fin (B.I.n ^ 2) :=
    finProdFinEquiv.symm.trans (e.prodCongr (Equiv.refl _))
  let ψ : (InfinitePlace B.I.F → Fin (B.I.n ^ 2) → ℝ) → (Fin (m * B.I.n ^ 2) → ℝ) :=
    fun t l => t (ee l).1 (ee l).2
  have hψ : MeasurePreserving ψ volume volume := measurePreserving_reindex ee
  have hΘ : ∀ t v, uMat ((Pr (ψ t)).1 v) =
      (List.ofFn fun i => NormedSpace.exp ((t v i : ℂ) • (E v i).1)).prod := by
    intro t v
    have := map_list_prod (matAt B.I v)
      (List.ofFn fun l => onePar B (atPlace B (e l.divNat) (E _ l.modNat)) (ψ t l))
    refine this.trans ?_
    rw [List.map_ofFn]
    obtain ⟨a, rfl⟩ := e.surjective v
    refine (prod_ofFn_block (fun i j => matAt B.I (e a) (onePar B (atPlace B (e i) (E _ j)) (t (e i) j))) a ?_).trans ?_
    · intro i hi j
      have : e a ≠ e i := fun h => hi (e.injective h).symm
      simp [matAt, onePar, atPlace, Pi.single_eq_of_ne this]
    · congr 2
      funext j
      simp [matAt, onePar, atPlace]
  obtain ⟨S, hSm, hSd, hSi⟩ := GlobalTheory.T.lintegral_productExpChart_allRealPlaces_le B.I c s (fun v i => (E v i).1) (fun t => (Pr (ψ t)).1) hc
    (fun v i => (E v i).2) hE hs h3 h5 hΘ
  have hΦm : Measurable fun x => ‖φ x‖ₑ ^ 2 := (hφ.1.measurable.enorm.pow_const 2)
  have hU := GlobalTheory.T.lintegral_translate_le_multiplicity_fundamental B S y (fun x => ‖φ x‖ₑ ^ 2) hn hg hSm hSd hΦm
    (fun γ hγ z => by simp only [hφ.2.1 γ hγ z]) (fun k hk' z => by simp only [hk k hk' z])
  rw [((GlobalTheory.T.continuous_representative_properties B).2.2.2 F φ hφ).2] at hU
  have hJ := hSi (fun a => ‖φ (y * (a, 1))‖ₑ ^ 2)
    (hΦm.comp (continuous_const.mul (continuous_id.prodMk continuous_const)).measurable)
  obtain ⟨-, hK0, hK1⟩ := GlobalTheory.CongIndex.measure_Kset_le B.I B.μf B.g hg
  have hK2 : B.μf (B.I.Kg B.g) ≠ ⊤ := ((measure_mono fun x hx => hx.1).trans_lt hK1).ne
  have hK3 : 0 < (B.μf (B.I.Kg B.g)).toReal := ENNReal.toReal_pos hK0.ne' hK2
  have hcp : 0 ≤ ∏ v, c v := Finset.prod_nonneg fun v _ => (gauge_pos (hc v)).le
  have hM : 0 ≤ (1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) := by positivity
  set M := (1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f))
  have hcont : Continuous fun t => φ (y * Pr t) := hφ.1.comp (continuous_const.mul hPc)
  have hpre : ψ ⁻¹' Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) s) =
      Set.pi Set.univ (fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) s) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, ψ]
    constructor
    · intro h v j
      simpa using h (ee.symm (v, j))
    · intro h l
      exact h _ _
  have hL : ∫⁻ t in Set.pi Set.univ (fun _ : Fin (m * B.I.n ^ 2) => Set.Icc (0 : ℝ) s), ‖φ (y * Pr t)‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp B.I.f * ∏ v, c v) * ∫⁻ a in S, ‖φ (y * (a, 1))‖ₑ ^ 2 ∂(muInf B.I) := by
    rw [← hψ.setLIntegral_comp_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
      (hcont.measurable.enorm.pow_const 2), hpre]
    refine le_of_eq_of_le ?_ hJ
    congr 1
    funext t
    rw [← hP2 (ψ t)]
  have hI : ∫⁻ a in S, ‖φ (y * (a, 1))‖ₑ ^ 2 ∂(muInf B.I) ≤
      ENNReal.ofReal (M * ‖F‖ ^ 2 / (B.μf (B.I.Kg B.g)).toReal) := by
    rw [ENNReal.ofReal_div_of_pos hK3, ENNReal.ofReal_toReal hK2, ENNReal.ofReal_mul hM,
      ENNReal.le_div_iff_mul_le (Or.inl hK0.ne') (Or.inl hK2), mul_comm]
    exact hU
  show ∫ t in _, ‖φ (y * Pr t)‖ ^ 2 ≤ _
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun t => ‖φ (y * Pr t)‖ ^ 2) (Filter.Eventually.of_forall fun t => by positivity)
    (hcont.norm.pow 2).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  refine hL.trans ((mul_le_mul_right hI _).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem monotone₂ (n : ℕ) (b : ℝ) {P Q : ℕ} (h : P ≤ Q) : beP n b P ≤ beP n b Q := by
  have : (P : ℝ) ≤ Q := by exact_mod_cast h
  unfold beP
  linarith

theorem le_beP {n : ℕ} {b : ℝ} (hn : 8 ≤ n) (hb : (n : ℝ) ^ 19 ≤ b ^ 2) (P : ℕ) : 8 * (n : ℝ) ^ 5 ≤ beP n b P := by
  have h8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 (by linarith)
  have h2 : (n : ℝ) ^ 6 ≤ (n : ℝ) ^ 19 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h3 : 8 * (n : ℝ) ^ 5 ≤ (n : ℝ) ^ 6 := by
    rw [pow_succ' _ 5]; gcongr
  have h4 : b ^ 2 ≤ Real.sqrt n * b ^ 2 := le_mul_of_one_le_left (sq_nonneg b) h1
  have h5 : 0 ≤ 3 / 2 * ((n : ℝ) * Real.sqrt n) + 3 * (P : ℝ) := by positivity
  unfold beP
  linarith

theorem sobolev_bound : ∀ (B : RowsAut) (b : ℝ) (c : InfinitePlace B.I.F → ℝ) (P₀ : ℕ) (D : ℕ) (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ), 8 ≤ B.I.n → 1 ≤ B.g → (B.I.n : ℝ) ^ 19 ≤ b ^ 2 → (∀ v, IsGauge (B.I.ε v) (c v)) → (∀ P, StepBoundAt B b P) → (∀ i, IsReps B (T i) (Fr i)) → (∀ i u, ‖T i u‖ = ‖u‖) → ∀ (y : B.I.GA), ∀ u ∈ VP B P₀, ‖vv B Fr u y‖ ^ 2 ≤ (6 * beP B.I.n b (P₀ + B.I.n ^ 2 * B.I.f)) ^ (B.I.n ^ 2 * B.I.f) * Real.exp B.I.f * (1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) * D * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal * ‖u‖ ^ 2 := by
  intro B b c P₀ D T Fr hn hg hb hc hS hR hT y u hu
  have e : Fin B.I.f ≃ InfinitePlace B.I.F := (Fintype.equivFinOfCardEq (card_places B.I)).symm
  choose E₀ hE1 hE2 _ using fun v => GlobalTheory.LieONB.exists_orthonormal_basis B.I.n (B.I.ε v)
  let E : ∀ v, Fin (B.I.n ^ 2) → gLie (B.I.ε v) := fun v i => ⟨E₀ v i, (hE1 v i).1⟩
  have h8 : (8 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  set be := beP B.I.n b (P₀ + B.I.n ^ 2 * B.I.f) with hbe
  have hbe5 : 8 * (B.I.n : ℝ) ^ 5 ≤ be := le_beP hn hb _
  have hbe3 : 12 * (B.I.n : ℝ) ^ 3 ≤ be := by
    refine le_trans ?_ hbe5
    have : (B.I.n : ℝ) ^ 5 = (B.I.n : ℝ) ^ 2 * (B.I.n : ℝ) ^ 3 := by ring
    have h2 : (2 : ℝ) ≤ (B.I.n : ℝ) ^ 2 := by nlinarith
    have h3 : (0 : ℝ) ≤ (B.I.n : ℝ) ^ 3 := by positivity
    nlinarith
  have hbe0 : 0 < be := lt_of_lt_of_le (by positivity) hbe5
  have hcp : 0 ≤ ∏ v, c v := Finset.prod_nonneg fun v _ => (gauge_pos (hc v)).le
  set C := Real.exp B.I.f * (1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) * (∏ v, c v) /
        (B.μf (B.I.Kg B.g)).toReal with hC
  have hC0 : 0 ≤ C := by positivity
  have key : ∀ i, ‖Fr i u y‖ ^ 2 ≤ (6 * be) ^ (B.I.n ^ 2 * B.I.f) * C * ‖u‖ ^ 2 := by
    intro i
    have h := GlobalTheory.sobolev_iterated_one_parameter_subgroups B.I.GA B.Hs ℂ (B.I.f * B.I.n ^ 2) P₀
      (fun l => onePar B (atPlace B (e l.divNat) (E _ l.modNat))) (fun p => (VP B p : Set B.Hs))
      (fun l => dAct B (atPlace B (e l.divNat) (E _ l.modNat))) (Fr i) (1 / be) be C y (by positivity) hbe0.le hC0
      (fun l => onePar_spec B _) (fun p q h => stepSpan_mono B h)
      (fun p w hw => ⟨(hR i p w hw).1.1, fun l => ⟨(hS p).2.2.2.2.2.2 _ w hw, fun x => (hR i p w hw).2.2 _ x⟩⟩)
      (fun p hp w hw l => ?_) (fun w hw => ?_) u hu
    · rw [mul_comm B.I.f] at h
      refine h.trans ?_
      have : 2 / (1 / be) + 2 * (1 / be) * be ^ 2 = 4 * be := by field_simp; ring
      rw [this]
      gcongr
      norm_num
    · refine ((hS p).2.2.2.2.1 _ _ w hw).trans ?_
      have h1 : hs (E (e l.divNat) l.modNat).1 = 1 := by
        rw [hs_eq_trace]; simpa using hE2 (e l.divNat) l.modNat l.modNat
      rw [h1, Real.sqrt_one, one_mul]
      rw [mul_comm B.I.f] at hp
      exact mul_le_mul_of_nonneg_right (monotone₂ _ _ hp) (norm_nonneg _)
    · rw [← hT i w]
      exact cube_bound B c (1 / be) e E (by omega) hg hc hE2 (by positivity)
        (by rw [mul_one_div, div_le_one hbe0]; exact hbe3) (by rw [mul_one_div, div_le_one hbe0]; exact hbe5)
        (T i w) (Fr i w) (hR i _ w hw).1 (hR i _ w hw).2.1 y
  rw [EuclideanSpace.norm_sq_eq]
  refine (Finset.sum_le_sum fun i _ => key i).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hC]
  ring

end GlobalTheory.SobolevBound
