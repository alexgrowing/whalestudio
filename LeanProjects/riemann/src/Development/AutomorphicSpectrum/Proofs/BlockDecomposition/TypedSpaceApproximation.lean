import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.AutomorphicLipschitz.NiceAut
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UpdateLeUpdate
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundConstantTermStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundOfArchimedeanLipschitzStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousArchimedeanSmoothingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothingLipschitzBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformFamilySmoothingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundSmoothingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KilledByPolynomialSmoothingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundSiegelSetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsSiegelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsExponentPolynomialDiscreteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothingFundamentalDomainIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothingFundamentalDomainBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionEquicontinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenIntegralSubgroupStatement
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem ubnd_mono {ι : Type*} {f : ι → AdelicGLn.AdelicGL K n → ℂ} {m m' : ℕ → ℝ}
    (hm : ∀ r, 0 < r → r < n → m r ≤ m' r) (h : UBnd f m) : UBnd f m' := by
  intro ω hω hB t₀ Q hQ
  obtain ⟨C, hC⟩ := h ω hω hB t₀ Q hQ
  refine ⟨max C 0 * Real.exp (∑ r ∈ Finset.range n,
    (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)), ?_⟩
  intro i b hb x hx q hq
  have h1 := hC i b hb x hx q hq
  have hs : ∑ r ∈ Finset.range n, m r * An.sr x r ≤
      (∑ r ∈ Finset.range n, (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) +
        ∑ r ∈ Finset.range n, m' r * An.sr x r := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    by_cases hr : 0 < r ∧ r < n
    · rw [if_pos hr]
      have := mul_le_mul_of_nonneg_left (hx r) (sub_nonneg.2 (hm r hr.1 hr.2))
      nlinarith
    · rw [if_neg hr, GlobalTheory.CompanionTheory.AnBoot.sr_eq_zero x hr]
      simp
  calc ‖f i (b * An.tor K x * q)‖ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * An.sr x r) := h1
    _ ≤ max C 0 * Real.exp (∑ r ∈ Finset.range n, m r * An.sr x r) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp ((∑ r ∈ Finset.range n,
          (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) +
            ∑ r ∈ Finset.range n, m' r * An.sr x r) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hs) (le_max_right _ _)
    _ = max C 0 * Real.exp (∑ r ∈ Finset.range n,
          (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) *
            Real.exp (∑ r ∈ Finset.range n, m' r * An.sr x r) := by
        rw [Real.exp_add, mul_assoc]

theorem ubnd_add {ι : Type*} {f g : ι → AdelicGLn.AdelicGL K n → ℂ} {m : ℕ → ℝ} (hf : UBnd f m) (hg : UBnd g m) :
    UBnd (fun i y => f i y + g i y) m := by
  intro ω hω hB t₀ Q hQ
  obtain ⟨C, hC⟩ := hf ω hω hB t₀ Q hQ
  obtain ⟨D, hD⟩ := hg ω hω hB t₀ Q hQ
  refine ⟨C + D, fun i b hb x hx q hq => ?_⟩
  have h1 := hC i b hb x hx q hq
  have h2 := hD i b hb x hx q hq
  calc ‖f i (b * An.tor K x * q) + g i (b * An.tor K x * q)‖
      ≤ ‖f i (b * An.tor K x * q)‖ + ‖g i (b * An.tor K x * q)‖ := norm_add_le _ _
    _ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * An.sr x r) +
          D * Real.exp (∑ r ∈ Finset.range n, m r * An.sr x r) := add_le_add h1 h2
    _ = (C + D) * Real.exp (∑ r ∈ Finset.range n, m r * An.sr x r) := by ring

section Iter

variable [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]

theorem step {β : archGroup K n → ℝ} (hβ : Ker ν β) {ι : Type} {f : ι → AdelicGLn.AdelicGL K n → ℂ} {m : ℕ → ℝ}
    {r D : ℕ} {κ' κ : ℝ} {p : ι → ℂ[X]} (h0 : 0 < r) (h1 : r < n) (hf : UFam f) (hb : UBnd f m) (hk : κ' < κ)
    (hp : ∀ i, (p i).Monic ∧ (p i).natDegree ≤ D ∧ An.Kill r (sm ν β (f i)) (p i) ∧
      ∀ z, (p i).IsRoot z → ‖z‖ ≤ Real.exp κ') :
    UBnd (fun i => sm ν β (f i)) (Function.update m r (max (m r - 1) κ)) := by
  have hf₁ : UFam (fun i => sm ν β (f i)) := GlobalTheory.T.uniform_family_smoothing K n ν β ι f hβ hf
  have hb₁ : UBnd (fun i => sm ν β (f i)) m := GlobalTheory.T.uniform_bound_smoothing K n ν β ι f m hβ hf.cont hb
  have hct := GlobalTheory.T.uniform_bound_constant_term K n ι (fun i => sm ν β (f i)) m r D κ' κ p h0 h1 hf₁ hb₁ hk hp
  have hdiff := GlobalTheory.T.uniform_bound_of_archimedean_lipschitz K n ι f (fun i => sm ν β (f i)) m r h0 h1 hf₁ (fun R => by
    obtain ⟨Q₀, C, hQ₀, hC, h⟩ := GlobalTheory.T.smoothing_lipschitz_bound K n ν β hβ R
    exact ⟨Q₀, C, hQ₀, hC, fun i g Y M hY hR hM => h (f i) (hf.cont i) g Y M hY hR hM⟩) hb
  have a : UBnd (fun i g => sm ν β (f i) g - An.ctn r (sm ν β (f i)) g) (Function.update m r (max (m r - 1) κ)) :=
    ubnd_mono (fun s _ _ => GlobalTheory.CompanionTheory.AnBoot.update_le_update m r (le_max_left _ _) s) hdiff
  have b : UBnd (fun i => An.ctn r (sm ν β (f i))) (Function.update m r (max (m r - 1) κ)) :=
    ubnd_mono (fun s _ _ => GlobalTheory.CompanionTheory.AnBoot.update_le_update m r (le_max_right _ _) s) hct
  have c := ubnd_add a b
  simpa using c

theorem iter_fam {β : archGroup K n → ℝ} (hβ : Ker ν β) {ι : Type} {f : ι → AdelicGLn.AdelicGL K n → ℂ}
    (hf : UFam f) (j : ℕ) : UFam (fun i => (sm ν β)^[j] (f i)) := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    simp only [Function.iterate_succ_apply']
    exact GlobalTheory.T.uniform_family_smoothing K n ν β ι _ hβ ih

theorem iter_kill {β : archGroup K n → ℝ} (hβ : Ker ν β) {ι : Type} {f : ι → AdelicGLn.AdelicGL K n → ℂ} {r : ℕ}
    {p : ℂ[X]} (h0 : 0 < r) (h1 : r < n) (hf : UFam f) (i : ι) (hk : An.Kill r (f i) p) (j : ℕ) :
    An.Kill r ((sm ν β)^[j] (f i)) p := by
  induction j with
  | zero => simpa using hk
  | succ j ih =>
    simp only [Function.iterate_succ_apply']
    exact GlobalTheory.T.killed_by_polynomial_smoothing K n ν β _ r p hβ h0 h1 ((iter_fam ν hβ hf j).cont i) ih

theorem iter_one {β : archGroup K n → ℝ} (hβ : Ker ν β) {ι : Type} {f : ι → AdelicGLn.AdelicGL K n → ℂ} {m : ℕ → ℝ}
    {r D : ℕ} {κ' κ : ℝ} {p : ι → ℂ[X]} (h0 : 0 < r) (h1 : r < n) (hf : UFam f) (hb : UBnd f m) (hk : κ' < κ)
    (hp : ∀ i, (p i).Monic ∧ (p i).natDegree ≤ D ∧ An.Kill r (f i) (p i) ∧
      ∀ z, (p i).IsRoot z → ‖z‖ ≤ Real.exp κ') (j : ℕ) :
    UBnd (fun i => (sm ν β)^[j] (f i)) (Function.update m r (max (m r - j) κ)) := by
  induction j with
  | zero =>
    refine ubnd_mono (fun s _ _ => ?_) hb
    by_cases hs : s = r
    · subst hs
      simp
    · simp [Function.update_of_ne hs]
  | succ j ih =>
    have := step ν hβ (r := r) (D := D) (κ' := κ') (κ := κ) (p := p) h0 h1 (iter_fam ν hβ hf j) ih hk
      (fun i => ⟨(hp i).1, (hp i).2.1, by
        have := iter_kill ν hβ h0 h1 hf i (hp i).2.2.1 (j + 1)
        rwa [Function.iterate_succ_apply'] at this, (hp i).2.2.2⟩)
    simp only [Function.iterate_succ_apply']
    rw [Function.update_self, Function.update_idem] at this
    refine ubnd_mono (fun s _ _ => GlobalTheory.CompanionTheory.AnBoot.update_le_update m r ?_ s) this
    push_cast
    refine max_le ?_ (le_max_right _ _)
    rcases le_total (m r - j) κ with h' | h'
    · rw [max_eq_right h']
      exact le_trans (by linarith) (le_max_right _ _)
    · rw [max_eq_left h']
      exact le_trans (by linarith) (le_max_left _ _)

theorem iterU {ι : Type} {f : ι → AdelicGLn.AdelicGL K n → ℂ} {M : ℝ} {κ' κ : ℕ → ℝ} {D : ℕ} {p : ℕ → ι → ℂ[X]}
    (hf : UFam f) (hb : UBnd f fun _ => M)
    (hp : ∀ r, 0 < r → r < n → κ' r < κ r ∧ ∀ i, (p r i).Monic ∧ (p r i).natDegree ≤ D ∧ An.Kill r (f i) (p r i) ∧
      ∀ z, (p r i).IsRoot z → ‖z‖ ≤ Real.exp (κ' r)) :
    ∃ k : ℕ, ∀ β, Ker ν β → UBnd (fun i => (sm ν β)^[k] (f i)) κ := by
  classical
  have key : ∀ s : Finset ℕ, (∀ r ∈ s, 0 < r ∧ r < n) → ∃ k : ℕ, ∀ β, Ker ν β →
      UBnd (fun i => (sm ν β)^[k] (f i)) (fun r => if r ∈ s then κ r else M) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨0, fun β _ => by simpa using hb⟩
    | insert a s ha ih =>
      intro hs
      obtain ⟨k, hk⟩ := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
      obtain ⟨h0, h1⟩ := hs a (Finset.mem_insert_self a s)
      obtain ⟨j, hj⟩ := exists_nat_ge (M - κ a)
      refine ⟨j + k, fun β hβ => ?_⟩
      have hfk := iter_fam ν hβ hf k
      have := iter_one ν hβ (D := D) (κ' := κ' a) (κ := κ a) (p := p a) h0 h1 hfk (hk β hβ) (hp a h0 h1).1
        (fun i => ⟨((hp a h0 h1).2 i).1, ((hp a h0 h1).2 i).2.1,
          iter_kill ν hβ h0 h1 hf i ((hp a h0 h1).2 i).2.2.1 k, ((hp a h0 h1).2 i).2.2.2⟩) j
      simp only [Function.iterate_add_apply]
      refine ubnd_mono (fun r _ _ => ?_) this
      have hna : a ∉ s := ha
      by_cases hr : r = a
      · subst hr
        simp only [Function.update_self, Finset.mem_insert, true_or, if_true, hna, if_false]
        exact max_le (by linarith) le_rfl
      · simp [Function.update_of_ne hr, Finset.mem_insert, hr]
  obtain ⟨k, hk⟩ := key (Finset.Ioo 0 n) (fun r hr => Finset.mem_Ioo.1 hr)
  refine ⟨k, fun β hβ => ubnd_mono (fun r h0 h1 => ?_) (hk β hβ)⟩
  simp [h0, h1]

end Iter

theorem initU (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)]
    [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N))
    (hα : Continuous α) (hαc : HasCompactSupport α) (hδ : 0 < δ) (hF : IsFundamentalDomain (latticeGL E N) F μ) :
    ∃ M : ℝ, ∀ (ι : Type) (f : ι → GA E N → ℂ), (∀ i, Continuous (f i)) →
      (∀ i, ∀ γ ∈ latticeGL E N, ∀ g, f i (γ * g) = f i g) →
      (∀ i, ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * f i (x * y) ∂μ = s * f i x) →
      (∀ i, (∫⁻ x in F, ‖f i x‖ₑ ^ 2 ∂μ) = 1) → UBnd f (fun _ => M) := by
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.kernel_eigenfunction_bound E N μ α δ F hα hαc hδ hF
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.T.finite_lattice_points_siegel E N
  refine ⟨M / 2, fun ι f hc hl hs hn ω hω hωB t₀ Q hQ => ?_⟩
  obtain ⟨C, hC⟩ := hM (tsupport α) ω t₀ Q hαc hω hωB hQ
  set c : ℝ := Real.exp (M * ((N : ℝ) * |t₀|)) with hc'
  refine ⟨Real.sqrt (|C₀| * (|C| + c)), fun i b hb x hx q hq => ?_⟩
  set S : ℝ := ∑ r ∈ Finset.range N, An.sr x r with hS
  have hsum : ∑ r ∈ Finset.range N, (M / 2) * An.sr x r = M / 2 * S := by rw [hS, Finset.mul_sum]
  have hS0 : -((N : ℝ) * |t₀|) ≤ S := by
    have : ∑ r ∈ Finset.range N, (-|t₀|) ≤ S := Finset.sum_le_sum fun r _ => by
      have := hx r
      have := le_abs_self t₀
      linarith
    simpa using this
  set g := b * An.tor E x * q with hg
  set k : ℕ := ⌈C * Real.exp (M * S)⌉₊ with hk
  have h1 := hC₀ (f i) (hc i) (hl i) (hs i) (hn i) g k (by
    refine le_trans (Set.encard_le_encard ?_) (hC b hb x hx q hq)
    intro γ hγ
    exact hγ)
  have hE : 0 < Real.exp (M * S) := Real.exp_pos _
  have hone : 1 ≤ c * Real.exp (M * S) := by
    rw [hc', ← Real.exp_add]
    apply Real.one_le_exp
    nlinarith
  have hkle : (k : ℝ) ≤ (|C| + c) * Real.exp (M * S) := by
    have h3 : C * Real.exp (M * S) ≤ |C| * Real.exp (M * S) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hE.le
    have h4 : 0 ≤ |C| * Real.exp (M * S) := by positivity
    have h5 : k ≤ ⌈|C| * Real.exp (M * S)⌉₊ := Nat.ceil_mono h3
    have h6 : (k : ℝ) ≤ |C| * Real.exp (M * S) + 1 :=
      (Nat.cast_le.2 h5).trans (Nat.ceil_lt_add_one h4).le
    nlinarith
  have hsq : ‖f i g‖ ^ 2 ≤ |C₀| * (|C| + c) * Real.exp (M * S) := by
    calc ‖f i g‖ ^ 2 ≤ C₀ * k := h1
      _ ≤ |C₀| * k := mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)
      _ ≤ |C₀| * ((|C| + c) * Real.exp (M * S)) := mul_le_mul_of_nonneg_left hkle (abs_nonneg _)
      _ = _ := by ring
  rw [hsum]
  have e : Real.exp (M / 2 * S) ^ 2 = Real.exp (M * S) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hA : 0 ≤ |C₀| * (|C| + c) := by positivity
  refine abs_le_of_sq_le_sq' ?_ ?_ |>.2
  · rw [mul_pow, Real.sq_sqrt hA, e]; exact hsq
  · positivity

theorem enorm_sq_le (a b : ℂ) : ‖a‖ₑ ^ 2 ≤ 2 * ‖a - b‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  have h : ‖a‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have h1 : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by simpa using norm_add_le (a - b) b
    have h2 := norm_nonneg a
    nlinarith [sq_nonneg (‖a - b‖ - ‖b‖)]
  have e : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e, e, e]
  calc ENNReal.ofReal (‖a‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖a - b‖ ^ 2 + 2 * ‖b‖ ^ 2) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num)]
      simp

section Approx

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
  [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure]

theorem sm_integrable {β : archGroup E N → ℝ} (hβ : Ker ν β) {f : GA E N → ℂ} (hf : Continuous f) (x : GA E N) :
    Integrable (fun y => (β y : ℂ) * f (x * infEmb E N y)) ν := by
  refine Continuous.integrable_of_hasCompactSupport
    ((Complex.continuous_ofReal.comp hβ.cont).mul (hf.comp (continuous_const.mul continuous_infEmb))) ?_
  exact (hβ.cpt.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).mul_right

theorem sm_sub {β : archGroup E N → ℝ} (hβ : Ker ν β) {f g : GA E N → ℂ} (hf : Continuous f) (hg : Continuous g)
    (x : GA E N) : sm ν β (fun x => f x - g x) x = sm ν β f x - sm ν β g x := by
  unfold sm
  rw [← integral_sub (sm_integrable ν hβ hf x) (sm_integrable ν hβ hg x)]
  simp only [mul_sub]

theorem iter_cont {β : archGroup E N → ℝ} (hβ : Ker ν β) {f : GA E N → ℂ} (hf : Continuous f) (j : ℕ) :
    Continuous ((sm ν β)^[j] f) := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact GlobalTheory.T.continuous_archimedean_smoothing E N ν β _ hβ ih

theorem iter_left {β : archGroup E N → ℝ} {f : GA E N → ℂ} (hf : ∀ γ ∈ latticeGL E N, ∀ g, f (γ * g) = f g) (j : ℕ) :
    ∀ γ ∈ latticeGL E N, ∀ g, (sm ν β)^[j] f (γ * g) = (sm ν β)^[j] f g := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    intro γ hγ g
    rw [Function.iterate_succ_apply']
    simp only [sm, mul_assoc]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [ih γ hγ]

theorem approxU [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure]
    (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)) (hα : Continuous α) (hαc : HasCompactSupport α) (hδ : 0 < δ)
    (hF : IsFundamentalDomain (latticeGL E N) F μ) (η : ℝ≥0∞) (hη : 0 < η) (k : ℕ) :
    ∃ β, Ker ν β ∧ ∀ ψ : GA E N → ℂ, Continuous ψ → (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) →
      (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
      ∫⁻ x in F, ‖ψ x - (sm ν β)^[k] ψ x‖ₑ ^ 2 ∂μ ≤ η := by
  have h4 : (4 : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have h4' : (4 : ℝ≥0∞) ^ k ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  set e : ℝ≥0∞ := η / 4 ^ k with he
  have he0 : 0 < e := ENNReal.div_pos hη.ne' h4'
  obtain ⟨U, hU, hUψ⟩ := GlobalTheory.T.kernel_eigenfunction_equicontinuous E N μ α δ F hα hαc hδ hF e he0
  have hU' : (infEmb E N) ⁻¹' U ∈ 𝓝 (1 : archGroup E N) := by
    refine continuous_infEmb.continuousAt.preimage_mem_nhds ?_
    rwa [map_one]
  obtain ⟨β, hβ, hsupp⟩ := exists_ker ν hU'
  refine ⟨β, hβ, fun ψ hc hl hs hn => ?_⟩
  have hnear : ∫⁻ x in F, ‖ψ x - sm ν β ψ x‖ₑ ^ 2 ∂μ ≤ e :=
    GlobalTheory.T.smoothing_fundamental_domain_bound E N μ ν F β e hF hβ ψ hc fun y hy => hUψ ψ hc hl hs hn _ (hsupp hy)
  have key : ∀ j : ℕ, ∫⁻ x in F, ‖ψ x - (sm ν β)^[j] ψ x‖ₑ ^ 2 ∂μ ≤ 4 ^ j * e := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hcj := iter_cont ν hβ hc j
      have hcj1 := iter_cont ν hβ hc (j + 1)
      have hh : Continuous fun x => ψ x - (sm ν β)^[j] ψ x := hc.sub hcj
      have hcontr := GlobalTheory.T.smoothing_fundamental_domain_integral E N μ ν F β hF hβ _ hh (fun γ hγ g => by
        simp only [hl γ hγ g, iter_left ν hl j γ hγ g])
      have hS1 : Continuous (sm ν β ψ) := GlobalTheory.T.continuous_archimedean_smoothing E N ν β ψ hβ hc
      have hpt : ∀ x, ‖ψ x - (sm ν β)^[j + 1] ψ x‖ₑ ^ 2 ≤
          2 * ‖ψ x - sm ν β ψ x‖ₑ ^ 2 + 2 * ‖sm ν β (fun x => ψ x - (sm ν β)^[j] ψ x) x‖ₑ ^ 2 := by
        intro x
        have h := enorm_sq_le (ψ x - (sm ν β)^[j + 1] ψ x) (sm ν β (fun x => ψ x - (sm ν β)^[j] ψ x) x)
        have e1 : ψ x - (sm ν β)^[j + 1] ψ x - sm ν β (fun x => ψ x - (sm ν β)^[j] ψ x) x = ψ x - sm ν β ψ x := by
          rw [sm_sub ν hβ hc hcj, Function.iterate_succ_apply']
          ring
        rwa [e1] at h
      have hm1 : Measurable fun x => 2 * ‖ψ x - sm ν β ψ x‖ₑ ^ 2 :=
        (((hc.sub hS1).enorm.measurable).pow_const 2).const_mul 2
      calc ∫⁻ x in F, ‖ψ x - (sm ν β)^[j + 1] ψ x‖ₑ ^ 2 ∂μ
          ≤ ∫⁻ x in F, (2 * ‖ψ x - sm ν β ψ x‖ₑ ^ 2 + 2 * ‖sm ν β (fun x => ψ x - (sm ν β)^[j] ψ x) x‖ₑ ^ 2) ∂μ :=
            lintegral_mono hpt
        _ = 2 * ∫⁻ x in F, ‖ψ x - sm ν β ψ x‖ₑ ^ 2 ∂μ +
              2 * ∫⁻ x in F, ‖sm ν β (fun x => ψ x - (sm ν β)^[j] ψ x) x‖ₑ ^ 2 ∂μ := by
            rw [lintegral_add_left hm1, lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
        _ ≤ 2 * e + 2 * (4 ^ j * e) := by gcongr; exact hcontr.trans ih
        _ ≤ 4 ^ (j + 1) * e := by
            have h1 : (1 : ℝ≥0∞) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
            calc 2 * e + 2 * (4 ^ j * e) ≤ 2 * (4 ^ j * e) + 2 * (4 ^ j * e) := by
                  gcongr
                  calc e = 1 * e := (one_mul e).symm
                    _ ≤ 4 ^ j * e := by gcongr
              _ = 4 ^ (j + 1) * e := by rw [pow_succ]; ring
  calc _ ≤ 4 ^ k * e := key k
    _ = η := by rw [he, ENNReal.mul_div_cancel h4 h4']

end Approx

section Half

variable {G : Type} [Group G] [TopologicalSpace G] [T2Space G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]

theorem half_of_cover {F Ω Sl : Set (G)} (hF : IsFundamentalDomain (Γ) F μ) (hΩ : IsCompact Ω)
    (hS : ∀ x, ∃ γ ∈ Γ, γ * x ∈ Sl) {ψ f : G → ℂ} (hψ : Continuous ψ) (hf : Continuous f)
    (lψ : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) (lf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g)
    (h1 : (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1) (h2 : ∫⁻ x in F, ‖ψ x - f x‖ₑ ^ 2 ∂μ ≤ 1 / 8)
    (h3 : ∫⁻ x in Sl \ Ω, ‖f x‖ₑ ^ 2 ∂μ ≤ 1 / 8) : 1 ≤ 2 * ∫⁻ x in Ω, ‖ψ x‖ₑ ^ 2 ∂μ := by
  have : MeasurableConstSMul (Γ) (G) := ⟨fun γ => measurable_const_mul (γ : G)⟩
  have : SMulInvariantMeasure (Γ) (G) μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set T : Set (G) := ⋃ γ : Γ, (fun g => (γ : G) * g) ⁻¹' Ω with hTdef
  have hT : MeasurableSet T := MeasurableSet.iUnion fun γ => (measurable_const_mul _) hΩ.measurableSet
  have hmem : ∀ x, x ∈ T ↔ ∃ γ : Γ, (γ : G) * x ∈ Ω := fun x => by
    simp [hTdef, Set.mem_iUnion]
  have hTinv : ∀ (γ : Γ) x, γ • x ∈ T ↔ x ∈ T := by
    intro γ x
    rw [hmem, hmem]
    constructor
    · rintro ⟨γ', h⟩
      refine ⟨γ' * γ, ?_⟩
      simpa [Subgroup.smul_def, mul_assoc] using h
    · rintro ⟨γ', h⟩
      refine ⟨γ' * γ⁻¹, ?_⟩
      simpa [Subgroup.smul_def, mul_assoc] using h
  have hΩT : Ω ⊆ T := fun x hx => (hmem x).2 ⟨1, by simpa using hx⟩
  have hmψ : Measurable fun x => ‖ψ x‖ₑ ^ 2 := (hψ.enorm.measurable).pow_const 2
  have hmf : Measurable fun x => ‖f x‖ₑ ^ 2 := (hf.enorm.measurable).pow_const 2
  set u : G → ℝ≥0∞ := T.indicator fun x => ‖ψ x‖ₑ ^ 2 with hu
  set w : G → ℝ≥0∞ := Tᶜ.indicator fun x => ‖ψ x‖ₑ ^ 2 with hw
  set v : G → ℝ≥0∞ := Tᶜ.indicator fun x => ‖f x‖ₑ ^ 2 with hv
  have invI : ∀ (A : Set (G)) (h : G → ℝ≥0∞), (∀ (γ : Γ) x, γ • x ∈ A ↔ x ∈ A) →
      (∀ (γ : Γ) x, h (γ • x) = h x) → ∀ (γ : Γ) x, A.indicator h (γ • x) = A.indicator h x := by
    intro A h hA hh γ x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hA γ x).2 hx), hh]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx ((hA γ x).1 h'))]
  have hinvψ : ∀ (γ : Γ) x, ‖ψ (γ • x)‖ₑ ^ 2 = ‖ψ x‖ₑ ^ 2 := fun γ x => by
    rw [Subgroup.smul_def, smul_eq_mul, lψ γ.1 γ.2 x]
  have hinvf : ∀ (γ : Γ) x, ‖f (γ • x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2 := fun γ x => by
    rw [Subgroup.smul_def, smul_eq_mul, lf γ.1 γ.2 x]
  have hTcinv : ∀ (γ : Γ) x, γ • x ∈ Tᶜ ↔ x ∈ Tᶜ := fun γ x => not_congr (hTinv γ x)

  have A : ∫⁻ x in F, u x ∂μ ≤ ∫⁻ x in Ω, ‖ψ x‖ₑ ^ 2 ∂μ := by
    have c1 : ∫⁻ x in F, u x ∂μ ≤ ∫⁻ x in Ω ∪ Tᶜ, u x ∂μ := by
      refine JSqIntGlue.setLIntegral_le_of_cover hF (fun x => ?_) u (invI _ _ hTinv hinvψ)
      by_cases hx : x ∈ T
      · obtain ⟨γ, hγ⟩ := (hmem x).1 hx
        exact ⟨γ, Or.inl hγ⟩
      · exact ⟨1, Or.inr (by simpa using hx)⟩
    have c2 : ∫⁻ x in Tᶜ, u x ∂μ = 0 := by
      rw [setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) hT.compl fun x hx => Set.indicator_of_notMem hx _]
      simp
    calc _ ≤ _ := c1
      _ ≤ ∫⁻ x in Ω, u x ∂μ + ∫⁻ x in Tᶜ, u x ∂μ := lintegral_union_le _ _ _
      _ = ∫⁻ x in Ω, u x ∂μ := by rw [c2, add_zero]
      _ ≤ _ := lintegral_mono (Set.indicator_le_self _ _)

  have B : ∫⁻ x in F, v x ∂μ ≤ 1 / 8 := by
    have c1 : ∫⁻ x in F, v x ∂μ ≤ ∫⁻ x in Sl, v x ∂μ := by
      refine JSqIntGlue.setLIntegral_le_of_cover hF (fun x => ?_) v (invI _ _ hTcinv hinvf)
      obtain ⟨γ, hγ, h⟩ := hS x
      exact ⟨⟨γ, hγ⟩, h⟩
    have c2 : ∫⁻ x in Ω, v x ∂μ = 0 := by
      rw [setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) hΩ.measurableSet
        fun x hx => Set.indicator_of_notMem (Set.notMem_compl_iff.2 (hΩT hx)) _]
      simp
    calc _ ≤ _ := c1
      _ ≤ ∫⁻ x in (Sl \ Ω) ∪ Ω, v x ∂μ := lintegral_mono_set fun x hx => by
          by_cases h : x ∈ Ω
          · exact Or.inr h
          · exact Or.inl ⟨hx, h⟩
      _ ≤ ∫⁻ x in Sl \ Ω, v x ∂μ + ∫⁻ x in Ω, v x ∂μ := lintegral_union_le _ _ _
      _ = ∫⁻ x in Sl \ Ω, v x ∂μ := by rw [c2, add_zero]
      _ ≤ ∫⁻ x in Sl \ Ω, ‖f x‖ₑ ^ 2 ∂μ := lintegral_mono (Set.indicator_le_self _ _)
      _ ≤ _ := h3
  have C : ∫⁻ x in F, w x ∂μ ≤ 1 / 2 := by
    have hpt : ∀ x, w x ≤ 2 * ‖ψ x - f x‖ₑ ^ 2 + 2 * v x := by
      intro x
      by_cases hx : x ∈ Tᶜ
      · simp only [hw, hv, Set.indicator_of_mem hx]
        exact enorm_sq_le _ _
      · simp only [hw, Set.indicator_of_notMem hx]
        exact zero_le
    have hm1 : Measurable fun x => 2 * ‖ψ x - f x‖ₑ ^ 2 := (((hψ.sub hf).enorm.measurable).pow_const 2).const_mul 2
    calc ∫⁻ x in F, w x ∂μ ≤ ∫⁻ x in F, (2 * ‖ψ x - f x‖ₑ ^ 2 + 2 * v x) ∂μ := lintegral_mono hpt
      _ = 2 * ∫⁻ x in F, ‖ψ x - f x‖ₑ ^ 2 ∂μ + 2 * ∫⁻ x in F, v x ∂μ := by
          rw [lintegral_add_left hm1, lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ 2 * (1 / 8) + 2 * (1 / 8) := by gcongr
      _ = 1 / 2 := by
          have e8 : (2 : ℝ≥0∞) * (1 / 8) = 1 / 4 := by
            rw [mul_one_div, ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
            norm_num
          rw [e8]
          have e4 : (1 / 4 : ℝ≥0∞) + 1 / 4 = 1 / 2 := by
            rw [ENNReal.div_add_div_same, ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
            norm_num
          exact e4
  have D : (1 : ℝ≥0∞) ≤ ∫⁻ x in Ω, ‖ψ x‖ₑ ^ 2 ∂μ + 1 / 2 := by
    have e : ∀ x, ‖ψ x‖ₑ ^ 2 = u x + w x := fun x => by
      by_cases hx : x ∈ T
      · simp [hu, hw, hx]
      · simp [hu, hw, hx]
    have hmu : Measurable u := hmψ.indicator hT
    calc (1 : ℝ≥0∞) = ∫⁻ x in F, (u x + w x) ∂μ := by rw [← h1]; exact lintegral_congr e
      _ = ∫⁻ x in F, u x ∂μ + ∫⁻ x in F, w x ∂μ := lintegral_add_left hmu _
      _ ≤ _ := add_le_add A C
  have h12 : (1 / 2 : ℝ≥0∞) + 1 / 2 ≤ ∫⁻ x in Ω, ‖ψ x‖ₑ ^ 2 ∂μ + 1 / 2 := by
    rwa [ENNReal.add_halves]
  have h5 : (1 / 2 : ℝ≥0∞) ≤ ∫⁻ x in Ω, ‖ψ x‖ₑ ^ 2 ∂μ :=
    (ENNReal.add_le_add_iff_right (by simp)).1 h12
  calc (1 : ℝ≥0∞) = 2 * (1 / 2) := by
        rw [mul_one_div, ENNReal.div_self (by norm_num) (by norm_num)]
    _ ≤ _ := by gcongr

end Half

open PositivityTheory.Rg.BcB.SpectralAccumulation in
open scoped Classical in

theorem conc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
  (R ε δ : ℝ) (α : GA E N → ℂ) (F : Set (GA E N)), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → 0 < ε →
  Continuous α → HasCompactSupport α → 0 < δ → IsFundamentalDomain (latticeGL E N) F μ →
  ∃ Ω : Set (GA E N), IsCompact Ω ∧ ∀ (V : Submodule ℂ (Sm E N)) (ψ : Sm E N), IsDiscrete V → ψ ∈ V → TypeB K W ψ →
    InfBdd R V → (∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r))) →
    (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ.1 (x * y) ∂μ = s * ψ.1 x) →
    (∫⁻ x in F, ‖ψ.1 x‖ₑ ^ 2 ∂μ) = 1 → 1 ≤ 2 * ∫⁻ x in Ω, ‖ψ.1 x‖ₑ ^ 2 ∂μ := by
  intro E _ _ _ N _ _ μ _ K W R ε δ α F hK hW hε hα hαc hδ hF
  letI : MeasurableSpace (archGroup E N) := borel _
  haveI : BorelSpace (archGroup E N) := ⟨rfl⟩
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  let ν : Measure (archGroup E N) := Measure.haar
  let P : Sm E N → Prop := fun ψ => ∃ V : Submodule ℂ (Sm E N), IsDiscrete V ∧ ψ ∈ V ∧ TypeB K W ψ ∧ InfBdd R V ∧
    (∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r))) ∧
    (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ.1 (x * y) ∂μ = s * ψ.1 x) ∧ (∫⁻ x in F, ‖ψ.1 x‖ₑ ^ 2 ∂μ) = 1
  let ι : Type := {ψ : Sm E N // P ψ}
  let f : ι → GA E N → ℂ := fun i => i.1.1
  have hAut : ∀ i : ι, IsAutForm i.1 := by
    rintro ⟨ψ, V, hV, hψ, -⟩
    exact hV.aut ψ hψ
  have hcen : ∀ (i : ι) t g, f i (splitCentre E N t * g) = f i g := by
    rintro ⟨ψ, V, hV, hψ, -⟩
    exact (hV.sqInt ψ hψ).1
  have hcont : ∀ i, Continuous (f i) := fun i => ContAut.continuous_of_isOpen_stab E N _ (hAut i).level
  have hLI : ∀ i, IsLeftInvariant (f i) := fun i => GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E N _ (hAut i)
  have hleft : ∀ (i : ι), ∀ γ ∈ latticeGL E N, ∀ g, f i (γ * g) = f i g := by
    intro i
    let S : Subgroup (GA E N) :=
      { carrier := {γ | ∀ g, f i (γ * g) = f i g}
        one_mem' := fun g => by rw [one_mul]
        mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
        inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
    have : latticeGL E N ≤ S :=
      sup_le (by rintro _ ⟨γ, rfl⟩; exact (hAut i).left γ) (Subgroup.zpowers_le.2 (hcen i 1))
    exact this
  obtain ⟨U, hU, hUk⟩ := GlobalTheory.T.exists_open_integral_subgroup E N K hK
  have hfam : UFam f := by
    refine ⟨hcont, hLI, U, hU, fun i g u => ?_⟩
    obtain ⟨k, hk, e⟩ := hUk u
    rw [e]
    obtain ⟨ψ, V, hV, hψ, hT, -⟩ := i
    exact hT.1 k hk g
  have hrep : ∀ i : ι, ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * f i (x * y) ∂μ = s * f i x := by
    rintro ⟨ψ, V, hV, hψ, hT, hI, hE, hs, hn⟩
    exact hs
  have hnorm : ∀ i : ι, (∫⁻ x in F, ‖f i x‖ₑ ^ 2 ∂μ) = 1 := by
    rintro ⟨ψ, V, hV, hψ, hT, hI, hE, hs, hn⟩
    exact hn
  obtain ⟨M, hM⟩ := initU E N μ α δ F hα hαc hδ hF
  have hM' := hM ι f hcont hleft hrep hnorm

  have hD : ∀ r, ∃ D : ℕ, 0 < r → r < N → ∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
      (∀ τ : E →+* ℂ, ∃ m, HasInfCharGL V τ m) → ∀ φ ∈ V, ∃ p : ℂ[X], p.Monic ∧ p.natDegree ≤ D ∧ An.Kill r φ.1 p ∧
        ∀ z, p.IsRoot z → ∃ c ∈ Exp r φ.1, z = Complex.exp c := by
    intro r
    by_cases hr : 0 < r ∧ r < N
    · obtain ⟨D, h⟩ := GlobalTheory.T.exists_exponent_polynomial_discrete E N r hr.1 hr.2
      exact ⟨D, fun _ _ => h⟩
    · exact ⟨0, fun h0 h1 => (hr ⟨h0, h1⟩).elim⟩
  choose Dr hDr using hD
  set D : ℕ := (Finset.range N).sup Dr with hDdef
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hrho : ∀ r, 0 < r → r < N → 0 < An.rho E N r := by
    intro r h0 h1
    unfold An.rho
    have a1 : (0 : ℝ) < r := by exact_mod_cast h0
    have a2 : (0 : ℝ) < (N : ℝ) - r := sub_pos.2 (by exact_mod_cast h1)
    positivity
  set κ' : ℕ → ℝ := fun r => An.rho E N r * (1 - 2 * ε) with hκ'
  set κ : ℕ → ℝ := fun r => An.rho E N r * (1 - ε) with hκ
  have hp : ∀ r (i : ι), ∃ p : ℂ[X], 0 < r → r < N → p.Monic ∧ p.natDegree ≤ D ∧ An.Kill r (f i) p ∧
      ∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp (κ' r) := by
    rintro r ⟨ψ, V, hV, hψ, hT, hI, hE, hs, hn⟩
    by_cases hr : 0 < r ∧ r < N
    swap
    · exact ⟨1, fun h0 h1 => (hr ⟨h0, h1⟩).elim⟩
    obtain ⟨h0, h1⟩ := hr
    obtain ⟨p, hpm, hpd, hpk, hpz⟩ := hDr r h0 h1 V hV (fun τ => (hI τ).imp fun m h => h.1) ψ hψ
    refine ⟨p, fun _ _ => ⟨hpm, hpd.trans (Finset.le_sup (Finset.mem_range.2 (by omega))), hpk, fun z hz => ?_⟩⟩
    obtain ⟨c, hc, rfl⟩ := hpz z hz
    have h2 := hE r h0 h1 c ⟨ψ, hψ, hc⟩
    unfold pE at h2
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have h3 : c.re / (Module.finrank ℚ E : ℝ) ≤ (r : ℝ) * ((N : ℝ) - r) / 2 - ε * (r * ((N : ℝ) - r)) := by linarith
    have h4 := (div_le_iff₀ hd).1 h3
    simp only [hκ', An.rho]
    calc c.re ≤ _ := h4
      _ = _ := by ring
  choose p hpp using hp
  obtain ⟨k, hk⟩ := iterU ν (κ' := κ') (κ := κ) (D := D) (p := p) hfam hM' (fun r h0 h1 =>
    ⟨by
      have := hrho r h0 h1
      simp only [hκ', hκ]
      nlinarith, fun i => hpp r i h0 h1⟩)
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := GroundTheory.Automorphic.Reduction.exists_siegelSet (K := E) N
  obtain ⟨-, hS, hL, -⟩ := dict_holds E N
  have h8 : (0 : ℝ≥0∞) < 1 / 8 := by simp
  obtain ⟨β, hβ, hβψ⟩ := approxU ν μ α δ F hα hαc hδ hF (1 / 8) h8 k
  obtain ⟨Ω, hΩ, hΩf⟩ := GlobalTheory.T.uniform_bound_siegel_set E N μ ι (fun i => (sm ν β)^[k] (f i)) κ (iter_fam ν hβ hfam k).cont (hk β hβ)
    (fun r h0 h1 => by
      have := hrho r h0 h1
      simp only [hκ]
      nlinarith) ω hω hωB (max 0 (-Real.log t)) (1 / 8) h8
  refine ⟨Ω, hΩ, fun V ψ hV hψ hT hI hE hs hn => ?_⟩
  let i : ι := ⟨ψ, V, hV, hψ, hT, hI, hE, hs, hn⟩
  exact half_of_cover (latticeGL E N) μ hF hΩ (fun g => JSqIntGlue.exists_mem_slab hS hL ht hsieg g)
    (hcont i) ((iter_fam ν hβ hfam k).cont i) (hleft i) (iter_left ν (hleft i) k) hn
    (hβψ _ (hcont i) (hleft i) (hrep i) hn) (hΩf i)

end GlobalTheory.CompanionTheory.Conc

end
