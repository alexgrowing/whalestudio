import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCosetScaledRiemannSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantBoxApproximationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCongruenceRefinementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetEmptyPlacesLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetUnitIdealIntegralStatement

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi

theorem squeeze_of_approx {α : Type} {l : Filter α} {A : α → ℝ} {a K : ℝ} (hK : 0 ≤ K)
    (h : ∀ δ : ℝ, 0 < δ → ∃ (B E : α → ℝ) (b e : ℝ), Tendsto B l (𝓝 b) ∧ Tendsto E l (𝓝 e) ∧
      (∀ᶠ t in l, |A t - B t| ≤ δ * E t) ∧ |b - a| ≤ δ * K ∧ e ≤ K) : Tendsto A l (𝓝 a) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have hK1 : 0 < K + 1 := by linarith
  set δ := η / (4 * (K + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδK : δ * (K + 1) = η / 4 := by rw [hδ]; field_simp
  obtain ⟨B, E, b, e, hB, hE, hAB, hb, he⟩ := h δ hδ0
  have h1 := (Metric.tendsto_nhds.1 hB) (η / 4) (by linarith)
  have h2 : ∀ᶠ t in l, E t < K + 1 := hE.eventually (gt_mem_nhds (by linarith))
  filter_upwards [h1, h2, hAB] with t t1 t2 t3
  rw [Real.dist_eq] at t1 ⊢
  have t4 : δ * E t ≤ δ * (K + 1) := by gcongr
  have t5 : δ * K ≤ δ * (K + 1) := by gcongr; linarith
  have e1 : A t - a = (A t - B t) + (B t - b) + (b - a) := by ring
  rw [e1]
  calc _ ≤ |A t - B t| + |B t - b| + |b - a| := abs_add_three _ _ _
    _ < η := by linarith

theorem summable_of_close {X γ : Type} {g : X → ℝ} (C : Finset γ) (a : γ → ℝ) (u w : γ → X → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : ∀ c ∈ C, Summable (u c)) (hw : ∀ c ∈ C, Summable (w c))
    (h : ∀ x, |g x - ∑ c ∈ C, a c * u c x| ≤ δ * ∑ c ∈ C, w c x) :
    Summable g ∧ |(∑' x, g x) - ∑ c ∈ C, a c * ∑' x, u c x| ≤ δ * ∑ c ∈ C, ∑' x, w c x := by
  have hsw : Summable fun x => δ * ∑ c ∈ C, w c x := (summable_sum hw).mul_left δ
  have hsu : Summable fun x => ∑ c ∈ C, a c * u c x := summable_sum fun c hc => (hu c hc).mul_left (a c)
  have hsh : Summable fun x => g x - ∑ c ∈ C, a c * u c x := Summable.of_norm_bounded hsw fun x => by simpa using h x
  have hg : Summable g := by simpa using hsh.add hsu
  refine ⟨hg, ?_⟩
  have e1 : (∑' x, g x) - ∑ c ∈ C, a c * ∑' x, u c x = ∑' x, (g x - ∑ c ∈ C, a c * u c x) := by
    rw [hg.tsum_sub hsu, Summable.tsum_finsetSum fun c hc => (hu c hc).mul_left (a c)]
    simp only [tsum_mul_left]
  have e2 : δ * ∑ c ∈ C, ∑' x, w c x = ∑' x, δ * ∑ c ∈ C, w c x := by
    rw [tsum_mul_left, Summable.tsum_finsetSum hw]
  rw [e1, e2]
  have hn : Summable fun x => ‖g x - ∑ c ∈ C, a c * u c x‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => by simpa using h x) hsw
  calc _ = ‖∑' x, (g x - ∑ c ∈ C, a c * u c x)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' x, ‖g x - ∑ c ∈ C, a c * u c x‖ := norm_tsum_le_tsum_norm hn
    _ ≤ _ := hn.tsum_le_tsum (fun x => by simpa using h x) hsw

variable {F : Type} [Field F] [NumberField F]

def Claim (θ : ℝ →+* Ainf F) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (ι : Type) [Fintype ι]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∀ (I : Ideal (𝓞 F)), I ≠ ⊥ → (∀ v ∈ S, ¬ I ≤ v.asIdeal) → ∀ (x0 : ι → F) (φ : (ι → Ainf F) → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (ι → Fv F v) → ℝ), Continuous φ → HasCompactSupport φ →
    (∀ v ∈ S, Continuous (ψ v) ∧ HasCompactSupport (ψ v)) →
    (∀ ε : ℝ, 0 < ε → Summable fun x : cosetOff S I x0 => term θ S φ ψ ε x.1) ∧
    Tendsto (fun ε : ℝ => ε ^ (Module.finrank ℚ F * Fintype.card ι) * ∑' x : cosetOff S I x0, term θ S φ ψ ε x.1)
      (𝓝[>] 0) (𝓝 (((Ideal.absNorm I : ℝ) ^ Fintype.card ι)⁻¹ *
        ((∫ y, φ y ∂(Measure.pi fun _ => li)) * ∏ v ∈ S, ∫ y, ψ v y ∂(Measure.pi fun _ => lam v))))

theorem claim_empty (hF : IsTotallyReal F) (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (li : Measure (Ainf F)) (hli : IsStdInf li)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (ι : Type) [Fintype ι] : Claim θ li lam ι ∅ := by
  intro I hI _ x0 φ ψ hφ hc _
  rw [GlobalTheory.T.coset_empty_places_lattice]
  have := GlobalTheory.T.lattice_coset_scaled_riemann_sum F hF θ hθ li hli ι I hI x0 φ hφ hc
  simpa [term] using this

theorem mul_pow_prime {S : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {I : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) (hc : ∀ w ∈ S, ¬ I ≤ w.asIdeal) (k : ℕ) :
    I * v.asIdeal ^ k ≠ ⊥ ∧ ∀ w ∈ S, ¬ I * v.asIdeal ^ k ≤ w.asIdeal := by
  refine ⟨mul_ne_zero hI (pow_ne_zero _ v.ne_bot), fun w hw h => ?_⟩
  rcases w.isPrime.mul_le.1 h with h | h
  · exact hc w hw h
  · have h1 := w.isPrime.le_of_pow_le h
    have h2 : v.asIdeal = w.asIdeal := v.isMaximal.eq_of_le w.isPrime.ne_top h1
    exact hv ((HeightOneSpectrum.ext h2) ▸ hw)

abbrev yV {ι : Type} (v : HeightOneSpectrum (𝓞 F)) (x : ι → F) : ι → Fv F v := fun i => algebraMap F (Fv F v) (x i)

theorem term_insert {ι : Type} (θ : ℝ →+* Ainf F) {S : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    (φ : (ι → Ainf F) → ℝ) (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (ι → Fv F v) → ℝ) (ε : ℝ) (x : ι → F) :
    term θ (insert v S) φ ψ ε x = ψ v (yV v x) * term θ S φ ψ ε x := by
  simp only [term, Finset.prod_insert hv, yV]
  ring

theorem term_abs {ι : Type} (θ : ℝ →+* Ainf F) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (φ : (ι → Ainf F) → ℝ) (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (ι → Fv F v) → ℝ) (ε : ℝ) (x : ι → F) :
    term θ S (fun y => |φ y|) (fun w y => |ψ w y|) ε x = |term θ S φ ψ ε x| := by
  simp only [term, abs_mul, Finset.abs_prod]

theorem indicator_box {ι : Type} {A A' : Set (ι → F)} {v : HeightOneSpectrum (𝓞 F)} {k : ℕ} {c : ι → Fv F v}
    (h : ∀ x : ι → F, (x ∈ A ∧ ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k) ↔ x ∈ A') (f : (ι → F) → ℝ) :
    (A.indicator fun x => boxInd v k c (yV v x) * f x) = A'.indicator f := by
  funext x
  by_cases hb : ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k
  · by_cases hA : x ∈ A
    · have hA' := (h x).1 ⟨hA, hb⟩
      simp [Set.indicator, hA, hA', boxInd, yV, hb]
    · have hA' : x ∉ A' := fun e => hA ((h x).2 e).1
      simp [Set.indicator, hA, hA']
  · have hA' : x ∉ A' := fun e => hb ((h x).2 e).2
    have hz : boxInd v k c (yV v x) = 0 := by simp only [boxInd, yV]; rw [if_neg hb]
    simp [Set.indicator, hA', hz]

theorem est {ι : Type} (θ : ℝ →+* Ainf F) {S : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    (φ : (ι → Ainf F) → ℝ) (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (ι → Fv F v) → ℝ) (ε δ : ℝ) (hδ : 0 ≤ δ) {A : Set (ι → F)}
    {k : ℕ} (C : Finset (ι → Fv F v)) (A' : (ι → Fv F v) → Set (ι → F))
    (hA : ∀ c ∈ C, ∀ x : ι → F, (x ∈ A ∧ ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k) ↔ x ∈ A' c)
    (hap : ∀ y, |ψ v y - ∑ c ∈ C, ψ v c * boxInd v k c y| ≤ δ * ∑ c ∈ C, boxInd v k c y)
    (hs : ∀ c ∈ C, Summable fun x : A' c => term θ S φ ψ ε x.1)
    (hs' : ∀ c ∈ C, Summable fun x : A' c => term θ S (fun y => |φ y|) (fun w y => |ψ w y|) ε x.1) :
    Summable (fun x : A => term θ (insert v S) φ ψ ε x.1) ∧
      |(∑' x : A, term θ (insert v S) φ ψ ε x.1) - ∑ c ∈ C, ψ v c * ∑' x : A' c, term θ S φ ψ ε x.1| ≤
        δ * ∑ c ∈ C, ∑' x : A' c, term θ S (fun y => |φ y|) (fun w y => |ψ w y|) ε x.1 := by
  set f : (ι → F) → ℝ := term θ S φ ψ ε with hf
  set f' : (ι → F) → ℝ := term θ S (fun y => |φ y|) (fun w y => |ψ w y|) ε with hf'
  set u : (ι → Fv F v) → (ι → F) → ℝ := fun c => (A' c).indicator f with hu
  set w : (ι → Fv F v) → (ι → F) → ℝ := fun c => (A' c).indicator f' with hw
  have key : ∀ x, |A.indicator (fun x => term θ (insert v S) φ ψ ε x) x - ∑ c ∈ C, ψ v c * u c x| ≤ δ * ∑ c ∈ C, w c x := by
    intro x
    have e1 : ∀ c ∈ C, u c x = A.indicator (fun x => boxInd v k c (yV v x) * f x) x := fun c hc => by
      simp only [hu]
      exact (congrFun (indicator_box (hA c hc) f) x).symm
    have e2 : ∀ c ∈ C, w c x = A.indicator (fun x => boxInd v k c (yV v x) * f' x) x := fun c hc => by
      simp only [hw]
      exact (congrFun (indicator_box (hA c hc) f') x).symm
    rw [Finset.sum_congr rfl fun c hc => by rw [e1 c hc], Finset.sum_congr rfl e2]
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx, term_insert θ hv]
      have e3 : ψ v (yV v x) * f x - ∑ c ∈ C, ψ v c * (boxInd v k c (yV v x) * f x) =
          (ψ v (yV v x) - ∑ c ∈ C, ψ v c * boxInd v k c (yV v x)) * f x := by
        rw [sub_mul, Finset.sum_mul]
        simp only [mul_assoc]
      rw [e3, abs_mul, ← Finset.sum_mul, hf', term_abs, ← hf, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hap _) (abs_nonneg _)
    · simp [Set.indicator_of_notMem hx]
  have hsu : ∀ c ∈ C, Summable (u c) := fun c hc => summable_subtype_iff_indicator.1 (hs c hc)
  have hsw : ∀ c ∈ C, Summable (w c) := fun c hc => summable_subtype_iff_indicator.1 (hs' c hc)
  obtain ⟨h1, h2⟩ := summable_of_close C (ψ v) u w hδ hsu hsw key
  refine ⟨summable_subtype_iff_indicator.2 h1, ?_⟩
  have t1 : ∑' x : A, term θ (insert v S) φ ψ ε x.1 = ∑' x, A.indicator (fun x => term θ (insert v S) φ ψ ε x) x :=
    tsum_subtype A _
  have t2 : ∀ c, ∑' x : A' c, f x.1 = ∑' x, u c x := fun c => tsum_subtype (A' c) f
  have t3 : ∀ c, ∑' x : A' c, f' x.1 = ∑' x, w c x := fun c => tsum_subtype (A' c) f'
  simp only [t1, t2, t3]
  exact h2

theorem claim_insert {θ : ℝ →+* Ainf F} {li : Measure (Ainf F)} {lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)}
    (hlam : ∀ v, IsStdV v (lam v)) {ι : Type} [Fintype ι] {S : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ S) (hS : Claim θ li lam ι S) : Claim θ li lam ι (insert v S) := by
  intro I hI hcop x0 φ ψ hφ hφc hψ
  have hcopS : ∀ w ∈ S, ¬ I ≤ w.asIdeal := fun w hw => hcop w (Finset.mem_insert_of_mem hw)
  have hcopv : ¬ I ≤ v.asIdeal := hcop v (Finset.mem_insert_self _ _)
  have hψS : ∀ w ∈ S, Continuous (ψ w) ∧ HasCompactSupport (ψ w) := fun w hw => hψ w (Finset.mem_insert_of_mem hw)
  obtain ⟨hψc, hψs⟩ := hψ v (Finset.mem_insert_self _ _)
  have hφa : Continuous fun y => |φ y| := hφ.abs
  have hφca : HasCompactSupport fun y => |φ y| := hφc.comp_left (g := fun t : ℝ => |t|) abs_zero
  have hψa : ∀ w ∈ S, Continuous (fun y => |ψ w y|) ∧ HasCompactSupport (fun y => |ψ w y|) := fun w hw =>
    ⟨(hψS w hw).1.abs, (hψS w hw).2.comp_left (g := fun t : ℝ => |t|) abs_zero⟩
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.locally_constant_box_approximation F v (lam v) (hlam v) ι (ψ v) hψc hψs
  have hcell : ∀ (k : ℕ) (c : ι → Fv F v), ∃ x1 : ι → F, ∀ x : ι → F,
      (x ∈ cosetOff (insert v S) I x0 ∧ ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k) ↔
        x ∈ cosetOff S (I * v.asIdeal ^ k) x1 := fun k c => GlobalTheory.T.coset_congruence_refinement F ι S v hv I hI hcopv k x0 c
  choose x1 hx1 using hcell
  have hJ := fun k => mul_pow_prime hv hI hcopS k
  have hP := fun (k : ℕ) (c : ι → Fv F v) => hS _ (hJ k).1 (hJ k).2 (x1 k c) φ ψ hφ hφc hψS
  have hQ := fun (k : ℕ) (c : ι → Fv F v) => hS _ (hJ k).1 (hJ k).2 (x1 k c) (fun y => |φ y|) (fun w y => |ψ w y|) hφa hφca hψa
  have hest := fun (δ : ℝ) (hδ : 0 ≤ δ) (k : ℕ) (C : Finset (ι → Fv F v))
      (hap : ∀ y, |ψ v y - ∑ c ∈ C, ψ v c * boxInd v k c y| ≤ δ * ∑ c ∈ C, boxInd v k c y) (ε : ℝ) (hε : 0 < ε) =>
    est θ hv φ ψ ε δ hδ C (fun c => cosetOff S (I * v.asIdeal ^ k) (x1 k c)) (fun c _ => hx1 k c) hap
      (fun c _ => (hP k c).1 ε hε) (fun c _ => (hQ k c).1 ε hε)
  refine ⟨fun ε hε => ?_, ?_⟩
  · obtain ⟨k, C, h1, -, -⟩ := hB 1 one_pos
    exact (hest 1 zero_le_one k C h1 ε hε).1
  set N := Fintype.card ι
  set D := Module.finrank ℚ F * N
  set Nf : ℝ := ((Ideal.absNorm I : ℝ) ^ N)⁻¹ with hNf
  have hNf0 : 0 ≤ Nf := by positivity
  set M : ℝ := (∫ y, φ y ∂(Measure.pi fun _ => li)) * ∏ w ∈ S, ∫ y, ψ w y ∂(Measure.pi fun _ => lam w) with hM
  set M' : ℝ := (∫ y, |φ y| ∂(Measure.pi fun _ => li)) * ∏ w ∈ S, ∫ y, |ψ w y| ∂(Measure.pi fun _ => lam w) with hM'
  have hM'0 : 0 ≤ M' := mul_nonneg (integral_nonneg fun _ => abs_nonneg _)
    (Finset.prod_nonneg fun _ _ => integral_nonneg fun _ => abs_nonneg _)
  have hnorm : ∀ k : ℕ, ((Ideal.absNorm (I * v.asIdeal ^ k) : ℝ) ^ N)⁻¹ =
      Nf * (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ N)⁻¹ := fun k => by
    rw [map_mul, map_pow, hNf]
    push_cast
    rw [mul_pow, mul_inv]
  have htarget : ((Ideal.absNorm I : ℝ) ^ N)⁻¹ * ((∫ y, φ y ∂(Measure.pi fun _ => li)) *
      ∏ w ∈ insert v S, ∫ y, ψ w y ∂(Measure.pi fun _ => lam w)) =
      Nf * M * ∫ y, ψ v y ∂(Measure.pi fun _ => lam v) := by
    rw [Finset.prod_insert hv, hM]
    ring
  rw [htarget]
  refine squeeze_of_approx (K := Nf * M' * B + Nf * |M| * B) (by positivity) fun δ hδ => ?_
  obtain ⟨k, C, h1, h2, h3⟩ := hB δ hδ
  set q : ℝ := (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ N)⁻¹ with hq
  refine ⟨fun ε => ∑ c ∈ C, ψ v c * (ε ^ D * ∑' x : cosetOff S (I * v.asIdeal ^ k) (x1 k c), term θ S φ ψ ε x.1),
    fun ε => ∑ c ∈ C, ε ^ D * ∑' x : cosetOff S (I * v.asIdeal ^ k) (x1 k c),
      term θ S (fun y => |φ y|) (fun w y => |ψ w y|) ε x.1,
    ∑ c ∈ C, ψ v c * (Nf * q * M), ∑ c ∈ C, Nf * q * M', ?_, ?_, ?_, ?_, ?_⟩
  · refine tendsto_finset_sum _ fun c _ => Tendsto.const_mul _ ?_
    have := (hP k c).2
    rwa [hnorm] at this
  · refine tendsto_finset_sum _ fun c _ => ?_
    have := (hQ k c).2
    rwa [hnorm] at this
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0 : ℝ) < ε := hε
    have h4 := (hest δ hδ.le k C h1 ε hε0).2
    have hp : 0 ≤ ε ^ D := by positivity
    have e1 : ε ^ D * (∑' x : cosetOff (insert v S) I x0, term θ (insert v S) φ ψ ε x.1) -
        ∑ c ∈ C, ψ v c * (ε ^ D * ∑' x : cosetOff S (I * v.asIdeal ^ k) (x1 k c), term θ S φ ψ ε x.1) =
        ε ^ D * ((∑' x : cosetOff (insert v S) I x0, term θ (insert v S) φ ψ ε x.1) -
          ∑ c ∈ C, ψ v c * ∑' x : cosetOff S (I * v.asIdeal ^ k) (x1 k c), term θ S φ ψ ε x.1) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e1, abs_mul, abs_of_nonneg hp, ← Finset.mul_sum, mul_left_comm]
    exact mul_le_mul_of_nonneg_left h4 hp
  · have e1 : ∑ c ∈ C, ψ v c * (Nf * q * M) = Nf * M * ∑ c ∈ C, ψ v c * q := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e1, ← mul_sub, abs_mul, abs_mul, abs_of_nonneg hNf0, abs_sub_comm]
    calc Nf * |M| * _ ≤ Nf * |M| * (δ * B) := by gcongr
      _ ≤ δ * (Nf * M' * B + Nf * |M| * B) := by
        have : 0 ≤ δ * (Nf * M' * B) := by positivity
        nlinarith
  · rw [Finset.sum_const, nsmul_eq_mul]
    have e1 : (C.card : ℝ) * (Nf * q * M') = Nf * M' * ((C.card : ℝ) * q) := by ring
    rw [e1]
    have h5 : Nf * M' * ((C.card : ℝ) * q) ≤ Nf * M' * B := by gcongr
    have h6 : 0 ≤ Nf * |M| * B := by positivity
    linarith

theorem equi : PositivityTheory.Rg.Mass.Equi := by
  intro F _ _ hF θ hθ li lam hli hlam ι _ S φ ψ hφ hφc hψ
  have hc : Claim θ li lam ι S := by
    induction S using Finset.induction_on with
    | empty => exact claim_empty hF θ hθ li hli lam ι
    | insert v S hv ih => exact claim_insert hlam hv (ih fun w hw => hψ w (Finset.mem_insert_of_mem hw))
  have h := (hc ⊤ top_ne_bot (fun w _ h => w.isPrime.ne_top (top_le_iff.1 h)) 0 φ ψ hφ hφc hψ).2
  rw [GlobalTheory.T.coset_unit_ideal_integral] at h
  simp only [term, Ideal.absNorm_top, Nat.cast_one, one_pow, inv_one, one_mul] at h
  exact h

end GlobalTheory.CompanionTheory.Equi

end
