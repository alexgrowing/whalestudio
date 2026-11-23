import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
open Classical MeasureTheory

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

variable {ι : Type} [Fintype ι]

def scalAt {a : ℕ} (τ₀ : ι) (ζ : ℂ) : ι → Matrix (Fin a) (Fin a) ℂ := fun τ => if τ = τ₀ then ζ • 1 else 1

def degAt {d a : ℕ} (τ₀ : ι) (t : Var ι d a →₀ ℕ) : ℕ := t.sum fun y n => if y.1 = τ₀ then n else 0

theorem colSub_scalAt_X {d a : ℕ} (τ₀ : ι) (ζ : ℂ) (y : Var ι d a) :
    (∑ j' : Fin a, C (scalAt τ₀ ζ y.1 j' y.2.2) * (X (y.1, y.2.1, j') : Pol ι d a)) =
      C (if y.1 = τ₀ then ζ else 1) * X y := by
  obtain ⟨τ, i, j⟩ := y
  by_cases h : τ = τ₀
  · subst h
    rw [Finset.sum_eq_single j]
    · simp [scalAt, Matrix.smul_apply, Matrix.one_apply]
    · intro b _ hb
      simp [scalAt, Matrix.smul_apply, Matrix.one_apply, hb]
    · simp
  · simp [scalAt, h, Matrix.one_apply]

theorem colSub_scalAt_monomial {d a : ℕ} (τ₀ : ι) (ζ : ℂ) (t : Var ι d a →₀ ℕ) (c : ℂ) :
    colSub (scalAt τ₀ ζ) (monomial t c : Pol ι d a) = monomial t (c * ζ ^ degAt τ₀ t) := by
  unfold colSub
  rw [aeval_monomial]
  simp only [colSub_scalAt_X, mul_pow, Finsupp.prod_mul]
  have h1 : (t.prod fun y k => (C (if y.1 = τ₀ then ζ else 1) : Pol ι d a) ^ k) = C (ζ ^ degAt τ₀ t) := by
    unfold Finsupp.prod degAt Finsupp.sum
    rw [← Finset.prod_pow_eq_pow_sum, map_prod]
    refine Finset.prod_congr rfl fun y _ => ?_
    beta_reduce
    split_ifs <;> simp
  rw [h1, ← monomial_eq, algebraMap_eq, C_mul_monomial]

theorem degAt_le {d a : ℕ} (τ₀ : ι) (t : Var ι d a →₀ ℕ) : degAt τ₀ t ≤ t.sum fun _ e => e := by
  unfold degAt Finsupp.sum
  exact Finset.sum_le_sum fun y _ => by beta_reduce; split_ifs <;> omega

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

variable {ι : Type} [Fintype ι]

theorem colSub_mul {d a : ℕ} (A B : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    colSub (fun τ => A τ * B τ) P = colSub A (colSub B P) := by
  have : (colSub (fun τ => A τ * B τ) : Pol ι d a →ₐ[ℂ] Pol ι d a) = (colSub A).comp (colSub B) := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [AlgHom.comp_apply, colSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply,
      Finset.mul_sum, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem sum_scalAt_eq_zero {d a : ℕ} (τ₀ : ι) (N : ℕ) (hN : 0 < N) (P : Pol ι d a) {ω : ℂ}
    (hω : IsPrimitiveRoot ω (N + P.totalDegree + 1)) :
    ∑ k ∈ Finset.range (N + P.totalDegree + 1), (ω ^ k) ^ N • colSub (scalAt τ₀ (ω ^ k)) P = 0 := by
  generalize hM : N + P.totalDegree + 1 = M at hω ⊢
  conv_lhs => rw [as_sum P]
  simp only [map_sum, colSub_scalAt_monomial, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t ht => ?_
  have hsum : ∑ k ∈ Finset.range M, (ω ^ (N + degAt τ₀ t)) ^ k = 0 := by
    have hne : ω ^ (N + degAt τ₀ t) ≠ 1 := by
      rw [Ne, hω.pow_eq_one_iff_dvd]
      intro hdvd
      have h1 := degAt_le τ₀ t
      have h2 := le_totalDegree ht
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self, zero_div]
  have : ∀ k ∈ Finset.range M,
      (ω ^ k) ^ N • (monomial t (coeff t P * (ω ^ k) ^ degAt τ₀ t) : Pol ι d a) =
        monomial t (coeff t P * (ω ^ (N + degAt τ₀ t)) ^ k) := by
    intro k _
    rw [smul_monomial, smul_eq_mul]
    congr 1
    rw [← pow_mul, ← pow_mul, ← pow_mul, show (N + degAt τ₀ t) * k = k * N + k * degAt τ₀ t by ring, pow_add]
    ring
  rw [Finset.sum_congr rfl this, ← map_sum, ← Finset.mul_sum, hsum, mul_zero, map_zero]

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

theorem prod_det_scalAt_zpow {ι : Type} [Fintype ι] {a : ℕ} (τ₀ : ι) (ζ : ℂ) (m : ι → ℤ) (n : ℕ)
    (hn : (n : ℤ) = m τ₀) : (∏ τ, (scalAt (a := a) τ₀ ζ τ).det ^ (m τ)) = ζ ^ (a * n) := by
  rw [Finset.prod_eq_single τ₀]
  · simp [scalAt, Matrix.det_smul, ← hn, zpow_natCast, pow_mul]
  · intro τ _ h
    simp [scalAt, h]
  · simp

theorem integral_detZpow_colSub_eq_zero :
    ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ) (τ₀ : ι), 0 < a → 0 < m τ₀ → ∀ {K : Type} [Group K]
      [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
    ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)),
      (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) →
      Function.Surjective ρ →
    ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
        Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) ∂ν = 0 := by
  intro ι _ a d m τ₀ ha hm K _ _ ν hν hinv ρ _ hρ Λ P
  set B : K → ι → Matrix (Fin a) (Fin a) ℂ := fun g τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) with hB_def
  set c : K → ℂ := fun g => ∏ τ, (B g τ).det ^ (m τ) with hc_def
  set f : K → ℂ := fun g => c g * Λ (colSub (B g) P) with hf_def
  show ∫ g, f g ∂ν = 0
  by_cases hint : Integrable f ν
  swap
  · exact integral_undef hint

  have hinvar : ∀ u : K, Integrable (fun x => f (u * x)) ν ∧ ∫ x, f (u * x) ∂ν = ∫ x, f x ∂ν := by
    intro u
    have hmap : Measure.map (fun x => u * x) ν = ν := map_mul_left_eq_self ν u
    have hae : AEMeasurable (fun x => u * x) ν := by
      by_contra h
      rw [Measure.map_of_not_aemeasurable h] at hmap
      exact (IsProbabilityMeasure.ne_zero ν) hmap.symm
    refine ⟨?_, ?_⟩
    · have : Integrable f (Measure.map (fun x => u * x) ν) := by rw [hmap]; exact hint
      exact this.comp_aemeasurable hae
    · have h := integral_map hae (f := f) (by rw [hmap]; exact hint.aestronglyMeasurable)
      rw [hmap] at h
      exact h.symm

  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m τ₀ := ⟨(m τ₀).toNat, Int.toNat_of_nonneg hm.le⟩
  have hnpos : 0 < n := by omega
  set N := a * n with hN_def
  have hN : 0 < N := Nat.mul_pos ha hnpos
  set M := N + P.totalDegree + 1 with hM_def
  have hM0 : M ≠ 0 := by omega
  set ω := Complex.exp (2 * Real.pi * Complex.I / M) with hω_def
  have hω : IsPrimitiveRoot ω M := Complex.isPrimitiveRoot_exp M hM0
  have hmemU : ∀ k : ℕ, ((ω ^ k) • (1 : Matrix (Fin a) (Fin a) ℂ)) ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    intro k
    have hnorm : ‖ω ^ k‖ = 1 := by rw [norm_pow, hω.norm'_eq_one hM0, one_pow]
    have hc : ω ^ k * star (ω ^ k) = 1 := by
      rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      hc, one_smul]
  let U : ℕ → ι → Matrix.unitaryGroup (Fin a) ℂ := fun k τ => if τ = τ₀ then ⟨(ω ^ k) • 1, hmemU k⟩ else 1
  have hU : ∀ k τ, (U k τ : Matrix (Fin a) (Fin a) ℂ) = scalAt τ₀ (ω ^ k) τ := by
    intro k τ
    simp only [U, scalAt]
    split_ifs <;> rfl
  choose u hu using fun k => hρ (U k)

  have hpt : ∀ k g, f (u k * g) = c g * Λ ((ω ^ k) ^ N • colSub (B g) (colSub (scalAt τ₀ (ω ^ k)) P)) := by
    intro k g
    have hBu : B (u k * g) = fun τ => B g τ * scalAt τ₀ (ω ^ k) τ := by
      funext τ
      simp only [hB_def, map_mul, Pi.mul_apply, hu k]
      rw [Submonoid.coe_mul, hU k τ]
      simp only [scalAt]
      split_ifs <;> simp [Matrix.smul_mul, Matrix.mul_smul]
    simp only [hf_def, hc_def]
    rw [hBu, colSub_mul, map_smul, smul_eq_mul]
    simp only [Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
    rw [prod_det_scalAt_zpow τ₀ (ω ^ k) m n hn]
    ring
  have hsum0 : ∀ g, ∑ k ∈ Finset.range M, f (u k * g) = 0 := by
    intro g
    simp only [hpt, ← Finset.mul_sum, ← map_sum]
    have : ∑ k ∈ Finset.range M, (ω ^ k) ^ N • colSub (B g) (colSub (scalAt τ₀ (ω ^ k)) P) =
        colSub (B g) (∑ k ∈ Finset.range M, (ω ^ k) ^ N • colSub (scalAt τ₀ (ω ^ k)) P) := by
      rw [map_sum]; simp only [map_smul]
    rw [this, sum_scalAt_eq_zero τ₀ N hN P hω, map_zero, map_zero, mul_zero]
  have hkey : (M : ℂ) * ∫ x, f x ∂ν = 0 := by
    calc (M : ℂ) * ∫ x, f x ∂ν = ∑ k ∈ Finset.range M, ∫ x, f (u k * x) ∂ν := by
          rw [Finset.sum_congr rfl fun k _ => (hinvar (u k)).2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ∫ x, ∑ k ∈ Finset.range M, f (u k * x) ∂ν :=
          (integral_finset_sum _ fun k _ => (hinvar (u k)).1).symm
      _ = 0 := by simp [hsum0]
  exact (mul_eq_zero.1 hkey).resolve_left (by exact_mod_cast hM0)

end GlobalTheory.MinorFrame
