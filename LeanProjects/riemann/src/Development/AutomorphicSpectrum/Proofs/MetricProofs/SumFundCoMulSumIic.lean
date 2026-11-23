import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund

def fundCo {N : ℕ} (f : Fin N → ℝ) (i : Fin N) : ℝ :=
  f i - if h : (i : ℕ) + 1 < N then f ⟨i + 1, h⟩ else 0

theorem fundCo_sub {N : ℕ} (f g : Fin N → ℝ) (i : Fin N) : fundCo (f - g) i = fundCo f i - fundCo g i := by
  unfold fundCo
  split_ifs <;> simp <;> ring

theorem fundCo_smul {N : ℕ} (c : ℝ) (f : Fin N → ℝ) (i : Fin N) : fundCo (c • f) i = c * fundCo f i := by
  unfold fundCo
  split_ifs <;> simp <;> ring

private theorem abel_range (F B : ℕ → ℝ) (M : ℕ) :
    ∑ i ∈ Finset.range M, (F i - F (i + 1)) * ∑ k ∈ Finset.range (i + 1), B k + F M * ∑ k ∈ Finset.range M, B k =
      ∑ k ∈ Finset.range M, F k * B k := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k => F k * B k), ← ih, Finset.sum_range_succ B M]
    ring

theorem sum_fundCo_mul_sum_Iic {N : ℕ} (f B : Fin N → ℝ) :
    ∑ i, fundCo f i * ∑ k ∈ Finset.Iic i, B k = ∑ k, f k * B k := by
  classical
  let F : ℕ → ℝ := fun j => if h : j < N then f ⟨j, h⟩ else 0
  let B' : ℕ → ℝ := fun j => if h : j < N then B ⟨j, h⟩ else 0
  have hF : ∀ i : Fin N, F i = f i := fun i => by simp [F, i.2]
  have hB : ∀ i : Fin N, B' i = B i := fun i => by simp [B', i.2]
  have hFN : F N = 0 := by simp [F]
  have hco : ∀ i : Fin N, fundCo f i = F i - F (i + 1) := fun i => by
    simp only [fundCo, hF]
    congr 1
  have hI : ∀ i : Fin N, ∑ k ∈ Finset.Iic i, B k = ∑ k ∈ Finset.range ((i : ℕ) + 1), B' k := by
    intro i
    symm
    refine Finset.sum_bij' (fun j hj => (⟨j, by have := Finset.mem_range.1 hj; have := i.2; omega⟩ : Fin N))
      (fun k _ => (k : ℕ)) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Iic, Fin.le_def]
      have := Finset.mem_range.1 hj
      omega
    · intro k hk
      have : (k : ℕ) ≤ i := Fin.le_def.1 (Finset.mem_Iic.1 hk)
      exact Finset.mem_range.2 (by omega)
    · intro j hj; rfl
    · intro k hk; rfl
    · intro j hj
      have h1 : j < N := by have := Finset.mem_range.1 hj; have := i.2; omega
      simp [B', h1]
  have h := abel_range F B' N
  rw [hFN, zero_mul, add_zero] at h
  simp only [hco, hI]
  rw [Fin.sum_univ_eq_sum_range (fun i => (F i - F (i + 1)) * ∑ k ∈ Finset.range (i + 1), B' k) N, h,
    ← Fin.sum_univ_eq_sum_range (fun k => F k * B' k) N]
  exact Finset.sum_congr rfl fun k _ => by rw [hF, hB]

theorem aeval_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {S : Type} [CommRing S]
    {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) (t : K → S) (x : (Σ k, ι k) → S) :
    aeval (fun p => t p.1 * x p) g = (∏ k, t k ^ a k) * aeval x g := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ p, (t p.1 * x p) ^ m p = (∏ k, t k ^ a k) * ∏ p, x p ^ m p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = t k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [hprod]
  ring

theorem isMultiHomog_mul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {f g : MRing ι}
    {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hm)
  simp [Finset.sum_add_distrib, hf m₁ h₁ k, hg m₂ h₂ k]

theorem aeval_eq_zero_of_mem {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω)
    {f : MRing ι} (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  have hc : (MvPolynomial.eval (fun _ : K => (1 : Ω))).comp (mConeMap y).toRingHom = (aeval y).toRingHom :=
    MvPolynomial.ringHom_ext (fun n => by simp) (fun p => by simp [mConeMap])
  have h0 : mConeMap y f = 0 := hf
  have := congrArg (fun φ => φ f) hc
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h0, map_zero] at this
  exact this.symm

theorem hasVal_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (h : HasVal y a s z v) : HasVal y a s (fun p => c p.1 * z p) (v * ∏ k, c k ^ a k) := by
  obtain ⟨dg, dh, g, k', hg, hk, hd, hy, h0, hv⟩ := h
  refine ⟨dg, dh, g, k', hg, hk, hd, hy, ?_, ?_⟩
  · rw [aeval_scale hk]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)) h0
  · rw [aeval_scale hg, aeval_scale hk, hv]
    have e : ∀ k, c k ^ dg k = c k ^ a k * c k ^ dh k := fun k => by
      rw [← zpow_natCast, hd k, zpow_add₀ (hc k), zpow_natCast, mul_comm]
    simp only [e, Finset.prod_mul_distrib]
    ring

theorem isSmoothHerm_comb {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {σ : Type} [Fintype σ]
    {A : σ → HermLine ι} (hA : ∀ a, IsSmoothHerm (A a)) (n : σ → ℤ) : IsSmoothHerm (combLine A n) := by
  refine contDiffOn_prod fun a _ => ?_
  intro z hz
  have h0 : (A a).h z ≠ 0 := ((A a).pos z hz).ne'
  have hf := hA a z hz
  have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (A a).h z ^ m)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
    intro m
    cases m with
    | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
    | negSucc k =>
      simp only [zpow_negSucc]
      exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
  exact key _

end GlobalTheory.CompanionTheory.Ar.Small.Fund
