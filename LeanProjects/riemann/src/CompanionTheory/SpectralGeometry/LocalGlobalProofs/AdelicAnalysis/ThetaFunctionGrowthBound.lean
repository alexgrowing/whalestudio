import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DenominatorPowerSummableStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierCoefficientGrowthBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanGaussianFourierStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EisensteinLatticeSumBoundStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.EiBound

theorem prod_sum_bound {S R : Type} (h : S × R → ℝ) (a : S → ℝ) (K : ℝ) (h0 : ∀ p, 0 ≤ h p)
    (ha : Summable a)
    (hin : ∀ s, Summable (fun r => h (s, r)) ∧ ∑' r, h (s, r) ≤ a s * K) :
    Summable h ∧ ∑' p, h p ≤ (∑' s, a s) * K := by
  have hout : Summable (fun s => ∑' r, h (s, r)) :=
    Summable.of_nonneg_of_le (fun s => tsum_nonneg fun r => h0 _) (fun s => (hin s).2)
      (ha.mul_right K)
  have hs : Summable h := (summable_prod_of_nonneg (fun p => h0 p)).2 ⟨fun s => (hin s).1, hout⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod, ← tsum_mul_right]
  exact Summable.tsum_le_tsum (fun s => (hin s).2) hout (ha.mul_right K)

theorem exists_decomp (F : Type) [Field F] [NumberField F] :
    ∃ (Q : Type) (out : Q → F), Function.Injective out ∧
      (∀ q q', (∃ r : 𝓞 F, out q - out q' = (r : F)) → q = q') ∧
      Function.Bijective (fun p : Q × 𝓞 F => out p.1 + (p.2 : F)) := by
  let L : AddSubgroup F := (algebraMap (𝓞 F) F).toAddMonoidHom.range
  have hL : ∀ x : F, x ∈ L ↔ ∃ r : 𝓞 F, (r : F) = x := fun x => by
    simp [L, AddMonoidHom.mem_range]
  have hsep : ∀ q q' : F ⧸ L, (∃ r : 𝓞 F, (Quotient.out q : F) - Quotient.out q' = (r : F)) →
      q = q' := by
    rintro q q' ⟨r, hr⟩
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
    refine (QuotientAddGroup.eq).2 ?_
    have : -(Quotient.out q : F) + Quotient.out q' = ((-r : 𝓞 F) : F) := by
      push_cast
      linear_combination -hr
    exact (hL _).2 ⟨-r, this.symm⟩
  refine ⟨F ⧸ L, Quotient.out, ?_, hsep, ?_, ?_⟩
  · intro q q' h
    exact hsep q q' ⟨0, by simp [h]⟩
  · rintro ⟨q, r⟩ ⟨q', r'⟩ h
    simp only at h
    have hq : q = q' := hsep q q' ⟨r' - r, by push_cast; linear_combination h⟩
    subst hq
    have : (r : F) = r' := add_left_cancel h
    have : r = r' := RingOfIntegers.ext this
    rw [this]
  · intro b
    have h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk b : F ⧸ L)) : F ⧸ L) =
        QuotientAddGroup.mk b := QuotientAddGroup.out_eq' _
    obtain ⟨r, hr⟩ := (hL _).1 ((QuotientAddGroup.eq).1 h1)
    refine ⟨⟨QuotientAddGroup.mk b, r⟩, ?_⟩
    simp only
    rw [hr]; ring

theorem place_bound (M : ℕ) (hM : 2 ≤ M) (t y : ℝ) (ht : 0 < t) (hy : t ≤ y) :
    Real.sqrt y ^ M * (y * (y ^ M)⁻¹) ≤ ((Real.sqrt t) ^ (M - 2))⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
  have hy0 : 0 < y := ht.trans_le hy
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hyy : y = Real.sqrt y ^ 2 := (Real.sq_sqrt hy0.le).symm
  have e : Real.sqrt y ^ (k + 2) * (y * (y ^ (k + 2))⁻¹) = (Real.sqrt y ^ k)⁻¹ := by
    generalize Real.sqrt y = s at hs hyy
    subst hyy
    field_simp
    ring
  rw [e, Nat.add_sub_cancel]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hst.le (Real.sqrt_le_sqrt hy) k)

theorem ei_bound : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)]
    (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M →
    ∀ φ : (ι → A F) → ℂ, SB φ → ∀ t : ℝ, 0 < t → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ,
    (∀ w, t ≤ (τ w).im) → Summable (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖) ∧
      wt M τ * ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖ ≤ C := by
  intro F _ _ _ _ lf hlf hO ψ hψ ι _ _ M B ρ P hQ hM φ hφ t ht
  have hTR : IsTotallyReal F := hQ.1
  have hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x := hQ.2.2.2.2.1
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.fourier_coefficient_growth_bound F lf hlf hO ψ hψ ι M B ρ P hQ φ hφ
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.eisenstein_lattice_sum_bound F hTR ρ hρ M (by omega) t ht
  obtain ⟨Q, out, hinj, hsep, hbij⟩ := exists_decomp F
  obtain ⟨hd1, hd2, hd3⟩ := GlobalTheory.T.denominator_power_summable F M hM 1 one_pos
  let a : Q → ℝ := fun q => ((den (out q) : ℝ) ^ M)⁻¹
  have ha0 : ∀ q, 0 ≤ a q := fun q => by positivity
  have ha : Summable a := by
    have h := hd3 (Set.range out) (by
      rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩ ⟨r, hr⟩
      rw [hsep q q' ⟨r, by simpa using hr⟩])
    exact (Equiv.ofInjective out hinj).summable_iff.2 h
  have hterm : ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ b : F,
      ‖eiTerm ψ lf B ρ P φ τ b‖ ≤
        |C1| * ((den b : ℝ) ^ M)⁻¹ * (∏ w, ‖τ w + (ρ w b : ℝ)‖ ^ M)⁻¹ := by
    intro τ hτ b
    have hc := (GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P hQ (fun w => τ w + (ρ w b : ℝ))
      (fun w => by simpa using hτ w)).2.1
    unfold eiTerm
    rw [norm_mul, hc]
    refine mul_le_mul_of_nonneg_right ((hC1 b).trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  refine ⟨(∑' q, a q) * |C1| * |C2| * ∏ _w : InfinitePlace F, ((Real.sqrt t) ^ (M - 2))⁻¹, ?_⟩
  intro τ hτ
  have hτ0 : ∀ w, 0 < (τ w).im := fun w => ht.trans_le (hτ w)
  set Y : ℝ := ∏ w, (τ w).im * ((τ w).im ^ M)⁻¹ with hYdef
  have hY0 : 0 ≤ Y := Finset.prod_nonneg fun w _ => by
    have := hτ0 w
    positivity
  let e : Q × 𝓞 F ≃ F := Equiv.ofBijective _ hbij
  let h' : Q × 𝓞 F → ℝ := fun p =>
    |C1| * a p.1 * (∏ w, ‖(τ w + (ρ w (out p.1) : ℝ)) + (ρ w (p.2 : F) : ℝ)‖ ^ M)⁻¹
  have hh'0 : ∀ p, 0 ≤ h' p := fun p => by
    have := ha0 p.1
    positivity
  have hle : ∀ p, ‖eiTerm ψ lf B ρ P φ τ (e p)‖ ≤ h' p := by
    rintro ⟨q, r⟩
    have h1 := hterm τ hτ0 (out q + (r : F))
    have h2 : den (out q + (r : F)) = den (out q) := hd1 _ _
    rw [h2] at h1
    have h3 : ∀ w, τ w + ((ρ w (out q + (r : F)) : ℝ) : ℂ) =
        (τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ) := fun w => by
      rw [map_add]; push_cast; ring
    simp only [h3] at h1
    exact h1
  have hin : ∀ q, Summable (fun r => h' (q, r)) ∧
      ∑' r, h' (q, r) ≤ a q * (|C1| * (|C2| * Y)) := by
    intro q
    obtain ⟨hs, hb⟩ := hC2 (fun w => τ w + (ρ w (out q) : ℝ)) (fun w => by simpa using hτ w)
    have him : ∀ w, (τ w + ((ρ w (out q) : ℝ) : ℂ)).im = (τ w).im := fun w => by simp
    simp only [him] at hb
    have hs' : Summable (fun r : 𝓞 F => |C1| * a q *
        (∏ w, ‖(τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹) := hs.mul_left _
    refine ⟨hs', ?_⟩
    have hq0 := ha0 q
    change ∑' r : 𝓞 F, |C1| * a q *
        (∏ w, ‖(τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹ ≤ _
    rw [tsum_mul_left]
    calc |C1| * a q * ∑' r : 𝓞 F, (∏ w, ‖(τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹
        ≤ |C1| * a q * (|C2| * Y) :=
          mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hY0))
            (by positivity)
      _ = a q * (|C1| * (|C2| * Y)) := by ring
  obtain ⟨hsum', hbd'⟩ := prod_sum_bound h' a (|C1| * (|C2| * Y)) hh'0 ha hin
  have hsumc : Summable (fun p => ‖eiTerm ψ lf B ρ P φ τ (e p)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum'
  have hsum : Summable (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖) := e.summable_iff.1 hsumc
  refine ⟨hsum, ?_⟩
  have htot : ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖ ≤ (∑' q, a q) * (|C1| * (|C2| * Y)) := by
    rw [← e.tsum_eq (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖)]
    exact (Summable.tsum_le_tsum hle hsumc hsum').trans hbd'
  have hwt0 : 0 ≤ wt M τ := Finset.prod_nonneg fun w _ => by positivity
  have hA0 : 0 ≤ ∑' q, a q := tsum_nonneg ha0
  have hwY : wt M τ * Y ≤ ∏ _w : InfinitePlace F, ((Real.sqrt t) ^ (M - 2))⁻¹ := by
    rw [hYdef]
    unfold wt
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun w _ => ?_) (fun w _ => place_bound M (by omega) t _ ht (hτ w))
    have := hτ0 w
    positivity
  calc wt M τ * ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖
      ≤ wt M τ * ((∑' q, a q) * (|C1| * (|C2| * Y))) :=
        mul_le_mul_of_nonneg_left htot hwt0
    _ = (∑' q, a q) * |C1| * |C2| * (wt M τ * Y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwY (by positivity)

end GlobalTheory.CompanionTheory.SW.Core.EiBound
