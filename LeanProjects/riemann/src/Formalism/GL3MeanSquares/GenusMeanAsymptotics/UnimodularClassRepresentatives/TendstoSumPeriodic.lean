import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSumCoset

open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem finite_quot {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : Finite (𝓞 F ⧸ I) :=
  Ideal.finiteQuotientOfFreeOfNeBot I hI

theorem exists_crt {b 𝔞 : Ideal (𝓞 F)} (hco : b ⊔ 𝔞 = ⊤) (x₀ : 𝓞 F) (c : 𝓞 F ⧸ 𝔞) :
    ∃ x : 𝓞 F, x - x₀ ∈ b ∧ Ideal.Quotient.mk 𝔞 x = c := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective c
  have h1 : (1 : 𝓞 F) ∈ b ⊔ 𝔞 := by rw [hco]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h1
  refine ⟨x₀ * v + y * u, ?_, ?_⟩
  · have e : x₀ * v + y * u - x₀ = (y - x₀) * u := by linear_combination x₀ * huv
    rw [e]
    exact b.mul_mem_left _ hu
  · rw [Ideal.Quotient.eq]
    have e : x₀ * v + y * u - y = (x₀ - y) * v := by linear_combination y * huv
    rw [e]
    exact 𝔞.mul_mem_left _ hv

theorem sum_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) {b 𝔞 : Ideal (𝓞 F)}
    [Fintype (𝓞 F ⧸ 𝔞)] (hco : b ⊔ 𝔞 = ⊤) (x₀ : 𝓞 F) (g : 𝓞 F → ℝ) (φ : 𝓞 F ⧸ 𝔞 → ℝ)
    (x : 𝓞 F ⧸ 𝔞 → 𝓞 F) (hx : ∀ c, x c - x₀ ∈ b ∧ Ideal.Quotient.mk 𝔞 (x c) = c) :
    ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x₀ ∈ b}, g n * φ (Ideal.Quotient.mk 𝔞 n) =
      ∑ c, φ c * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x c ∈ b * 𝔞}, g n := by
  set S := {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x₀ ∈ b} with hSdef
  have hS : S.Finite := finite_box_inter hK hF T {n | n - x₀ ∈ b}
  have hT : ∀ c, {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x c ∈ b * 𝔞} = {n | n ∈ S ∧ Ideal.Quotient.mk 𝔞 n = c} := by
    intro c
    ext n
    simp only [Set.mem_setOf_eq, hSdef]
    rw [Ideal.mul_eq_inf_of_coprime hco, Ideal.mem_inf]
    constructor
    · rintro ⟨hn, h1, h2⟩
      refine ⟨⟨hn, ?_⟩, ?_⟩
      · have := b.add_mem h1 (hx c).1
        rwa [sub_add_sub_cancel] at this
      · rw [← (hx c).2]
        exact Ideal.Quotient.eq.mpr h2
    · rintro ⟨⟨hn, h1⟩, h2⟩
      refine ⟨hn, ?_, ?_⟩
      · have := b.sub_mem h1 (hx c).1
        rwa [sub_sub_sub_cancel_right] at this
      · rw [← (hx c).2] at h2
        exact Ideal.Quotient.eq.mp h2
  have hSc : ∀ c, ({n | n ∈ S ∧ Ideal.Quotient.mk 𝔞 n = c} : Set (𝓞 F)).Finite :=
    fun c => hS.subset fun n hn => hn.1
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, ← Finset.sum_fiberwise hS.toFinset (Ideal.Quotient.mk 𝔞)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hT c, finsum_mem_eq_finite_toFinset_sum _ (hSc c), Finset.mul_sum]
  have e : (hSc c).toFinset = hS.toFinset.filter (fun n => Ideal.Quotient.mk 𝔞 n = c) := by
    ext n
    simp
  rw [e]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [(Finset.mem_filter.mp hn).2, mul_comm]

theorem tendsto_sum_periodic (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    (k : ℕ) (φ : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (𝓞 F ⧸ 𝔭.1 ^ k) → ℝ)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∀ (b : Ideal (𝓞 F)), b ≠ ⊥ → (∀ 𝔭 ∈ S, b ⊔ 𝔭.1 = ⊤) → ∀ x₀ : 𝓞 F,
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x₀ ∈ b},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
            ∏ 𝔭 ∈ S, φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n))
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm b : ℝ) *
          ∏ 𝔭 ∈ S, ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) * ∑ᶠ c, φ 𝔭 c))) := by
  induction S using Finset.induction_on with
  | empty =>
    intro b hb _ x₀
    have := tendsto_sum_coset hK hF hm hb x₀
    simp only [Finset.prod_empty, mul_one]
    exact this
  | insert 𝔮 S' h𝔮S ih =>
    intro b hb hcop x₀
    have h𝔮0 : 𝔮.1 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField 𝔮.2 (RingOfIntegers.not_isField F)
    have h𝔞0 : 𝔮.1 ^ k ≠ ⊥ := by
      have h0 : 𝔮.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using h𝔮0
      simpa only [Ideal.zero_eq_bot] using pow_ne_zero k h0
    haveI : Fintype (𝓞 F ⧸ 𝔮.1 ^ k) := @Fintype.ofFinite _ (finite_quot h𝔞0)
    have hco : b ⊔ 𝔮.1 ^ k = ⊤ := by
      have h1 : IsCoprime b 𝔮.1 := Ideal.isCoprime_iff_sup_eq.mpr (hcop 𝔮 (Finset.mem_insert_self _ _))
      exact Ideal.isCoprime_iff_sup_eq.mp h1.pow_right
    choose x hx using fun c => exists_crt hco x₀ c
    have hb' : b * 𝔮.1 ^ k ≠ ⊥ := by
      have h0 : b ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hb
      have h1 : 𝔮.1 ^ k ≠ 0 := by simpa only [Ideal.zero_eq_bot] using h𝔞0
      simpa only [Ideal.zero_eq_bot] using mul_ne_zero h0 h1
    have hcop' : ∀ 𝔭 ∈ S', b * 𝔮.1 ^ k ⊔ 𝔭.1 = ⊤ := by
      intro 𝔭 h𝔭
      have h1 : IsCoprime b 𝔭.1 := Ideal.isCoprime_iff_sup_eq.mpr (hcop 𝔭 (Finset.mem_insert_of_mem h𝔭))
      have hne : 𝔮.1 ≠ 𝔭.1 := fun e => h𝔮S ((Subtype.ext e : 𝔮 = 𝔭) ▸ h𝔭)
      have h2 : IsCoprime 𝔮.1 𝔭.1 := Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne 𝔮.2 𝔭.2 hne)
      have h3 : IsCoprime (𝔮.1 ^ k) 𝔭.1 := h2.pow_left
      exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h3)
    have hlim := fun c => ih (b * 𝔮.1 ^ k) hb' hcop' (x c)

    have hsplit : ∀ j : ℕ, ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x₀ ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ insert 𝔮 S', φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n) =
        ∑ c, φ 𝔮 c * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x c ∈ b * 𝔮.1 ^ k},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S', φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n) := by
      intro j
      rw [← sum_split hK hF _ hco x₀ (fun n => (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
        ∏ 𝔭 ∈ S', φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n)) (φ 𝔮) x hx]
      refine finsum_mem_congr rfl fun n _ => ?_
      rw [Finset.prod_insert h𝔮S]
      ring
    have hT := tendsto_finset_sum (Finset.univ : Finset (𝓞 F ⧸ 𝔮.1 ^ k)) fun c _ => (hlim c).const_mul (φ 𝔮 c)
    convert hT using 1
    · funext j
      rw [hsplit j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    · congr 1
      rw [Finset.prod_insert h𝔮S, finsum_eq_sum_of_fintype]
      simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow, zpow_neg, zpow_natCast, Finset.mul_sum,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring

end Formalism.HermitianLattices.Ext.L3.BoxSum
