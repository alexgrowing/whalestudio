import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityFieldTer

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem mem_pow_iff_le_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (e : ℕ) :
    n ∈ 𝔭 ^ e ↔ e ≤ vF 𝔭 n := by
  have hbdd : BddAbove {e : ℕ | n ∈ 𝔭 ^ e} := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    apply hn
    have hI := Ideal.iInf_pow_eq_bot_of_isDomain (I := 𝔭) h𝔭.ne_top
    rw [← Ideal.mem_bot, ← hI, Ideal.mem_iInf]
    intro i
    obtain ⟨e', he', hie'⟩ := hnb i
    exact Ideal.pow_le_pow_right hie'.le he'
  have hne : {e : ℕ | n ∈ 𝔭 ^ e}.Nonempty := ⟨0, by simp⟩
  unfold vF
  constructor
  · intro he
    exact le_csSup hbdd he
  · intro he
    have hmem : sSup {e : ℕ | n ∈ 𝔭 ^ e} ∈ {e : ℕ | n ∈ 𝔭 ^ e} := Nat.sSup_mem hne hbdd
    exact Ideal.pow_le_pow_right he hmem

theorem cnt_congr (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) {n n' : 𝓞 K}
    (h : n - n' ∈ extP K 𝔭 ^ k) : cnt hF 𝔭 k M n = cnt hF 𝔭 k M n' := by
  unfold cnt
  rw [Ideal.Quotient.eq.mpr h]

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem cnt_one_of_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ∈ 𝔭) :
    (cnt hF 𝔭 1 (finrank K V) (ι n) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V) -
      ((Ideal.absNorm 𝔭 : ℝ) - 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V - 1) *
        (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ)))) := by
  classical
  have h0 := sum_nkCount hK hF hs hd hL hLi h𝔭 1
  have := MeanC.finite_quot_pow h𝔭 1
  have := Fintype.ofFinite (𝓞 F ⧸ 𝔭 ^ 1)
  rw [finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl fun n' _ => nkCount_eq_cnt hK hF hs hd hL hLi h𝔭 hv le_rfl _,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : 𝓞 F ⧸ 𝔭 ^ 1))] at h0
  have h1 : (cnt hF 𝔭 1 (finrank K V) (ι (Quotient.out (0 : 𝓞 F ⧸ 𝔭 ^ 1))) : ℝ) +
      ∑ n' ∈ Finset.univ.erase (0 : 𝓞 F ⧸ 𝔭 ^ 1),
        (cnt hF 𝔭 1 (finrank K V) (ι (Quotient.out n')) : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V * 1) := by exact_mod_cast h0
  have h2 : cnt hF 𝔭 1 (finrank K V) (ι (Quotient.out (0 : 𝓞 F ⧸ 𝔭 ^ 1))) =
      cnt hF 𝔭 1 (finrank K V) (ι n) := by
    apply cnt_congr
    rw [← map_sub, idealPowerSpanBounds.mem_pow_iff]
    refine sub_mem ?_ (by rwa [pow_one])
    rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out]
  have h3 : ∀ n' ∈ Finset.univ.erase (0 : 𝓞 F ⧸ 𝔭 ^ 1),
      (cnt hF 𝔭 1 (finrank K V) (ι (Quotient.out n')) : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V - 1) *
        (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) := by
    intro n' hn'
    have hne : Quotient.out n' ∉ 𝔭 := by
      intro hmem
      apply Finset.ne_of_mem_erase hn'
      rw [← Ideal.Quotient.mk_out n', Ideal.Quotient.eq_zero_iff_mem]
      exact (pow_one 𝔭).ge hmem
    rw [cnt_unit hK hF h𝔭 hm le_rfl hne, mul_one]
  have hcard : ((Finset.univ.erase (0 : 𝓞 F ⧸ 𝔭 ^ 1)).card : ℝ) = (Ideal.absNorm 𝔭 : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card,
      MeanC.card_quot_pow, pow_one, Nat.cast_sub (MeanC.one_lt_absNorm h𝔭).le, Nat.cast_one]
  rw [h2, Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul, hcard, mul_one] at h1
  linarith

theorem real_step (q T ε β c1 cI : ℝ) (j t : ℕ) (hq : 0 < q) (hT : T = q ^ t) (hε : ε ^ 2 = 1)
    (hβ : β = 1 - ε * (q ^ (t + 1))⁻¹)
    (hc1 : c1 = q ^ (2 * (t + 1)) - (q - 1) * (q ^ (2 * (t + 1) - 1) * β)) :
    (q ^ ((2 * (t + 1) - 1) * (j + 1)) * (c1 - 1) + cI) / q ^ ((j + 2) * (2 * (t + 1) - 1)) =
      β * (1 + ε * T⁻¹) + cI / q ^ ((j + 2) * (2 * (t + 1) - 1)) := by
  subst hT hβ hc1
  have e : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
  have hq' : q ≠ 0 := hq.ne'
  have h1 : (j + 2) * (2 * t + 1) = (2 * t + 1) * (j + 1) + (2 * t + 1) := by ring
  rw [e, h1, pow_add q ((2 * t + 1) * (j + 1)) (2 * t + 1), add_div,
    mul_div_mul_left _ _ (pow_ne_zero _ hq')]
  congr 1
  have hε2 : ε = 1 ∨ ε = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact hε)
  rcases hε2 with rfl | rfl
  · field_simp
    ring
  · field_simp
    ring

end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
