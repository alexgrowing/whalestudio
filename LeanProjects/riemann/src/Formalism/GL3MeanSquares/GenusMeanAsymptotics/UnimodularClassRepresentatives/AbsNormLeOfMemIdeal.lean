import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormEqProdOfMem

open NumberField Module
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxCube

open BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem absNorm_le_of_mem_ideal {b : Ideal (𝓞 F)} {n : 𝓞 F} (hn : n ∈ b) (h0 : n ≠ 0) :
    (Ideal.absNorm b : ℝ) ≤ (Ideal.absNorm (Ideal.span {n}) : ℝ) := by
  have h1 : Ideal.absNorm b ∣ Ideal.absNorm (Ideal.span {n}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem b).2 hn)
  have h2 : Ideal.absNorm (Ideal.span {n}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact h0
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1

theorem absNorm_le_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)} {T : ℝ}
    {n : 𝓞 F} (hn : n ∈ boxSet K F T) (hb : n ∈ b) :
    (Ideal.absNorm b : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K :=
  (absNorm_le_of_mem_ideal hb (ne_zero_of_mem_boxSet hn)).trans (absNorm_le_of_mem hK hF hn)

theorem eq_of_close (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)} {δ : ℝ}
    (hδ : δ ^ Formalism.HermitianLatticesTheory.fDeg K ≤ (Ideal.absNorm b : ℝ)) {n n' : 𝓞 F} (hn : n ∈ b) (hn' : n' ∈ b)
    (hc : ∀ w : {w : InfinitePlace F // w.IsReal}, |rEmb w n - rEmb w n'| < δ) : n = n' := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  by_contra hne
  have h0 : n - n' ≠ 0 := sub_ne_zero.2 hne
  have h1 := absNorm_le_of_mem_ideal (b.sub_mem hn hn') h0
  rw [absNorm_eq_prod] at h1
  have hne' : (Finset.univ : Finset {w : InfinitePlace F // w.IsReal}).Nonempty := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact ⟨⟨w, IsTotallyReal.isReal w⟩, Finset.mem_univ _⟩
  have h2 : ∏ w : {w : InfinitePlace F // w.IsReal}, |rEmb w (n - n')| <
      ∏ _w : {w : InfinitePlace F // w.IsReal}, δ := by
    refine Finset.prod_lt_prod_of_nonempty (fun w _ => ?_) (fun w _ => ?_) hne'
    · rw [abs_pos]
      intro h3
      apply h0
      have : (InfinitePlace.embedding_of_isReal w.2) ((n - n' : 𝓞 F) : F) = 0 := h3
      rw [map_eq_zero] at this
      exact RingOfIntegers.coe_injective (by simpa using this)
    · rw [map_sub]
      exact hc w
  rw [Finset.prod_const, Finset.card_univ, card_real hK hF] at h2
  linarith

theorem abs_sub_lt_of_floor_eq {δ a a' : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (h : ⌊a / δ⌋₊ = ⌊a' / δ⌋₊) : |a - a'| < δ := by
  have h1 := Nat.floor_le (div_nonneg ha hδ.le)
  have h2 := Nat.lt_floor_add_one (a / δ)
  have h3 := Nat.floor_le (div_nonneg ha' hδ.le)
  have h4 := Nat.lt_floor_add_one (a' / δ)
  rw [h] at h1 h2
  have h5 : a / δ - a' / δ < 1 := by linarith
  have h6 : a' / δ - a / δ < 1 := by linarith
  rw [← sub_div, div_lt_one hδ] at h5 h6
  rw [abs_lt]
  constructor <;> linarith

theorem card_le_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)} {δ T : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ^ Formalism.HermitianLatticesTheory.fDeg K ≤ (Ideal.absNorm b : ℝ)) :
    Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} ≤ (⌊T / δ⌋₊ + 1) ^ Formalism.HermitianLatticesTheory.fDeg K := by
  let W := {w : InfinitePlace F // w.IsReal}
  let g : {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} → (W → Fin (⌊T / δ⌋₊ + 1)) := fun n w =>
    ⟨⌊rEmb w n.1 / δ⌋₊, Nat.lt_succ_of_le (Nat.floor_le_floor
      (div_le_div_of_nonneg_right (((mem_boxSet_iff hK hF).1 n.2.1) w).2 hδ0.le))⟩
  have hg : Function.Injective g := by
    intro n n' h
    refine Subtype.ext (eq_of_close hK hF hδ n.2.2 n'.2.2 fun w => ?_)
    have h1 : ⌊rEmb w n.1 / δ⌋₊ = ⌊rEmb w n'.1 / δ⌋₊ := congrArg Fin.val (congrFun h w)
    exact abs_sub_lt_of_floor_eq hδ0 (((mem_boxSet_iff hK hF).1 n.2.1) w).1.le
      (((mem_boxSet_iff hK hF).1 n'.2.1) w).1.le h1
  have h1 := Nat.card_le_card_of_injective g hg
  have h2 : Nat.card (W → Fin (⌊T / δ⌋₊ + 1)) = (⌊T / δ⌋₊ + 1) ^ Formalism.HermitianLatticesTheory.fDeg K := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, card_real hK hF]
  rwa [h2] at h1

theorem fDeg_pos : 0 < Formalism.HermitianLatticesTheory.fDeg K := Fintype.card_pos

theorem card_box_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)}
    (hb : b ≠ ⊥) {T : ℝ} (hT0 : 0 ≤ T) :
    (Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} : ℝ) ≤
      2 ^ Formalism.HermitianLatticesTheory.fDeg K * T ^ Formalism.HermitianLatticesTheory.fDeg K / (Ideal.absNorm b : ℝ) := by
  have hf : Formalism.HermitianLatticesTheory.fDeg K ≠ 0 := (fDeg_pos (K := K)).ne'
  have hN : (0 : ℝ) < (Ideal.absNorm b : ℝ) := by
    have : Ideal.absNorm b ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.pos_of_ne_zero this
  by_cases he : IsEmpty {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b}
  · rw [Nat.card_of_isEmpty, Nat.cast_zero, ← mul_pow]
    positivity
  rw [not_isEmpty_iff] at he
  obtain ⟨n, hn, hnb⟩ := he
  have hT : 0 < T := by
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    exact (hn φ).1.trans_le (hn φ).2
  set δ : ℝ := (Ideal.absNorm b : ℝ) ^ ((Formalism.HermitianLatticesTheory.fDeg K : ℝ)⁻¹) with hδdef
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hN _
  have hδ : δ ^ Formalism.HermitianLatticesTheory.fDeg K = (Ideal.absNorm b : ℝ) := Real.rpow_inv_natCast_pow hN.le hf
  have hδT : δ ≤ T := by
    have := absNorm_le_pow hK hF hn hnb
    rw [← hδ] at this
    exact (pow_le_pow_iff_left₀ hδ0.le hT.le hf).1 this
  have h1 := card_le_pow hK hF (T := T) hδ0 hδ.le
  have h2 : ((⌊T / δ⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T / δ := by
    have h3 := Nat.floor_le (div_nonneg hT.le hδ0.le)
    have h4 : 1 ≤ T / δ := (one_le_div hδ0).2 hδT
    push_cast
    rw [mul_div_assoc]
    linarith
  calc (Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ b} : ℝ)
      ≤ (((⌊T / δ⌋₊ + 1) ^ Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ((⌊T / δ⌋₊ + 1 : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K := by push_cast; rfl
    _ ≤ (2 * T / δ) ^ Formalism.HermitianLatticesTheory.fDeg K := pow_le_pow_left₀ (by positivity) h2 _
    _ = _ := by rw [div_pow, mul_pow, hδ]

end Formalism.HermitianLattices.Ext.L3.BoxCube
