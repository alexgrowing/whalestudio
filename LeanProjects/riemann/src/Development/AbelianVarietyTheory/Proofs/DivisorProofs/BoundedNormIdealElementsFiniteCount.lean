import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CountBox

theorem exists_emb_place_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ w : InfinitePlace F, ∃ τ : E →+* ℂ, ∀ c : E,
      w (Algebra.norm F c) = ‖τ c‖ ^ 2 := by
  intro F E _ _ _ _ _ σ h w
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  refine ⟨τ.1, fun x => ?_⟩
  have hext : ∀ y : w.Completion ⊗[F] E, InfinitePlace.Completion.extensionEmbedding w (Algebra.norm w.Completion y)
      = ((‖infEmb τ y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    have h1 := congrArg (infEmb τ) (GlobalTheory.Doubling.algebraMap_norm_eq h y)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, infEmb_tmul, map_one,
      mul_one, map_mul, ← infEmb_sigR h τ, Complex.mul_conj'] at h1
    rw [h1]; push_cast; ring
  have e1 : infEmb τ (inclR (F := F) w.Completion x) = τ.1 x := by simp [inclR, infEmb_tmul]
  have e2 : InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion (Algebra.norm F x)) =
      w.embedding (Algebra.norm F x) :=
    InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm _)
  have h1 := hext (inclR (F := F) w.Completion x)
  rw [GlobalTheory.Doubling.norm_inclR, e2, e1] at h1
  have h2 := congrArg norm h1
  rwa [InfinitePlace.norm_embedding_eq, Complex.norm_of_nonneg (by positivity)] at h2

theorem cell_bound (m : ℕ) (hm : 1 ≤ m) (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ m) :
    ((min ⌊u⌋₊ (m - 1) : ℕ) : ℝ) ≤ u ∧ u ≤ ((min ⌊u⌋₊ (m - 1) : ℕ) : ℝ) + 1 := by
  rcases le_total ⌊u⌋₊ (m - 1) with h | h
  · rw [min_eq_left h]; exact ⟨Nat.floor_le h0, (Nat.lt_floor_add_one u).le⟩
  · rw [min_eq_right h]
    have e : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub hm]; simp
    refine ⟨?_, by rw [e]; linarith⟩
    calc ((m - 1 : ℕ) : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast h
      _ ≤ u := Nat.floor_le h0

noncomputable def cellIdx (m : ℕ) (s x : ℝ) : ℕ := min ⌊(x + s) / (2 * s) * m⌋₊ (m - 1)

theorem cellIdx_lt (m : ℕ) (hm : 1 ≤ m) (s x : ℝ) : cellIdx m s x < m :=
  lt_of_le_of_lt (min_le_right _ _) (by omega)

theorem cellIdx_close (m : ℕ) (hm : 1 ≤ m) (s x y : ℝ) (hs : 0 ≤ s) (hx : |x| ≤ s) (hy : |y| ≤ s)
    (he : cellIdx m s x = cellIdx m s y) : |x - y| ≤ 2 * s / m := by
  rcases hs.eq_or_lt with rfl | hs
  · have hx0 : x = 0 := abs_nonpos_iff.mp hx
    have hy0 : y = 0 := abs_nonpos_iff.mp hy
    simp [hx0, hy0]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  have key : ∀ t : ℝ, -s ≤ t → t ≤ s → 0 ≤ (t + s) / (2 * s) * m ∧ (t + s) / (2 * s) * m ≤ m := by
    intro t h1 h2
    refine ⟨mul_nonneg (div_nonneg (by linarith) (by positivity)) (Nat.cast_nonneg _), ?_⟩
    have : (t + s) / (2 * s) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  obtain ⟨a0, a1⟩ := key x hx1 hx2
  obtain ⟨b0, b1⟩ := key y hy1 hy2
  obtain ⟨u1, u2⟩ := cell_bound m hm _ a0 a1
  obtain ⟨v1, v2⟩ := cell_bound m hm _ b0 b1
  unfold cellIdx at he
  rw [he] at u1 u2
  have huv : |(x + s) / (2 * s) * m - (y + s) / (2 * s) * m| ≤ 1 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have e : (x + s) / (2 * s) * m - (y + s) / (2 * s) * m = (x - y) * (m / (2 * s)) := by
    field_simp; ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < m / (2 * s))] at huv
  rw [le_div_iff₀ hm']
  have : |x - y| * m ≤ 2 * s := by
    have h := mul_le_mul_of_nonneg_right huv (by positivity : (0:ℝ) ≤ 2 * s)
    have e2 : |x - y| * (m / (2 * s)) * (2 * s) = |x - y| * m := by field_simp
    linarith
  linarith

theorem cell_close_sq (m : ℕ) (hm : 1 ≤ m) (T : ℝ) (hT : 0 ≤ T) (z w : ℂ) (hz : ‖z‖ ^ 2 ≤ T) (hw : ‖w‖ ^ 2 ≤ T)
    (hre : cellIdx m (Real.sqrt T) z.re = cellIdx m (Real.sqrt T) w.re)
    (him : cellIdx m (Real.sqrt T) z.im = cellIdx m (Real.sqrt T) w.im) :
    ‖z - w‖ ^ 2 ≤ 8 * T / (m : ℝ) ^ 2 := by
  have hz' : ‖z‖ ≤ Real.sqrt T := by simpa using Real.abs_le_sqrt hz
  have hw' : ‖w‖ ≤ Real.sqrt T := by simpa using Real.abs_le_sqrt hw
  have s0 := Real.sqrt_nonneg T
  have h1 := cellIdx_close m hm _ _ _ s0 ((Complex.abs_re_le_norm z).trans hz') ((Complex.abs_re_le_norm w).trans hw') hre
  have h2 := cellIdx_close m hm _ _ _ s0 ((Complex.abs_im_le_norm z).trans hz') ((Complex.abs_im_le_norm w).trans hw') him
  have q1 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have q2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  rw [sq_abs] at q1 q2
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  have e : (2 * Real.sqrt T / m) ^ 2 = 4 * T / (m : ℝ) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hT]; ring
  rw [e] at q1 q2
  have : 8 * T / (m : ℝ) ^ 2 = 4 * T / (m : ℝ) ^ 2 + 4 * T / (m : ℝ) ^ 2 := by ring
  nlinarith

theorem count_sep : ∀ (X ι : Type) [Fintype ι] [Nonempty ι] (S : Set X) (z : X → ι → ℂ) (T : ι → ℝ) (N : ℝ),
    0 < N → (∀ i, 0 ≤ T i) → (∀ x ∈ S, ∀ i, ‖z x i‖ ^ 2 ≤ T i) →
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → N ≤ ∏ i, ‖z x i - z y i‖ ^ 2) →
    S.Finite ∧ (S.ncard : ℝ) ≤ 1 + 32 ^ Fintype.card ι * (∏ i, T i) / N := by
  intro X ι _ _ S z T N hN hT hS hsep
  set d := Fintype.card ι with hd
  have hd1 : 1 ≤ d := Fintype.card_pos
  set P := ∏ i, T i with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => hT i
  have hex : ∃ m : ℕ, 1 ≤ m ∧ 8 ^ d * P < (m : ℝ) ^ (2 * d) * N := by
    refine ⟨⌈8 ^ d * P / N⌉₊ + 1, by omega, ?_⟩
    set m := ⌈8 ^ d * P / N⌉₊ + 1
    have h1 : 8 ^ d * P / N < m := by
      have := Nat.le_ceil (8 ^ d * P / N)
      simp only [m]; push_cast; linarith
    have h2 : (m : ℝ) ≤ (m : ℝ) ^ (2 * d) := le_self_pow₀ (by simp [m]) (by omega)
    rw [div_lt_iff₀ hN] at h1
    nlinarith
  classical
  set m := Nat.find hex with hmdef
  have hm1 : 1 ≤ m := (Nat.find_spec hex).1
  have hmN : 8 ^ d * P < (m : ℝ) ^ (2 * d) * N := (Nat.find_spec hex).2
  let cell : X → ι → Fin m × Fin m := fun x i =>
    (⟨cellIdx m (Real.sqrt (T i)) (z x i).re, cellIdx_lt m hm1 _ _⟩,
     ⟨cellIdx m (Real.sqrt (T i)) (z x i).im, cellIdx_lt m hm1 _ _⟩)
  have hinj : Set.InjOn cell S := by
    intro x hx y hy hxy
    by_contra hne
    have hle := hsep x hx y hy hne
    have hb : ∀ i, ‖z x i - z y i‖ ^ 2 ≤ 8 * T i / (m : ℝ) ^ 2 := by
      intro i
      have hc := congrFun hxy i
      simp only [cell, Prod.mk.injEq, Fin.mk.injEq] at hc
      exact cell_close_sq m hm1 (T i) (hT i) _ _ (hS x hx i) (hS y hy i) hc.1 hc.2
    have hprod : ∏ i, ‖z x i - z y i‖ ^ 2 ≤ ∏ i, (8 * T i / (m : ℝ) ^ 2) :=
      Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hb i)
    have e : ∏ i, (8 * T i / (m : ℝ) ^ 2) = 8 ^ d * P / (m : ℝ) ^ (2 * d) := by
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
        Finset.card_univ, ← hd, ← hP]
      ring
    have hmpos : (0 : ℝ) < (m : ℝ) ^ (2 * d) := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      positivity
    rw [e] at hprod
    have hlt : 8 ^ d * P / (m : ℝ) ^ (2 * d) < N := by rw [div_lt_iff₀ hmpos]; linarith
    linarith
  have hfin : S.Finite := Set.Finite.of_finite_image (Set.toFinite _) hinj
  refine ⟨hfin, ?_⟩
  have hcard : S.ncard ≤ (m * m) ^ d := by
    have := Set.ncard_le_ncard_of_injOn cell (fun _ _ => Set.mem_univ _) hinj Set.finite_univ
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin] at this
    exact this
  have hcardR : (S.ncard : ℝ) ≤ (m : ℝ) ^ (2 * d) := by
    have : (((m * m) ^ d : ℕ) : ℝ) = (m : ℝ) ^ (2 * d) := by push_cast; rw [pow_mul, sq]
    rw [← this]; exact_mod_cast hcard
  have hC0 : 0 ≤ 32 ^ d * P / N := by positivity
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have : m = 1 := by omega
    rw [this, Nat.cast_one, one_pow] at hcardR
    linarith
  · have hmin := Nat.find_min hex (show m - 1 < m by omega)
    have hk1 : 1 ≤ m - 1 := by omega
    have hk : ((m - 1 : ℕ) : ℝ) ^ (2 * d) * N ≤ 8 ^ d * P := by
      by_contra hc
      exact hmin ⟨hk1, lt_of_not_ge hc⟩
    have ek : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [ek] at hk
    have hm2' : (m : ℝ) ≤ 2 * ((m : ℝ) - 1) := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      linarith
    have hpow : (m : ℝ) ^ (2 * d) ≤ 4 ^ d * ((m : ℝ) - 1) ^ (2 * d) := by
      calc (m : ℝ) ^ (2 * d) ≤ (2 * ((m : ℝ) - 1)) ^ (2 * d) :=
            pow_le_pow_left₀ (by positivity) hm2' _
        _ = 4 ^ d * ((m : ℝ) - 1) ^ (2 * d) := by
            rw [mul_pow, pow_mul]; norm_num
    have h32 : (4 : ℝ) ^ d * 8 ^ d = 32 ^ d := by rw [← mul_pow]; norm_num
    have : (m : ℝ) ^ (2 * d) ≤ 32 ^ d * P / N := by
      rw [le_div_iff₀ hN, ← h32]
      have h4 : (0 : ℝ) ≤ 4 ^ d := by positivity
      calc (m : ℝ) ^ (2 * d) * N ≤ 4 ^ d * ((m : ℝ) - 1) ^ (2 * d) * N :=
            mul_le_mul_of_nonneg_right hpow hN.le
        _ = 4 ^ d * (((m : ℝ) - 1) ^ (2 * d) * N) := by ring
        _ ≤ 4 ^ d * (8 ^ d * P) := mul_le_mul_of_nonneg_left hk h4
        _ = 4 ^ d * 8 ^ d * P := by ring
    linarith

theorem prod_norm_rel (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hF : NumberField.IsTotallyReal F) (c : E) :
    ∏ w : InfinitePlace F, w (Algebra.norm F c) = ((|Algebra.norm ℚ c| : ℚ) : ℝ) := by
  have h := InfinitePlace.prod_eq_abs_norm (Algebra.norm F c)
  rw [Algebra.norm_norm] at h
  rw [← h]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [InfinitePlace.mult, if_pos (hF.isReal w), pow_one]

theorem count_ideal_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∃ C : ℝ, ∀ 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, 𝔞 ≠ 0 →
      ∀ T : InfinitePlace F → ℝ, (∀ w, 0 ≤ T w) →
        {c : E | c ∈ 𝔞 ∧ ∀ w, ‖Algebra.norm w.Completion (inclR (F := F) w.Completion c)‖ ≤ T w}.Finite ∧
        ({c : E | c ∈ 𝔞 ∧ ∀ w, ‖Algebra.norm w.Completion (inclR (F := F) w.Completion c)‖ ≤ T w}.ncard : ℝ) ≤
          1 + C * (∏ w, T w) / (FractionalIdeal.absNorm 𝔞 : ℝ) := by
  intro F E _ _ _ _ _ σ hcm
  refine ⟨32 ^ Fintype.card (InfinitePlace F), ?_⟩
  intro 𝔞 h𝔞 T hT
  choose τ hτ using exists_emb_place_norm F E σ hcm
  have hNw : ∀ w c, ‖Algebra.norm w.Completion (inclR (F := F) w.Completion c)‖ = ‖τ w c‖ ^ 2 := by
    intro w c
    rw [GlobalTheory.Doubling.norm_inclR, GlobalTheory.FrobDense.norm_inf, hτ]
  have hN0 : (0 : ℝ) < FractionalIdeal.absNorm 𝔞 := by
    have : FractionalIdeal.absNorm 𝔞 ≠ 0 := by
      rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have h0 : (0 : ℚ) ≤ FractionalIdeal.absNorm 𝔞 := FractionalIdeal.absNorm_nonneg 𝔞
    exact_mod_cast lt_of_le_of_ne h0 (Ne.symm this)
  simp_rw [hNw]
  refine count_sep E (InfinitePlace F) _ (fun c w => τ w c) T _ hN0 hT (fun x hx i => hx.2 i) ?_
  intro x hx y hy hxy
  have hsub : x - y ∈ 𝔞 := Submodule.sub_mem (𝔞 : Submodule (𝓞 E) E) hx.1 hy.1
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have e : ∏ i, ‖τ i x - τ i y‖ ^ 2 = ((|Algebra.norm ℚ (x - y)| : ℚ) : ℝ) := by
    rw [← prod_norm_rel F E hcm.1 (x - y)]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [hτ, map_sub]
  rw [e]
  exact_mod_cast GlobalTheory.absNorm_le_abs_norm_of_mem hsub hne

end GlobalTheory.CountBox
