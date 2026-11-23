import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Bad

section Gen

variable {V H : Type} [MeasurableSpace V] [MeasurableSpace H]
  {μ : Measure V} {ν : Measure H} {q : V → H}

theorem denLE_mono {S T : Set V} {C D : ℝ≥0∞} (hST : S ⊆ T) (hCD : C ≤ D)
    (h : DenLE μ ν q T C) : DenLE μ ν q S D := by
  intro Y hY
  calc μ (S ∩ q ⁻¹' Y) ≤ μ (T ∩ q ⁻¹' Y) := measure_mono (Set.inter_subset_inter_left _ hST)
    _ ≤ C * ν Y := h Y hY
    _ ≤ D * ν Y := by gcongr

theorem denLE_biUnion {ι : Type} (I : Finset ι) (S : ι → Set V) (C : ι → ℝ≥0∞)
    (h : ∀ i ∈ I, DenLE μ ν q (S i) (C i)) :
    DenLE μ ν q (⋃ i ∈ I, S i) (∑ i ∈ I, C i) := by
  intro Y hY
  calc μ ((⋃ i ∈ I, S i) ∩ q ⁻¹' Y) = μ (⋃ i ∈ I, S i ∩ q ⁻¹' Y) := by
        rw [Set.iUnion₂_inter]
    _ ≤ ∑ i ∈ I, μ (S i ∩ q ⁻¹' Y) := measure_biUnion_finset_le I _
    _ ≤ ∑ i ∈ I, C i * ν Y := Finset.sum_le_sum fun i hi => h i hi Y hY
    _ = (∑ i ∈ I, C i) * ν Y := (Finset.sum_mul _ _ _).symm

end Gen

section Grid

def grid (L : ℕ) : Finset ℂ :=
  open Classical in
  ((Finset.Icc (-(L : ℤ)) L) ×ˢ (Finset.Icc (-(L : ℤ)) L)).image
    (fun p : ℤ × ℤ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) / L)

theorem card_grid_le (L : ℕ) : (grid L).card ≤ (2 * L + 1) ^ 2 := by
  classical
  unfold grid
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Int.card_Icc]
  have : ((L : ℤ) + 1 - (-(L : ℤ))).toNat = 2 * L + 1 := by omega
  rw [this, sq]

theorem round_bound (L : ℕ) (u : ℝ) (hu : |u| ≤ 1) :
    round ((L : ℝ) * u) ∈ Finset.Icc (-(L : ℤ)) L ∧ |(L : ℝ) * u - round ((L : ℝ) * u)| ≤ 1 := by
  have h := abs_sub_round ((L : ℝ) * u)
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have h1 := abs_le.1 hu
  have h2 := abs_le.1 h
  have hb1 : (L : ℝ) * u ≤ L := by nlinarith [h1.2]
  have hb2 : -(L : ℝ) ≤ (L : ℝ) * u := by nlinarith [h1.1]
  refine ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, h.trans (by norm_num)⟩
  · have : (-(L : ℝ) - 1) < (round ((L : ℝ) * u) : ℝ) := by linarith [h2.1, h2.2]
    have h3 : (-(L : ℤ) - 1) < round ((L : ℝ) * u) := by exact_mod_cast this
    omega
  · have : (round ((L : ℝ) * u) : ℝ) < (L : ℝ) + 1 := by linarith [h2.1, h2.2]
    have h3 : round ((L : ℝ) * u) < (L : ℤ) + 1 := by exact_mod_cast this
    omega

theorem exists_grid {L : ℕ} (hL : 0 < L) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ∃ g ∈ grid L, ‖z - g‖ ≤ 2 / L := by
  classical
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨hx, hx'⟩ := round_bound L z.re ((Complex.abs_re_le_norm z).trans hz)
  obtain ⟨hy, hy'⟩ := round_bound L z.im ((Complex.abs_im_le_norm z).trans hz)
  set x := round ((L : ℝ) * z.re)
  set y := round ((L : ℝ) * z.im)
  refine ⟨((x : ℂ) + (y : ℂ) * Complex.I) / L, ?_, ?_⟩
  · unfold grid
    exact Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩
  · have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have e : z - ((x : ℂ) + (y : ℂ) * Complex.I) / L
        = (((((L : ℝ) * z.re - x : ℝ) : ℂ)) + (((L : ℝ) * z.im - y : ℝ) : ℂ) * Complex.I) / L := by
      field_simp
      apply Complex.ext <;> simp <;> ring
    rw [e, norm_div, Complex.norm_natCast]
    gcongr
    calc ‖((((L : ℝ) * z.re - x : ℝ) : ℂ)) + (((L : ℝ) * z.im - y : ℝ) : ℂ) * Complex.I‖
        ≤ ‖((((L : ℝ) * z.re - x : ℝ) : ℂ))‖ + ‖(((L : ℝ) * z.im - y : ℝ) : ℂ) * Complex.I‖ :=
          norm_add_le _ _
      _ ≤ 2 := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
          linarith

end Grid

section Shear

variable {K W : Type} [CommRing K] {n M : ℕ}

theorem shearK_self (a : Fin n) (s : Fin n → K) (X : Fin n → Fin M → K) (i : Fin M) :
    shearK a s X a i = X a i + ∑ b, s b * X b i := by
  simp [shearK]

theorem shearK_ne {a b : Fin n} (h : b ≠ a) (s : Fin n → K) (X : Fin n → Fin M → K) :
    shearK a s X b = X b := by
  simp [shearK, h]

theorem shearK_neg_shearK (a : Fin n) (s : Fin n → K) (hs : s a = 0) (X : Fin n → Fin M → K) :
    shearK a (-s) (shearK a s X) = X := by
  funext b i
  by_cases hb : b = a
  · subst hb
    rw [shearK_self, shearK_self]
    have : ∑ c, (-s) c * shearK b s X c i = -∑ c, s c * X c i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : c = b
      · subst hc; simp [hs]
      · rw [shearK_ne hc]; simp
    rw [this]; ring
  · rw [shearK_ne hb, shearK_ne hb]

end Shear

section Cover

variable {K W : Type} [CommRing K] [Fintype W] [DecidableEq W] {n M : ℕ}

def sig (κ : K ≃+* (W → ℂ)) (w : W) (a : Fin n) (t : Fin n → ℂ) : Fin n → K :=
  fun b => if b = a then 0 else κ.symm (Pi.single w (t b))

def rad (R ε : ℝ) (a : Fin n) (w : W) : Fin n → W → ℝ :=
  fun b v => if b = a ∧ v = w then 2 * ε else R

theorem sig_self (κ : K ≃+* (W → ℂ)) (w : W) (a : Fin n) (t : Fin n → ℂ) : sig κ w a t a = 0 := by
  simp [sig]

theorem κ_sig (κ : K ≃+* (W → ℂ)) (w v : W) (a b : Fin n) (t : Fin n → ℂ) :
    κ (sig κ w a t b) v = if b = a then 0 else if v = w then t b else 0 := by
  by_cases hb : b = a
  · simp [sig, hb]
  · by_cases hv : v = w
    · subst hv; simp [sig, hb]
    · simp [sig, hb, hv]

theorem κ_shear (κ : K ≃+* (W → ℂ)) (w v : W) (a : Fin n) (t : Fin n → ℂ)
    (X : Fin n → Fin M → K) (i : Fin M) :
    κ (shearK a (sig κ w a t) X a i) v = κ (X a i) v +
      ∑ b, (if b = a then 0 else if v = w then t b else 0) * κ (X b i) v := by
  rw [shearK_self, map_add, map_sum, Pi.add_apply, Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, Pi.mul_apply, κ_sig]

theorem shear_mem (κ : K ≃+* (W → ℂ)) (w : W) (a : Fin n) (s t : Fin n → ℂ) {R ε L : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (hR : 0 ≤ R) (hLε : 4 * n * R ≤ L * ε) (hsa : s a = 1)
    (hst : ∀ b, ‖s b - t b‖ ≤ 2 / L) {X : Fin n → Fin M → K}
    (hX : X ∈ boxK κ (fun _ _ => R)) (hN : X ∈ nearK κ w s ε) :
    shearK a (sig κ w a t) X ∈ boxK κ (rad R ε a w) := by
  intro b i v
  by_cases hb : b = a
  · subst hb
    by_cases hv : v = w
    · subst hv
      have hr : rad R ε b v b v = 2 * ε := by simp [rad]
      rw [hr, κ_shear]
      have e : κ (X b i) v + ∑ c, (if c = b then 0 else if v = v then t c else 0) * κ (X c i) v
          = ∑ c, s c * κ (X c i) v + ∑ c, (if c = b then 0 else t c - s c) * κ (X c i) v := by
        have h1 : κ (X b i) v = ∑ c, (if c = b then 1 else 0) * κ (X c i) v := by simp
        rw [h1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases hc : c = b
        · subst hc; simp [hsa]
        · simp [hc]; ring
      rw [e]
      have h2 : ‖∑ c, (if c = b then 0 else t c - s c) * κ (X c i) v‖ ≤ ε := by
        calc ‖∑ c, (if c = b then 0 else t c - s c) * κ (X c i) v‖
            ≤ ∑ c, ‖(if c = b then 0 else t c - s c) * κ (X c i) v‖ := norm_sum_le _ _
          _ ≤ ∑ _c : Fin n, 2 / L * R := by
              refine Finset.sum_le_sum fun c _ => ?_
              rw [norm_mul]
              have h3 : ‖(if c = b then 0 else t c - s c : ℂ)‖ ≤ 2 / L := by
                by_cases hc : c = b
                · simp only [hc, if_true, norm_zero]; positivity
                · simp only [hc, if_false]; rw [norm_sub_rev]; exact hst c
              exact mul_le_mul h3 (hX c i v) (norm_nonneg _) (by positivity)
          _ = n * (2 / L * R) := by simp
          _ ≤ ε := by
              have : (n : ℝ) * (2 / L * R) = (2 * n * R) / L := by ring
              rw [this, div_le_iff₀ hL]
              have : 0 ≤ (n : ℝ) * R := by positivity
              nlinarith
      have h4 := hN i
      calc _ ≤ ‖∑ c, s c * κ (X c i) v‖ + ‖∑ c, (if c = b then 0 else t c - s c) * κ (X c i) v‖ :=
            norm_add_le _ _
        _ ≤ 2 * ε := by linarith
    · have hr : rad R ε b w b v = R := by simp [rad, hv]
      rw [hr, κ_shear]
      simpa [hv] using hX b i v
  · have hr : rad R ε a w b v = R := by simp [rad, hb]
    rw [hr, shearK_ne hb]
    exact hX b i v

theorem rad_pos {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (a : Fin n) (w : W) (b : Fin n) (v : W) :
    0 < rad R ε a w b v := by
  unfold rad
  split_ifs <;> positivity

theorem prod_rad_le {R ε : ℝ} (hR : 1 ≤ R) (a : Fin n) (w : W) (m : ℕ) :
    ∏ b, ∏ v, ENNReal.ofReal (rad R ε a w b v) ^ m
      ≤ ENNReal.ofReal (2 * ε) ^ m * (ENNReal.ofReal R ^ m) ^ (n * Fintype.card W) := by
  classical
  have hA : 1 ≤ ENNReal.ofReal R ^ m := one_le_pow₀ (by simpa using ENNReal.one_le_ofReal.2 hR)
  have e : ∏ b, ∏ v, ENNReal.ofReal (rad R ε a w b v) ^ m
      = ∏ p : Fin n × W, Function.update (fun _ => ENNReal.ofReal R ^ m) (a, w)
          (ENNReal.ofReal (2 * ε) ^ m) p := by
    rw [← Fintype.prod_prod_type']
    refine Finset.prod_congr rfl fun p _ => ?_
    obtain ⟨b, v⟩ := p
    by_cases h : b = a ∧ v = w
    · obtain ⟨rfl, rfl⟩ := h
      simp [rad]
    · have h' : (b, v) ≠ (a, w) := fun hh => h (by simpa using hh)
      rw [Function.update_of_ne h']
      simp [rad, h]
  rw [e, Finset.prod_update_of_mem (Finset.mem_univ _), Finset.prod_const]
  gcongr
  refine (Finset.card_le_univ _).trans ?_
  simp

end Cover

section Main

variable {K W : Type} [CommRing K] [Fintype W] {n M : ℕ} {H : Type} [MeasurableSpace H]
  [MeasurableSpace (Fin n → Fin M → K)]

theorem bad_le (κ : K ≃+* (W → ℂ)) (μ : Measure (Fin n → Fin M → K)) (ν : Measure H)
    (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞)
    (hbox : ∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → DenLE μ ν q (boxK κ r)
      (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n))))
    (hshear : ∀ (S : Set (Fin n → Fin M → K)) (C : ℝ≥0∞) (a : Fin n) (s : Fin n → K), s a = 0 →
      DenLE μ ν q S C → DenLE μ ν q (shearK a s '' S) C)
    {R ε : ℝ} (hR : 1 ≤ R) (hε : 0 < ε) {L : ℕ} (hL : 0 < L) (hLε : 4 * n * R ≤ L * ε) :
    DenLE μ ν q (boxK κ (fun _ _ => R) \ goodK κ R ε)
      (((Fintype.card W * n * (2 * L + 1) ^ (2 * n) : ℕ) : ℝ≥0∞) *
        (C₀ * (ENNReal.ofReal (2 * ε) ^ (2 * (M - n)) *
          (ENNReal.ofReal R ^ (2 * (M - n))) ^ (n * Fintype.card W)))) := by
  classical
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  set P : ℝ≥0∞ := C₀ * (ENNReal.ofReal (2 * ε) ^ (2 * (M - n)) *
          (ENNReal.ofReal R ^ (2 * (M - n))) ^ (n * Fintype.card W)) with hP
  let I : Finset (W × Fin n × (Fin n → ℂ)) :=
    Finset.univ ×ˢ (Finset.univ ×ˢ Fintype.piFinset (fun _ : Fin n => grid L))
  let S : W × Fin n × (Fin n → ℂ) → Set (Fin n → Fin M → K) := fun p =>
    shearK p.2.1 (-(sig κ p.1 p.2.1 p.2.2)) '' boxK κ (rad R ε p.2.1 p.1)
  have hS : ∀ p ∈ I, DenLE μ ν q (S p) P := by
    rintro ⟨w, a, t⟩ -
    refine hshear _ _ a _ (by simp [sig_self]) ?_
    refine denLE_mono subset_rfl ?_
      (hbox (rad R ε a w) (rad_pos (by linarith) hε a w))
    rw [hP]
    have h := prod_rad_le (ε := ε) hR a w (2 * (M - n))
    gcongr
  have hcover : boxK κ (fun _ _ => R) \ goodK κ R ε ⊆ ⋃ p ∈ I, S p := by
    rintro X ⟨hX, hg⟩
    have hU : X ∈ ⋃ w : W, ⋃ a : Fin n, ⋃ s ∈ {s : Fin n → ℂ | s a = 1 ∧ ∀ b, ‖s b‖ ≤ 1},
        nearK κ w s ε := by
      by_contra hc
      exact hg ⟨hX, hc⟩
    simp only [Set.mem_iUnion] at hU
    obtain ⟨w, a, s, ⟨hsa, hsb⟩, hN⟩ := hU
    choose t ht hst using fun b => exists_grid hL (s b) (hsb b)
    refine Set.mem_biUnion (x := (w, a, t)) ?_ ?_
    · simp only [I, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ,
        Fintype.mem_piFinset, true_and, Finset.coe_univ, Set.mem_univ]
      exact ht
    · refine ⟨_, shear_mem κ w a s t hε hL' (by linarith) hLε hsa hst hX hN, ?_⟩
      exact shearK_neg_shearK a _ (sig_self κ w a t) X
  refine denLE_mono hcover ?_ (denLE_biUnion I S (fun _ => P) hS)
  have hcard : I.card ≤ Fintype.card W * n * (2 * L + 1) ^ (2 * n) := by
    simp only [I, Finset.card_product, Finset.card_univ, Fintype.card_fin, Fintype.card_piFinset,
      Finset.prod_const]
    rw [mul_assoc]
    refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_)
    calc (grid L).card ^ n ≤ ((2 * L + 1) ^ 2) ^ n := Nat.pow_le_pow_left (card_grid_le L) n
      _ = (2 * L + 1) ^ (2 * n) := (pow_mul _ _ _).symm
  rw [Finset.sum_const, nsmul_eq_mul]
  gcongr

theorem pow_inv_le (T : ℕ) (hT : T ≠ 0) (k m : ℕ) (hm : k < m) :
    (T : ℝ≥0∞) ^ k * ENNReal.ofReal (2 * (1 / (T : ℝ))) ^ m ≤ 2 ^ m * (T : ℝ≥0∞)⁻¹ := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hT
  have e : ENNReal.ofReal (2 * (1 / (T : ℝ))) = 2 * (T : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_mul (by norm_num), one_div, ENNReal.ofReal_inv_of_pos hT',
      ENNReal.ofReal_natCast]
    simp
  obtain ⟨d, rfl⟩ : ∃ d, m = k + (d + 1) := ⟨m - k - 1, by omega⟩
  have h1 : (T : ℝ≥0∞) ^ k * (T : ℝ≥0∞)⁻¹ ^ k = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by exact_mod_cast hT) (ENNReal.natCast_ne_top T),
      one_pow]
  have h2 : (T : ℝ≥0∞)⁻¹ ^ d ≤ 1 := by
    refine pow_le_one₀ (by simp) ?_
    rw [ENNReal.inv_le_one]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hT
  rw [e, mul_pow]
  calc (T : ℝ≥0∞) ^ k * (2 ^ (k + (d + 1)) * (T : ℝ≥0∞)⁻¹ ^ (k + (d + 1)))
      = 2 ^ (k + (d + 1)) * (((T : ℝ≥0∞) ^ k * (T : ℝ≥0∞)⁻¹ ^ k) *
          ((T : ℝ≥0∞)⁻¹ ^ d * (T : ℝ≥0∞)⁻¹)) := by
        rw [pow_add _ k, pow_succ _ d]; ring
    _ ≤ 2 ^ (k + (d + 1)) * (1 * (1 * (T : ℝ≥0∞)⁻¹)) := by
        rw [h1]; gcongr
    _ = _ := by simp

end Main

theorem bad_density : ∀ (K W : Type) [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) (n M : ℕ), 0 < n → 2 * n < M → ∀ (H : Type) [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] (μ : Measure (Fin n → Fin M → K)) (ν : Measure H) (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞), C₀ ≠ ⊤ → (∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)))) → (∀ (S : Set (Fin n → Fin M → K)) (C : ℝ≥0∞) (a : Fin n) (s : Fin n → K), s a = 0 → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q S C → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearK a s '' S) C) → ∀ R : ℝ, 1 ≤ R → ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ ε : ℝ, 0 < ε ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) \ GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK κ R ε) δ := by
  intro K W _ _ κ n M hn hM H _ _ μ ν q C₀ hC₀ hbox hshear R hR δ hδ
  classical
  set m := 2 * (M - n) with hm
  have hkm : 2 * n < m := by omega
  set Rn : ℕ := ⌈R⌉₊ with hRn
  have hRle : R ≤ Rn := Nat.le_ceil R
  have hRn1 : 0 < Rn := Nat.ceil_pos.2 (by linarith)
  set c : ℕ := 8 * n * Rn + 1 with hc
  set D : ℝ≥0∞ := C₀ * (ENNReal.ofReal R ^ m) ^ (n * Fintype.card W) with hD
  set E : ℝ≥0∞ := ((Fintype.card W * n * c ^ (2 * n) : ℕ) : ℝ≥0∞) * (D * 2 ^ m) with hE
  have hDtop : D ≠ ⊤ := ENNReal.mul_ne_top hC₀ (by simp [ENNReal.pow_eq_top_iff])
  have hEtop : E ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.mul_ne_top hDtop (by simp [ENNReal.pow_eq_top_iff]))
  obtain ⟨T, hT⟩ := ENNReal.exists_inv_nat_lt (ENNReal.div_ne_zero.2 ⟨hδ, hEtop⟩)
  have hT0 : T ≠ 0 := by
    rintro rfl
    simp at hT
  have hTpos : 0 < T := Nat.pos_of_ne_zero hT0
  have hT' : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨1 / (T : ℝ), by positivity, ?_⟩
  have hLpos : 0 < 4 * n * Rn * T := by positivity
  have key := bad_le κ μ ν q C₀ hbox hshear (ε := 1 / (T : ℝ)) hR (by positivity)
    (L := 4 * n * Rn * T) hLpos (by
      push_cast
      have : 4 * (n : ℝ) * (Rn : ℝ) * (T : ℝ) * (1 / (T : ℝ)) = 4 * n * Rn := by
        field_simp
      rw [this]
      gcongr)
  refine denLE_mono subset_rfl ?_ key
  have hcount : (2 * (4 * n * Rn * T) + 1) ^ (2 * n) ≤ c ^ (2 * n) * T ^ (2 * n) := by
    rw [← mul_pow]
    refine Nat.pow_le_pow_left ?_ _
    have : 8 * n * Rn * T + 1 ≤ 8 * n * Rn * T + T := by omega
    calc 2 * (4 * n * Rn * T) + 1 = 8 * n * Rn * T + 1 := by ring
      _ ≤ 8 * n * Rn * T + T := this
      _ = c * T := by rw [hc]; ring
  calc ((Fintype.card W * n * (2 * (4 * n * Rn * T) + 1) ^ (2 * n) : ℕ) : ℝ≥0∞) *
        (C₀ * (ENNReal.ofReal (2 * (1 / (T : ℝ))) ^ m * (ENNReal.ofReal R ^ m) ^ (n * Fintype.card W)))
      ≤ ((Fintype.card W * n * (c ^ (2 * n) * T ^ (2 * n)) : ℕ) : ℝ≥0∞) *
        (C₀ * (ENNReal.ofReal (2 * (1 / (T : ℝ))) ^ m * (ENNReal.ofReal R ^ m) ^ (n * Fintype.card W))) := by
        gcongr
    _ = ((Fintype.card W * n * c ^ (2 * n) : ℕ) : ℝ≥0∞) * (D *
          ((T : ℝ≥0∞) ^ (2 * n) * ENNReal.ofReal (2 * (1 / (T : ℝ))) ^ m)) := by
        rw [hD]; push_cast; ring
    _ ≤ ((Fintype.card W * n * c ^ (2 * n) : ℕ) : ℝ≥0∞) * (D * (2 ^ m * (T : ℝ≥0∞)⁻¹)) := by
        have h := pow_inv_le T hT0 (2 * n) m hkm
        gcongr
    _ = E * (T : ℝ≥0∞)⁻¹ := by rw [hE]; ring
    _ ≤ E * (δ / E) := by gcongr
    _ ≤ δ := ENNReal.mul_div_le

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Bad
