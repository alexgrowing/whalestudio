import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc

noncomputable section

open Finset GroundTheory.Automorphic GroundTheory.Automorphic.Spherical
open scoped ComplexConjugate

namespace PositivityTheory.RgJS

namespace LocalizationEmbedding

def cU (z : ℂˣ) : ℂˣ := Units.map (starRingEnd ℂ).toMonoidHom z

theorem cU_coe (z : ℂˣ) : ((cU z : ℂˣ) : ℂ) = conj (z : ℂ) := rfl

theorem hN_conj {m : ℕ} (p : ℕ) (α : Fin m → ℂ) : hN p (fun i => conj (α i)) = conj (hN p α) := by
  simp [hN, map_sum, map_prod, map_pow]

theorem hZ_conj {m : ℕ} (z : ℤ) (α : Fin m → ℂ) : hZ z (fun i => conj (α i)) = conj (hZ z α) := by
  unfold hZ
  split_ifs
  · simp
  · exact hN_conj _ _

theorem jt_conj {m m' : ℕ} (α : Fin m → ℂ) (l : Fin m' → ℕ) : jt (fun i => conj (α i)) l = conj (jt α l) := by
  unfold jt
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [hZ_conj]

theorem hN_zero {m : ℕ} (α : Fin m → ℂ) : hN 0 α = 1 := by
  simp [hN, Finset.Nat.antidiagonalTuple_zero_right]

theorem jt_zero {m m' : ℕ} (α : Fin m → ℂ) : jt α (0 : Fin m' → ℕ) = 1 := by
  unfold jt
  rw [Matrix.det_of_lowerTriangular]
  · simp [hZ, hN_zero]
  · intro i j hij
    have h' : i < j := hij
    have h'' : (i : ℕ) < j := h'
    simp only [Matrix.of_apply, Pi.zero_apply, Nat.cast_zero, zero_sub, hZ]
    rw [if_pos (by omega)]

theorem schur_conj (hS : SchurJT) {n : ℕ} (z : Fin n → ℂˣ) (L : Fin n → ℕ) :
    evalAt (fun i => cU (z i)) (schur fun i => (L i : ℤ)) = conj (evalAt z (schur fun i => (L i : ℤ))) := by
  rw [hS, hS]
  exact jt_conj _ _

theorem padN_self {m : ℕ} (L : Fin m → ℕ) : padN m L = L := by
  funext i
  simp [padN]

theorem padN_sum {m k : ℕ} (hk : k ≤ m) (l : Fin k → ℕ) : ∑ i, padN m l i = ∑ j, l j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Fin.sum_univ_add]
  simp [padN]

theorem padN_antitone {m k : ℕ} (hk : k ≤ m) {l : Fin k → ℕ} (hl : Antitone l) : Antitone (padN m l) := by
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  simp only [padN]
  by_cases hj : (j : ℕ) < k
  · have hi : (i : ℕ) < k := lt_of_le_of_lt hij' hj
    rw [dif_pos hj, dif_pos hi]
    exact hl (show (⟨i, hi⟩ : Fin k) ≤ ⟨j, hj⟩ from hij')
  · rw [dif_neg hj]
    exact Nat.zero_le _

theorem padN_inj {m k : ℕ} (hk : k ≤ m) {l l' : Fin k → ℕ} (h : padN m l = padN m l') : l = l' := by
  funext j
  have := congrFun h ⟨j, lt_of_lt_of_le j.isLt hk⟩
  simpa [padN] using this

def padS {m k : ℕ} (hk : k ≤ m) (l : {l : Fin k → ℕ // Antitone l}) : {l : Fin m → ℕ // Antitone l} :=
  ⟨padN m l.1, padN_antitone hk l.2⟩

theorem padS_inj {m k : ℕ} (hk : k ≤ m) : Function.Injective (padS hk) := fun l l' h =>
  Subtype.ext (padN_inj hk (congrArg Subtype.val h))

def emb {k : ℕ} (l : {l : Fin k → ℕ // Antitone l}) : Fin k → ℤ := fun i => (l.1 i : ℤ)

theorem emb_inj {k : ℕ} : Function.Injective (emb (k := k)) := fun l l' h => by
  apply Subtype.ext
  funext i
  have := congrFun h i
  simpa [emb] using this

theorem mem_range_emb {k : ℕ} {l : Fin k → ℤ} (h : Antitone l ∧ ∀ i, 0 ≤ l i) : l ∈ Set.range (emb (k := k)) := by
  refine ⟨⟨fun i => (l i).toNat, fun i j hij => Int.toNat_le_toNat (h.1 hij)⟩, ?_⟩
  funext i
  simp [emb, Int.toNat_of_nonneg (h.2 i)]

theorem loc_off {m k q : ℕ} (α : Fin m → ℂˣ) (β : Fin k → ℂˣ) (s : ℂ) {l : Fin k → ℤ}
    (hl : l ∉ Set.range (emb (k := k))) : loc q α β s l = 0 := by
  unfold loc
  rw [if_neg fun h => hl (mem_range_emb h)]

theorem pad_emb {m k : ℕ} (l : {l : Fin k → ℕ // Antitone l}) : pad m (emb l) = fun i => (padN m l.1 i : ℤ) := by
  funext i
  by_cases h : (i : ℕ) < k <;> simp [pad, padN, emb, h]

theorem loc_emb (hS : SchurJT) {m k q : ℕ} (α : Fin m → ℂˣ) (β : Fin k → ℂˣ) (s : ℂ)
    (l : {l : Fin k → ℕ // Antitone l}) :
    loc q α β s (emb l) = evalAt α (schur fun i => (padN m l.1 i : ℤ)) *
      evalAt (fun j => cU (β j)) (schur fun j => (l.1 j : ℤ)) * ((q : ℂ) ^ (-s)) ^ (∑ j, l.1 j) := by
  have hcond : Antitone (emb l) ∧ ∀ i, 0 ≤ emb l i :=
    ⟨fun i j hij => by simp only [emb]; exact_mod_cast l.2 hij, fun i => by simp [emb]⟩
  unfold loc
  rw [if_pos hcond, pad_emb, schur_conj hS]
  congr 1
  have hs : (∑ i, emb l i : ℤ) = ((∑ j, l.1 j : ℕ) : ℤ) := by simp [emb]
  rw [hs, Int.cast_natCast, mul_comm, Complex.cpow_nat_mul]

theorem norm_X {q : ℕ} (hq : 2 ≤ q) (s : ℂ) : ‖(q : ℂ) ^ (-s)‖ = (q : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

theorem qx {q : ℕ} (hq : 2 ≤ q) (s : ℂ) :
    (q : ℝ) ^ (-s.re) * Real.sqrt q * Real.sqrt q = (q : ℝ) ^ (1 - s.re) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rw [mul_assoc, Real.mul_self_sqrt hq0.le, show 1 - s.re = -s.re + 1 by ring, Real.rpow_add_one hq0.ne']

theorem qx_lt {q : ℕ} (hq : 2 ≤ q) {s : ℂ} (hs : 1 < s.re) : (q : ℝ) ^ (1 - s.re) < 1 := by
  have h1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)

theorem diag (hC : Cauchy) (hS : SchurJT) {n q : ℕ} (hq : 2 ≤ q) {s : ℂ} (hs : 1 < s.re) (z : Fin n → ℂˣ)
    (hz : ∀ i, ‖(z i : ℂ)‖ ≤ Real.sqrt q) :
    HasSum (fun L : {l : Fin n → ℕ // Antitone l} => ‖evalAt z (schur fun i => (L.1 i : ℤ))‖ ^ 2 *
      ((q : ℝ) ^ (-s.re)) ^ (∑ i, L.1 i)) (‖∏ a, ∏ b, (1 - (z a : ℂ) * conj (z b : ℂ) * (((q : ℝ) ^ (-s.re) : ℝ) : ℂ))⁻¹‖) := by
  set x : ℝ := (q : ℝ) ^ (-s.re) with hxdef
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcond : ‖((x : ℝ) : ℂ)‖ * Real.sqrt q * Real.sqrt q < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hx0, hxdef, qx hq s]
    exact qx_lt hq hs
  have hβ : ∀ j, ‖((cU (z j) : ℂˣ) : ℂ)‖ ≤ Real.sqrt q := fun j => by
    rw [cU_coe, Complex.norm_conj]
    exact hz j
  have h := (hC n n le_rfl z (fun j => cU (z j)) (x : ℂ) (Real.sqrt q) (Real.sqrt q) hz hβ hcond).2
  set P : ℂ := ∏ a, ∏ b, (1 - (z a : ℂ) * conj (z b : ℂ) * (x : ℂ))⁻¹ with hP
  have h' : HasSum (fun L : {l : Fin n → ℕ // Antitone l} =>
      (((‖evalAt z (schur fun i => (L.1 i : ℤ))‖ ^ 2 * x ^ (∑ i, L.1 i) : ℝ)) : ℂ)) P := by
    convert h using 1
    · funext L
      rw [padN_self, schur_conj hS, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    · simp only [hP, cU_coe]
  have hre := ((Complex.hasSum_iff _ _).mp h').1
  have him := ((Complex.hasSum_iff _ _).mp h').2
  simp only [Complex.ofReal_re, Complex.ofReal_im] at hre him
  have hPim : P.im = 0 := (hasSum_zero.unique him).symm
  have hPre : 0 ≤ P.re := hre.nonneg (fun L => by positivity)
  have hPe : P = (P.re : ℂ) := Complex.ext (by simp) (by simp [hPim])
  have hnorm : ‖P‖ = P.re := by
    calc ‖P‖ = ‖(P.re : ℂ)‖ := congrArg norm hPe
      _ = P.re := by rw [Complex.norm_real, Real.norm_of_nonneg hPre]
  rw [hnorm]
  exact hre

theorem diag_le {n q : ℕ} (hq : 2 ≤ q) {s : ℂ} (hs : 1 < s.re) (z : Fin n → ℂˣ) (hz : ∀ i, ‖(z i : ℂ)‖ ≤ Real.sqrt q) :
    ‖∏ a, ∏ b, (1 - (z a : ℂ) * conj (z b : ℂ) * (((q : ℝ) ^ (-s.re) : ℝ) : ℂ))⁻¹‖ ≤
      ((1 - (q : ℝ) ^ (1 - s.re))⁻¹) ^ (n * n) := by
  have hx0 : (0 : ℝ) ≤ (q : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hc : (q : ℝ) ^ (1 - s.re) < 1 := qx_lt hq hs
  have hw : ∀ a b, ‖(z a : ℂ) * conj (z b : ℂ) * (((q : ℝ) ^ (-s.re) : ℝ) : ℂ)‖ ≤ (q : ℝ) ^ (1 - s.re) := by
    intro a b
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hx0, ← qx hq s]
    calc ‖(z a : ℂ)‖ * ‖(z b : ℂ)‖ * (q : ℝ) ^ (-s.re)
        ≤ Real.sqrt q * Real.sqrt q * (q : ℝ) ^ (-s.re) := by
          gcongr
          · exact hz a
          · exact hz b
      _ = (q : ℝ) ^ (-s.re) * Real.sqrt q * Real.sqrt q := by ring
  have hfac : ∀ a b, ‖(1 - (z a : ℂ) * conj (z b : ℂ) * (((q : ℝ) ^ (-s.re) : ℝ) : ℂ))⁻¹‖ ≤
      (1 - (q : ℝ) ^ (1 - s.re))⁻¹ := by
    intro a b
    rw [norm_inv]
    apply inv_anti₀ (by linarith)
    have h1 := norm_sub_norm_le (1 : ℂ) ((z a : ℂ) * conj (z b : ℂ) * (((q : ℝ) ^ (-s.re) : ℝ) : ℂ))
    rw [norm_one] at h1
    linarith [hw a b]
  rw [norm_prod]
  calc ∏ a, ‖∏ b, (1 - (z a : ℂ) * conj (z b : ℂ) * (((q : ℝ) ^ (-s.re) : ℝ) : ℂ))⁻¹‖
      ≤ ∏ _a : Fin n, ((1 - (q : ℝ) ^ (1 - s.re))⁻¹) ^ n := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro a _
        rw [norm_prod]
        calc ∏ b, ‖(1 - (z a : ℂ) * conj (z b : ℂ) * (((q : ℝ) ^ (-s.re) : ℝ) : ℂ))⁻¹‖
            ≤ ∏ _b : Fin n, (1 - (q : ℝ) ^ (1 - s.re))⁻¹ :=
              Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun b _ => hfac a b)
          _ = ((1 - (q : ℝ) ^ (1 - s.re))⁻¹) ^ n := by simp
    _ = ((1 - (q : ℝ) ^ (1 - s.re))⁻¹) ^ (n * n) := by simp [pow_mul]

end LocalizationEmbedding

open LocalizationEmbedding in
theorem cauchy_local_of_cauchy : Cauchy → SchurJT → JTPad → CauchyLoc := by
  intro hC hS _ m k q α β s hkm hq hα hβ hs
  have hβ' : ∀ j, ‖((cU (β j) : ℂˣ) : ℂ)‖ ≤ Real.sqrt q := fun j => by
    rw [cU_coe, Complex.norm_conj]
    exact hβ j
  have hcond : ‖(q : ℂ) ^ (-s)‖ * Real.sqrt q * Real.sqrt q < 1 := by
    rw [norm_X hq, qx hq s]
    exact qx_lt hq hs
  obtain ⟨hsumm, hsum⟩ := hC m k hkm α (fun j => cU (β j)) ((q : ℂ) ^ (-s)) _ _ hα hβ' hcond
  have hsumm' : Summable (fun l : {l : Fin k → ℕ // Antitone l} => ‖loc q α β s (emb l)‖) := by
    simpa only [loc_emb hS] using hsumm
  have hsum' : HasSum (fun l : {l : Fin k → ℕ // Antitone l} => loc q α β s (emb l))
      (∏ a : Fin m, ∏ b : Fin k, (1 - (α a : ℂ) * conj (β b : ℂ) * (q : ℂ) ^ (-s))⁻¹) := by
    simpa only [loc_emb hS, cU_coe] using hsum
  have hoff : ∀ l ∉ Set.range (emb (k := k)), loc q α β s l = 0 := fun l hl => loc_off α β s hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h0 : (0 : Fin k → ℤ) = emb (⟨0, antitone_const⟩ : {l : Fin k → ℕ // Antitone l}) := by
      funext i
      simp [emb]
    rw [h0, loc_emb hS, hS, hS]
    have hp : padN m (0 : Fin k → ℕ) = 0 := by
      funext i
      simp [padN]
    simp [hp, jt_zero]
  · exact (emb_inj.hasSum_iff hoff).mp hsum'
  · exact (emb_inj.summable_iff (f := fun l => ‖loc q α β s l‖) (fun l hl => by simp [hoff l hl])).mp hsumm'
  · have hsupp : Function.support (fun l => ‖loc q α β s l‖) ⊆ Set.range (emb (k := k)) := by
      intro l hl
      by_contra h
      exact hl (by simp [hoff l h])
    rw [← emb_inj.tsum_eq hsupp]
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (q : ℝ) ^ (-s.re) := ⟨_, rfl⟩
    have hx0 : 0 ≤ x := hx ▸ Real.rpow_nonneg (Nat.cast_nonneg _) _
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (1 - (q : ℝ) ^ (1 - s.re))⁻¹ := ⟨_, rfl⟩
    have hr0 : 0 ≤ (q : ℝ) ^ (1 - s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hlt := qx_lt hq hs
    have hc1 : 1 ≤ c := by
      rw [hc]
      exact (one_le_inv₀ (by linarith)).mpr (by linarith)
    have hw := diag hC hS hq hs α hα
    have hv := diag hC hS hq hs β hβ
    have hwle := diag_le hq hs α hα
    have hvle := diag_le hq hs β hβ
    rw [← hx] at hw hwle hv hvle
    rw [← hc] at hwle hvle
    have hwS := hw.summable.comp_injective (padS_inj hkm)
    have hwle' := tsum_comp_le_tsum_of_inj hw.summable (fun L => by positivity) (padS_inj hkm)
    have hpt : ∀ l : {l : Fin k → ℕ // Antitone l}, ‖loc q α β s (emb l)‖ ≤
        (‖evalAt α (schur fun i => ((padS hkm l).1 i : ℤ))‖ ^ 2 * x ^ (∑ i, (padS hkm l).1 i) +
          ‖evalAt β (schur fun i => (l.1 i : ℤ))‖ ^ 2 * x ^ (∑ i, l.1 i)) / 2 := by
      intro l
      rw [loc_emb hS, schur_conj hS, norm_mul, norm_mul, Complex.norm_conj, norm_pow, norm_X hq, ← hx]
      simp only [padS, padN_sum hkm]
      have := mul_nonneg (sq_nonneg (‖evalAt α (schur fun i => (padN m l.1 i : ℤ))‖ -
        ‖evalAt β (schur fun j => (l.1 j : ℤ))‖)) (pow_nonneg hx0 (∑ j, l.1 j))
      nlinarith [this]
    have A := hw.tsum_eq
    have B := hv.tsum_eq
    rw [← A] at hwle
    rw [← B] at hvle
    have hkk : c ^ (k * k) ≤ c ^ (m * m) := pow_le_pow_right₀ hc1 (Nat.mul_le_mul hkm hkm)
    rw [← hc]
    calc ∑' l, ‖loc q α β s (emb l)‖
        ≤ ∑' l : {l : Fin k → ℕ // Antitone l},
            (‖evalAt α (schur fun i => ((padS hkm l).1 i : ℤ))‖ ^ 2 * x ^ (∑ i, (padS hkm l).1 i) +
              ‖evalAt β (schur fun i => (l.1 i : ℤ))‖ ^ 2 * x ^ (∑ i, l.1 i)) / 2 :=
          Summable.tsum_le_tsum hpt hsumm' ((hwS.add hv.summable).div_const 2)
      _ = ((∑' l, ‖evalAt α (schur fun i => ((padS hkm l).1 i : ℤ))‖ ^ 2 * x ^ (∑ i, (padS hkm l).1 i)) +
            ∑' l : {l : Fin k → ℕ // Antitone l}, ‖evalAt β (schur fun i => (l.1 i : ℤ))‖ ^ 2 * x ^ (∑ i, l.1 i)) / 2 := by
          rw [tsum_div_const]
          congr 1
          exact Summable.tsum_add hwS hv.summable
      _ ≤ c ^ (m * m) := by
          have h1 : (∑' l : {l : Fin k → ℕ // Antitone l},
              ‖evalAt α (schur fun i => ((padS hkm l).1 i : ℤ))‖ ^ 2 * x ^ (∑ i, (padS hkm l).1 i)) ≤
              ∑' L : {l : Fin m → ℕ // Antitone l}, ‖evalAt α (schur fun i => (L.1 i : ℤ))‖ ^ 2 * x ^ (∑ i, L.1 i) :=
            hwle'
          linarith [hwle, hvle, hkk, h1]

end PositivityTheory.RgJS
