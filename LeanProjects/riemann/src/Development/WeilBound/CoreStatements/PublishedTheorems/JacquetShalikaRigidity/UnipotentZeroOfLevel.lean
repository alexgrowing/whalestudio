import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKLt1

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m k : ℕ}

theorem lastRow_mir {p : GA E k} (g : GA E k) (hp : Mir (k - 1) p) : lastRow (p * g) = lastRow g := by
  funext c
  unfold lastRow
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · have hr : ∀ j, p.val i j = (1 : Matrix (Fin k) (Fin k) (Ad E)) i j := fun j => hp i j (Or.inl (by omega))
    rw [Units.val_mul, Matrix.mul_apply]
    simp only [hr, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · rfl

theorem pw_eq (hK5a : TransformsEmbedding) (hk : 1 ≤ k) (hkm : k < m) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ)
    {ι : GA E k →* GA E m} (hι : IsEmb ι) {φ : XB E m} (hφ : Good ψ (m - 1) (φ : GA E m → ℂ)) (φ' : XB E k)
    (g : GA E k) :
    PW ψ (fun g => pT ψ k (m - k) φ (ι g)) φ' g = Wh ψ φ (ι g) * conj (Wh ψ φ' g) := by
  unfold PW Wh
  rw [(hK5a E m k hk hkm ψ hψ ι hι φ hφ).2.2.2.1 g]

omit [IsTotallyComplex E] in
theorem unipotent_zero_of_level {j : ℕ} {u : GA E m} (h : UU j u) : UU 0 u :=
  ⟨h.1, h.2.1, fun _ _ hc => absurd hc (Nat.not_lt_zero _)⟩

omit [IsTotallyComplex E] in
theorem unipotent_zero_mul {u v : GA E m} (hu : UU 0 u) (hv : UU 0 v) : UU 0 (u * v) := by
  refine ⟨fun i c hci => ?_, fun i => ?_, fun _ _ hc => absurd hc (Nat.not_lt_zero _)⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_ge j i with h | h
    · rw [hu.1 i j h, zero_mul]
    · rw [hv.1 j c (lt_of_lt_of_le hci h), mul_zero]
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hu.2.1, hv.2.1, one_mul]
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hu.1 i j h, zero_mul]
      · rw [hv.1 j i h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

omit [IsTotallyComplex E] in
theorem blkU_unipotent_zero (x : UnipotentBlockColumnIndex m k k → Ad E) : UU 0 (blkU x : GA E m) := by
  have hp : ∀ i c : Fin m, (c : ℕ) ≤ i → posM (Subtype.val : UnipotentBlockColumnIndex m k k → Fin m × Fin m) x i c = 0 := by
    intro i c hci
    rw [posM, Matrix.sum_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [Matrix.single_apply_of_ne]
    rintro ⟨e1, e2⟩
    have := t.2
    rw [e1, e2] at this
    omega
  refine ⟨fun i c hci => ?_, fun i => ?_, fun _ _ hc => absurd hc (Nat.not_lt_zero _)⟩
  · change (1 + posM _ x : Matrix (Fin m) (Fin m) (Ad E)) i c = 0
    rw [Matrix.add_apply, hp i c (le_of_lt hci), add_zero, Matrix.one_apply_ne (ne_of_gt hci)]
  · change (1 + posM _ x : Matrix (Fin m) (Fin m) (Ad E)) i i = 1
    rw [Matrix.add_apply, hp i i le_rfl, add_zero, Matrix.one_apply_eq]

theorem sq_real {D C : ℝ} (hD : 0 < D) (M m : ℕ) (hm : 0 < m) :
    (C * min 1 (D ^ (-(m : ℝ)⁻¹)) ^ M) ^ 2 = C ^ 2 * min D D⁻¹ ^ ((M : ℝ) / m) * D ^ (-((M : ℝ) / m)) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  rcases le_or_gt 1 D with h | h
  · have h1 : D ^ (-(m : ℝ)⁻¹) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by simp [hm'.le])
    have h2 : D⁻¹ ≤ D := le_trans (inv_le_one_of_one_le₀ h) h
    have e1 : (D ^ (-(m : ℝ)⁻¹)) ^ (M * 2) = D ^ (-(2 * M / m : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le]
      congr 1
      push_cast
      field_simp
    have e2 : D⁻¹ ^ ((M : ℝ) / m) * D ^ (-((M : ℝ) / m)) = D ^ (-(2 * M / m : ℝ)) := by
      rw [Real.inv_rpow hD.le, ← Real.rpow_neg hD.le, ← Real.rpow_add hD]
      congr 1
      ring
    rw [min_eq_right h1, min_eq_right h2, mul_pow, ← pow_mul, e1, mul_assoc, e2]
  · have h1 : 1 ≤ D ^ (-(m : ℝ)⁻¹) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hD h.le (by simp [hm'.le])
    have h2 : D ≤ D⁻¹ := le_trans h.le (one_le_inv₀ hD |>.2 h.le)
    rw [min_eq_left h1, min_eq_left h2, one_pow, mul_one, mul_assoc, ← Real.rpow_add hD, add_neg_cancel,
      Real.rpow_zero, mul_one]

theorem sq (hK1 : K1) (hK5a : TransformsEmbedding) (hK5b : FourierSeriesColumn) (hK5c : ShortRowsEmbedding) (hk : 1 ≤ k) (hkm : k < m)
    {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {ι : GA E k →* GA E m} (hι : IsEmb ι) {φ : XB E m}
    (hφ : Good ψ (m - 1) (φ : GA E m → ℂ)) {M : ℕ} (hM : 1 ≤ M) (hdec : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * wt M g)
    (hD : ∀ g : GA E k, 0 < Dt g) :
    ∃ a ε C : ℝ, 0 < ε ∧ ∀ g, ∑' ξ : RowT E k k, ‖(fun g => pT ψ k (m - k) φ (ι g)) (ratGL E k (gam ξ) * g)‖ₑ ^ 2 ≤
      ENNReal.ofReal (C * min (Dt g) (Dt g)⁻¹ ^ ε * Dt g ^ (-a)) := by
  obtain ⟨C, hC⟩ := hdec
  obtain ⟨Cc, hCc⟩ := hK5c E m k hk hkm ι hι
  obtain ⟨hgood, heq, -, -, -, hbd⟩ := hK5a E m k hk hkm ψ hψ ι hι φ hφ
  have hm : 1 ≤ m := by omega
  have hdpos := (hK1 E m hm).2.1
  refine ⟨(M : ℝ) / m, (M : ℝ) / m, (max C 0) ^ 2, by positivity, fun g => ?_⟩
  have hB : ∀ x : UnipotentBlockColumnIndex m k k → Ad E, ‖pT ψ (k + 1) (m - (k + 1)) φ (blkU x * ι g)‖ ≤
      max C 0 * min 1 (Dt g ^ (-(m : ℝ)⁻¹)) ^ M := by
    intro x
    refine hbd (k + 1) _ _ (by omega) (by omega) fun v hv => ?_
    have hvu : UU 0 (v * blkU x) := unipotent_zero_mul (unipotent_zero_of_level hv) (blkU_unipotent_zero x)
    have hdm := (hCc g (v * blkU x)).1 hvu
    rw [← mul_assoc]
    refine (hC _).trans ?_
    unfold wt
    refine (mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg (le_min zero_le_one (hdpos _).le) M)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (le_max_right C 0)
    exact pow_le_pow_left₀ (le_min zero_le_one (hdpos _).le) (min_le_min_left 1 hdm) M
  have h := (hK5b E m k hk hkm ψ hψ ι hι _ hgood g).1 _ hB
  simp only [heq]
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  exact sq_real (hD g) M m (by omega)

omit [IsTotallyComplex E] in
theorem law_superdiag {F : Type} [Field F] (A : Matrix (Fin k) (Fin k) F) (hkm : k ≤ m) :
    Whittaker.superdiagSum (embM m A) = Whittaker.superdiagSum A := by
  classical
  set G : ℕ → ℕ → F := fun i j =>
    if h : i < k ∧ j < k then (if j = i + 1 then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0) else 0 with hG
  have e1 : ∀ i j : Fin m, (if (j : ℕ) = i + 1 then embM m A i j else 0) = G i j := by
    intro i j
    simp only [hG, embM, Matrix.of_apply]
    by_cases h : (i : ℕ) < k ∧ (j : ℕ) < k
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h]
      split_ifs with h1
      · rw [Matrix.one_apply_ne]
        intro e; rw [e] at h1; omega
      · rfl
  have e2 : ∀ i j : Fin k, (if (j : ℕ) = i + 1 then A i j else 0) = G i j := by
    intro i j
    simp only [hG]
    rw [dif_pos ⟨i.2, j.2⟩]
  unfold Whittaker.superdiagSum
  simp_rw [e1, e2]
  have h3 : ∀ n, (∑ i : Fin n, ∑ j : Fin n, G i j) = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, G i j := by
    intro n
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin n, G i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Fin.sum_univ_eq_sum_range (G i) n
  rw [h3, h3]
  have h4 : ∀ i, ∑ j ∈ Finset.range m, G i j = ∑ j ∈ Finset.range k, G i j := by
    intro i
    refine (Finset.sum_subset (Finset.range_mono hkm) fun j _ hj => ?_).symm
    simp only [Finset.mem_range] at hj
    simp only [hG]
    rw [dif_neg (by omega)]
  simp_rw [h4]
  refine (Finset.sum_subset (Finset.range_mono hkm) fun i _ hi => ?_).symm
  simp only [Finset.mem_range] at hi
  refine Finset.sum_eq_zero fun j _ => ?_
  simp only [hG]
  rw [dif_neg (by omega)]

theorem law (hG0 : jumpWindows.G0) (hK5e : CornerEmbedding) (hK5a : TransformsEmbedding) (hK7 : K7) (hK8a : LocalHeckeAlgebra) (hk : 1 ≤ k) (hkm : k < m)
    {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)} (hS : ∀ w, w ∉ S → Cond ψ w)
    {ι : GA E k →* GA E m} (hι : IsEmb ι) (α : Off E S → Fin m → ℂˣ) (α' : Off E S → Fin k → ℂˣ)
    {φ : XB E m} (hφ : Good ψ (m - 1) (φ : GA E m → ℂ))
    (hsat : ∀ w : Off E S, SatFn w.1 (Finset.univ.val.map (α w)) φ) {φ' : XB E k}
    (hφ' : Good ψ (k - 1) (φ' : GA E k → ℂ)) (hsat' : ∀ w : Off E S, SatFn w.1 (Finset.univ.val.map (α' w)) φ') :
    LawOff S (PW ψ (fun g => pT ψ k (m - k) φ (ι g)) φ') (aLoc α α') := by
  intro w g hg n hn κ hκ l
  have hK := (hK5e E m k hkm.le).2 ι hι
  obtain ⟨ιw, hιw⟩ := (hK5e E m k hkm.le).1 (w.1.adicCompletion E)
  obtain ⟨hfl, hcl, hun, hint, htor⟩ := hK.2.2.2.2.2.2.2.1 w.1 ιw hιw
  obtain ⟨χ, hχ, hχv, hW⟩ := hK7 E m ψ hψ w.1 (hS w.1 w.2)
  obtain ⟨χ', hχ', hχv', hW'⟩ := hK7 E k ψ hψ w.1 (hS w.1 w.2)
  have hχχ : χ' = χ := DFunLike.ext _ _ fun y => by rw [hχv y, hχv' y]
  rw [hχχ] at hW'
  have hι1 : cLoc w.1 (ι g) = 1 := by rw [hcl, hg, map_one]
  rw [pw_eq hK5a hk hkm hψ hι hφ, pw_eq hK5a hk hkm hψ hι hφ, map_mul ι, hfl, map_mul ιw, map_mul ιw, htor,
    hW (α w) φ hφ (hsat w) (ι g) hι1, hW' (α' w) φ' hφ' (hsat' w) g hg,
    sphericalWhittaker_mul_right hχ.1 _ _ (hint κ hκ), sphericalWhittaker_mul_left hχ.1 _ (hun n hn),
    sphericalWhittaker_mul_right hχ.1 _ _ hκ, sphericalWhittaker_mul_left hχ.1 _ hn]
  have hps : Whittaker.psiN χ (ιw n) = Whittaker.psiN χ n := by
    unfold Whittaker.psiN
    rw [hιw n, law_superdiag _ hkm.le]
  have hnorm : Whittaker.psiN χ n * conj (Whittaker.psiN χ n) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Whittaker.psiN, hχ.2.2]
    simp
  have h8 := ((hK8a E S m k α α' w χ hχ hk hkm.le).2 l).2.1 (Or.inl hkm)
  rw [hps, ← h8]
  simp only [map_mul]
  linear_combination (Wh ψ φ (ι g) * conj (Wh ψ φ' g) *
    sphericalWhittaker χ (α w) (Iwasawa.torusPow _ m (pad m l)) *
    conj (sphericalWhittaker χ (α' w) (Iwasawa.torusPow _ k l))) * hnorm

theorem pos_wh (hP2 : P2) {a : ℕ} (ha : 1 ≤ a) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {φ : XB E a}
    (hφ : Good ψ (a - 1) (φ : GA E a → ℂ)) {n : GA E a} (hn : UU 0 n) (h : GA E a) :
    Wh ψ φ (n * h) = psN ψ n * Wh ψ φ h := by
  obtain ⟨h1, -, h3, h4, -, h6, -⟩ := hP2 E a ψ hψ
  have hpre : Pre ψ 0 (whit ψ (a - 1) (φ : GA E a → ℂ)) := h4 (a - 1) (by omega) _ (h6 _ _ hφ)
  exact h1 0 _ hpre n (h3 n hn) h

theorem pos_unit (hP2 : P2) {a : ℕ} {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (n : GA E a) :
    psN ψ n * conj (psN ψ n) = 1 := by
  obtain ⟨-, h2, -⟩ := hP2 E a ψ hψ
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h2]
  simp

theorem pos (hG0 : jumpWindows.G0) (hP2 : P2) (hD0 : D0) (hC0 : C0) (hK5e : CornerEmbedding) (hK5a : TransformsEmbedding) (hk : 1 ≤ k) (hkm : k < m)
    {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)} {ι : GA E k →* GA E m} (hι : IsEmb ι) {u : ℝ}
    {φ' : XB E k} {U' : Set (GA E k)}
    (hU'p : ∀ c ∈ U', 1 / 2 ≤ Dt c ∧ Dt c ≤ 2 ∧ 0 < (conj (Wh ψ φ' c) * (Dt c : ℂ) ^ ((u : ℂ) * Complex.I)).re)
    {U : Set (GA E m)} (hUU : ∀ g, ι g ∈ U → g ∈ U') {φ : XB E m} (hφ : Good ψ (m - 1) (φ : GA E m → ℂ))
    (hb : ∃ C, C ⊆ U ∧ (∀ c ∈ C, GlobalTheory k c) ∧ Bump ψ S (fun g => InS S g ∧ Mir k g) C (Wh ψ φ))
    (hφ' : Good ψ (k - 1) (φ' : GA E k → ℂ)) (hsph : SphOff S (PW ψ (fun g => pT ψ k (m - k) φ (ι g)) φ')) :
    ∃ a b : ℝ, 0 < a ∧ ∀ g ∈ G0 S, PW ψ (fun g => pT ψ k (m - k) φ (ι g)) φ' g ≠ 0 →
      a ≤ Dt g ∧ Dt g ≤ b ∧
        0 ≤ (PW ψ (fun g => pT ψ k (m - k) φ (ι g)) φ' g * (Dt g : ℂ) ^ ((u : ℂ) * Complex.I)).re := by
  obtain ⟨C, hCU, hCblk, -, -, -, hB⟩ := hb
  obtain ⟨hex, hK⟩ := hK5e E m k hkm.le
  obtain ⟨-, hblk, hsurj, -, -, -, -, hloc, -, huu, hpsn⟩ := hK ι hι
  obtain ⟨-, hmul, -, -, hDuu, -, -, -, -, -, hDint⟩ := hD0 E k
  obtain ⟨-, hmulm, -, -, hDuum, -⟩ := hD0 E m
  have hm1 : 1 ≤ m := by omega
  refine ⟨1 / 2, 2, by norm_num, fun g hg hpw => ?_⟩
  obtain ⟨n, g₀, κ, hn, hg₀, hκi, hκS, hκw, rfl⟩ := (hC0 E k S).2.2.2.1 g hg
  have e1 : PW ψ (fun g => pT ψ k (m - k) φ (ι g)) φ' (n * g₀ * κ) =
      Wh ψ φ (ι g₀) * conj (Wh ψ φ' g₀) := by
    rw [hsph _ κ hκi hκS hκw, pw_eq hK5a hk hkm hψ hι hφ, map_mul, pos_wh hP2 hm1 hψ hφ ((huu n).2 hn),
      pos_wh hP2 hk hψ hφ' hn, hpsn]
    have hc : conj (psN ψ n * Wh ψ φ' g₀) = conj (psN ψ n) * conj (Wh ψ φ' g₀) := map_mul _ _ _
    rw [hc]
    linear_combination (Wh ψ φ (ι g₀) * conj (Wh ψ φ' g₀)) * pos_unit hP2 hψ n
  have hDg : Dt (n * g₀ * κ) = Dt g₀ := by
    rw [hmul, hmul, hDuu 0 n hn, hDint κ hκi hκw]; ring
  rw [e1] at hpw ⊢
  rw [hDg]
  have hIn : InS S (ι g₀) := fun w hw => by
    obtain ⟨ιw, hιw⟩ := hex (w.adicCompletion E)
    rw [(hloc w ιw hιw).2.1 g₀, hg₀ w hw, map_one]
  have hMir : Mir k (ι g₀) := fun i c h => hblk g₀ i c (h.imp id fun h => h.le)
  obtain ⟨n', c, hcC, t, hn', -, hgc, ht, hWt⟩ := hB (ι g₀) ⟨hIn, hMir⟩ (left_ne_zero_of_mul hpw)
  obtain ⟨c₀, rfl⟩ := hsurj c (hCblk c hcC)
  have hc₀ : c₀ ∈ U' := hUU c₀ (hCU hcC)
  obtain ⟨n₀, hn₀d⟩ : ∃ n₀, n₀ = g₀ * c₀⁻¹ := ⟨_, rfl⟩
  have hιn : ι n₀ = n' := by rw [hn₀d, map_mul, map_inv, hgc, mul_inv_cancel_right]
  have hn₀ : UU 0 n₀ := (huu n₀).1 (hιn ▸ hn')
  have hg₀eq : g₀ = n₀ * c₀ := by rw [hn₀d, inv_mul_cancel_right]
  have hDt : Dt g₀ = Dt c₀ := by rw [hg₀eq, hmul, hDuu 0 n₀ hn₀, one_mul]
  obtain ⟨hlo, hhi, hre⟩ := hU'p c₀ hc₀
  refine ⟨hDt ▸ hlo, hDt ▸ hhi, ?_⟩
  have hval : Wh ψ φ (ι g₀) * conj (Wh ψ φ' g₀) = (t : ℂ) * conj (Wh ψ φ' c₀) := by
    rw [hWt, ← hιn, hpsn, hg₀eq, pos_wh hP2 hk hψ hφ' hn₀]
    have hc : conj (psN ψ n₀ * Wh ψ φ' c₀) = conj (psN ψ n₀) * conj (Wh ψ φ' c₀) := map_mul _ _ _
    rw [hc]
    linear_combination ((t : ℂ) * conj (Wh ψ φ' c₀)) * pos_unit hP2 hψ n₀
  rw [hval, hDt, mul_assoc, Complex.re_ofReal_mul]
  exact mul_nonneg ht hre.le

end PKLt1

theorem kernel_less_first_of : jumpWindows.G0 → jumpWindows.G5 → D0 → P2 → C0 → K1 → CornerEmbedding → TransformsEmbedding → FourierSeriesColumn → ShortRowsEmbedding → K6 → K7 → K8 → LocalHeckeAlgebra → KU → KLt1 := by
  intro hG0 hG5 hD0 hP2 hC0 hK1 hK5e hK5a hK5b hK5c hK6 hK7 hK8 hK8a hKU
  intro E _ _ _ m k hk hkm ψ hψ S hS ι hι α α' u φ' hφ'
  obtain ⟨U', hU', hU'p⟩ := hKU E k ψ hψ φ' u hφ'.good hφ'.one
  obtain ⟨-, hK⟩ := hK5e E m k hkm.le
  obtain ⟨U, hU, hUU⟩ := (hK ι hι).2.2.2.2.1 U' hU'
  refine ⟨U, hU, fun M hM φ hφ => ?_⟩
  have hA := hK5a E m k hk hkm ψ hψ ι hι φ hφ.good
  have hsph : SphOff S (PW ψ (fun g => pT ψ k (m - k) φ (ι g)) φ') := by
    intro g κ hκi hκS hκw
    obtain ⟨hex, -, hinf, -, -⟩ := (hK ι hι).2.2.2.2.2.2
    obtain ⟨-, -, -, -, -, -, -, hloc, -, -, -⟩ := hK ι hι
    rw [PKLt1.pw_eq hK5a hk hkm hψ hι hφ.good, PKLt1.pw_eq hK5a hk hkm hψ hι hφ.good, map_mul,
      (hK8 E k ψ hψ S hS α' φ' hφ'.good hφ'.sat).2.1 g κ hκi hκS hκw]
    congr 1
    refine (hK8 E m ψ hψ S hS α φ hφ.good hφ.sat).2.1 (ι g) (ι κ) ?_ (fun w hw => ?_) (fun w => ?_)
    · exact (hK ι hι).2.2.2.2.2.2.2.2.1 κ hκi
    · obtain ⟨ιw, hιw⟩ := (hK5e E m k hkm.le).1 (w.adicCompletion E)
      rw [(hloc w ιw hιw).2.1 κ, hκS w hw, map_one]
    · obtain ⟨ιw, hιw⟩ := (hK5e E m k hkm.le).1 (w.adicCompletion E)
      rw [(hloc w ιw hιw).2.1 κ]
      exact (hloc w ιw hιw).2.2.2.1 _ (hκw w)
  exact
    { pre := hA.2.2.1
      supp := by
        obtain ⟨C, hC, hCp⟩ := hK6 E m k hk hkm ψ hψ S hS ι hι α M U φ hφ
        refine ⟨C, hC, fun g hg => ?_⟩
        obtain ⟨p, hp, hw⟩ := hA.2.2.2.2.1 g hg
        rw [← PKLt1.lastRow_mir g hp]
        exact hCp _ hw
      sq := PKLt1.sq hK1 hK5a hK5b hK5c hk hkm hψ hι hφ.good hM hφ.dec (hD0 E k).1
      good := hφ'.good
      inv := hφ'.inv
      dec := hφ'.dec
      law := PKLt1.law hG0 hK5e hK5a hK7 hK8a hk hkm hψ hS hι α α' hφ.good hφ.sat hφ'.good hφ'.sat
      sph := hsph
      one := by
        obtain ⟨C, -, -, -, -, ⟨t, ht, hW⟩, -⟩ := hφ.bump
        rw [PKLt1.pw_eq hK5a hk hkm hψ hι hφ.good, map_one, hW, hφ'.one]
        simp [ht]
      pos := PKLt1.pos hG0 hP2 hD0 hC0 hK5e hK5a hk hkm hψ hι hU'p hUU hφ.good hφ.bump hφ'.good hsph }

end PositivityTheory.AdelicQuotientData

end
