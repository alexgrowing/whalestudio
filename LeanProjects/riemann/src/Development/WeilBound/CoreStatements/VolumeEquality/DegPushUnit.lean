import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly

noncomputable section

namespace SheetDecomposition

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

namespace UnitZ

def locSub {S L : Type} [CommRing S] [Field L] (φ : S →+* L) (W : Ideal S) [hW : W.IsPrime] : Subring L where
  carrier := {x | ∃ a s, s ∉ W ∧ x * φ s = φ a}
  mul_mem' := by
    rintro x y ⟨a, s, hs, h⟩ ⟨b, t, ht, h'⟩
    exact ⟨a * b, s * t, fun e => (hW.mem_or_mem e).elim hs ht, by rw [map_mul, map_mul, ← h, ← h']; ring⟩
  one_mem' := ⟨1, 1, (Ideal.ne_top_iff_one W).1 hW.ne_top, by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, h⟩ ⟨b, t, ht, h'⟩
    exact ⟨a * t + b * s, s * t, fun e => (hW.mem_or_mem e).elim hs ht, by
      rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']; ring⟩
  zero_mem' := ⟨0, 1, (Ideal.ne_top_iff_one W).1 hW.ne_top, by simp⟩
  neg_mem' := by
    rintro x ⟨a, s, hs, h⟩
    exact ⟨-a, s, hs, by rw [map_neg, ← h]; ring⟩

private theorem isIntegral_of_mem_all_valuationSubrings {L : Type} [Field L] (A : Subring L) (x : L)
    (h : ∀ V : ValuationSubring L, A ≤ V.toSubring → x ∈ V) : IsIntegral A x := by
  obtain rfl | hx0 := eq_or_ne x 0
  · exact isIntegral_zero
  have hxi : x⁻¹ ≠ 0 := inv_ne_zero hx0
  letI : Invertible x⁻¹ := invertibleOfNonzero hxi
  let B := Algebra.adjoin A {x⁻¹}
  let xinv : B.toSubring := ⟨x⁻¹, Algebra.subset_adjoin rfl⟩
  by_contra hni
  have hne : Ideal.span {xinv} ≠ ⊤ := by
    intro eq
    apply hni
    obtain ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top
      (x⁻¹) (⊥ : Ideal A) bot_ne_top (top_unique <| eq.ge.trans le_add_self)
    refine ⟨p, by simpa [Polynomial.Monic, sub_eq_zero] using hp, ?_⟩
    simpa [Polynomial.aeval_def] using hpx
  obtain ⟨V, hAV, hV⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  have h1 : x⁻¹ ∈ V.nonunits := hV ⟨xinv, Ideal.subset_span rfl, rfl⟩
  have hBV : A ≤ V.toSubring := fun a ha => hAV (B.algebraMap_mem ⟨a, ha⟩)
  exact ((V.inv_mem_nonunits_iff.mp h1).resolve_left hx0) (h V hBV)

theorem exists_rel {S L : Type} [CommRing S] [Field L] (φ : S →+* L) (W : Ideal S) [hW : W.IsPrime]
    (hk : ∀ s, s ∉ W → φ s ≠ 0) (f g : S) (hg : φ g ≠ 0)
    (h : ∀ V : ValuationSubring L, (∀ a, φ a ∈ V) → (∀ s, s ∉ W → (φ s)⁻¹ ∈ V) → φ f / φ g ∈ V) :
    ∃ N : ℕ, ∀ m : ℕ, ∃ s r, s ∉ W ∧ φ (s * (g ^ N * f ^ m)) = φ (r * g ^ m) := by
  classical
  set A := locSub φ W with hA
  have h1W : (1 : S) ∉ W := (Ideal.ne_top_iff_one W).1 hW.ne_top
  have himg : ∀ a, φ a ∈ A := fun a => ⟨a, 1, h1W, by simp⟩
  set x := φ f / φ g with hx
  have hint : IsIntegral A x := isIntegral_of_mem_all_valuationSubrings A x fun V hV =>
    h V (fun a => hV (himg a)) fun s hs => hV ⟨1, s, hs, by rw [map_one]; exact inv_mul_cancel₀ (hk s hs)⟩
  obtain ⟨p, hpm, hpx⟩ := hint
  have hpx' : Polynomial.aeval x p = 0 := by rwa [Polynomial.aeval_def]
  set n := p.natDegree with hn
  have hp1 : p ≠ 1 := by
    rintro rfl
    simp at hpx'
  have key : ∀ m : ℕ, φ g ^ n * x ^ m ∈ A := by
    intro m
    let q : Polynomial A := Polynomial.X ^ m
    have hq := Polynomial.modByMonic_add_div q p
    have hev : x ^ m = Polynomial.aeval x (q %ₘ p) := by
      have := congrArg (Polynomial.aeval x) hq
      simp only [map_add, map_mul, hpx', zero_mul, add_zero] at this
      rw [this]
      simp [q]
    have hdeg : (q %ₘ p).natDegree < n := Polynomial.natDegree_modByMonic_lt _ hpm hp1
    rw [hev, Polynomial.aeval_eq_sum_range, Finset.mul_sum]
    refine sum_mem fun i hi => ?_
    have hi' : i < n := lt_of_le_of_lt (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hdeg
    rw [Algebra.smul_def, mul_left_comm]
    refine A.mul_mem (by exact ((q %ₘ p).coeff i).2) ?_
    have hrw : φ g ^ n * x ^ i = φ (g ^ (n - i) * f ^ i) := by
      have hni : n = (n - i) + i := by omega
      rw [map_mul, map_pow, map_pow, hx, div_pow]
      conv_lhs => rw [hni, pow_add]
      field_simp
    rw [hrw]
    exact himg _
  refine ⟨n, fun m => ?_⟩
  obtain ⟨a, s, hs, e⟩ := key m
  refine ⟨s, a, hs, ?_⟩
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, ← e, hx, div_pow]
  field_simp

section Div

variable {k : Type} [Field k] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]

omit [Fintype K] [∀ b, Fintype (ι b)] in
theorem divCycle_nonneg (P : Ideal (MRing ι k)) (f : MRing ι k) (W : Ideal (MRing ι k)) : 0 ≤ divCycle P f W := by
  unfold divCycle
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

theorem divCycle_pow (P : Ideal (MRing ι k)) (hP : P.IsPrime) (f : MRing ι k) (hf : f ∉ P) (W : Ideal (MRing ι k)) (m : ℕ) :
    divCycle P (f ^ m) W = m * divCycle P f W := by
  induction m with
  | zero => simp [divCycle_one]
  | succ m ih =>
    rw [pow_succ, DivCycleMul.proof k K ι P _ _ hP (fun h => hf (hP.mem_of_pow_mem _ h)) hf, Pi.add_apply, ih]
    push_cast; ring

theorem divCycle_le (P : Ideal (MRing ι k)) (hP : P.IsPrime) (f g : MRing ι k) (hf : f ∉ P) (hg : g ∉ P)
    (W : Ideal (MRing ι k)) (hW : W.IsPrime) (hPW : P ≤ W) (N : ℕ)
    (h : ∀ m : ℕ, ∃ s r, s ∉ W ∧ s * (g ^ N * f ^ m) - r * g ^ m ∈ P) : divCycle P g W ≤ divCycle P f W := by
  have hdiv : ∀ x y : MRing ι k, x ∉ P → y ∉ P →
      divCycle P (x * y) W = divCycle P x W + divCycle P y W := fun x y hx hy => by
    rw [congrFun (DivCycleMul.proof k K ι P x y hP hx hy) W, Pi.add_apply]
  have hpow : ∀ (x : MRing ι k) (n : ℕ), x ∉ P → x ^ n ∉ P := fun x n hx hxn =>
    hx (hP.mem_of_pow_mem _ hxn)
  by_contra hlt
  push_neg at hlt
  set M : ℕ := (N * divCycle P g W).toNat + 1 with hM
  obtain ⟨s, r, hs, hm⟩ := h M
  have hsP : s ∉ P := fun hsp => hs (hPW hsp)
  have hrP : r ∉ P := by
    intro hr
    have h1 : s * (g ^ N * f ^ M) ∈ P := by
      have := P.add_mem hm (P.mul_mem_right (g ^ M) hr)
      simpa using this
    rcases hP.mem_or_mem h1 with h2 | h2
    · exact hsP h2
    · rcases hP.mem_or_mem h2 with h3 | h3
      · exact hpow g N hg h3
      · exact hpow f M hf h3
  have h1W : (1 : MRing ι k) ∉ W := (Ideal.ne_top_iff_one W).1 hW.ne_top
  have heq : divCycle P (g ^ N * f ^ M) W = divCycle P (r * g ^ M) W :=
    divCycle_eq_of_mul_sub_mem hs h1W (by simpa using hm)
  rw [hdiv _ _ (hpow g N hg) (hpow f M hf), hdiv _ _ hrP (hpow g M hg),
    divCycle_pow P hP g hg W N, divCycle_pow P hP f hf W M, divCycle_pow P hP g hg W M] at heq
  have hr0 := divCycle_nonneg P r W
  have hle := Int.self_le_toNat (N * divCycle P g W)
  have hMc : (M : ℤ) = ((N * divCycle P g W).toNat : ℤ) + 1 := by rw [hM]; push_cast; ring
  have hgap : divCycle P f W + 1 ≤ divCycle P g W := hlt
  have hMnn : (0 : ℤ) ≤ M := Nat.cast_nonneg M
  nlinarith [mul_le_mul_of_nonneg_left hgap hMnn]

end Div

section Rep

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ b, Fintype (ι b)]

omit [Fintype K] [∀ b, Fintype (ι b)] in
theorem homog_X (p : Σ b, ι b) : IsMultiHomog (X p : MRing ι k) (Pi.single p.1 1) :=
  isWeightedHomogeneous_X k (blockWeight ι) p

theorem rep_of_mem (y : (Σ b, ι b) → Ω) {t : Ω} (ht : t ∈ fnField k y) :
    ∃ (d : K → ℕ) (F G : MRing ι k), IsMultiHomog F d ∧ IsMultiHomog G d ∧ aeval y G ≠ 0 ∧ t * aeval y G = aeval y F := by
  classical
  let Q : Ω → Prop := fun t => ∃ (d : K → ℕ) (F G : MRing ι k), IsMultiHomog F d ∧ IsMultiHomog G d ∧
    aeval y G ≠ 0 ∧ t * aeval y G = aeval y F
  have hzero : Q 0 := ⟨0, 0, 1, isWeightedHomogeneous_zero k _ _, isWeightedHomogeneous_one k _,
    by simp, by simp⟩
  change Q t
  unfold fnField at ht
  refine IntermediateField.adjoin_induction k (p := fun t _ => Q t) ?_ ?_ ?_ ?_ ?_ ht
  · rintro x ⟨p, q, hpq, rfl⟩
    by_cases hq : y q = 0
    · simpa [hq] using hzero
    · refine ⟨Pi.single p.1 1, X p, X q, homog_X p, ?_, by simpa using hq, ?_⟩
      · rw [hpq]
        exact homog_X q
      · simp [div_mul_cancel₀ _ hq]
  · intro c
    exact ⟨0, C c, 1, isWeightedHomogeneous_C _ _, isWeightedHomogeneous_one k _, by simp,
      by simp [aeval_C]⟩
  · rintro a b - - ⟨d1, F1, G1, hF1, hG1, hG1ne, h1⟩ ⟨d2, F2, G2, hF2, hG2, hG2ne, h2⟩
    refine ⟨d1 + d2, F1 * G2 + F2 * G1, G1 * G2, IsWeightedHomogeneous.add
      (IsWeightedHomogeneous.mul hF1 hG2) ?_, IsWeightedHomogeneous.mul hG1 hG2,
      by simpa using mul_ne_zero hG1ne hG2ne, ?_⟩
    · rw [add_comm d1 d2]
      exact IsWeightedHomogeneous.mul hF2 hG1
    · simp only [map_add, map_mul]
      linear_combination aeval y G2 * h1 + aeval y G1 * h2
  · rintro a - ⟨d, F, G, hF, hG, hGne, h⟩
    by_cases ha : a = 0
    · simpa [ha] using hzero
    · have hFne : aeval y F ≠ 0 := by
        rw [← h]
        exact mul_ne_zero ha hGne
      refine ⟨d, G, F, hG, hF, hFne, ?_⟩
      rw [← h]
      field_simp
  · rintro a b - - ⟨d1, F1, G1, hF1, hG1, hG1ne, h1⟩ ⟨d2, F2, G2, hF2, hG2, hG2ne, h2⟩
    refine ⟨d1 + d2, F1 * F2, G1 * G2, IsWeightedHomogeneous.mul hF1 hF2,
      IsWeightedHomogeneous.mul hG1 hG2, by simpa using mul_ne_zero hG1ne hG2ne, ?_⟩
    simp only [map_mul]
    linear_combination (b * aeval y G2) * h1 + aeval y F1 * h2

theorem homog_mono (c : ∀ b, ι b) (e : K → ℕ) : IsMultiHomog (∏ b, (X ⟨b, c b⟩ : MRing ι k) ^ e b) e := by
  have h := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ (fun b => (X ⟨b, c b⟩ : MRing ι k) ^ e b)
    (fun b => e b • (Pi.single b 1 : K → ℕ)) fun b _ => IsWeightedHomogeneous.pow (homog_X ⟨b, c b⟩) (e b)
  have e1 : ∑ b, e b • (Pi.single b 1 : K → ℕ) = e := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  rwa [e1] at h

theorem exists_section (y : (Σ b, ι b) → Ω) (hy : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (htop : fnField k y = ⊤) (b : K → ℤ) (ρ : Ω) :
    ∃ (bf bg : K → ℕ) (f g : MRing ι k), IsMultiHomog f bf ∧ IsMultiHomog g bg ∧ aeval y g ≠ 0 ∧
      ρ * aeval y g = aeval y f ∧ (fun j => (bf j : ℤ) - bg j) = b := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : ∀ j, ι j, ∀ j, y ⟨j, c j⟩ ≠ 0 :=
    ⟨fun j => (hy j).choose, fun j => (hy j).choose_spec⟩
  set ep : K → ℕ := fun j => (b j).toNat with hep
  set em : K → ℕ := fun j => (-b j).toNat with hem
  set Mp : MRing ι k := ∏ j, (X ⟨j, c j⟩ : MRing ι k) ^ ep j with hMp
  set Mm : MRing ι k := ∏ j, (X ⟨j, c j⟩ : MRing ι k) ^ em j with hMm
  have hMpne : aeval y Mp ≠ 0 := by
    rw [hMp, map_prod]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by simpa using pow_ne_zero _ (hc j)
  have hMmne : aeval y Mm ≠ 0 := by
    rw [hMm, map_prod]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by simpa using pow_ne_zero _ (hc j)
  have hmem : ρ * aeval y Mm / aeval y Mp ∈ fnField k y := by
    rw [htop]
    exact IntermediateField.mem_top
  obtain ⟨d, F, G, hF, hG, hGne, h⟩ := rep_of_mem y hmem
  refine ⟨d + ep, d + em, F * Mp, G * Mm, IsWeightedHomogeneous.mul hF (homog_mono (k := k) c ep),
    IsWeightedHomogeneous.mul hG (homog_mono (k := k) c em), ?_, ?_, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero hGne hMmne
  · rw [map_mul, map_mul, ← h]
    field_simp
  · funext j
    simp only [Pi.add_apply, hep, hem]
    push_cast
    omega

omit [DecidableEq K] in
theorem vdeg_chart (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (c : ∀ b, ι b) (hc : ∀ b, y ⟨b, c b⟩ ≠ 0)
    (h : ∀ b i, y ⟨b, i⟩ / y ⟨b, c b⟩ ∈ O) (a : K → ℤ) : vdeg O y a = O.valuation (∏ b, y ⟨b, c b⟩ ^ a b) := by
  unfold vdeg
  rw [map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [map_zpow₀]
  congr 1
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    have h1 := (O.valuation_le_one_iff _).2 (h b i)
    calc O.valuation (y ⟨b, i⟩)
        = O.valuation (y ⟨b, i⟩ / y ⟨b, c b⟩) * O.valuation (y ⟨b, c b⟩) := by
          rw [← map_mul, div_mul_cancel₀ _ (hc b)]
      _ ≤ 1 * O.valuation (y ⟨b, c b⟩) := by gcongr
      _ = O.valuation (y ⟨b, c b⟩) := one_mul _
  · exact Finset.le_sup (f := fun i => O.valuation (y ⟨b, i⟩)) (Finset.mem_univ (c b))

end Rep

end UnitZ

private theorem zpow_mem_valuationSubring_of_unit {L : Type} [Field L] (V : ValuationSubring L) (x : L) (h1 : x ∈ V)
    (h2 : x⁻¹ ∈ V) (z : ℤ) : x ^ z ∈ V := by
  cases z with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, zpow_natCast]
    exact V.pow_mem h1 n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow]
    exact V.pow_mem h2 _

set_option maxHeartbeats 400000 in
open UnitZ in
theorem unitZero : PtDim → UnitZero := by
  intro hpt k _ Ω _ _ K _ ι _ y n a b hy htop hval
  classical
  obtain ⟨hMP, hrel, -⟩ := hpt k Ω K ι y (n + 1) hy
  obtain ⟨ρ, hρ, hv⟩ := hval
  obtain ⟨bf, bg, f, g, hf, hg, hgne, hfg, hb⟩ := exists_section y hy.1 htop b ρ
  have hfne : aeval y f ≠ 0 := by
    rw [← hfg]
    exact mul_ne_zero hρ hgne
  set P := pointIdeal k y with hPdef
  have hP : P.IsPrime := hMP.isPrime
  let L := FractionRing (MvPolynomial K Ω)
  let T : K → L := fun j => algebraMap (MvPolynomial K Ω) L (X j)
  let ψ : Ω →+* L := (algebraMap (MvPolynomial K Ω) L).comp C
  let φ : MRing ι k →+* L := (algebraMap (MvPolynomial K Ω) L).comp (pointConeMap k y).toRingHom
  have hinj := IsFractionRing.injective (MvPolynomial K Ω) L
  have hφ0 : ∀ s, φ s = 0 ↔ s ∈ P := by
    intro s
    rw [hPdef, pointIdeal, RingHom.mem_ker]
    change algebraMap (MvPolynomial K Ω) L (pointConeMap k y s) = 0 ↔ _
    exact ⟨fun h => hinj (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩
  have hφeq : ∀ s t, φ s = φ t → s - t ∈ P := fun s t h =>
    (hφ0 _).1 (by rw [map_sub, h, sub_self])
  have hψ : ∀ z, ψ z = 0 ↔ z = 0 := fun z =>
    map_eq_zero_iff ψ (hinj.comp (MvPolynomial.C_injective _ _))
  have hT : ∀ j, T j ≠ 0 := fun j h => MvPolynomial.X_ne_zero j (hinj (h.trans (map_zero _).symm))
  have hφhom : ∀ (h : MRing ι k) (d : K → ℕ), IsMultiHomog h d →
      φ h = ψ (aeval y h) * ∏ j, T j ^ d j := by
    intro h d hh
    change algebraMap (MvPolynomial K Ω) L (pointConeMap k y h) = _
    rw [GenericProjClosureDivisor.pointConeMap_of_homog y hh, map_mul, map_prod]
    simp only [map_pow]
    rfl
  have hφX : ∀ p : (Σ j, ι j), φ (X p) = ψ (y p) * T p.1 := by
    intro p
    change algebraMap (MvPolynomial K Ω) L (pointConeMap k y (X p)) =
      algebraMap (MvPolynomial K Ω) L (C (y p)) * algebraMap (MvPolynomial K Ω) L (X p.1)
    rw [← map_mul]
    congr 1
    simp [pointConeMap]
  have hφne : ∀ (h : MRing ι k) (d : K → ℕ), IsMultiHomog h d → aeval y h ≠ 0 → h ∉ P := by
    intro h d hh hne hP'
    have h0 := (hφ0 h).2 hP'
    rw [hφhom h d hh] at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact hne ((hψ _).1 h1)
    · exact (Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hT j)) h1
  have hfP := hφne f bf hf hfne
  have hgP := hφne g bg hg hgne
  have hcut := GroundTheory.Heights₂.Heights.FieldNumbers.CutRational.full k K ι P hMP n hrel bf bg f g hf hg
    hfP hgP a
  have hunit : ∀ (W : Ideal (MRing ι k)) [W.IsPrime], P ≤ W → IsRelevant W →
      ∀ V : ValuationSubring L, (∀ s, φ s ∈ V) → (∀ s, s ∉ W → (φ s)⁻¹ ∈ V) →
        φ f / φ g ∈ V ∧ φ g / φ f ∈ V := by
    intro W _ hPW hWr V hVS hVinv
    have hWr' : ∀ j, ∃ i, (X ⟨j, i⟩ : MRing ι k) ∉ W := hWr
    choose c hc using hWr'
    have hk : ∀ s, s ∉ W → φ s ≠ 0 := fun s hs h0 => hs (hPW ((hφ0 s).1 h0))
    have hyc : ∀ j, y ⟨j, c j⟩ ≠ 0 := fun j h0 =>
      hk _ (hc j) (by rw [hφX, h0, map_zero, zero_mul])
    let O := V.comap ψ
    have hdiv : ∀ j i, y ⟨j, i⟩ / y ⟨j, c j⟩ ∈ O := by
      intro j i
      change ψ (y ⟨j, i⟩ / y ⟨j, c j⟩) ∈ V
      have e : ψ (y ⟨j, i⟩ / y ⟨j, c j⟩) = φ (X ⟨j, i⟩) * (φ (X ⟨j, c j⟩))⁻¹ := by
        rw [hφX, hφX, map_div₀, mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ (hT j), mul_one,
          div_eq_mul_inv]
      rw [e]
      exact mul_mem (hVS _) (hVinv _ (hc j))
    have hkO : ∀ x : k, algebraMap k Ω x ∈ O := by
      intro x
      change ψ (algebraMap k Ω x) ∈ V
      have e : ψ (algebraMap k Ω x) = φ (C x) := by
        change algebraMap (MvPolynomial K Ω) L (C (algebraMap k Ω x)) =
          algebraMap (MvPolynomial K Ω) L (pointConeMap k y (C x))
        congr 1
        simp [pointConeMap, MvPolynomial.algebraMap_eq]
      rw [e]
      exact hVS _
    have hv' := hv O hkO
    have h0 : vdeg O y 0 = 1 := by simp [vdeg]
    rw [vdeg_chart O y c hyc hdiv b, h0, mul_one] at hv'
    set Y := ∏ j, y ⟨j, c j⟩ ^ b j with hYdef
    have hY : Y ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ (hyc j)
    have hw1 : O.valuation (ρ / Y) = 1 := by
      rw [map_div₀, ← hv']
      exact div_self ((Valuation.ne_zero_iff _).2 hY)
    have hwO : ψ (ρ / Y) ∈ V := (O.valuation_le_one_iff _).1 hw1.le
    have hwO' : ψ ((ρ / Y)⁻¹) ∈ V :=
      (O.valuation_le_one_iff _).1 (by rw [map_inv₀, hw1, inv_one])
    have he1 : ∀ j, φ (X ⟨j, c j⟩) ∈ V := fun j => hVS _
    have he2 : ∀ j, (φ (X ⟨j, c j⟩))⁻¹ ∈ V := fun j => hVinv _ (hc j)
    have hb' : ∀ j, b j = (bf j : ℤ) - bg j := fun j => (congrFun hb j).symm
    have hA : ∏ j, T j ^ b j = (∏ j, T j ^ bf j) / ∏ j, T j ^ bg j := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [hb', zpow_sub₀ (hT j), zpow_natCast, zpow_natCast]
    have hYψ : ∏ j, ψ (y ⟨j, c j⟩) ^ b j = ψ Y := by
      rw [hYdef, map_prod]
      simp [map_zpow₀]
    have hψY : ψ Y ≠ 0 := fun h0 => hY ((hψ _).1 h0)
    have hψg : ψ (aeval y g) ≠ 0 := fun h0 => hgne ((hψ _).1 h0)
    have hR : ∏ j, φ (X ⟨j, c j⟩) ^ b j = ψ Y * ((∏ j, T j ^ bf j) / ∏ j, T j ^ bg j) := by
      rw [← hA, ← hYψ, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [hφX, mul_zpow]
    have hprod : φ f / φ g = ψ (ρ / Y) * ∏ j, φ (X ⟨j, c j⟩) ^ b j := by
      rw [hR, hφhom f bf hf, hφhom g bg hg, ← hfg, map_mul, map_div₀]
      rw [mul_div_mul_comm, mul_div_cancel_right₀ _ hψg, ← mul_assoc, div_mul_cancel₀ _ hψY]
    have hprod' : φ g / φ f = ψ ((ρ / Y)⁻¹) * ∏ j, (φ (X ⟨j, c j⟩))⁻¹ ^ b j := by
      rw [← inv_div, hprod, mul_inv, map_inv₀, ← Finset.prod_inv_distrib]
      simp [inv_zpow]
    constructor
    · rw [hprod]
      exact mul_mem hwO (prod_mem fun j _ => zpow_mem_valuationSubring_of_unit V _ (he1 j) (he2 j) _)
    · rw [hprod']
      exact mul_mem hwO' (prod_mem fun j _ =>
        zpow_mem_valuationSubring_of_unit V _ (he2 j) (by rw [inv_inv]; exact he1 j) _)
  have hzero : ∀ W, divCycle P f W = divCycle P g W := by
    intro W
    by_cases hW : W.IsPrime ∧ P ≤ W ∧ IsRelevant W
    · obtain ⟨hWp, hPW, hWr⟩ := hW
      haveI := hWp
      have hk : ∀ s, s ∉ W → φ s ≠ 0 := fun s hs h0 => hs (hPW ((hφ0 s).1 h0))
      have hφf : φ f ≠ 0 := fun h0 => hfP ((hφ0 f).1 h0)
      have hφg : φ g ≠ 0 := fun h0 => hgP ((hφ0 g).1 h0)
      obtain ⟨N1, h1⟩ := exists_rel φ W hk f g hφg fun V hV1 hV2 =>
        (hunit W hPW hWr V hV1 hV2).1
      obtain ⟨N2, h2⟩ := exists_rel φ W hk g f hφf fun V hV1 hV2 =>
        (hunit W hPW hWr V hV1 hV2).2
      have l1 := divCycle_le P hP f g hfP hgP W hWp hPW N1 fun m => by
        obtain ⟨s, r, hs, e⟩ := h1 m
        exact ⟨s, r, hs, hφeq _ _ e⟩
      have l2 := divCycle_le P hP g f hgP hfP W hWp hPW N2 fun m => by
        obtain ⟨s, r, hs, e⟩ := h2 m
        exact ⟨s, r, hs, hφeq _ _ e⟩
      omega
    · have e1 : divCycle P f W = 0 := by
        by_contra hne
        exact hW (le_and_isRelevant_of_divCycle_ne_zero hne)
      have e2 : divCycle P g W = 0 := by
        by_contra hne
        exact hW (le_and_isRelevant_of_divCycle_ne_zero hne)
      rw [e1, e2]
  have hI : inum k y (Fin.snoc a b) = intNum k P (Fin.snoc a fun j => (bf j : ℤ) - bg j) := by
    rw [← hb]
    rfl
  rw [hI, hcut]
  unfold cycEval ratDiv
  simp [hzero]

end SheetDecomposition
