import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilTranslate
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilFixedField

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine AddSubgroup

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
  [W.IsElliptic]

local notation "ι" => algebraMap F W.toAffine.FunctionField

theorem divisorOf_pow {f : W.toAffine.FunctionField} (hf : f ≠ 0) (k : ℕ) :
    divisorOf W (f ^ k) = k • divisorOf W f := by
  induction k with
  | zero => rw [pow_zero, divisorOf_one, zero_smul]
  | succ k ih => rw [pow_succ, divisorOf_mul W (pow_ne_zero k hf) hf, ih, succ_nsmul]

theorem divisorOf_prod {ι' : Type*} (s : Finset ι') (φ : ι' → W.toAffine.FunctionField)
    (hφ : ∀ i ∈ s, φ i ≠ 0) : divisorOf W (∏ i ∈ s, φ i) = ∑ i ∈ s, divisorOf W (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, divisorOf_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      divisorOf_mul W (hφ a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hφ i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hφ i (Finset.mem_insert_of_mem hi)]

omit [DecidableEq F] [IsAlgClosed F] in
theorem mulPullback_congr {m n : ℤ} (h : m = n) (hm : m ≠ 0) (hn : n ≠ 0) :
    mulPullback W m hm = mulPullback W n hn := by
  subst h
  rfl

def IsWeilData (n : ℕ) (T : W.toAffine.Point) (f g : W.toAffine.FunctionField) : Prop :=
  f ≠ 0 ∧ g ≠ 0 ∧ divisorOf W f = (n : ℤ) • (Finsupp.single T 1 - Finsupp.single 0 1) ∧
    ∃ hn : (n : ℤ) ≠ 0, mulPullback W n hn f = g ^ n

open Classical in

noncomputable def weilPairing (n : ℕ) (S T : W.toAffine.Point) : F :=
  if h : ∃ ζ : F, ∃ f g, IsWeilData W n T f g ∧ translate W S g = ι ζ * g then h.choose else 1

variable {W}

theorem IsWeilData.exists_translate_eq {n : ℕ} {T : W.toAffine.Point} {f g : W.toAffine.FunctionField}
    (h : IsWeilData W n T f g) {S : W.toAffine.Point} (hS : n • S = 0) :
    ∃ ζ : F, ζ ^ n = 1 ∧ translate W S g = ι ζ * g := by
  obtain ⟨hf, hg, -, hn0, hpull⟩ := h
  have hn : n ≠ 0 := by exact_mod_cast hn0
  have hS' : (n : ℤ) • S = 0 := by rw [natCast_zsmul]; exact hS
  have hpow : (translate W S g / g) ^ n = ι 1 := by
    rw [div_pow, ← map_pow, ← hpull, translate_mulPullback_of_zsmul_eq_zero W hn0 hS', hpull,
      div_self (pow_ne_zero n hg), map_one]
  obtain ⟨d, hd⟩ := exists_algebraMap_eq_of_pow_eq W hn hpow
  refine ⟨d, ?_, ?_⟩
  · apply (algebraMap F W.toAffine.FunctionField).injective
    rw [map_pow, hd, hpow, map_one]
  · rw [hd, div_mul_cancel₀ _ hg]

theorem IsWeilData.exists_eq_mul {n : ℕ} {T : W.toAffine.Point} {f g f' g' : W.toAffine.FunctionField}
    (h : IsWeilData W n T f g) (h' : IsWeilData W n T f' g') : ∃ d : F, g' = ι d * g := by
  obtain ⟨hf, hg, hdiv, hn0, hpull⟩ := h
  obtain ⟨hf', hg', hdiv', hn0', hpull'⟩ := h'
  have hn : n ≠ 0 := by exact_mod_cast hn0
  obtain ⟨c, -, hc⟩ := exists_algebraMap_mul_eq_of_divisorOf_eq W hf hf' (hdiv.trans hdiv'.symm)
  have hpow : (g' / g) ^ n = ι c := by
    rw [div_pow, ← hpull', ← hc, map_mul, mulPullback_algebraMap, hpull,
      mul_div_cancel_right₀ _ (pow_ne_zero n hg)]
  obtain ⟨d, hd⟩ := exists_algebraMap_eq_of_pow_eq W hn hpow
  exact ⟨d, by rw [hd, div_mul_cancel₀ _ hg]⟩

theorem translate_eq_weilPairing_mul {n : ℕ} {S T : W.toAffine.Point}
    {f g : W.toAffine.FunctionField} (hS : n • S = 0) (h : IsWeilData W n T f g) :
    translate W S g = ι (weilPairing W n S T) * g := by
  obtain ⟨ζ, -, hζ⟩ := h.exists_translate_eq hS
  have hex : ∃ ζ : F, ∃ f g, IsWeilData W n T f g ∧ translate W S g = ι ζ * g := ⟨ζ, f, g, h, hζ⟩
  classical
  rw [weilPairing, dif_pos hex]
  obtain ⟨f₀, g₀, h₀, hζ₀⟩ := hex.choose_spec
  obtain ⟨d, rfl⟩ := h₀.exists_eq_mul h
  rw [map_mul, translate_algebraMap, hζ₀]
  ring

theorem weilPairing_eq_of_translate_eq {n : ℕ} {S T : W.toAffine.Point}
    {f g : W.toAffine.FunctionField} (hS : n • S = 0) (h : IsWeilData W n T f g) {ζ : F}
    (hζ : translate W S g = ι ζ * g) : weilPairing W n S T = ζ := by
  have := (translate_eq_weilPairing_mul hS h).symm.trans hζ
  exact (algebraMap F W.toAffine.FunctionField).injective (mul_right_cancel₀ h.2.1 this)

variable (W)

theorem exists_isWeilData {n : ℕ} (hn : (n : F) ≠ 0) {T : W.toAffine.Point} (hT : n • T = 0) :
    ∃ f g, IsWeilData W n T f g := by
  classical
  have hn' : n ≠ 0 := by rintro rfl; simp at hn
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn'
  have hnF : ((n : ℤ) : F) ≠ 0 := by exact_mod_cast hn
  have hT' : (n : ℤ) • T = 0 := by rw [natCast_zsmul]; exact hT

  obtain ⟨f, hf, hdivf⟩ := (exists_divisorOf_eq_iff W
    ((n : ℤ) • (Finsupp.single T 1 - Finsupp.single 0 1))).mpr ⟨by simp, by simp [hT]⟩

  obtain ⟨T', hT''⟩ := exists_zsmul_eq W hn0 T
  set K : Finset W.toAffine.Point := (finite_setOf_zsmul_eq W hnF 0).toFinset with hK
  have hmemK : ∀ R, R ∈ K ↔ (n : ℤ) • R = 0 := fun R => by simp [hK]
  have hcardK : K.card = n ^ 2 := by
    have h := card_zsmul_eq_zero W hnF
    rw [Int.natAbs_natCast] at h
    rw [← h, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun R => hmemK R)
  set D : CurveDivisor W := ∑ R ∈ K, (Finsupp.single (T' + R) 1 - Finsupp.single R 1) with hD
  have hDpull : D = mulPullbackDivisor W hnF (Finsupp.single T 1 - Finsupp.single 0 1) := by
    ext P
    rw [mulPullbackDivisor_apply, hD, Finsupp.finsetSum_apply]
    simp only [Finsupp.sub_apply, Finsupp.single_apply, Finset.sum_sub_distrib]
    have h1 : ∑ R ∈ K, (if T' + R = P then (1 : ℤ) else 0) =
        if (n : ℤ) • P = T then 1 else 0 := by
      have e : ∀ R, (T' + R = P) ↔ (R = P - T') := fun R => by
        constructor
        · rintro rfl; abel
        · rintro rfl; abel
      simp_rw [e]
      rw [Finset.sum_ite_eq' K (P - T') (fun _ => (1 : ℤ))]
      simp only [hmemK, zsmul_sub, hT'', sub_eq_zero]
    have h2 : ∑ R ∈ K, (if R = P then (1 : ℤ) else 0) = if (n : ℤ) • P = 0 then 1 else 0 := by
      rw [Finset.sum_ite_eq' K P (fun _ => (1 : ℤ))]
      simp only [hmemK]
    rw [h1, h2]
    simp only [eq_comm]
  have hdegD : divisorDegree W D = 0 := by
    rw [hD, map_sum]
    simp
  have hsumD : divisorSum W D = 0 := by
    rw [hD, map_sum]
    simp only [map_sub, divisorSum_single, one_smul, add_sub_cancel_right, Finset.sum_const,
      hcardK]
    have hT3 : n • T' = T := by rw [← natCast_zsmul]; exact hT''
    rw [pow_two, mul_nsmul, hT3, hT]
  obtain ⟨g₀, hg₀, hdivg₀⟩ := (exists_divisorOf_eq_iff W D).mpr ⟨hdegD, hsumD⟩

  have hdiv : divisorOf W (g₀ ^ n) = divisorOf W (mulPullback W n hn0 f) := by
    rw [divisorOf_pow W hg₀, divisorOf_mulPullback W hnF hn0 hf, hdivf, map_zsmul, ← hDpull,
      hdivg₀, natCast_zsmul]
  obtain ⟨c, hc0, hc⟩ := exists_algebraMap_mul_eq_of_divisorOf_eq W (pow_ne_zero n hg₀)
    (mulPullback_ne_zero W hn0 hf) hdiv
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hn')
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow hn'] at hd
    exact hc0 hd.symm
  refine ⟨f, ι d * g₀, hf, mul_ne_zero ((map_ne_zero_iff _ (algebraMap F W.toAffine.FunctionField).injective).mpr hd0) hg₀, hdivf, hn0, ?_⟩
  rw [← hc, mul_pow, ← map_pow, hd]

variable {W}

theorem weilPairing_pow_eq_one {n : ℕ} (hn : (n : F) ≠ 0) {S T : W.toAffine.Point}
    (hS : n • S = 0) (hT : n • T = 0) : weilPairing W n S T ^ n = 1 := by
  obtain ⟨f, g, h⟩ := exists_isWeilData W hn hT
  obtain ⟨ζ, hζn, hζ⟩ := h.exists_translate_eq hS
  rw [weilPairing_eq_of_translate_eq hS h hζ, hζn]

theorem weilPairing_ne_zero {n : ℕ} (hn : (n : F) ≠ 0) {S T : W.toAffine.Point}
    (hS : n • S = 0) (hT : n • T = 0) : weilPairing W n S T ≠ 0 := by
  intro h0
  have h := weilPairing_pow_eq_one hn hS hT
  have hn' : n ≠ 0 := by rintro rfl; simp at hn
  rw [h0, zero_pow hn'] at h
  exact zero_ne_one h

theorem weilPairing_add_left {n : ℕ} (hn : (n : F) ≠ 0) {S₁ S₂ T : W.toAffine.Point}
    (hS₁ : n • S₁ = 0) (hS₂ : n • S₂ = 0) (hT : n • T = 0) :
    weilPairing W n (S₁ + S₂) T = weilPairing W n S₁ T * weilPairing W n S₂ T := by
  obtain ⟨f, g, h⟩ := exists_isWeilData W hn hT
  apply weilPairing_eq_of_translate_eq (by rw [nsmul_add, hS₁, hS₂, add_zero]) h
  rw [← translate_translate, translate_eq_weilPairing_mul hS₂ h, map_mul, translate_algebraMap,
    translate_eq_weilPairing_mul hS₁ h, map_mul]
  ring

theorem weilPairing_add_right {n : ℕ} (hn : (n : F) ≠ 0) {S T₁ T₂ : W.toAffine.Point}
    (hS : n • S = 0) (hT₁ : n • T₁ = 0) (hT₂ : n • T₂ = 0) :
    weilPairing W n S (T₁ + T₂) = weilPairing W n S T₁ * weilPairing W n S T₂ := by
  obtain ⟨f₁, g₁, h₁⟩ := exists_isWeilData W hn hT₁
  obtain ⟨f₂, g₂, h₂⟩ := exists_isWeilData W hn hT₂
  obtain ⟨hf₁, hg₁, hdiv₁, hn0, hpull₁⟩ := h₁
  obtain ⟨hf₂, hg₂, hdiv₂, hn0', hpull₂⟩ := h₂
  have hS' : (n : ℤ) • S = 0 := by rw [natCast_zsmul]; exact hS

  obtain ⟨k, hk, hdivk⟩ := (exists_divisorOf_eq_iff W (Finsupp.single (T₁ + T₂) 1 -
    Finsupp.single T₁ 1 - Finsupp.single T₂ 1 + Finsupp.single 0 1)).mpr
    ⟨by simp, by simp⟩
  have hdata : IsWeilData W n (T₁ + T₂) (f₁ * f₂ * k ^ n) (g₁ * g₂ * mulPullback W n hn0 k) := by
    refine ⟨mul_ne_zero (mul_ne_zero hf₁ hf₂) (pow_ne_zero n hk),
      mul_ne_zero (mul_ne_zero hg₁ hg₂) (mulPullback_ne_zero W hn0 hk), ?_, hn0, ?_⟩
    · rw [divisorOf_mul W (mul_ne_zero hf₁ hf₂) (pow_ne_zero n hk), divisorOf_mul W hf₁ hf₂,
        divisorOf_pow W hk, hdiv₁, hdiv₂, hdivk, ← natCast_zsmul]
      simp only [smul_sub, smul_add]
      abel
    · rw [map_mul, map_mul, map_pow, hpull₁, hpull₂, mul_pow, mul_pow]
  apply weilPairing_eq_of_translate_eq hS hdata
  rw [map_mul, map_mul, translate_eq_weilPairing_mul hS ⟨hf₁, hg₁, hdiv₁, hn0, hpull₁⟩,
    translate_eq_weilPairing_mul hS ⟨hf₂, hg₂, hdiv₂, hn0', hpull₂⟩,
    translate_mulPullback_of_zsmul_eq_zero W hn0 hS', map_mul]
  ring

omit [IsAlgClosed F] [W.IsElliptic] in

theorem sum_range_add_zsmul_shift {M : Type*} [AddCommGroup M] (φ : W.toAffine.Point → M) {n : ℕ}
    {T : W.toAffine.Point} (hT : n • T = 0) (Q : W.toAffine.Point) :
    ∑ i ∈ Finset.range n, φ (Q + T + (i : ℤ) • T) = ∑ i ∈ Finset.range n, φ (Q + (i : ℤ) • T) := by
  have h1 := Finset.sum_range_succ' (fun i : ℕ => φ (Q + (i : ℤ) • T)) n
  have h2 := Finset.sum_range_succ (fun i : ℕ => φ (Q + (i : ℤ) • T)) n
  rw [natCast_zsmul, hT, add_zero] at h2
  simp only [Nat.cast_zero, zero_smul, add_zero] at h1
  have h3 : ∀ i : ℕ, Q + ((i + 1 : ℕ) : ℤ) • T = Q + T + (i : ℤ) • T := fun i => by
    push_cast
    rw [add_zsmul, one_zsmul]
    abel
  simp only [h3] at h1
  exact add_right_cancel (h1.symm.trans h2)

theorem weilPairing_self {n : ℕ} (hn : (n : F) ≠ 0) {T : W.toAffine.Point} (hT : n • T = 0) :
    weilPairing W n T T = 1 := by
  classical
  obtain ⟨f, g, h⟩ := exists_isWeilData W hn hT
  obtain ⟨hf, hg, hdiv, hn0, hpull⟩ := h
  have hn' : n ≠ 0 := by exact_mod_cast hn0
  have hT' : (n : ℤ) • T = 0 := by rw [natCast_zsmul]; exact hT
  obtain ⟨T'', hT''⟩ := exists_zsmul_eq W hn0 T

  set H := ∏ i ∈ Finset.range n, translate W ((i : ℤ) • T) f with hH
  have hH0 : ∀ i ∈ Finset.range n, translate W ((i : ℤ) • T) f ≠ 0 :=
    fun i _ => translate_ne_zero W _ hf
  set χ : W.toAffine.Point → ℤ := fun Q => if (0 : W.toAffine.Point) = Q then 1 else 0 with hχ
  have hdivH : divisorOf W H = 0 := by
    ext P
    rw [hH, divisorOf_prod W _ _ hH0, Finsupp.finsetSum_apply, Finsupp.zero_apply]
    have key : ∀ i : ℕ, divisorOf W (translate W ((i : ℤ) • T) f) P =
        n * (χ (P - T + (i : ℤ) • T) - χ (P - T + T + (i : ℤ) • T)) := by
      intro i
      have c1 : (T = P + (i : ℤ) • T) ↔ ((0 : W.toAffine.Point) = P - T + (i : ℤ) • T) := by
        rw [show P - T + (i : ℤ) • T = P + (i : ℤ) • T - T by abel,
          eq_comm (a := (0 : W.toAffine.Point)), sub_eq_zero, eq_comm]
      rw [divisorOf_translate_apply W _ hf, hdiv, Finsupp.smul_apply, Finsupp.sub_apply,
        Finsupp.single_apply, Finsupp.single_apply, smul_eq_mul, sub_add_cancel, hχ]
      simp only [c1]
    simp only [key]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_range_add_zsmul_shift χ hT (P - T), sub_self,
      mul_zero]
  have hHne : H ≠ 0 := Finset.prod_ne_zero_iff.mpr hH0
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_divisorOf_eq_zero W hHne hdivH

  set ψ : ℕ → W.toAffine.FunctionField := fun i => translate W ((i : ℤ) • T'') g with hψ
  set G := ∏ i ∈ Finset.range n, ψ i with hG
  have hstep : ∀ i : ℕ, (ψ i) ^ n = mulPullback W n hn0 (translate W ((i : ℤ) • T) f) := by
    intro i
    rw [hψ]
    dsimp only
    rw [← map_pow, ← hpull]
    have := DFunLike.congr_fun (translate_comp_mulPullback W hn0 ((i : ℤ) • T'')) f
    simp only [AlgHom.comp_apply] at this
    rw [this, smul_comm, hT'']
  have hGn : G ^ n = ι c := by
    rw [hG, ← Finset.prod_pow, Finset.prod_congr rfl fun i _ => hstep i, ← map_prod, ← hH, ← hc,
      mulPullback_algebraMap]
  obtain ⟨d, hd⟩ := exists_algebraMap_eq_of_pow_eq W hn' hGn
  have hshift : translate W T'' G = ∏ i ∈ Finset.range n, ψ (i + 1) := by
    rw [hG, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hψ]
    dsimp only
    rw [translate_translate]
    congr 1
    push_cast
    rw [add_zsmul, one_zsmul, add_comm]
  have hfix : translate W T'' G = G := by rw [← hd, translate_algebraMap]
  have h1 := Finset.prod_range_succ' ψ n
  have h2 := Finset.prod_range_succ ψ n
  rw [← hshift, hfix] at h1
  rw [← hG] at h2
  have hGne : G ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => translate_ne_zero W _ hg
  have hψn : ψ n = ψ 0 := mul_left_cancel₀ hGne (h2.symm.trans h1)
  have hgT : translate W T g = ι 1 * g := by
    have : ψ n = translate W T g := by rw [hψ]; dsimp only; rw [hT'']
    rw [← this, hψn, hψ]
    dsimp only
    rw [Nat.cast_zero, zero_smul, translate_zero, map_one, one_mul, AlgHom.id_apply]
  exact weilPairing_eq_of_translate_eq hT ⟨hf, hg, hdiv, hn0, hpull⟩ hgT

theorem weilPairing_mul_weilPairing_swap {n : ℕ} (hn : (n : F) ≠ 0) {S T : W.toAffine.Point}
    (hS : n • S = 0) (hT : n • T = 0) : weilPairing W n S T * weilPairing W n T S = 1 := by
  have hST : n • (S + T) = 0 := by rw [nsmul_add, hS, hT, add_zero]
  have h := weilPairing_self hn hST
  rw [weilPairing_add_left hn hS hT hST, weilPairing_add_right hn hS hS hT,
    weilPairing_add_right hn hT hS hT, weilPairing_self hn hS, weilPairing_self hn hT] at h
  rw [← h]
  ring

theorem weilPairing_mul {m n : ℕ} (hmn : ((m * n : ℕ) : F) ≠ 0) {S T : W.toAffine.Point}
    (hS : (m * n) • S = 0) (hT : n • T = 0) :
    weilPairing W (m * n) S T = weilPairing W n (m • S) T := by
  have hm : (m : F) ≠ 0 := fun h => hmn (by rw [Nat.cast_mul, h, zero_mul])
  have hn : (n : F) ≠ 0 := fun h => hmn (by rw [Nat.cast_mul, h, mul_zero])
  have hm0 : (m : ℤ) ≠ 0 := by
    have : m ≠ 0 := by rintro rfl; simp at hm
    exact_mod_cast this
  obtain ⟨f, g, h⟩ := exists_isWeilData W hn hT
  obtain ⟨hf, hg, hdiv, hn0, hpull⟩ := h
  have hmn0 : ((m * n : ℕ) : ℤ) ≠ 0 := by push_cast; exact mul_ne_zero hm0 hn0
  have hmS : n • (m • S) = 0 := by rw [smul_smul, mul_comm]; exact hS
  have hdata : IsWeilData W (m * n) T (f ^ m) (mulPullback W m hm0 g) := by
    refine ⟨pow_ne_zero m hf, mulPullback_ne_zero W hm0 hg, ?_, hmn0, ?_⟩
    · rw [divisorOf_pow W hf, hdiv, ← natCast_zsmul, smul_smul]
      push_cast
      ring_nf
    · rw [mulPullback_congr W (by push_cast; ring) hmn0 (mul_ne_zero hm0 hn0), mulPullback_mul W hm0 hn0,
        AlgHom.comp_apply, map_pow, hpull, ← map_pow, ← pow_mul, mul_comm n m]
  apply weilPairing_eq_of_translate_eq hS hdata
  have := DFunLike.congr_fun (translate_comp_mulPullback W hm0 S) g
  simp only [AlgHom.comp_apply] at this
  rw [this, natCast_zsmul, translate_eq_weilPairing_mul hmS ⟨hf, hg, hdiv, hn0, hpull⟩, map_mul,
    mulPullback_algebraMap]

theorem eq_zero_of_forall_weilPairing_eq_one {n : ℕ} (hn : (n : F) ≠ 0) {T : W.toAffine.Point}
    (hT : n • T = 0) (h : ∀ S : W.toAffine.Point, n • S = 0 → weilPairing W n S T = 1) : T = 0 := by
  obtain ⟨f, g, hd⟩ := exists_isWeilData W hn hT
  obtain ⟨hf, hg, hdiv, hn0, hpull⟩ := hd
  have hnF : ((n : ℤ) : F) ≠ 0 := by exact_mod_cast hn
  have hinv : ∀ S : W.toAffine.Point, (n : ℤ) • S = 0 → translate W S g = g := by
    intro S hS
    rw [natCast_zsmul] at hS
    rw [translate_eq_weilPairing_mul hS ⟨hf, hg, hdiv, hn0, hpull⟩, h S hS, map_one, one_mul]
  obtain ⟨k, hk⟩ := exists_mulPullback_eq_of_forall_translate_eq W hnF hn0 hinv
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact hg hk.symm
  have hkf : k ^ n = f := by
    apply mulPullback_injective W hn0
    rw [map_pow, hk, hpull]
  have hdk : (n : ℤ) • divisorOf W k = (n : ℤ) • (Finsupp.single T 1 - Finsupp.single 0 1) := by
    rw [natCast_zsmul, ← divisorOf_pow W hk0, hkf, hdiv, natCast_zsmul]
  have hdk' := smul_right_injective (CurveDivisor W) hn0 hdk
  have hsum := divisorSum_divisorOf W hk0
  rw [hdk'] at hsum
  simpa using hsum

theorem eq_zero_of_forall_weilPairing_eq_one' {n : ℕ} (hn : (n : F) ≠ 0) {S : W.toAffine.Point}
    (hS : n • S = 0) (h : ∀ T : W.toAffine.Point, n • T = 0 → weilPairing W n S T = 1) : S = 0 := by
  refine eq_zero_of_forall_weilPairing_eq_one hn hS fun T hT => ?_
  have := weilPairing_mul_weilPairing_swap hn hS hT
  rwa [h T hT, one_mul] at this

noncomputable def weilPairingRoot {n : ℕ} (hn : (n : F) ≠ 0)
    (S T : torsionBy W.toAffine.Point n) : rootsOfUnity n F :=
  ⟨Units.mk0 (weilPairing W n S T)
      (weilPairing_ne_zero hn (torsionBy.nsmul_iff.mp S.2) (torsionBy.nsmul_iff.mp T.2)), by
    rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    exact weilPairing_pow_eq_one hn (torsionBy.nsmul_iff.mp S.2) (torsionBy.nsmul_iff.mp T.2)⟩

@[simp]
theorem coe_weilPairingRoot {n : ℕ} (hn : (n : F) ≠ 0) (S T : torsionBy W.toAffine.Point n) :
    ((weilPairingRoot hn S T : Fˣ) : F) = weilPairing W n S T :=
  rfl

theorem weilPairingRoot_add_left {n : ℕ} (hn : (n : F) ≠ 0) (S₁ S₂ T : torsionBy W.toAffine.Point n) :
    weilPairingRoot hn (S₁ + S₂) T = weilPairingRoot hn S₁ T * weilPairingRoot hn S₂ T := by
  apply Subtype.ext
  apply Units.ext
  change weilPairing W n ((S₁ + S₂ : torsionBy W.toAffine.Point n) : W.toAffine.Point) T =
    weilPairing W n S₁ T * weilPairing W n S₂ T
  rw [AddSubgroup.coe_add]
  exact weilPairing_add_left hn (torsionBy.nsmul_iff.mp S₁.2) (torsionBy.nsmul_iff.mp S₂.2)
    (torsionBy.nsmul_iff.mp T.2)

theorem weilPairingRoot_add_right {n : ℕ} (hn : (n : F) ≠ 0) (S T₁ T₂ : torsionBy W.toAffine.Point n) :
    weilPairingRoot hn S (T₁ + T₂) = weilPairingRoot hn S T₁ * weilPairingRoot hn S T₂ := by
  apply Subtype.ext
  apply Units.ext
  change weilPairing W n S ((T₁ + T₂ : torsionBy W.toAffine.Point n) : W.toAffine.Point) =
    weilPairing W n S T₁ * weilPairing W n S T₂
  rw [AddSubgroup.coe_add]
  exact weilPairing_add_right hn (torsionBy.nsmul_iff.mp S.2) (torsionBy.nsmul_iff.mp T₁.2)
    (torsionBy.nsmul_iff.mp T₂.2)

noncomputable def weilPairingHom {n : ℕ} (hn : (n : F) ≠ 0) :
    torsionBy W.toAffine.Point n →+ torsionBy W.toAffine.Point n →+ Additive (rootsOfUnity n F) :=
  AddMonoidHom.mk' (fun S => AddMonoidHom.mk' (fun T => Additive.ofMul (weilPairingRoot hn S T))
      fun T₁ T₂ => by rw [weilPairingRoot_add_right]; rfl)
    fun S₁ S₂ => AddMonoidHom.ext fun T => by
      change Additive.ofMul (weilPairingRoot hn (S₁ + S₂) T) =
        Additive.ofMul (weilPairingRoot hn S₁ T) + Additive.ofMul (weilPairingRoot hn S₂ T)
      rw [weilPairingRoot_add_left]
      rfl

theorem weilPairingHom_apply {n : ℕ} (hn : (n : F) ≠ 0) (S T : torsionBy W.toAffine.Point n) :
    (((Additive.toMul (weilPairingHom hn S T) : rootsOfUnity n F) : Fˣ) : F) =
      weilPairing W n S T :=
  rfl

end GroundTheory.Arith.Abelian
