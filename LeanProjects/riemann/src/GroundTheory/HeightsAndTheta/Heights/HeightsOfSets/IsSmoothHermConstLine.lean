import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.MemMCoordIdealIffOfIsWeightedHomogeneous
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Imports
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def invLine (A : Geo.HermLine ι) : Geo.HermLine ι where
  a := -A.a
  h z := (A.h z)⁻¹
  pos z hz := inv_pos.mpr (A.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Pi.neg_apply, zpow_neg]

def constLine (M : ℝ) (hM : 0 < M) : Geo.HermLine ι where
  a := 0
  h _ := M
  pos _ _ := hM
  smul c z hc := by simp

def powLine (A : Geo.HermLine ι) : ℕ → Geo.HermLine ι
  | 0 => constLine 1 one_pos
  | m + 1 => (powLine A m).tensor A

theorem isSmoothHerm_invLine {A : Geo.HermLine ι} (hA : IsSmoothHerm A) : IsSmoothHerm (invLine A) :=
  ContDiffOn.inv hA fun z hz ↦ (A.pos z hz).ne'

theorem isSmoothHerm_constLine (M : ℝ) (hM : 0 < M) : IsSmoothHerm (constLine (ι := ι) M hM) :=
  contDiffOn_const

theorem isSmoothHerm_tensor {A B : Geo.HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  ContDiffOn.mul hA hB

theorem isSmoothHerm_powLine {A : Geo.HermLine ι} (hA : IsSmoothHerm A) (m : ℕ) :
    IsSmoothHerm (powLine A m) := by
  induction m with
  | zero => exact isSmoothHerm_constLine 1 one_pos
  | succ m ih => exact isSmoothHerm_tensor ih hA

theorem powLine_a (A : Geo.HermLine ι) (m : ℕ) (k : K) : (powLine A m).a k = m * A.a k := by
  induction m with
  | zero => simp [powLine, constLine]
  | succ m ih =>
    simp only [powLine, Geo.HermLine.tensor, Pi.add_apply, ih]
    push_cast
    ring

theorem isMultiHomog_mul {p q : MRing ι} {a b : K → ℕ} (hp : IsMultiHomog p a)
    (hq : IsMultiHomog q b) : IsMultiHomog (p * q) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul p q hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hp m₁ hm₁ k, hq m₂ hm₂ k]

theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  intro m hm k
  rw [← C_1, support_C, if_neg one_ne_zero, Finset.mem_singleton] at hm
  subst hm
  simp

theorem isMultiHomog_X [DecidableEq K] (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (Pi.single p.1 1) := by
  classical
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k₀, i₀⟩ := p
  by_cases hk : k = k₀
  · subst hk
    rw [Pi.single_eq_same, Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hi (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
    · simp
  · rw [Pi.single_eq_of_ne hk]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (Sigma.mk.inj_iff.mp h).1.symm

theorem isMultiHomog_pow {p : MRing ι} {a : K → ℕ} (hp : IsMultiHomog p a) (e : ℕ) :
    IsMultiHomog (p ^ e) (e • a) := by
  induction e with
  | zero => simpa using isMultiHomog_one
  | succ e ih => rw [pow_succ, succ_nsmul]; exact isMultiHomog_mul ih hp

def chartMon (c : (k : K) → ι k) (d : K → ℕ) : MRing ι :=
  ∏ k, X ⟨k, c k⟩ ^ d k

theorem isMultiHomog_chartMon (c : (k : K) → ι k) (d : K → ℕ) :
    IsMultiHomog (chartMon c d) d := by
  classical
  have h : ∀ S : Finset K, IsMultiHomog (∏ k ∈ S, (X ⟨k, c k⟩ : MRing ι) ^ d k)
      (∑ k ∈ S, d k • Pi.single k 1) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using isMultiHomog_one
    | insert k S hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X ⟨k, c k⟩) (d k)) ih
  have e : (∑ k, d k • Pi.single k 1 : K → ℕ) = d := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := h Finset.univ
  rwa [e] at this

theorem chartMon_zero (c : (k : K) → ι k) : chartMon c 0 = (1 : MRing ι) := by
  simp [chartMon]

theorem eval_chartMon (c : (k : K) → ι k) (d : K → ℕ) (z : (Σ k, ι k) → ℂ) :
    eval z (map (Int.castRingHom ℂ) (chartMon c d)) = ∏ k, z ⟨k, c k⟩ ^ d k := by
  simp [chartMon, map_prod, map_pow]

theorem exists_chartMon_notMem {W : Ideal (MRing ι)} (hW : IsArithVar W 1) :
    ∃ c : (k : K) → ι k, ∀ d : K → ℕ, chartMon c d ∉ W := by
  have hprime : W.IsPrime := hW.2.1.1
  have hrel := hW.2.1.2.2
  refine ⟨fun k ↦ (hrel k).choose, fun d h ↦ ?_⟩
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact (hrel k).choose_spec (hprime.mem_of_pow_mem _ hk)

theorem maDensity_fin_zero (φ : Fin 0 → (Fin 0 → ℂ) → ℝ) (y : Fin 0 → ℂ) : maDensity φ y = 1 := by
  simp [maDensity, mixedDisc]

theorem finsum_nonpos' {α : Sort*} {f : α → ℝ} (h : ∀ a, f a ≤ 0) : ∑ᶠ a, f a ≤ 0 := by
  have := finsum_nonneg (f := fun a ↦ -f a) fun a ↦ neg_nonneg.mpr (h a)
  rwa [finsum_neg_distrib, neg_nonneg] at this

theorem segre_torus_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (fun p ↦ c p.1 * z p) = (∏ k, c k) • segre z := by
  funext i
  simp [segre, Finset.prod_mul_distrib]

theorem ptsIntegral_nonpos (P : Ideal (MRing ι)) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z ≤ 0) : ptsIntegral P φ g ≤ 0 := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · refine integral_nonpos fun y ↦ finsum_nonpos' fun w ↦ finsum_nonpos' fun _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · rw [maDensity_fin_zero, mul_one]
      exact hg _ hγ.choose_spec.2.self_of_nhds.2.1
    · exact le_rfl
  · exact le_rfl

theorem ptsIntegral_const_ge (P : Ideal (MRing ι)) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) {t : ℝ}
    (ht : t ≤ 0) (hP : 0 < degC P) : t * degC P ≤ ptsIntegral P φ (fun _ ↦ t) := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · set Ψ := hΨ.choose
    have hvol : (volume : Measure (Fin 0 → ℂ)) = Measure.dirac (fun i ↦ i.elim0) := by
      rw [volume_pi]
      exact Measure.pi_of_empty _
    rw [hvol, integral_dirac]
    set y₀ : Fin 0 → ℂ := fun i ↦ i.elim0
    unfold degC at hP ⊢
    obtain ⟨-, hfinQ⟩ := Nat.card_pos_iff.mp hP

    let r := fun z z' : mcPts P ↦
      ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ (z' : (Σ k, ι k) → ℂ) = fun p ↦ c p.1 * (z : (Σ k, ι k) → ℂ) p
    let G : Quot r → (((k : K) → ι k) → ℂ) := Quot.lift
      (fun z : mcPts P ↦ (Ψ (segre (z : (Σ k, ι k) → ℂ)) 0)⁻¹ • segre (z : (Σ k, ι k) → ℂ))
      (by
        rintro z z' ⟨c, hc, hz'⟩
        rw [hz', segre_torus_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_smul, mul_inv]
        have hμ : (∏ k, c k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k
        congr 1
        field_simp)
    let F : fibre P Ψ y₀ → Quot r := fun w ↦ Quot.mk r ⟨w.2.choose, w.2.choose_spec.1⟩
    have hGF : ∀ w, G (F w) = w := by
      intro w
      obtain ⟨h1, h2, h3⟩ := w.2.choose_spec
      show (Ψ (segre w.2.choose) 0)⁻¹ • segre w.2.choose = (w : ((k : K) → ι k) → ℂ)
      rw [h2, h3]
      simp
    have hinj : Function.Injective F := fun a b hab ↦ Subtype.ext (by
      rw [← hGF a, ← hGF b, hab])
    have : Finite (fibre P Ψ y₀) := Finite.of_injective F hinj
    have hcard := Nat.card_le_card_of_injective F hinj
    have hfin : (fibre P Ψ y₀).Finite := Set.toFinite _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hterm : ∀ w ∈ hfin.toFinset, t ≤ sheetDensity P Ψ φ (fun _ ↦ t) y₀ w := by
      intro w _
      unfold sheetDensity
      split_ifs
      · rw [maDensity_fin_zero, mul_one]
      · exact ht
    have hsum := Finset.card_nsmul_le_sum _ _ t hterm
    rw [nsmul_eq_mul] at hsum
    have hc : (hfin.toFinset.card : ℝ) ≤ Nat.card (Quot r) := by
      rw [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq]
      exact_mod_cast hcard
    nlinarith
  · have : (0 : ℝ) ≤ degC P := Nat.cast_nonneg _
    nlinarith

variable (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → Geo.HermLine ι) → ℝ)

theorem snoc_elim0 (C : Geo.HermLine ι) :
    (Fin.snoc (Fin.elim0 : Fin 0 → Geo.HermLine ι) C : Fin 1 → _) = ![C] := by
  funext i
  fin_cases i
  rfl

theorem geoNum_zero_nonneg (V : Ideal (MRing ι)) (a : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 V a := by
  rw [geoNum]
  split_ifs <;> positivity

theorem recR_one (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → Geo.HermLine ι) (E : Geo.HermLine ι) :
    recR I P L E 1 = -arInt P 1 E L := by
  have h : divSupp P 1 = ∅ := by
    ext V
    simp only [divSupp, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hV _
    have hp : V.IsPrime := hV.1.1
    have hle : P ⊔ Ideal.span {1} ≤ V := hV.1.2
    rw [Ideal.span_singleton_one, sup_top_eq, top_le_iff] at hle
    exact hp.ne_top hle
  unfold recR
  rw [h, finsum_mem_empty, zero_sub]

theorem inter_eq_recR (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    {E : Geo.HermLine ι} (hE : IsSmoothHerm E) {d : K → ℕ} (hd : ∀ k, E.a k = d k)
    {s : MRing ι} (hs : IsMultiHomog s d) (hsW : s ∉ W) :
    I W 1 ![E] = recR I W (Fin.elim0 : Fin 0 → Geo.HermLine ι) E s := by
  have h := hI.2.2 W 0 Fin.elim0 E s d hW (fun j ↦ j.elim0) hE hd hs hsW
  rwa [snoc_elim0] at h

theorem inter_tensor (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    {A B : Geo.HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    I W 1 ![A.tensor B] = I W 1 ![A] + I W 1 ![B] := by
  have h := hI.2.1 W 0 Fin.elim0 A B hW (fun j ↦ j.elim0) hA hB
  simpa only [snoc_elim0] using h

theorem inter_congr (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    {B B' : Geo.HermLine ι} (hB : IsSmoothHerm B) (hB' : IsSmoothHerm B') {d : K → ℕ}
    (hd : ∀ k, B.a k = d k) (hd' : ∀ k, B'.a k = d k) (hh : ∀ z ∈ mcPts W, B.h z = B'.h z) :
    I W 1 ![B] = I W 1 ![B'] := by
  obtain ⟨c, hc⟩ := exists_chartMon_notMem hW
  rw [inter_eq_recR I hI hW hB hd (isMultiHomog_chartMon c d) (hc d),
    inter_eq_recR I hI hW hB' hd' (isMultiHomog_chartMon c d) (hc d)]
  exact recR_congr I W Fin.elim0 (chartMon c d) hh

theorem inter_constLine_one (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)}
    (hW : IsArithVar W 1) : I W 1 ![constLine 1 one_pos] = 0 := by
  obtain ⟨c, hc⟩ := exists_chartMon_notMem hW
  rw [inter_eq_recR I hI hW (isSmoothHerm_constLine 1 one_pos) (d := 0) (fun k ↦ rfl)
    (isMultiHomog_chartMon c 0) (hc 0), chartMon_zero, recR_one, neg_eq_zero]
  have h : logNorm (constLine (ι := ι) 1 one_pos) 1 = fun _ ↦ 0 := by
    funext z
    simp [logNorm, constLine]
  unfold arInt
  rw [h]
  simp [ptsIntegral, ptsIntegralAt, sheetDensity]

theorem inter_invLine (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    {A : Geo.HermLine ι} (hA : IsSmoothHerm A) : I W 1 ![invLine A] = -I W 1 ![A] := by
  have h1 := inter_tensor I hI hW hA (isSmoothHerm_invLine hA)
  have h2 : I W 1 ![A.tensor (invLine A)] = I W 1 ![constLine 1 one_pos] :=
    inter_congr I hI hW (isSmoothHerm_tensor hA (isSmoothHerm_invLine hA))
      (isSmoothHerm_constLine 1 one_pos) (d := 0)
      (fun k ↦ by simp [Geo.HermLine.tensor, invLine]) (fun k ↦ rfl)
      (fun z hz ↦ by
        simp only [Geo.HermLine.tensor, invLine, constLine]
        exact mul_inv_cancel₀ (A.pos z hz.1).ne')
  rw [inter_constLine_one I hI hW] at h2
  linarith

theorem inter_powLine (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    {A : Geo.HermLine ι} (hA : IsSmoothHerm A) (m : ℕ) :
    I W 1 ![powLine A m] = m * I W 1 ![A] := by
  induction m with
  | zero => simpa [powLine] using inter_constLine_one I hI hW
  | succ m ih =>
    rw [powLine, inter_tensor I hI hW (isSmoothHerm_powLine hA m) hA, ih]
    push_cast
    ring

theorem inter_constLine_le (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)}
    (hW : IsArithVar W 1) {M : ℝ} (hM0 : 0 < M) (hM : 1 ≤ M) (hdeg : 0 < degC W) :
    I W 1 ![constLine M hM0] ≤ Real.log M * degC W := by
  obtain ⟨c, hc⟩ := exists_chartMon_notMem hW
  rw [inter_eq_recR I hI hW (isSmoothHerm_constLine M hM0) (d := 0) (fun k ↦ rfl)
    (isMultiHomog_chartMon c 0) (hc 0), chartMon_zero, recR_one]
  have h : logNorm (constLine (ι := ι) M hM0) 1 = fun _ ↦ -Real.log M := by
    funext z
    simp [logNorm, constLine, Real.log_inv]
  unfold arInt
  rw [h]
  have := ptsIntegral_const_ge W (fun j z ↦ Real.log (((Fin.elim0 : Fin 0 → Geo.HermLine ι) j).h z))
    (neg_nonpos.mpr (Real.log_nonneg hM)) hdeg
  linarith

theorem inter_nonneg (hV : CurveDivVertical.Statement) (hI : IsIntersectionFamily I)
    {W : Ideal (MRing ι)} (hW : IsArithVar W 1) {E : Geo.HermLine ι} (hE : IsSmoothHerm E)
    {d : K → ℕ} (hd : ∀ k, E.a k = d k) (c : (k : K) → ι k) (hc : chartMon c d ∉ W)
    (hle : ∀ z ∈ mcPts W, ‖∏ k, z ⟨k, c k⟩ ^ d k‖ ≤ E.h z) : 0 ≤ I W 1 ![E] := by
  rw [inter_eq_recR I hI hW hE hd (isMultiHomog_chartMon c d) hc]
  have h2 : arInt W (chartMon c d) E (Fin.elim0 : Fin 0 → Geo.HermLine ι) ≤ 0 :=
    ptsIntegral_nonpos _ _ fun z hz ↦ by
      have hpos := E.pos z hz.1
      unfold logNorm
      rw [eval_chartMon]
      exact Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le)
        ((div_le_one hpos).mpr (hle z hz))
  unfold recR
  rw [sub_nonneg]
  refine le_trans h2 (finsum_nonneg fun V ↦ finsum_nonneg fun hV' ↦ ?_)
  rw [if_neg (hV K ι W _ d hW (isMultiHomog_chartMon c d) hc V hV')]
  exact mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (Int.cast_nonneg (geoNum_zero_nonneg _ _)) (Real.log_natCast_nonneg _))

theorem exists_chartMon_bound {E : Geo.HermLine ι} (hE : IsSmoothHerm E) {d : K → ℕ}
    (hd : ∀ k, E.a k = d k) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (c : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ‖∏ k, z ⟨k, c k⟩ ^ d k‖ ≤ M * E.h z := by
  set U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∑ i, ‖z ⟨k, i⟩‖ ^ 2 = 1}
  have hsq : ∀ (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k),
      ‖z ⟨k, i⟩‖ ^ 2 ≤ ∑ i', ‖z ⟨k, i'⟩‖ ^ 2 := fun z k i ↦
    Finset.single_le_sum (f := fun i' ↦ ‖z ⟨k, i'⟩‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
      (Finset.mem_univ i)
  have hSU : S ⊆ U := by
    intro z hz k
    by_contra h
    push Not at h
    have := hz k
    simp [h] at this
  have hS_le : ∀ z ∈ S, ∀ p, ‖z p‖ ≤ 1 := by
    intro z hz p
    have h1 : ‖z ⟨p.1, p.2⟩‖ ^ 2 ≤ 1 := (hz p.1) ▸ hsq z p.1 p.2
    nlinarith [norm_nonneg (z p)]
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have : S = ⋂ k, (fun z : (Σ k, ι k) → ℂ ↦ ∑ i, ‖z ⟨k, i⟩‖ ^ 2) ⁻¹' {1} := by
        ext z
        simp [S]
      rw [this]
      exact isClosed_iInter fun k ↦ isClosed_singleton.preimage (by fun_prop)
    · refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun z hz ↦ ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (hS_le z hz)
  have hcont : ContinuousOn (fun z ↦ (E.h z)⁻¹) S :=
    (hE.continuousOn.mono hSU).inv₀ fun z hz ↦ (E.pos z (hSU hz)).ne'
  obtain ⟨M₀, hM₀⟩ := hSc.bddAbove_image hcont
  refine ⟨max M₀ 1, le_max_right _ _, fun c z hz ↦ ?_⟩
  set r : K → ℝ := fun k ↦ Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2)
  have hsum : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    intro k
    obtain ⟨i, hi⟩ := hz k
    exact lt_of_lt_of_le (by positivity) (hsq z k i)
  have hr : ∀ k, 0 < r k := fun k ↦ Real.sqrt_pos.mpr (hsum k)
  set t : K → ℂ := fun k ↦ (((r k)⁻¹ : ℝ) : ℂ)
  have hnt : ∀ k, ‖t k‖ = (r k)⁻¹ := fun k ↦ by
    simp [t, abs_of_pos (hr k)]
  have ht : ∀ k, t k ≠ 0 := fun k ↦ by
    rw [← norm_ne_zero_iff, hnt]
    exact (inv_pos.mpr (hr k)).ne'
  set w : (Σ k, ι k) → ℂ := fun p ↦ t p.1 * z p
  have hw : w ∈ S := by
    intro k
    simp only [w, norm_mul, mul_pow, ← Finset.mul_sum, hnt, inv_pow]
    rw [Real.sq_sqrt (hsum k).le]
    exact inv_mul_cancel₀ (hsum k).ne'
  have hEw : E.h w = (∏ k, ‖t k‖ ^ d k) * E.h z := by
    rw [E.smul t z ht]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [hd k, zpow_natCast]
  have hmon : ‖∏ k, w ⟨k, c k⟩ ^ d k‖ = (∏ k, ‖t k‖ ^ d k) * ‖∏ k, z ⟨k, c k⟩ ^ d k‖ := by
    simp only [w, mul_pow, Finset.prod_mul_distrib, norm_mul, norm_prod, norm_pow]
  have hmon1 : ‖∏ k, w ⟨k, c k⟩ ^ d k‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) fun k _ ↦ by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hS_le w hw _)
  have hEw1 : 1 ≤ max M₀ 1 * E.h w := by
    have h1 : (E.h w)⁻¹ ≤ M₀ := hM₀ (Set.mem_image_of_mem _ hw)
    have hpos := E.pos w (hSU hw)
    calc (1 : ℝ) = (E.h w)⁻¹ * E.h w := (inv_mul_cancel₀ hpos.ne').symm
      _ ≤ max M₀ 1 * E.h w := mul_le_mul_of_nonneg_right (h1.trans (le_max_left _ _)) hpos.le
  have hT : 0 < ∏ k, ‖t k‖ ^ d k :=
    Finset.prod_pos fun k _ ↦ pow_pos (norm_pos_iff.mpr (ht k)) _
  have key : (∏ k, ‖t k‖ ^ d k) * ‖∏ k, z ⟨k, c k⟩ ^ d k‖ ≤
      (∏ k, ‖t k‖ ^ d k) * (max M₀ 1 * E.h z) := by
    rw [← hmon]
    calc ‖∏ k, w ⟨k, c k⟩ ^ d k‖ ≤ 1 := hmon1
      _ ≤ max M₀ 1 * E.h w := hEw1
      _ = (∏ k, ‖t k‖ ^ d k) * (max M₀ 1 * E.h z) := by rw [hEw]; ring
  exact le_of_mul_le_mul_left key hT

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
