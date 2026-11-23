import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatMulVec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegerApproximationCountHolds
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EventuallyComparable
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
open scoped ComplexConjugate

namespace GlobalTheory.CuspFrom.OrbitThick

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem min_le_sum {ι : Type} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) {δ : ℝ}
    (h : δ ≤ ∏ i, a i) : min 1 δ ≤ ∑ i, a i := by
  rcases le_total 1 (∑ i, a i) with h1 | h1
  · exact (min_le_left _ _).trans h1
  refine (min_le_right _ _).trans (h.trans ?_)
  have h0 : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha i
  calc ∏ i, a i ≤ ∏ _i : ι, ∑ j, a j := Finset.prod_le_prod (fun i _ => ha i) fun i _ =>
        Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
    _ = (∑ j, a j) ^ Fintype.card ι := by simp
    _ ≤ ∑ j, a j := pow_le_of_le_one h0 h1 Fintype.card_ne_zero

theorem c_pos (τ : X.Ψ) : 0 < X.c τ := by
  have : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  unfold Data.c
  positivity

omit [NumberField E] [IsCMField E] in
theorem emb_ne_zero (τ : E →+* ℂ) {v : Fin r → E} (hv : v ≠ 0) : Data.emb τ v ≠ 0 := by
  intro h
  apply hv
  funext a
  exact (map_eq_zero τ).mp (congrFun h a)

omit [NumberField E] [IsCMField E] in
theorem emb_smul (τ : E →+* ℂ) (e : E) (v : Fin r → E) : Data.emb τ (e • v) = τ e • Data.emb τ v := by
  funext a
  simp [Data.emb]

omit [NumberField E] [IsCMField E] in
theorem emb_sub (τ : E →+* ℂ) (v w : Fin r → E) : Data.emb τ (v - w) = Data.emb τ v - Data.emb τ w := by
  funext a
  simp [Data.emb]

theorem maj_smul {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : ℂ) (v : Fin r → ℂ) :
    X.maj x τ (k • v) = ‖k‖ ^ 2 * X.maj x τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hx τ, MajorantConjugateTransfer.Hf_smul_left, MajorantConjugateTransfer.Hf_smul_right, X.Hf_self hx τ, ← mul_assoc,
    Complex.mul_conj']
  push_cast
  ring

theorem maj_sub_smul {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u : Fin r → ℂ) {e : Fin r → ℂ}
    (he : e ≠ 0) (b : ℂ) :
    X.maj x τ (u - b • e) = X.maj x τ (u - (X.Hf x τ u e / X.Hf x τ e e) • e) +
      ‖X.Hf x τ u e / X.Hf x τ e e - b‖ ^ 2 * X.maj x τ e := by
  set a := X.Hf x τ u e / X.Hf x τ e e with ha
  have hee : X.Hf x τ e e ≠ 0 := by
    rw [X.Hf_self hx τ]
    exact_mod_cast (X.maj_pos hx τ he).ne'
  have h1 : X.Hf x τ (u - a • e) e = 0 := by
    rw [MajorantConjugateTransfer.Hf_sub_left, MajorantConjugateTransfer.Hf_smul_left, ha, div_mul_cancel₀ _ hee, sub_self]
  have h2 : X.Hf x τ e (u - a • e) = 0 := by
    rw [← MajorantConjugateTransfer.Hf_conj X hx, h1, map_zero]
  have h3 : u - b • e = (u - a • e) - (b - a) • e := by
    rw [sub_smul]; abel
  apply Complex.ofReal_injective
  rw [h3, ← X.Hf_self hx τ, MajorantConjugateTransfer.Hf_sub_left, MajorantConjugateTransfer.Hf_sub_right X x τ _ (u - a • e),
    MajorantConjugateTransfer.Hf_sub_right X x τ _ (u - a • e), MajorantConjugateTransfer.Hf_smul_right, h1, MajorantConjugateTransfer.Hf_smul_left, h2,
    X.Hf_self hx τ, X.Hf_self hx τ, maj_smul X hx, norm_sub_rev b a]
  push_cast
  ring

theorem exists_herm_ne_zero {ξ : Fin r → E} (hξ : ξ ≠ 0) : ∃ η ∈ X.Λ, herm X.Gm ξ η ≠ 0 := by
  by_contra h
  push Not at h
  apply hξ
  refine Matrix.eq_zero_of_vecMul_eq_zero X.Gm_det ?_
  funext b
  obtain ⟨l, hl, hm⟩ := LatFin.exists_int_smul_mem X.Λ X.Λ_span (Pi.single b 1)
  have h1 := h _ hm
  have h2 : herm X.Gm ξ (l • Pi.single b 1) = Matrix.vecMul ξ X.Gm b * l := by
    unfold herm cc
    simp only [Matrix.vecMul, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc
      simp [Pi.single_eq_of_ne hc]
    · simp
  rw [h2] at h1
  have hl' : (l : E) ≠ 0 := Int.cast_ne_zero.mpr hl
  simpa [hl'] using h1

theorem den_ne_zero : (X.den : E) ≠ 0 := fun h => X.den_ne (RingOfIntegers.coe_eq_zero_iff.mp h)

theorem prod_norm_pos {γ : E} (hγ : γ ≠ 0) : 0 < ∏ τ : X.Ψ, ‖τ.1 γ‖ ^ 2 :=
  Finset.prod_pos fun τ _ => pow_pos (norm_pos_iff.mpr ((map_ne_zero τ.1).mpr hγ)) 2

theorem prod_lower_of_ne {y : Frame X.Ψ r}
    (hcs : ∀ (τ : X.Ψ) (v w : Fin r → ℂ), ‖hermC τ.1 X.Gm v w‖ ^ 2 ≤ X.maj y τ v * X.maj y τ w)
    {ξ v : Fin r → E} (hξ : ξ ∈ X.Λ) (hv : v ∈ X.Λ) (h : herm X.Gm v ξ ≠ 0) :
    ∏ τ, X.c τ ^ 2 ≤ (∏ τ, X.c τ * X.maj y τ (Data.emb τ.1 v)) *
      ((∏ τ : X.Ψ, ‖τ.1 (X.den : E)‖ ^ 2) * ∏ τ, X.c τ * X.maj y τ (Data.emb τ.1 ξ)) := by
  have h1 := QuadraticCoefficientForms.one_le_prod_norm X _ (X.Λ_int v hv ξ hξ) (mul_ne_zero (den_ne_zero X) h)
  have h2 : 0 ≤ ∏ τ, X.c τ ^ 2 := Finset.prod_nonneg fun τ _ => sq_nonneg _
  refine (le_mul_of_one_le_right h2 h1).trans ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun τ _ => by positivity) fun τ _ => ?_
  rw [map_mul, norm_mul, mul_pow, emb_herm]
  have := mul_le_mul_of_nonneg_left (hcs τ (Data.emb τ.1 v) (Data.emb τ.1 ξ))
    (show 0 ≤ X.c τ ^ 2 * ‖τ.1 (X.den : E)‖ ^ 2 by positivity)
  nlinarith

theorem prod_lower_of_smul {y : Frame X.Ψ r} (hy : y ∈ X.dom) {ξ η : Fin r → E} (hη : η ∈ X.Λ)
    (h : herm X.Gm ξ η ≠ 0) {e : E} (he : e ≠ 0) (hv : e • ξ ∈ X.Λ) :
    ∏ τ, X.c τ * X.maj y τ (Data.emb τ.1 ξ) ≤ (∏ τ, X.c τ * X.maj y τ (Data.emb τ.1 (e • ξ))) *
      ∏ τ : X.Ψ, ‖τ.1 ((X.den : E) * herm X.Gm ξ η)‖ ^ 2 := by
  have h0 := X.Λ_int _ hv η hη
  rw [HermitianTraceFormVanishing.herm_smul_left] at h0
  have h1 := QuadraticCoefficientForms.one_le_prod_norm X _ h0 (mul_ne_zero (den_ne_zero X) (mul_ne_zero he h))
  have h2 : 0 ≤ ∏ τ, X.c τ * X.maj y τ (Data.emb τ.1 ξ) := Finset.prod_nonneg fun τ _ =>
    mul_nonneg (c_pos X τ).le (MajorantConjugateTransfer.maj_nonneg X hy τ _)
  refine (le_mul_of_one_le_right h2 h1).trans (le_of_eq ?_)
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [emb_smul, maj_smul X hy]
  simp only [map_mul, norm_mul]
  ring

theorem finite_of_maj_le {x : Frame X.Ψ r} (hx : x ∈ X.dom) (B : X.Ψ → ℝ) :
    {v : Fin r → E | v ∈ X.Λ ∧ ∀ τ, X.maj x τ (Data.emb τ.1 v) ≤ B τ}.Finite := by
  obtain ⟨c, C, hc, h⟩ := MajorantContinuity.compact_bounds X (isCompact_singleton (x := x))
    (Set.singleton_subset_iff.mpr hx)
  refine (LatFin.finite_vectors r X (∑ τ, Real.sqrt (B τ / c))).subset ?_
  rintro v ⟨hv, hb⟩
  refine ⟨hv, fun τ a => ?_⟩
  have h1 := (h x rfl τ (Data.emb τ.1 v)).1.trans (hb τ)
  have h2 : ‖Data.emb τ.1 v‖ ≤ Real.sqrt (B τ / c) := by
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc]
    linarith
  calc ‖τ.1 (v a)‖ ≤ ‖Data.emb τ.1 v‖ := norm_le_pi_norm (Data.emb τ.1 v) a
    _ ≤ Real.sqrt (B τ / c) := h2
    _ ≤ _ := Finset.single_le_sum (f := fun τ => Real.sqrt (B τ / c))
      (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ τ)

theorem dist_line_lower {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : ξ ∈ X.Λ) (hξ0 : ξ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ X.Λ, (∀ e : E, v ≠ e • ξ) → ∀ a : X.Ψ → ℂ,
      δ ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v - a τ • Data.emb τ.1 ξ) := by
  have hne : Nonempty X.Ψ := Fintype.card_pos_iff.mp (QuadraticCoefficientForms.card_Psi_pos X)
  obtain ⟨τ0⟩ := hne
  set ρ : ℝ := 2 * (fdeg E : ℝ) ^ 2 * rdE E with hρ
  let A : X.Ψ → (Fin r → E) → ℂ := fun τ w => X.Hf x τ (Data.emb τ.1 w) (Data.emb τ.1 ξ) /
    X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)
  let m : X.Ψ → (Fin r → E) → ℝ := fun τ w => X.maj x τ (Data.emb τ.1 w - A τ w • Data.emb τ.1 ξ)
  have hP : ∀ τ w b, X.maj x τ (Data.emb τ.1 w - b • Data.emb τ.1 ξ) =
      m τ w + ‖A τ w - b‖ ^ 2 * X.maj x τ (Data.emb τ.1 ξ) := fun τ w b =>
    maj_sub_smul X hx τ _ (emb_ne_zero τ.1 hξ0) b
  have hm : ∀ τ w b, m τ w ≤ X.maj x τ (Data.emb τ.1 w - b • Data.emb τ.1 ξ) := fun τ w b => by
    rw [hP]
    have := MajorantConjugateTransfer.maj_nonneg X hx τ (Data.emb τ.1 ξ)
    have : 0 ≤ ‖A τ w - b‖ ^ 2 * X.maj x τ (Data.emb τ.1 ξ) := by positivity
    linarith
  set F : Set (Fin r → E) := {w | (w ∈ X.Λ ∧ ∀ τ, X.maj x τ (Data.emb τ.1 w) ≤
    1 / X.c τ + ρ ^ 2 * X.maj x τ (Data.emb τ.1 ξ)) ∧ ∀ e : E, w ≠ e • ξ} with hF
  have hFf : F.Finite := (finite_of_maj_le X hx _).subset fun w hw => hw.1
  have hpos : ∀ t ∈ m τ0 '' F, (0 : ℝ) < id t := by
    rintro _ ⟨w, hw, rfl⟩
    refine X.maj_pos hx τ0 fun h0 => ?_
    refine one_ne_zero (QuadraticCoefficientForms.coef_zero hξ0 hw.2 τ0.1 (-A τ0 w) 1 ?_)
    rw [← h0, neg_smul, one_smul]
    abel
  obtain ⟨μ, hμ, hμF⟩ := (hFf.image (m τ0)).isCompact.exists_forall_le' continuousOn_id hpos
  have hc0 := c_pos X τ0
  refine ⟨min 1 (X.c τ0 * μ), lt_min one_pos (mul_pos hc0 hμ), fun v hv hve a => ?_⟩
  have hterm : ∀ τ, X.c τ * m τ v ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v - a τ • Data.emb τ.1 ξ) :=
    fun τ => (mul_le_mul_of_nonneg_left (hm τ v (a τ)) (c_pos X τ).le).trans
      (Finset.single_le_sum (f := fun τ => X.c τ * X.maj x τ (Data.emb τ.1 v - a τ • Data.emb τ.1 ξ))
        (fun τ _ => mul_nonneg (c_pos X τ).le (MajorantConjugateTransfer.maj_nonneg X hx τ _)) (Finset.mem_univ τ))
  rcases le_total 1 (∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v - a τ • Data.emb τ.1 ξ)) with h1 | h1
  · exact (min_le_left _ _).trans h1
  refine (min_le_right _ _).trans (le_trans ?_ (hterm τ0))
  obtain ⟨α, hα⟩ := (integerApproximationCount_holds r X).1 fun τ => A τ v
  have hw : v - (α : E) • ξ ∈ F := by
    refine ⟨⟨X.Λ.sub_mem hv (X.Λ.smul_mem α hξ), fun τ => ?_⟩, fun e he => hve (e + α) ?_⟩
    · rw [emb_sub, emb_smul, hP]
      have h2 : m τ v ≤ 1 / X.c τ := by
        rw [le_div_iff₀ (c_pos X τ), mul_comm]
        exact (hterm τ).trans h1
      have h3 : ‖A τ v - τ.1 (α : E)‖ ^ 2 ≤ ρ ^ 2 := by
        rw [norm_sub_rev]
        exact pow_le_pow_left₀ (norm_nonneg _) (hα τ) 2
      have := mul_le_mul_of_nonneg_right h3 (MajorantConjugateTransfer.maj_nonneg X hx τ (Data.emb τ.1 ξ))
      linarith
    · rw [add_smul, ← he, sub_add_cancel]
  have h4 : μ ≤ m τ0 (v - (α : E) • ξ) := hμF _ ⟨_, hw, rfl⟩
  have h5 := hm τ0 (v - (α : E) • ξ) (A τ0 v - τ0.1 (α : E))
  have h6 : Data.emb τ0.1 (v - (α : E) • ξ) - (A τ0 v - τ0.1 (α : E)) • Data.emb τ0.1 ξ =
      Data.emb τ0.1 v - A τ0 v • Data.emb τ0.1 ξ := by
    rw [emb_sub, emb_smul, sub_smul]
    abel
  rw [h6] at h5
  exact mul_le_mul_of_nonneg_left (h4.trans h5) hc0.le

theorem orbitThick_of_flowMaj : FlowMajSt → OrbitThickSt := by
  intro hF E _ _ _ r X ξ hξ x hx
  obtain ⟨hF1, hF2⟩ := hF E r X
  have hne : Nonempty X.Ψ := Fintype.card_pos_iff.mp (QuadraticCoefficientForms.card_Psi_pos X)
  obtain ⟨η, hη, hξη⟩ := exists_herm_ne_zero X hξ.2.2
  obtain ⟨δ3, hδ3, h3⟩ := dist_line_lower X hx hξ.1 hξ.2.2
  set P : ℝ := ∏ τ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) with hP
  have hPp : 0 < P := Finset.prod_pos fun τ _ =>
    mul_pos (c_pos X τ) (X.maj_pos hx τ (emb_ne_zero τ.1 hξ.2.2))
  have hD := prod_norm_pos X (den_ne_zero X)
  have hK := prod_norm_pos X (mul_ne_zero (den_ne_zero X) hξη)
  have hC : 0 < ∏ τ, X.c τ ^ 2 := Finset.prod_pos fun τ _ => pow_pos (c_pos X τ) 2
  set δ1 : ℝ := (∏ τ, X.c τ ^ 2) / ((∏ τ : X.Ψ, ‖τ.1 (X.den : E)‖ ^ 2) * P) with hδ1
  set δ2 : ℝ := P / ∏ τ : X.Ψ, ‖τ.1 ((X.den : E) * herm X.Gm ξ η)‖ ^ 2 with hδ2
  have hδ1p : 0 < δ1 := div_pos hC (mul_pos hD hPp)
  have hδ2p : 0 < δ2 := div_pos hPp hK
  refine ⟨Real.sqrt (min (min (min 1 δ1) (min 1 δ2)) δ3), Real.sqrt_pos.mpr
    (lt_min (lt_min (lt_min one_pos hδ1p) (lt_min one_pos hδ2p)) hδ3), fun s hy ht => ?_⟩
  have hPy : ∏ τ, X.c τ * X.maj (X.flow ξ s x) τ (Data.emb τ.1 ξ) = P := by
    simp only [Data.tt, one_div, Finset.prod_inv_distrib] at ht
    exact inv_injective ht
  refine Real.sqrt_le_sqrt (le_csInf ⟨_, ξ, hξ.1, hξ.2.2, rfl⟩ ?_)
  rintro _ ⟨v, hv, hv0, rfl⟩
  have hnn : ∀ τ, 0 ≤ X.c τ * X.maj (X.flow ξ s x) τ (Data.emb τ.1 v) := fun τ =>
    mul_nonneg (c_pos X τ).le (MajorantConjugateTransfer.maj_nonneg X hy τ _)
  by_cases h : herm X.Gm v ξ = 0
  · by_cases he : ∃ e : E, v = e • ξ
    · obtain ⟨e, rfl⟩ := he
      have he0 : e ≠ 0 := by
        rintro rfl
        exact hv0 (zero_smul _ _)
      refine ((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_sum _ hnn ?_)
      rw [hδ2, div_le_iff₀ hK, ← hPy]
      exact prod_lower_of_smul X hy hη hξη he0 hv
    · push Not at he
      refine (min_le_right _ _).trans ((h3 v hv he fun τ => X.Hf x τ (Data.emb τ.1 v) (Data.emb τ.1 ξ) /
        X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)).trans (Finset.sum_le_sum fun τ _ => ?_))
      refine mul_le_mul_of_nonneg_left ?_ (c_pos X τ).le
      have h4 := hF1 ξ hξ x hx s hy τ (Data.emb τ.1 v) (by rw [← emb_herm, h, map_zero])
      have h5 := maj_sub_smul X hx τ (Data.emb τ.1 v) (emb_ne_zero τ.1 hξ.2.2) 0
      rw [zero_smul, sub_zero, sub_zero] at h5
      have h6 := mul_nonneg (sq_nonneg ‖X.Hf x τ (Data.emb τ.1 v) (Data.emb τ.1 ξ) /
        X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖) (MajorantConjugateTransfer.maj_nonneg X hy τ (Data.emb τ.1 ξ))
      linarith
  · refine ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_sum _ hnn ?_)
    rw [hδ1, div_le_iff₀ (mul_pos hD hPp), ← hPy]
    exact prod_lower_of_ne X (fun τ v w => (hF2 _ hy τ v w).1) hξ.1 hv h

end GlobalTheory.CuspFrom.OrbitThick
