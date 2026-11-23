import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open TrivSqZeroExt hiding map lift
open scoped Classical

namespace GlobalTheory.FlagTan

theorem det_eq_prod_diag_of_height {m R : Type} [Fintype m] [DecidableEq m] [CommRing R] (P : Matrix m m R)
    (b : m → ℤ) (h : ∀ k j, P k j ≠ 0 → k = j ∨ b j < b k) : P.det = ∏ k, P k k := by
  rw [Matrix.det_apply, Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    suffices ∏ i, P (σ i) i = 0 by rw [this, smul_zero]
    by_contra hne
    have h1 : ∀ i, P (σ i) i ≠ 0 := fun i hi => hne (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra hc
      exact hσ (Equiv.ext fun i => by_contra fun k => hc ⟨i, k⟩)
    have := Finset.sum_lt_sum (s := Finset.univ) (f := b) (g := fun i => b (σ i))
      (fun j _ => (h _ _ (h1 j)).elim (fun e => by rw [e]) le_of_lt)
      ⟨i, Finset.mem_univ _, (h _ _ (h1 i)).resolve_left hi⟩
    rw [Equiv.sum_comp σ b] at this
    exact lt_irrefl _ this
  · simp

theorem prod_pairs_lt {G : Type} [CommGroup G] {n : ℕ} (x : Fin n → G) :
    ∏ q : {q : Fin n × Fin n // q.1 < q.2}, ((x q.1.1)⁻¹ * x q.1.2) =
      ∏ i, x i ^ (((Finset.Iio i).card : ℤ) - (Finset.Ioi i).card) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun q : Fin n × Fin n => q.1 < q.2) (by simp)
    (fun q => (x q.1)⁻¹ * x q.2), Finset.prod_mul_distrib, Finset.prod_filter, Finset.prod_filter,
    Fintype.prod_prod_type, Fintype.prod_prod_type_right, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  dsimp only
  rw [← Finset.prod_filter, ← Finset.prod_filter, Finset.prod_const, Finset.prod_const, zpow_sub, mul_comm]
  simp only [zpow_natCast, inv_pow, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem IsHalf.prod_univ {Φ : Finset (E →+* ℂ)} (h : IsHalf Φ) {G : Type} [CommMonoid G] (g : (E →+* ℂ) → G) :
    ∏ σ, g σ = ∏ τ ∈ Φ, (g τ * g (conjEmb τ)) := by
  rw [Finset.prod_mul_distrib, ← Finset.prod_mul_prod_compl Φ]
  congr 1
  refine Finset.prod_bij' (fun σ _ => conjEmb σ) (fun σ _ => conjEmb σ) (fun σ hσ => ?_) (fun σ hσ => ?_)
    (fun σ _ => conjEmb_conjEmb σ) (fun σ _ => conjEmb_conjEmb σ) fun σ _ => by rw [conjEmb_conjEmb]
  · rw [h, conjEmb_conjEmb]; exact Finset.mem_compl.1 hσ
  · exact Finset.mem_compl.2 ((h σ).1 hσ)

theorem prod_char_eq {Φ : Finset (E →+* ℂ)} (h : IsHalf Φ) {G : Type} [CommGroup G] (t : Ix Dw → G) :
    (∏ k : HIx Dw Φ, (t (some ⟨conjEmb k.1.1, k.2.1⟩) * t (some ⟨k.1.1, k.2.2⟩))) *
      ∏ k : VIx Dw, ((t (some ⟨k.1, k.2.1.1⟩))⁻¹ * t (some ⟨k.1, k.2.1.2⟩)) = ∏ k, t k ^ detTanEx Dw k := by
  have e1 : ∏ k : HIx Dw Φ, (t (some ⟨conjEmb k.1.1, k.2.1⟩) * t (some ⟨k.1.1, k.2.2⟩)) =
      ∏ σ, ∏ i, t (some ⟨σ, i⟩) ^ Dw.mult (conjEmb σ) := by
    rw [h.prod_univ, Fintype.prod_sigma, ← Finset.prod_coe_sort Φ]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Fintype.prod_prod_type, conjEmb_conjEmb]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow]
    exact mul_comm _ _
  rw [e1, Fintype.prod_sigma, Fintype.prod_option, Fintype.prod_sigma, ← Finset.prod_mul_distrib]
  simp only [detTanEx, zpow_zero, one_mul]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [prod_pairs_lt fun i => t (some ⟨σ, i⟩), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_add, zpow_natCast, mul_comm]

variable {K : Type} [Field K] [Algebra c.F K] {K₀ : Type} [CommRing K₀] [Algebra c.F K₀] {ι : Type} [Fintype ι]

theorem exists_move {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K} {a : K}
    {y y' : FrPt Xo c K} (h : FrChg g a y y') {v' : FrPt Xo c (DualNumber K)} (hv : IsDef y' v') :
    ∃ w, IsDef y w ∧ FrChg (fun τ => (g τ).map (cst c K)) (cst c K a) w v' := by
  obtain ⟨g', a', hg', h'⟩ := (frChg_exists_unique E H Dw l Xo c K y' y).1 h.1.symm
  have C := frChg_calculus E H Dw l Xo c K
  have D := frChg_calculus E H Dw l Xo c (DualNumber K)
  obtain ⟨e, e'⟩ := (frChg_exists_unique E H Dw l Xo c K y' y').2 _ _ _ _ ((C.1 _ _ _ _ _ _ _ h').1 h) (C.2.1 y')
  obtain ⟨w, hw, -⟩ := existsUnique_frChg E H Dw l Xo c _ v' (fun τ => (g' τ).map (cst c K))
    (Units.map (cst c K).toRingHom.toMonoidHom a') fun τ => by
      have := (hg' τ).map (cst c K).toRingHom
      rwa [RingHom.map_det] at this
  refine ⟨w, (frMap_iff_frChg hw hv).2 ?_, (D.1 _ _ _ _ _ _ _ hw).2 ?_⟩
  · convert h' using 2 with τ
    · ext i j; simp
    · rfl
  · convert D.2.1 v' using 2 with τ
    · rw [← Matrix.map_mul, congrFun e τ, Matrix.map_one _ (map_zero _) (map_one _)]
    · exact (map_mul (cst c K) a a').symm.trans (by rw [e', map_one])

theorem isVert_move {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K} {a : Kˣ}
    {y y' : FrPt Xo c K} (h : FrChg g a y y') (hg : ∀ τ, g τ * g' τ = 1) {N : FIx Dw → K}
    {w v' : FrPt Xo c (DualNumber K)} (hv : IsVert y' N v')
    (hw : FrChg (fun τ => (g τ).map (cst c K)) (cst c K a) w v') :
    IsVert y (fun k => k.elim (N none) fun q =>
      (g' q.1 * (Matrix.of fun i j => N (some ⟨q.1, i, j⟩)) * g q.1) q.2.1 q.2.2) w := by
  have D := frChg_calculus E H Dw l Xo c (DualNumber K)
  obtain ⟨y₀', h₀', hs⟩ := hv
  obtain ⟨y₀, h₀⟩ := exists_frMap (cst c K) y
  have k1 := (D.1 _ _ _ _ _ _ _ ((frMap_iff_frChg h h₀).1 h₀')).1 hs
  obtain ⟨w', hw', -⟩ := existsUnique_isShift (fun k : FIx Dw => k.elim (N none) fun q =>
      (g' q.1 * (Matrix.of fun i j => N (some ⟨q.1, i, j⟩)) * g q.1) q.2.1 q.2.2) y₀
  have k2 : FrChg (fun τ => (g τ).map (cst c K)) (cst c K a) w' v' := by
    refine (D.1 _ _ _ _ _ _ _ hw').2 ?_
    convert k1 using 1
    · funext τ
      have : g τ * (g' τ * (Matrix.of fun i j => N (some ⟨τ, i, j⟩)) * g τ) =
          (Matrix.of fun i j => N (some ⟨τ, i, j⟩)) * g τ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg, Matrix.one_mul]
      ext i j
      · simp [unip, Matrix.mul_apply, fst_sum, Matrix.one_apply]
      · have := congrFun (congrFun this i) j
        rw [Matrix.mul_apply, Matrix.mul_apply] at this
        simpa [unip, Matrix.mul_apply (M := Matrix.map _ _), Matrix.mul_apply (N := Matrix.map _ _), snd_sum] using this
    · ext <;> simp [unip₀, mul_comm]
  obtain ⟨G, A, -, k3⟩ := (frChg_exists_unique E H Dw l Xo c _ v' w).1 hw.1.symm
  obtain ⟨e, e'⟩ := (frChg_exists_unique E H Dw l Xo c _ w w).2 _ _ _ _ ((D.1 _ _ _ _ _ _ _ hw).1 k3) (D.2.1 w)
  have k4 := (D.1 _ _ _ _ _ _ _ k2).1 k3
  rw [e, e'] at k4
  obtain rfl : w = w' :=
    (existsUnique_frChg E H Dw l Xo c _ w' (fun _ => 1) 1 fun _ => by simp).unique k4 (D.2.1 w')
  exact ⟨y₀, h₀, hw'⟩

end GlobalTheory.FlagTan
