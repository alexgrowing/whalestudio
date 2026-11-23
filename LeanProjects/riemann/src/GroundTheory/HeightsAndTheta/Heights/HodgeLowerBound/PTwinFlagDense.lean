import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HypLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HypLineMore
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HypLineBis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HypLineAlt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HypLineTer
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.EventuallyInFrameDomain
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.MCoordIdealGenericPointEq
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagModelAlt

namespace FlagDense

section Generic

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem aeval_eq_zero_of_mem {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (hm : g ∈ mCoordIdeal y) :
    aeval y g = 0 := by
  have h0 : mConeMap y g = 0 := hm
  rw [mConeMap_of_isMultiHomog y hg] at h0
  have hX : (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)
  exact C_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hX)

theorem isValueAt_ne_zero (hgen : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = 0 → f ∈ mCoordIdeal y)
    {s : Ω} {v : ℂ} (hv : IsValueAt y s z v) (hs : s ≠ 0) : v ≠ 0 := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  intro h0
  have hgz : eval z (map (Int.castRingHom ℂ) g) = 0 := (div_eq_zero_iff.1 h0).resolve_right hz0
  have hgy := aeval_eq_zero_of_mem hg (hgen g hgz)
  rw [heq] at hgy
  exact mul_ne_zero hs hy hgy

theorem isUnitAt_of_mem_chartRing (hgen : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = 0 → f ∈ mCoordIdeal y)
    {c : (k : K) → ι k} (hyc : segreCoord y c ≠ 0) (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) {r : Ω}
    (hr : r ∈ chartRing ℤ (segreCoord y) c) (hr0 : r ≠ 0) : IsUnitAt y r z := by
  obtain ⟨v, hv⟩ := exists_isValueAt_of_mem_chartRing hyc hz hr
  exact ⟨v, hv, isValueAt_ne_zero hgen hv hr0⟩

theorem exists_chart (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ c : (k : K) → ι k, segreCoord y c ≠ 0 ∧ ∀ k, z ⟨k, c k⟩ ≠ 0 := by
  classical
  choose c hc using hz.1
  refine ⟨c, Finset.prod_ne_zero_iff.2 fun k _ => ?_, hc⟩
  intro h0
  have hm := mem_mCoordIdeal_of_aeval_eq_zero y (isMultiHomog_X_single (ι := ι) ⟨k, c k⟩) (by simpa using h0)
  have := hz.2 _ hm
  simp only [map_X, eval_X] at this
  exact hc k this

theorem isValueAt_coord {p : Σ k, ι k} {c : (k : K) → ι k} (hy : y ⟨p.1, c p.1⟩ ≠ 0)
    (hz : z ⟨p.1, c p.1⟩ ≠ 0) : IsValueAt y ((y ⟨p.1, c p.1⟩)⁻¹ * y p) z (z p / z ⟨p.1, c p.1⟩) := by
  classical
  refine ⟨_, X p, X ⟨p.1, c p.1⟩, isMultiHomog_X_single p, isMultiHomog_X_single (ι := ι) ⟨p.1, c p.1⟩,
    by simpa using hy, ?_, by simpa using hz, by simp⟩
  simp only [aeval_X]
  field_simp

end Generic

section Frames

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}

omit [∀ k, Fintype (ι k)] in

theorem exists_isFrameOver (W : ChartBundle ℤ (segreCoord y) N E) (c : (k : K) → ι k)
    (hyc : segreCoord y c ≠ 0) : ∃ (f : Ω) (b : Fin N → E), IsFrameOver y W c f b := by
  obtain ⟨m, f, cc, hf, -, hsum, hb⟩ := W.frame c hyc
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra hne
    push Not at hne
    simp [hne] at hsum
  obtain ⟨b, hli, -, hiff⟩ := hb l
  exact ⟨f l, b, hyc, hf l, hl, hli, hiff⟩

omit [∀ k, Fintype (ι k)] in

theorem exists_pow_smul_mem {c : (k : K) → ι k} {W : ChartBundle ℤ (segreCoord y) N E} {f : Ω}
    {b : Fin N → E} (hfr : IsFrameOver y W c f b) (p : Fin N) : ∃ n : ℕ, f ^ n • b p ∈ W.lat c := by
  classical
  refine (hfr.2.2.2.2 (b p)).2 ⟨Pi.single p 1, fun q => ⟨0, ?_⟩, ?_⟩
  · rw [pow_zero, one_mul]
    rcases eq_or_ne q p with rfl | hq
    · rw [Pi.single_eq_same]; exact Subalgebra.one_mem _
    · rw [Pi.single_eq_of_ne hq]; exact Subalgebra.zero_mem _
  · simp [Pi.single_apply, ite_smul]

theorem exists_isValueAt_dualSec {c : (k : K) → ι k} {W : ChartBundle ℤ (segreCoord y) N E} {bt : K → ℤ}
    {r : ℕ} {φ : E [⋀^Fin r]→ₗ[Ω] Ω} (hφ : IndefiniteRowSideFullHecke.LowerBoundFree.IsDualSectionOver y W c bt φ) {f : Ω}
    {b : Fin N → E} (hfr : IsFrameOver y W c f b) (hzP : z ∈ mcPts (mCoordIdeal y))
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) (hf : IsUnitAt y f z) (q : Fin r → Fin N) :
    ∃ v, IsValueAt y (φ (b ∘ q) * IndefiniteRowSideFullHecke.LowerBoundFree.twistFactor y c bt) z v := by
  choose n hn using exists_pow_smul_mem hfr
  have hmem := hφ (fun a => f ^ n (q a) • b (q a)) (fun a => hn (q a))
  have e : φ (fun a => f ^ n (q a) • b (q a)) = f ^ (∑ a, n (q a)) * φ (b ∘ q) := by
    rw [show (fun a => f ^ n (q a) • b (q a)) = fun a => f ^ n (q a) • (b ∘ q) a from rfl,
      AlternatingMap.map_smul_univ, smul_eq_mul, Finset.prod_pow_eq_pow_sum]
  rw [e, mul_assoc] at hmem
  exact exists_isValueAt_of_pow_mul_mem hzP hfr.1 hz hf hmem

end Frames

theorem det_gvar_ne_zero {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (τ : Ψ) :
    (Matrix.of fun a p => (X (Sum.inr (τ, a, p)) : MvPolynomial (GV D) ℂ)).det ≠ 0 := by
  classical
  let g : Fin D.N × Fin D.N → GV D := fun ap => Sum.inr (τ, ap.1, ap.2)
  have hg : Function.Injective g := by
    rintro ⟨a, p⟩ ⟨a', p'⟩ he
    simp only [g, Sum.inr.injEq, Prod.mk.injEq] at he
    rw [he.2.1, he.2.2]
  have e : (Matrix.of fun a p => (X (Sum.inr (τ, a, p)) : MvPolynomial (GV D) ℂ)) =
      (rename g).toRingHom.mapMatrix (Matrix.mvPolynomialX (Fin D.N) (Fin D.N) ℂ) := by
    ext a p
    simp [g, Matrix.mvPolynomialX]
  rw [e, ← RingHom.map_det]
  exact (map_ne_zero_iff _ (rename_injective g hg)).2 (Matrix.det_mvPolynomialX_ne_zero _ _)

theorem proof (h₁ : FlagPolynomialValue.Statement) (h₂ : FlagGenericPointValue.Statement)
    (h₃ : FlagGenericPointScale.Statement) (h₄ : FlagGenericPoint.Statement) : FlagDense.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl P h
  classical
  obtain ⟨z0, hz0, hgen⟩ := h₄ (mCoordIdeal D.y) _ D.arith
  obtain ⟨c, hyc, hzc⟩ := exists_chart hz0
  have hyk : ∀ k, D.y ⟨k, c k⟩ ≠ 0 := fun k => by
    have := hyc
    simp only [segreCoord] at this
    exact Finset.prod_ne_zero_iff.1 this k (Finset.mem_univ _)
  choose f b hfr using fun τ => exists_isFrameOver (D.W τ) c hyc
  have hfu : ∀ τ, IsUnitAt D.y (f τ) z0 := fun τ =>
    isUnitAt_of_mem_chartRing hgen hyc hzc (hfr τ).2.1 (hfr τ).2.2.1
  have hV : ∀ τ (i : Fin D.N) (m : Fin (P.M τ i)) (q : Fin ((i : ℕ) + 1) → Fin D.N),
      ∃ v, IsValueAt D.y (P.gen τ i m (b τ ∘ q) * IndefiniteRowSideFullHecke.LowerBoundFree.twistFactor D.y c P.b) z0 v :=
    fun τ i m q => exists_isValueAt_dualSec (P.global τ i m c hyc) (hfr τ) hz0 hzc (hfu τ) q
  choose VT hVT using hV
  refine ⟨b, fun τ => (hfr τ).2.2.2.1, fun F hF => ?_⟩

  have htw0 : IndefiniteRowSideFullHecke.LowerBoundFree.twistFactor D.y c P.b ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyk k)
  let α : K ⊕ (Ψ × Fin (D.N - 1)) → Ω :=
    Sum.elim (fun k => (D.y ⟨k, c k⟩)⁻¹) (fun _ => IndefiniteRowSideFullHecke.LowerBoundFree.twistFactor D.y c P.b)
  have hα : ∀ β, IsUnit (α β) := by
    rintro (k | q)
    · exact isUnit_iff_ne_zero.2 (inv_ne_zero (hyk k))
    · exact isUnit_iff_ne_zero.2 htw0
  have hF' := (h₃ Pl D.y (wedgeVals Pl b) α hα F).not.2 hF
  let x' : (Σ k, ι k) → ℂ := fun p => z0 p / z0 ⟨p.1, c p.1⟩
  let V' : WedgeVals Pl ℂ := fun q m cc => VT q.1 (stepTw q.2) (Fin.cast (h.M_eq q.1 q.2) m) cc
  have hx : ∀ p, IsValueAt D.y (α (Sum.inl p.1) * D.y p) z0 (x' p) := fun p =>
    isValueAt_coord (hyk p.1) (hzc p.1)
  have hVv : ∀ q m cc, IsValueAt D.y (α (Sum.inr q) * wedgeVals Pl b q m cc) z0 (V' q m cc) := by
    intro q m cc
    show IsValueAt D.y (IndefiniteRowSideFullHecke.LowerBoundFree.twistFactor D.y c P.b *
      Pl.gen q.1 q.2 m (exteriorPower.ιMulti Ω _ (b q.1 ∘ cc))) z0 _
    rw [h.gen_eq, mul_comm]
    exact hVT _ _ _ _
  have hval := h₁ D.y z0 _ _ (h₂ Pl z0 _ x' _ V' hx hVv) F

  have hQ0 : aeval (genPtR Pl x' V') F ≠ 0 := by
    obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.1 hF'
    intro h0
    exact isValueAt_ne_zero hgen (hval μ) hμ (by rw [h0, coeff_zero])

  obtain ⟨w, hw⟩ : ∃ w : GV D.toComponentData → ℂ, eval w (aeval (genPtR Pl x' V') F *
      (∏ β, X (Sum.inl β)) * ∏ τ, (Matrix.of fun a p =>
        (X (Sum.inr (τ, a, p)) : MvPolynomial (GV D.toComponentData) ℂ)).det) ≠ 0 := by
    by_contra hne
    push Not at hne
    refine mul_ne_zero (mul_ne_zero hQ0 (Finset.prod_ne_zero_iff.2 fun β _ => X_ne_zero _))
      (Finset.prod_ne_zero_iff.2 fun τ _ => det_gvar_ne_zero D.toComponentData τ)
      (MvPolynomial.funext fun x => by rw [hne x, map_zero])
  rw [map_mul, map_mul, map_prod, map_prod] at hw
  have hwQ := (mul_ne_zero_iff.1 (mul_ne_zero_iff.1 hw).1).1
  have hwT := (mul_ne_zero_iff.1 (mul_ne_zero_iff.1 hw).1).2
  have hwg := (mul_ne_zero_iff.1 hw).2
  have hwT' : ∀ β, w (Sum.inl β) ≠ 0 := fun β => by
    have := Finset.prod_ne_zero_iff.1 hwT β (Finset.mem_univ _)
    rwa [eval_X] at this
  have hwg' : ∀ τ, (Matrix.of fun a p => w (Sum.inr (τ, a, p))).det ≠ 0 := fun τ => by
    have := Finset.prod_ne_zero_iff.1 hwg τ (Finset.mem_univ _)
    rw [RingHom.map_det] at this
    convert this using 2
    ext a p
    simp

  let t : K → ℂ := fun k => w (Sum.inl (Sum.inl k)) / z0 ⟨k, c k⟩
  have ht : ∀ k, t k ≠ 0 := fun k => div_ne_zero (hwT' _) (hzc k)
  let z := torusSmul t z0
  have hzP : z ∈ mcPts (mCoordIdeal D.y) := ComponentDataEquivalence.mcPts_torus D.arith.2.1.2.1 hz0 ht
  have hzck : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k => mul_ne_zero (ht k) (hzc k)
  let Z : ℂ := ∏ k, z ⟨k, c k⟩ ^ P.b k
  have hZ : Z ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hzck k)
  let G : Ψ → Matrix (Fin D.N) (Fin D.N) ℂ := fun τ => Matrix.of fun p a => w (Sum.inr (τ, a, p))
  let lam : Ψ → Fin D.N → ℂ := fun τ i =>
    if hi : (i : ℕ) < D.N - 1 then w (Sum.inl (Sum.inr (τ, ⟨i, hi⟩))) / Z else 1
  let wv : ∀ q : Ψ × Fin D.N, Fin (P.M q.1 q.2) → ℂ := fun q m =>
    lam q.1 q.2 * ∑ qq : Fin ((q.2 : ℕ) + 1) → Fin D.N,
      (∏ a, IndefiniteRowSideFullHecke.LowerBoundFree.firstCols (G q.1) ((q.2 : ℕ) + 1) q.2.isLt (qq a) a) * (VT q.1 q.2 m qq * Z)
  refine ⟨IndefiniteRowSideFullHecke.LowerBoundFree.yJoin P z wv, ⟨hzP, fun τ => ⟨c, f τ, b τ, G τ, lam τ, hfr τ,
    HermMetricEq.inFrameDomain_smul t ht ⟨hzc, hfu τ⟩, ?_, ?_, fun i m =>
      ⟨_, ⟨fun qq => VT τ i m qq * Z, fun qq => ⟨hzck, VT τ i m qq,
        HermMetricEq.isValueAt_iff.2 ((HermMetricEq.isValueAt_iff.1 (hVT τ i m qq)).smul t ht), rfl⟩, rfl⟩,
        rfl⟩⟩⟩, ?_⟩
  · show (Matrix.transpose (Matrix.of fun a p => w (Sum.inr (τ, a, p)))).det ≠ 0
    rw [Matrix.det_transpose]
    exact hwg' τ
  · intro i
    simp only [lam]
    split_ifs
    · exact div_ne_zero (hwT' _) hZ
    · exact one_ne_zero

  suffices key : ((eval (IndefiniteRowSideFullHecke.LowerBoundFree.yJoin P z wv)).comp (map (Int.castRingHom ℂ))).comp
      (forget h).toRingHom = (eval w).comp (aeval (genPtR Pl x' V')).toRingHom by
    have := congrArg (fun φ => φ F) key
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this]
    exact hwQ
  refine MvPolynomial.ringHom_ext (fun n => by simp) fun j => ?_
  rcases j with ⟨k | ⟨τ, i⟩, t'⟩
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, forget,
      rename_X, map_X, eval_X, aeval_X]
    change z ⟨k, t'⟩ = eval w (X (Sum.inl (Sum.inl k)) * C (x' ⟨k, t'⟩))
    simp only [eval_mul, eval_X, eval_C, z, torusSmul, t, x']
    field_simp
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, forget,
      rename_X, map_X, eval_X, aeval_X]
    change lam τ (stepTw i) * _ = eval w (X (Sum.inl (Sum.inr (τ, i))) *
      ∑ cc : Fin ((i : ℕ) + 1) → Fin D.N, (∏ a, X (Sum.inr (τ, headIdx (step_le i) a, cc a))) *
        C (V' (τ, i) t' cc))
    have hl : lam τ (stepTw i) = w (Sum.inl (Sum.inr (τ, i))) / Z := by
      simp only [lam]
      rw [dif_pos (show ((stepTw i : Fin D.N) : ℕ) < D.N - 1 from i.isLt)]
      rfl
    have e : ∀ a v : ℂ, w (Sum.inl (Sum.inr (τ, i))) / Z * (a * (v * Z)) =
        w (Sum.inl (Sum.inr (τ, i))) * (a * v) := fun a v => by field_simp
    simp only [eval_mul, eval_X, eval_C, eval_sum, eval_prod]
    rw [hl, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun qq _ => e _ _

end FlagDense

end GroundTheory.Heights₂.Heights.LowerBoundFree
