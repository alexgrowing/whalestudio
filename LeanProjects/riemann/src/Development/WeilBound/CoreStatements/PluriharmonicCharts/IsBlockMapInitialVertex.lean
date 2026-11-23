import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MCoordIdealLeOfHomog
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTransferIdealEq
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFnFieldTrdeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagFormDiv
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

local instance (priority := 2000) intAlg2 {Φ : Type} [Field Φ] : Algebra ℤ (RatFunc Φ) := Ring.toIntAlgebra _

open GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]

abbrev iW (ι : K → Type) (k₀ : K) : Option K → Type := fun o => ι (o.getD k₀)

def ext2 {R : Type} (y : (Σ k, ι k) → R) (k₀ : K) (A : ι k₀ → R) : (Σ o : Option K, ι (o.getD k₀)) → R
  | ⟨some k, m⟩ => y ⟨k, m⟩
  | ⟨none, m⟩ => A m

theorem isBlockMap_initial_vertex (k₀ : K) : IsBlockMap (ι := ι) (ι' := iW ι k₀) some (v₀ k₀) := by
  refine ⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    cases h
    rfl
  · rintro ⟨k', i⟩ ⟨k, rfl⟩
    exact ⟨⟨k, i⟩, rfl⟩

def polyPen {R : Type} [CommRing R] (y : (Σ k, ι k) → R) (k₀ : K) (A B : ι k₀ → R) :
    (Σ o : Option K, ι (o.getD k₀)) → Polynomial R :=
  ext2 (fun q => Polynomial.C (y q)) k₀ fun m => Polynomial.C (A m) + Polynomial.X * Polynomial.C (B m)

variable (y : (Σ k, ι k) → Φ) (k₀ : K) (A B : ι k₀ → Φ)

theorem penCo_eq_poly (q) : penCo y k₀ A B RatFunc.X q = algebraMap (Polynomial Φ) (RatFunc Φ) (polyPen y k₀ A B q) := by
  rcases q with ⟨_ | k, m⟩ <;> simp [penCo, polyPen, ext2, -Polynomial.X_mul_C]

theorem ideal_pen_poly : mCoordIdeal (penCo y k₀ A B RatFunc.X) = RingHom.ker (coneOver (polyPen y k₀ A B)) :=
  mCoordIdeal_eq (algebraMap (Polynomial Φ) (RatFunc Φ)) (IsFractionRing.injective _ _) _ _ (fun _ => 1)
    (fun _ => one_ne_zero) fun q => by rw [one_mul, penCo_eq_poly]

theorem penCo_zero : penCo y k₀ A B 0 = fun q => algebraMap Φ (RatFunc Φ) (ext2 y k₀ A q) := by
  funext q
  rcases q with ⟨_ | k, m⟩ <;> simp [penCo, ext2]

theorem ideal_pen_zero : mCoordIdeal (penCo y k₀ A B 0) = mCoordIdeal (ext2 y k₀ A) := by
  rw [penCo_zero]
  exact CoordinateConeArithVar.mCoordIdeal_comp _ _

theorem pen_le_zero : mCoordIdeal (penCo y k₀ A B RatFunc.X) ≤ mCoordIdeal (ext2 y k₀ A) := by
  rw [ideal_pen_poly]
  intro f hf
  have hf' : coneOver (polyPen y k₀ A B) f = 0 := hf
  show mConeMap _ f = 0
  rw [mConeMap_eq (Polynomial.evalRingHom 0) (polyPen y k₀ A B) _ (fun _ => 1) (fun q => by
    rcases q with ⟨_ | k, m⟩ <;> simp [polyPen, ext2]), hf', map_zero, map_zero]

theorem imageZ_eq {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v) (w : (Σ k, ι' k) → Φ) :
    imageZ v (mCoordIdeal w) = mCoordIdeal (w ∘ v) := by
  ext f
  show mConeMap w (rename v f) = 0 ↔ mConeMap (w ∘ v) f = 0
  rw [CPts.mConeMap_rename hb]
  exact map_eq_zero_iff _ (rename_injective _ hb.1)

theorem image_pen (t : RatFunc Φ) : imageZ (v₀ k₀) (mCoordIdeal (penCo y k₀ A B t)) = mCoordIdeal y := by
  rw [imageZ_eq (isBlockMap_initial_vertex k₀)]
  exact CoordinateConeArithVar.mCoordIdeal_comp (algebraMap Φ (RatFunc Φ)) y

def planeMap : MRing (iW ι k₀) →+* MvPolynomial (Fin 2) (MvPolynomial K Φ) :=
  eval₂Hom (Int.castRingHom _)
    (ext2 (fun q => C (C (y q) * X q.1)) k₀ fun m => C (C (A m)) * X 0 + C (C (B m)) * X 1)

theorem ideal_pen_plane : mCoordIdeal (penCo y k₀ A B RatFunc.X) = RingHom.ker (planeMap y k₀ A B) := by
  apply le_antisymm
  · rw [ideal_pen_poly]
    let S := MvPolynomial (Fin 2) (MvPolynomial K Φ)
    let E := FractionRing S
    let i : S →+* E := algebraMap S E
    have hU : i (X 0) ≠ 0 := (map_ne_zero_iff i (IsFractionRing.injective S E)).2 (X_ne_zero _)
    let ω₀ : Polynomial Φ →+* E := Polynomial.eval₂RingHom (i.comp ((C : _ →+* S).comp C)) (i (X 1) / i (X 0))
    let ω : MvPolynomial (Option K) (Polynomial Φ) →+* E :=
      eval₂Hom ω₀ fun o => o.elim (i (X 0)) fun k => i (C (X k))
    have e : ω.comp (coneOver (polyPen y k₀ A B)).toRingHom = i.comp (planeMap y k₀ A B) := by
      refine MvPolynomial.ringHom_ext (fun r => by simp) fun q => ?_
      rcases q with ⟨_ | k, m⟩
      · simp only [ω, ω₀, coneOver, planeMap, polyPen, ext2, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, aeval_X, map_mul, map_add, eval₂Hom_C, eval₂Hom_X', Option.elim,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
        rw [add_mul, mul_right_comm (i (X 1) / i (X 0)), div_mul_cancel₀ _ hU, mul_comm (i (X 1))]
      · simp only [ω, ω₀, coneOver, planeMap, polyPen, ext2, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, aeval_X, map_mul, eval₂Hom_C, eval₂Hom_X', Option.elim,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    intro f hf
    have hf' : coneOver (polyPen y k₀ A B) f = 0 := hf
    have := RingHom.congr_fun e f
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hf', map_zero] at this
    exact (map_eq_zero_iff i (IsFractionRing.injective S E)).1 this.symm
  · let χ₀ : MvPolynomial K Φ →+* MvPolynomial (Option K) (RatFunc Φ) :=
      eval₂Hom ((C : RatFunc Φ →+* _).comp (algebraMap Φ (RatFunc Φ))) fun k => X (some k)
    let χ : MvPolynomial (Fin 2) (MvPolynomial K Φ) →+* MvPolynomial (Option K) (RatFunc Φ) :=
      eval₂Hom χ₀ ![X none, C RatFunc.X * X none]
    have e : χ.comp (planeMap y k₀ A B) = (mConeMap (penCo y k₀ A B RatFunc.X)).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun r => by simp) fun q => ?_
      rcases q with ⟨_ | k, m⟩
      · simp only [χ, χ₀, mConeMap, planeMap, penCo, ext2, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, aeval_X, map_mul, map_add, eval₂Hom_C, eval₂Hom_X', Matrix.cons_val_zero,
          Matrix.cons_val_one]
        ring
      · simp only [χ, χ₀, mConeMap, planeMap, penCo, ext2, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, aeval_X, map_mul, eval₂Hom_C, eval₂Hom_X']
    intro f hf
    have hf' : planeMap y k₀ A B f = 0 := hf
    have := RingHom.congr_fun e f
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hf', map_zero] at this
    exact this.symm

theorem ker_plane_le {A' B' : ι k₀ → Φ} (a b c d : Φ) (hA : ∀ m, A' m = a * A m + b * B m)
    (hB : ∀ m, B' m = c * A m + d * B m) :
    RingHom.ker (planeMap y k₀ A B) ≤ RingHom.ker (planeMap y k₀ A' B') := by
  let σ : MvPolynomial (Fin 2) (MvPolynomial K Φ) →+* MvPolynomial (Fin 2) (MvPolynomial K Φ) :=
    eval₂Hom C ![C (C a) * X 0 + C (C c) * X 1, C (C b) * X 0 + C (C d) * X 1]
  have e : σ.comp (planeMap y k₀ A B) = planeMap y k₀ A' B' := by
    refine MvPolynomial.ringHom_ext (fun r => by simp) fun q => ?_
    rcases q with ⟨_ | k, m⟩
    · simp only [σ, planeMap, ext2, RingHom.comp_apply, map_mul, map_add, eval₂Hom_C, eval₂Hom_X',
        Matrix.cons_val_zero, Matrix.cons_val_one, hA, hB]
      ring
    · simp only [σ, planeMap, ext2, RingHom.comp_apply, eval₂Hom_C, eval₂Hom_X']
  intro f hf
  rw [RingHom.mem_ker] at hf ⊢
  rw [← e, RingHom.comp_apply, hf, map_zero]

variable {y k₀ B}

theorem PenFrame.ker_eq {cf : Φ} {e : K → ℤ} {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (Fr : PenFrame y k₀ B cf e z c) :
    RingHom.ker (planeMap y k₀ (fun m => y ⟨k₀, m⟩) B) = RingHom.ker (planeMap y k₀ Fr.p Fr.r) := by
  have h1 := Fr.ε_ne
  have h2 := Fr.γ_ne
  refine le_antisymm (ker_plane_le _ _ _ _ Fr.ε 0 Fr.δ Fr.γ (fun m => ?_) fun m => ?_)
    (ker_plane_le _ _ _ _ Fr.ε⁻¹ 0 (-(Fr.δ / (Fr.γ * Fr.ε))) Fr.γ⁻¹ (fun m => ?_) fun m => ?_)
  · rw [Fr.p_eq]; ring
  · rw [Fr.r_eq]; ring
  · rw [Fr.p_eq]; field_simp; ring
  · rw [Fr.p_eq, Fr.r_eq]; field_simp; ring

theorem aeval_scale' {R : Type} [Field R] (u : K → R) (w : (Σ k, ι k) → R) {s : MRing ι} {d : K → ℕ}
    (hs : IsMultiHomog s d) : aeval (fun p => u p.1 * w p) s = (∏ k, u k ^ d k) * aeval w s :=
  GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor.aeval_scale u w s d hs

open CoordinateConeArithVar

theorem aeval_ratioPt {c : ∀ k, ι k} {s : MRing ι} {d : K → ℕ} (hs : IsMultiHomog s d) :
    aeval (ratioPt y c) s = (∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k) * aeval y s := by
  rw [← aeval_scale' (fun k => (y ⟨k, c k⟩)⁻¹) y hs]
  congr 2
  funext p
  rw [ratioPt, div_eq_mul_inv, mul_comm]

theorem HasVal.mem_ratioField [CharZero Φ] {z : (Σ k, ι k) → L} (hz : IsPt y z) {c : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {s : Φ} {v : L} (h : HasVal y z s v) : s ∈ ratioField y c := by
  obtain ⟨d, g, h, hg, hh, h0, e, -⟩ := h
  have h1 := hz.aeval_ne hh h0
  have hp : (∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (hc k))
  have : s = aeval (ratioPt y c) g / aeval (ratioPt y c) h := by
    rw [aeval_ratioPt hg, aeval_ratioPt hh, e, mul_div_mul_left _ _ hp, mul_div_cancel_right₀ _ h1]
  rw [this, ← coe_aeval_ratioPtL, ← coe_aeval_ratioPtL]
  exact div_mem (Subtype.property _) (Subtype.property _)

theorem arith_of_birational [CharZero Φ] [Nonempty K] (hb : Birational y) (h0 : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) {n : ℕ}
    (ht : Algebra.trdeg ℤ Φ = n) : IsArithVar (mCoordIdeal y) (n + 1) := by
  have hprime : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have hhor : IsHorizontal (mCoordIdeal y) := horizontal y
  choose c hc using h0
  refine ⟨‹_›, ⟨hprime, isMultiHomogIdeal y, relevant y c hc⟩, hhor, ?_⟩
  have htr := ConeTrdeg.full K ι Φ y hb (fun k => ⟨c k, hc k⟩) hhor
  rw [ht] at htr
  have hA := IntDomainDim.full (MRing ι ⧸ mCoordIdeal y) (algebraMap_injective _ hhor)
  rw [hA, htr]
  simp only [map_add, map_natCast]
  norm_cast
  omega

theorem trdeg_ratFunc [CharZero Φ] : Algebra.trdeg ℤ (RatFunc Φ) = Algebra.trdeg ℤ Φ + 1 := by
  have h1 : Algebra.trdeg Φ (RatFunc Φ) = 1 := by
    have : Algebra.IsAlgebraic (Polynomial Φ) (RatFunc Φ) := IsLocalization.isAlgebraic _ (nonZeroDivisors _)
    rw [← trdeg_add_eq Φ (Polynomial Φ), Polynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero]
  rw [← trdeg_add_eq ℤ Φ (A := RatFunc Φ), h1]

theorem birational_of_regO (h : ∀ s, s ∈ regO y y) : Birational y := fun s => by
  obtain ⟨v, d, g, h, hg, hh, h0, e, -⟩ := h s
  exact ⟨d, g, h, hg, hh, h0, e⟩

theorem regO_of_birational (hb : Birational y) (s : Φ) : HasVal y y s s := by
  obtain ⟨d, g, h, hg, hh, h0, e⟩ := hb s
  exact ⟨d, g, h, hg, hh, h0, e, e⟩

theorem birational_extension_two (hb : Birational y) (A : ι k₀ → Φ) : Birational (ext2 y k₀ A) :=
  birational_of_regO fun s => ⟨s, HasVal.pull (isBlockMap_initial_vertex k₀) (RingHom.id Φ) (y' := ext2 y k₀ A)
    (z' := ext2 y k₀ A) rfl (regO_of_birational hb s)⟩

theorem sum_smul_penCo_none_eq_one {α : ι k₀ → Φ} (hA : ∑ m, α m * A m = 1) (hB : ∑ m, α m * B m = 0) (t : RatFunc Φ) :
    ∑ m, algebraMap Φ (RatFunc Φ) (α m) * penCo y k₀ A B t ⟨none, m⟩ = 1 := by
  simp only [penCo, mul_add, Finset.sum_add_distrib, mul_left_comm _ t, ← Finset.mul_sum, ← map_mul, ← map_sum, hA, hB]
  simp

theorem pencil_coordinate_sum {β : ι k₀ → Φ} (hA : ∑ m, β m * A m = 0) (hB : ∑ m, β m * B m = 1) (t : RatFunc Φ) :
    ∑ m, algebraMap Φ (RatFunc Φ) (β m) * penCo y k₀ A B t ⟨none, m⟩ = t := by
  simp only [penCo, mul_add, Finset.sum_add_distrib, mul_left_comm _ t, ← Finset.mul_sum, ← map_mul, ← map_sum, hA, hB]
  simp

theorem exists_ne_of_sum {R σ : Type} [Field R] [Fintype σ] {a b : σ → R} (h : ∑ m, a m * b m ≠ 0) :
    ∃ m, b m ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (by simp [hc])

theorem pen_blocks (h0 : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) {α : ι k₀ → Φ} (hA : ∑ m, α m * A m = 1)
    (hB : ∑ m, α m * B m = 0) (t : RatFunc Φ) : ∀ o, ∃ i, penCo y k₀ A B t ⟨o, i⟩ ≠ 0 := by
  rintro (_ | k)
  · exact exists_ne_of_sum ((sum_smul_penCo_none_eq_one (y := y) A hA hB t).trans_ne one_ne_zero)
  · obtain ⟨i, hi⟩ := h0 k
    exact ⟨i, (map_ne_zero _).2 hi⟩

theorem birational_pen (hb : Birational y) (h0 : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) {α β : ι k₀ → Φ} (h1 : ∑ m, α m * A m = 1)
    (h2 : ∑ m, α m * B m = 0) (h3 : ∑ m, β m * A m = 0) (h4 : ∑ m, β m * B m = 1) :
    Birational (penCo y k₀ A B RatFunc.X) := by
  set w := penCo y k₀ A B RatFunc.X
  have hw := pen_blocks A h0 h1 h2 RatFunc.X
  have hpt : IsPt w w := isPt_self hw
  have hC : ∀ s : Φ, algebraMap Φ (RatFunc Φ) s ∈ regO w w := fun s => by
    obtain ⟨d, g, h, hg, hh, h0, e⟩ := hb s
    refine ⟨_, HasVal.pull (isBlockMap_initial_vertex k₀) (algebraMap Φ (RatFunc Φ)) (y' := w) (z' := w) (y := y) rfl
      (w := algebraMap Φ (RatFunc Φ) s) ⟨d, g, h, hg, hh, ?_, e, ?_⟩⟩
    · show aeval (algebraMap Φ (RatFunc Φ) ∘ y) h ≠ 0
      rw [CPts.aeval_comp_ringHom]
      exact (map_ne_zero _).2 h0
    · show aeval (algebraMap Φ (RatFunc Φ) ∘ y) g = _ * aeval (algebraMap Φ (RatFunc Φ) ∘ y) h
      rw [CPts.aeval_comp_ringHom, CPts.aeval_comp_ringHom, e, map_mul]
  have hinv : ∀ s ∈ regO w w, s⁻¹ ∈ regO w w := fun s ⟨v, hv⟩ => by
    by_cases h : v = 0
    · rw [← hasVal_self_eq hv, h, _root_.inv_zero]; exact zero_mem _
    · exact ⟨_, hv.inv hpt h⟩
  obtain ⟨c, hc⟩ := hw none
  have hlin : ∀ μ : ι k₀ → Φ, (∑ m, algebraMap Φ (RatFunc Φ) (μ m) * w ⟨none, m⟩) / w ⟨none, c⟩ ∈ regO w w := fun μ => by
    rw [Finset.sum_div]
    refine sum_mem fun m _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (hC _) ⟨_, hasVal_ratio hpt (k := none) m c hc⟩
  have hX : RatFunc.X ∈ regO w w := by
    have a := hlin α
    have b := hlin β
    rw [sum_smul_penCo_none_eq_one A h1 h2] at a
    rw [pencil_coordinate_sum A h3 h4] at b
    have := mul_mem b (hinv _ a)
    rwa [one_div, inv_inv, div_mul_cancel₀ _ hc] at this
  have hP : ∀ p : Polynomial Φ, algebraMap _ (RatFunc Φ) p ∈ regO w w := fun p => by
    induction p using Polynomial.induction_on with
    | C a => simpa using hC a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a h => rw [pow_succ, ← mul_assoc, map_mul]; exact mul_mem h (by simpa using hX)
  refine birational_of_regO fun s => ?_
  induction s using RatFunc.induction_on with
  | f p q hq => rw [div_eq_mul_inv]; exact mul_mem (hP p) (hinv _ (hP q))

theorem arith_pen [CharZero Φ] {cf : Φ} {e : K → ℤ} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (Fr : PenFrame y k₀ B cf e y c) {d : ℕ} (hY : IsArithVar (mCoordIdeal y) (d + 1)) :
    IsArithVar (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X)) (d + 2) ∧
      IsArithVar (mCoordIdeal (ext2 y k₀ fun m => y ⟨k₀, m⟩)) (d + 1) := by
  have hpt : IsPt y y := isPt_self fun k => ⟨c k, hc k⟩
  let F := ratioField y c
  let Y : (Σ k, ι k) → F := ratioPtL y c
  have hbir : Birational Y := birational y c hc
  have hYc : ∀ k, Y ⟨k, c k⟩ = 1 := fun k => Subtype.ext (div_self (hc k))
  have hY0 : ∀ k, ∃ i, Y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, by rw [hYc]; exact one_ne_zero⟩
  have htr : Algebra.trdeg ℤ F = d :=
    FnFieldTrdeg.full K ι F Y d hbir (by rw [mCoordIdeal_ratioPtL y c hc]; exact hY)
  have hsc : ∀ q, y q = y ⟨q.1, c q.1⟩ * (Y q : Φ) := fun q => (mul_div_cancel₀ _ (hc q.1)).symm
  constructor
  · let p : ι k₀ → F := fun m => ⟨Fr.p m, (Fr.hp m).mem_ratioField hpt hc⟩
    let r : ι k₀ → F := fun m => ⟨Fr.r m, (Fr.hr m).mem_ratioField hpt hc⟩
    let α : ι k₀ → F := fun m => ⟨Fr.α m, (Fr.hα m).mem_ratioField hpt hc⟩
    let β : ι k₀ → F := fun m => ⟨Fr.β m, (Fr.hβ m).mem_ratioField hpt hc⟩
    have h1 : ∑ m, α m * p m = 1 := Subtype.ext (by simpa [α, p] using Fr.αp)
    have h2 : ∑ m, α m * r m = 0 := Subtype.ext (by simpa [α, r] using Fr.αr)
    have h3 : ∑ m, β m * p m = 0 := Subtype.ext (by simpa [β, p] using Fr.βp)
    have h4 : ∑ m, β m * r m = 1 := Subtype.ext (by simpa [β, r] using Fr.βr)
    have e1 : mCoordIdeal (penCo y k₀ Fr.p Fr.r RatFunc.X) = mCoordIdeal (penCo Y k₀ p r RatFunc.X) := by
      rw [ideal_pen_poly Y]
      refine mCoordIdeal_eq ((algebraMap (Polynomial Φ) (RatFunc Φ)).comp (Polynomial.mapRingHom (algebraMap F Φ)))
        ((IsFractionRing.injective _ _).comp (Polynomial.map_injective _ (algebraMap F Φ).injective)) _ _
        (fun o => o.elim 1 fun k => algebraMap Φ (RatFunc Φ) (y ⟨k, c k⟩)) ?_ ?_
      · rintro (_ | k)
        · exact one_ne_zero
        · exact (map_ne_zero _).2 (hc k)
      · rintro ⟨_ | k, m⟩
        · simp [penCo, polyPen, ext2, p, r, -Polynomial.X_mul_C]
        · simp only [penCo, polyPen, ext2, Option.elim, RingHom.comp_apply, Polynomial.coe_mapRingHom,
            Polynomial.map_C, RatFunc.algebraMap_C]
          rw [hsc ⟨k, m⟩, map_mul]
          rfl
    rw [ideal_pen_plane, Fr.ker_eq, ← ideal_pen_plane, e1]
    refine arith_of_birational (birational_pen p hbir hY0 h1 h2 h3 h4) (pen_blocks p hY0 h1 h2 _) (n := d + 1) ?_
    rw [trdeg_ratFunc, htr]
    simp
  · have e1 : mCoordIdeal (ext2 y k₀ fun m => y ⟨k₀, m⟩) = mCoordIdeal (ext2 Y k₀ fun m => Y ⟨k₀, m⟩) := by
      rw [mCoordIdeal_eq (RingHom.id F) Function.injective_id (ext2 Y k₀ fun m => Y ⟨k₀, m⟩)
        (ext2 Y k₀ fun m => Y ⟨k₀, m⟩) (fun _ => 1)
        (fun _ => one_ne_zero) fun q => (one_mul _).symm]
      refine mCoordIdeal_eq (algebraMap F Φ) (algebraMap F Φ).injective _ _
        (fun o => y ⟨o.getD k₀, c _⟩) (fun o => hc _) ?_
      rintro ⟨_ | k, m⟩
      · exact hsc ⟨k₀, m⟩
      · exact hsc ⟨k, m⟩
    rw [e1]
    refine arith_of_birational (birational_extension_two hbir _) ?_ htr
    rintro (_ | k)
    · exact hY0 k₀
    · exact hY0 k

end PositivityTheory.Xgp.W
