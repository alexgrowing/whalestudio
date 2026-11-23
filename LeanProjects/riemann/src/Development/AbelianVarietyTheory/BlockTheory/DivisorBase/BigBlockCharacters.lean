import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters

open NumberField IsDedekindDomain
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth

section Group

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {i d : ℕ}

def pairDet (l w : Fin i → Fin d → C) : C := (Matrix.of fun a b : Fin i => ∑ e, l b e * w a e).det

def IsFrameOf (v : AddValuation C (WithTop ℝ)) (u w : Fin i → Fin d → C) : Prop :=
  IsSatFrame v w ∧ ∀ a, w a ∈ Submodule.span C (Set.range u)

def HasChars (G : LogFGL v d) (u : Fin i → Fin d → C) (r : EReal) : Prop :=
  ∃ l : Fin i → Fin d → C, (∀ b, IsCharLog G (l b)) ∧
    ∀ w : Fin i → Fin d → C, IsFrameOf v u w → toE (v (pairDet l w)) ≤ r

theorem isFrameOf_self {u : Fin i → Fin d → C} (hu : IsSatFrame v u) : IsFrameOf v u u :=
  ⟨hu, fun a => Submodule.subset_span ⟨a, rfl⟩⟩

theorem v_pairDet_eq {u w : Fin i → Fin d → C} (hu : IsSatFrame v u) (hw : IsFrameOf v u w)
    (l : Fin i → Fin d → C) : v (pairDet l w) = v (pairDet l u) := by
  choose M hM using fun a => (Submodule.mem_span_range_iff_exists_fun C).1 (hw.2 a)
  have hwe : ∀ a e, w a e = ∑ k, M a k * u k e := fun a e => by
    rw [← hM a]; simp [Finset.sum_apply]
  have hmin : ∀ r : Fin i → Fin d, (Matrix.of fun a b => w a (r b)).det =
      (Matrix.of M).det * (Matrix.of fun a b => u a (r b)).det := fun r => by
    rw [← Matrix.det_mul]; congr 1; ext a b; simp [Matrix.mul_apply, hwe]
  have hint : ∀ (x : Fin i → Fin d → C), (∀ a e, IsIntV v (x a e)) → ∀ r : Fin i → Fin d,
      0 ≤ v (Matrix.of fun a b => x a (r b)).det := fun x hx r => by
    rw [Matrix.det_apply']
    refine AddValuation.map_le_sum v fun σ _ => ?_
    rw [AddValuation.map_mul]
    refine add_nonneg ?_ ?_
    · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    · refine Finset.prod_induction _ (fun z => 0 ≤ v z) (fun a b ha hb => ?_) (by simp) fun k _ => hx _ _
      rw [AddValuation.map_mul]; exact add_nonneg ha hb
  obtain ⟨r, hr⟩ := hu.2
  obtain ⟨r', hr'⟩ := hw.1.2
  have h1 : 0 ≤ v (Matrix.of M).det := by
    have := hint w hw.1.1 r
    rwa [hmin, AddValuation.map_mul, hr, add_zero] at this
  have h2 : v (Matrix.of M).det ≤ 0 := by
    rw [hmin, AddValuation.map_mul] at hr'
    exact hr' ▸ le_add_of_nonneg_right (hint u hu.1 r')
  have h3 : pairDet l w = (Matrix.of M).det * pairDet l u := by
    unfold pairDet
    rw [← Matrix.det_mul]; congr 1; ext a b
    simp only [Matrix.mul_apply, Matrix.of_apply, hwe, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun e _ => by ring
  rw [h3, AddValuation.map_mul, le_antisymm h2 h1, zero_add]

theorem hasChars_iff {G : LogFGL v d} {u : Fin i → Fin d → C} (hu : IsSatFrame v u) (r : EReal) :
    HasChars G u r ↔ ∃ l : Fin i → Fin d → C, (∀ b, IsCharLog G (l b)) ∧ toE (v (pairDet l u)) ≤ r :=
  exists_congr fun l => and_congr_right fun _ =>
    ⟨fun h => h u (isFrameOf_self hu), fun h w hw => by rwa [v_pairDet_eq hu hw]⟩

end Group

section Prime

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def UnramIn (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop := ¬ (p : ℤ) ∣ discr E

def SplitInK (H : Host E) (p : ℕ) : Prop := (H.d : ZMod p) ≠ 0 ∧ IsSquare (-(H.d : ZMod p))

def InertInK (H : Host E) (p : ℕ) : Prop := ¬ IsSquare (-(H.d : ZMod p))

variable {H : Host E} {l : Level H} (c : Coeff l) {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime]
  (X : ValExt T p)

def embX (τ : E →+* ℂ) : 𝓞 E →+* X.C := X.ιF.comp (io.comp (embK c τ))

def vd_vp (τ : E →+* ℂ) : EReal :=
  ⨅ a ∈ differentIdeal ℤ (𝓞 E), toE (vX_vp X (embX c io X τ a))

end Prime

def BigBlockChars : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y)
      (X : ValExt T p) (f : Lt1 Dw), f.1 (H.rt : E) = H.rt0 →
      (p ≠ 2 → UnramIn E p → SplitInK H p →
        HasChars (fgl Ch X) (frame Ch X f) (((Dw.q : ℝ) / ((p : ℝ) - 1) : ℝ) : EReal)) ∧
      (p ≠ 2 → UnramIn E p → InertInK H p →
        HasChars (fgl Ch X) (frame Ch X f)
          (((Dw.q : ℝ) / ((p : ℝ) - 1) +
            (((Dw.p + Dw.q : ℕ) : ℝ) - 2 * (Dw.q : ℝ)) * (p : ℝ) / ((p : ℝ) ^ 2 - 1) : ℝ) : EReal)) ∧
      (p = 2 ∨ SplitInK H p →
        HasChars (fgl Ch X) (frame Ch X f)
          (min (((rk f : ℝ) / ((p : ℝ) - 1) : ℝ) : EReal)
            (((Dw.q : ℝ) : EReal) * ((((1 : ℝ) / ((p : ℝ) - 1) : ℝ) : EReal) + vd_vp c io X f.1))))

example {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {p : ℕ} [Fact p.Prime] {T : CDVR} {io : c.F →+* T.Fr}
    {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (f : Lt1 Dw) :
    IsFrameOf (vX_vp X) (frame Ch X f) (frame Ch X f) :=
  isFrameOf_self (isSatFrame_frame Ch X f)

example {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (τ : E →+* ℂ)
    (h : τ (H.rt : E) = H.rt0) : Dw.mult τ + Dw.q = Dw.p + Dw.q := by
  simp [Datum.mult, h]

example : ¬ IsSquare (-((7 : ℕ) : ZMod 3)) ∧ IsSquare (-((7 : ℕ) : ZMod 11)) := by decide

end GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters
