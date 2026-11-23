import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.LiftBoundOfHypotheses
import Formalism.SharpRestriction.GrowthBounds.Lemma5aAt
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

section Gen

theorem geQ_gen (y : WithTop ℚ) (t : ℝ) :
    Formalism.MainNotions.PlaneGramData.geQ y t ↔ ((t : ℝ) : WithTop ℝ) ≤ y.map (fun q : ℚ => (q : ℝ)) := by
  induction y using WithTop.recTopCoe with
  | top => simp [Formalism.MainNotions.PlaneGramData.geQ]
  | coe q => simp [Formalism.MainNotions.PlaneGramData.geQ]

theorem leQ_gen (y : WithTop ℚ) (t : ℝ) :
    Formalism.MainNotions.PlaneGramData.leQ y t ↔ y.map (fun q : ℚ => (q : ℝ)) ≤ ((t : ℝ) : WithTop ℝ) := by
  induction y using WithTop.recTopCoe with
  | top => simp [Formalism.MainNotions.PlaneGramData.leQ]
  | coe q => simp [Formalism.MainNotions.PlaneGramData.leQ]

theorem map_cast_add (a : WithTop ℚ) (q : ℚ) :
    (a + (q : WithTop ℚ)).map (fun q : ℚ => (q : ℝ)) = a.map (fun q : ℚ => (q : ℝ)) + (((q : ℚ) : ℝ) : WithTop ℝ) := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    rw [← WithTop.coe_add, WithTop.map_coe, WithTop.map_coe, ← WithTop.coe_add]
    push_cast
    rfl

theorem map_cast_mono : Monotone (fun y : WithTop ℚ => y.map (fun q : ℚ => (q : ℝ))) := by
  intro a b h
  induction a using WithTop.recTopCoe with
  | top =>
    rw [top_le_iff] at h
    subst h
    exact le_rfl
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe b =>
      simp only [WithTop.map_coe, WithTop.coe_le_coe] at h ⊢
      exact_mod_cast h

theorem map_cast_eq_zero (y : WithTop ℚ) : y = 0 ↔ y.map (fun q : ℚ => (q : ℝ)) = 0 := by
  induction y using WithTop.recTopCoe with
  | top => simp
  | coe q =>
    rw [WithTop.map_coe, ← WithTop.coe_zero, ← WithTop.coe_zero, WithTop.coe_inj, WithTop.coe_inj]
    exact_mod_cast Iff.rfl

end Gen

section Base

open Formalism.MainNotions.G.GLWeightTheory

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vK_one' (p : ℕ) : Formalism.MainNotions.G.vK p (1 : Formalism.MainNotions.G.KK O) = 0 := by
  have h := valuation_algebraMap_eq_alt (O := O) p 1 one_ne_zero
  rw [map_one] at h
  rw [h, dvr_order_unit_eq_zero isUnit_one]
  simp

def vQ (p : ℕ) (_S : Formalism.MainNotions.G.UniformizedDVR p O) : AddValuation (Formalism.MainNotions.G.KK O) (WithTop ℚ) :=
  AddValuation.of (fun x => Formalism.MainNotions.G.vK p x) (valuation_zero_alt p) (vK_one' p) (fun x y => valuation_add_ge_min p x y)
    (fun x y => valuation_mul_alt p x y)

theorem vQ_apply (S : Formalism.MainNotions.G.UniformizedDVR p O) (x : Formalism.MainNotions.G.KK O) : vQ p S x = Formalism.MainNotions.G.vK p x := rfl

theorem vQ_nat (hp : p.Prime) (S : Formalism.MainNotions.G.UniformizedDVR p O) (n : ℕ) (hn : n ≠ 0) :
    vQ p S (n : Formalism.MainNotions.G.KK O) = ((padicValNat p n : ℚ) : WithTop ℚ) := by
  rw [vQ_apply]
  exact valuation_natCast_padicVal hp S n hn

theorem dvrHyp (S : Formalism.MainNotions.G.UniformizedDVR p O) {n' : ℕ} (hG : Formalism.MainNotions.G.AdmissibleDVR p n' O) : DVRHyp (vQ p S) p := by
  haveI := Fact.mk hG.prime
  refine ⟨hG.prime, hG.five_le, ?_⟩
  rw [vQ_nat hG.prime S p hG.prime.ne_zero, padicValNat_self]
  simp

theorem vQ_nonneg_iff (S : Formalism.MainNotions.G.UniformizedDVR p O) (x : Formalism.MainNotions.G.KK O) :
    0 ≤ vQ p S x ↔ ∃ o : O, x = algebraMap O (Formalism.MainNotions.G.KK O) o := by
  rw [vQ_apply]
  exact valuation_nonneg_iff_integral S x

theorem geQ_iff (S : Formalism.MainNotions.G.UniformizedDVR p O) (x : Formalism.MainNotions.G.KK O) (t : ℝ) :
    Formalism.MainNotions.PlaneGramData.geQ (Formalism.MainNotions.G.vK p x) t ↔ ((t : ℝ) : WithTop ℝ) ≤ vR (vQ p S) x := geQ_gen _ t

theorem leQ_iff (S : Formalism.MainNotions.G.UniformizedDVR p O) (x : Formalism.MainNotions.G.KK O) (t : ℝ) :
    Formalism.MainNotions.PlaneGramData.leQ (Formalism.MainNotions.G.vK p x) t ↔ vR (vQ p S) x ≤ ((t : ℝ) : WithTop ℝ) := leQ_gen _ t

theorem geQ_nat_iff (S : Formalism.MainNotions.G.UniformizedDVR p O) (x : Formalism.MainNotions.G.KK O) (c : ℕ) :
    Formalism.MainNotions.PlaneGramData.geQ (Formalism.MainNotions.G.vK p x) (c : ℝ) ↔ ((c : ℕ) : WithTop ℚ) ≤ vQ p S x := by
  rw [geQ_gen, vQ_apply]
  generalize Formalism.MainNotions.G.vK p x = y
  induction y using WithTop.recTopCoe with
  | top => simp
  | coe q =>
    rw [WithTop.map_coe, ← WithTop.coe_natCast, WithTop.coe_le_coe, WithTop.coe_le_coe]
    constructor <;> intro h <;> exact_mod_cast h

theorem geZ_iff (x : WithTop ℤ) (t : ℝ) : Formalism.MainNotions.PlaneGramData.geZ x t ↔ ((t : ℝ) : WithTop ℝ) ≤ toR x := by
  induction x using WithTop.recTopCoe with
  | top => simp [Formalism.MainNotions.PlaneGramData.geZ, toR]
  | coe k => simp [Formalism.MainNotions.PlaneGramData.geZ, toR]

theorem fact_ne_zero' {σ : Type} (α : σ →₀ ℕ) : fact α ≠ 0 := by
  unfold fact Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _

theorem vBB_eq (hp : p.Prime) (S : Formalism.MainNotions.G.UniformizedDVR p O) {σ : Type} (F : MvPolynomial σ (Formalism.MainNotions.G.KK O)) :
    vBB (vQ p S) F = (Formalism.MainNotions.G.vBB (O := O) p F).map (fun q : ℚ => (q : ℝ)) := by
  unfold vBB Formalism.MainNotions.G.vBB
  rw [Finset.comp_inf_eq_inf_comp (fun y : WithTop ℚ => y.map (fun q : ℚ => (q : ℝ)))
    (fun x y => map_cast_mono.map_min) (by simp)]
  refine Finset.inf_congr rfl fun α _ => ?_
  simp only [Function.comp_apply]
  rw [map_cast_add]
  have hf : vQ p S (fact α : Formalism.MainNotions.G.KK O) =
      ((padicValNat p (Formalism.MainNotions.G.expFact α) : ℚ) : WithTop ℚ) := vQ_nat hp S _ (fact_ne_zero' α)
  rw [hf, WithTop.untopD_coe]
  simp only [vR, vQ_apply]
  push_cast
  rfl

theorem geQ_vBB_iff (hp : p.Prime) (S : Formalism.MainNotions.G.UniformizedDVR p O) {σ : Type} (F : MvPolynomial σ (Formalism.MainNotions.G.KK O))
    (t : ℝ) : Formalism.MainNotions.PlaneGramData.geQ (Formalism.MainNotions.G.vBB (O := O) p F) t ↔ ((t : ℝ) : WithTop ℝ) ≤ vBB (vQ p S) F := by
  rw [vBB_eq hp S]
  exact geQ_gen _ t

theorem vBB_zero_iff (hp : p.Prime) (S : Formalism.MainNotions.G.UniformizedDVR p O) {σ : Type} (F : MvPolynomial σ (Formalism.MainNotions.G.KK O)) :
    Formalism.MainNotions.G.vBB (O := O) p F = 0 ↔ vBB (vQ p S) F = 0 := by
  rw [vBB_eq hp S]
  exact map_cast_eq_zero _

end Base

section Pol

variable {K : Type} [Field K]

theorem sDiag_eq (r : ℕ) [NeZero r] (n : ℤ) :
    sDiag K r n = Matrix.diagonal (fun a => if a = Formalism.MainNotions.G.lastIdx r then (LaurentPolynomial.T n : LauF K r) else 1) := by
  have key : ∀ a : Fin r, (a.val + 1 = r) ↔ a = Formalism.MainNotions.G.lastIdx r := by
    intro a
    rw [Fin.ext_iff]
    simp only [Formalism.MainNotions.G.lastIdx]
    have := a.isLt
    omega
  unfold sDiag
  simp only [key]

theorem substS_eq_twistSub {L : Type} [DecidableEq L] {r : ℕ} [NeZero r] (sg : L → Bool) (S : Finset L) :
    substS (lauι K r) sg S (hMat K r) (hInvT K r) =
      Formalism.MainNotions.G.twistSub (⟨sg⟩ : Formalism.MainNotions.G.Letters L) (↑S : Set L) (Formalism.MainNotions.G.lastIdx r) := by
  unfold substS Formalism.MainNotions.G.twistSub hMat hInvT Formalism.MainNotions.G.twistMat lauι
  rw [sDiag_eq, sDiag_eq]
  congr 1
  funext x
  by_cases hx : x.1 ∈ S
  · have hx' : x.1 ∈ (↑S : Set L) := hx
    rw [if_pos hx, if_pos hx']
    rfl
  · have hx' : x.1 ∉ (↑S : Set L) := hx
    rw [if_neg hx, if_neg hx']

theorem valS_eq {L : Type} [DecidableEq L] {r : ℕ} [NeZero r] (sg : L → Bool) (S : Finset L)
    (F : MvPolynomial (L × Fin r) K) :
    valS sg S F = Formalism.MainNotions.G.valS (⟨sg⟩ : Formalism.MainNotions.G.Letters L) (↑S : Set L) F := by
  unfold valS Formalism.MainNotions.G.valS Formalism.MainNotions.G.sDegs
  simp only []
  rw [substS_eq_twistSub, Finset.inf_biUnion]
  refine Finset.inf_congr rfl fun β _ => ?_
  unfold lord
  exact Finset.min_eq_inf_withTop _

theorem PolK_eq {L : Type} (r : ℕ) (d : L → ℕ) : PolK K r d = Formalism.MainNotions.G.Pol K r d := rfl

theorem fock_eq {σ : Type} (F G : MvPolynomial σ K) : fock F G = Formalism.MainNotions.G.fock F G := rfl

theorem ddiv_eq_divDer {σ : Type} (M : σ →₀ ℕ) (F : MvPolynomial σ K) : ddiv M F = Formalism.MainNotions.G.divDer M F := by
  unfold ddiv Formalism.MainNotions.G.divDer
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs with h
  · have e : ((M.prod fun k j => (α k).choose j : ℕ) : K) = α.prod fun x k => ((k.choose (M x) : ℕ) : K) := by
      rw [Finsupp.prod_of_support_subset M (Finsupp.support_mono h) (fun k j => (α k).choose j)
        (fun k _ => Nat.choose_zero_right _), Nat.cast_prod]
      rfl
    rw [e]
  · rfl

theorem lastIdx_eq (r : ℕ) [NeZero r] : lastIdx r = Formalism.MainNotions.G.lastIdx r := rfl

end Pol

end Formalism.MainNotions.PlaneGram
