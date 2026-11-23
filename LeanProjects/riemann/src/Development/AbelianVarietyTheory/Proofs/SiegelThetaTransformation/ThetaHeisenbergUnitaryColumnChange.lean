import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLawsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ColHeis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

theorem hx_sum_left (x : Frame X.Ψ r) (z : Fin n → Fin g → ℂ) (w : Fin g → ℂ) :
    hx X bas idx x (∑ k, z k) w = ∑ k, hx X bas idx x (z k) w := by
  unfold hx
  rw [Matrix.mulVec_sum, sum_dotProduct]

theorem hx_sum_right (x : Frame X.Ψ r) (z : Fin g → ℂ) (w : Fin n → Fin g → ℂ) :
    hx X bas idx x z (∑ k, w k) = ∑ k, hx X bas idx x z (w k) := by
  unfold hx
  rw [Matrix.mulVec_sum, star_sum, Matrix.mulVec_sum, dotProduct_sum]

theorem hAct_eq_sum (h : Matrix (Fin n) (Fin n) E) (z : Fin n → Fin g → ℂ) (k : Fin n) :
    GlobalTheory.Dict.hAct X idx h z k = ∑ a, fun j => rowType X (idx j) (h k a) * z a j := by
  funext j
  rw [Finset.sum_apply]
  rfl

theorem hAct_add_smul (h : Matrix (Fin n) (Fin n) E) (z w : Fin n → Fin g → ℂ) (c : ℂ) (k : Fin n) :
    GlobalTheory.Dict.hAct X idx h (fun a => z a + c • w a) k =
      GlobalTheory.Dict.hAct X idx h z k + c • GlobalTheory.Dict.hAct X idx h w k := by
  funext j
  simp only [GlobalTheory.Dict.hAct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem sum_hx_hAct (x : Frame X.Ψ r)
    (hadj : ∀ (a : E) z w, hx X bas idx x (fun j => rowType X (idx j) a * z j) w =
      hx X bas idx x z (fun j => rowType X (idx j) (cc a) * w j))
    (h : Matrix (Fin n) (Fin n) E) (hh : ccT h * h = 1) (z w : Fin n → Fin g → ℂ) :
    ∑ k, hx X bas idx x (GlobalTheory.Dict.hAct X idx h z k) (GlobalTheory.Dict.hAct X idx h w k) =
      ∑ k, hx X bas idx x (z k) (w k) := by

  have key : ∀ k, hx X bas idx x (GlobalTheory.Dict.hAct X idx h z k) (GlobalTheory.Dict.hAct X idx h w k) =
      ∑ a, ∑ b, hx X bas idx x (z a) (fun j => rowType X (idx j) (cc (h k a) * h k b) * w b j) := by
    intro k
    rw [hAct_eq_sum, hAct_eq_sum, hx_sum_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx_sum_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hadj]
    congr 1
    funext j
    rw [map_mul, _root_.mul_assoc]

  have hcol : ∀ a b, ∑ k, cc (h k a) * h k b = (1 : Matrix (Fin n) (Fin n) E) a b := by
    intro a b
    rw [← hh, Matrix.mul_apply]
    rfl
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  simp only [← hx_sum_right]
  congr 1
  funext j
  simp only [Finset.sum_apply]
  have hj : ∀ b, ∑ k, rowType X (idx j) (cc (h k a) * h k b) * w b j =
      rowType X (idx j) ((1 : Matrix (Fin n) (Fin n) E) a b) * w b j := by
    intro b
    rw [← Finset.sum_mul, ← map_sum, hcol]
  simp only [hj, Matrix.one_apply, apply_ite, map_one, map_zero, ite_mul, _root_.one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem pv_mul_row (x : Frame X.Ψ r)
    (hsm : ∀ (a : E) v, pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j)
    (h : Matrix (Fin n) (Fin n) E) (y : Matrix (Fin n) (Fin r) E) (k : Fin n) :
    pv X idx x ((h * y) k) = GlobalTheory.Dict.hAct X idx h (fun a => pv X idx x (y a)) k := by
  have hrow : (h * y) k = ∑ a, h k a • y a := by
    funext i
    simp [Matrix.mul_apply, Finset.sum_apply]

  have hadd : pv X idx x (∑ a, h k a • y a) = ∑ a, pv X idx x (h k a • y a) := by
    funext j
    rw [Finset.sum_apply]
    exact (congrFun (map_sum (perLin X x) (fun a => h k a • y a) Finset.univ) (idx j)).trans
      (Finset.sum_apply _ _ _)
  rw [hrow, hadd, hAct_eq_sum]
  exact Finset.sum_congr rfl fun a _ => hsm (h k a) (y a)

end GlobalTheory.Dict.ColHeis

open GlobalTheory.Dict.ColHeis in

theorem GlobalTheory.Dict.thA_heisG_hAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ φ φ' : TF n g, IsSB φ → IsSB φ' → ∀ t : ℂ, ∀ x ∈ X.dom, (∀ z, thA X bas idx φ' x (hAct X idx h z) = t * thA X bas idx φ x z) → ∀ (y : Matrix (Fin n) (Fin r) E) z, thA X bas idx (heisG X bas (h * y) φ') x (hAct X idx h z) = t * thA X bas idx (heisG X bas y φ) x z := by
  intro E _ _ _ r X g bas idx n hS hn h hh φ φ' hφ hφ' t x hxd hrel y z
  obtain ⟨-, -, -, hadj, hsm, -⟩ := GlobalTheory.T.hermitianFormAtFrame_laws E r X g bas idx n hS hn x hxd
  have HL := (heisG_laws E r X g bas idx n hS hn).2.2.2
  rw [((HL (h * y) φ' hφ').2.2.2.2) x hxd (hAct X idx h z), ((HL y φ hφ).2.2.2.2) x hxd z]

  have hP : ∀ k, per X x ((h * y) k) ∘ idx = hAct X idx h (fun a => pv X idx x (y a)) k :=
    fun k => pv_mul_row X idx x hsm h y k
  simp only [hP]

  have hT : thA X bas idx φ' x (fun k => hAct X idx h z k + hAct X idx h (fun a => pv X idx x (y a)) k) =
      t * thA X bas idx φ x (fun k => z k + per X x (y k) ∘ idx) := by
    refine Eq.trans ?_ (hrel (fun k => z k + pv X idx x (y k)))
    congr 1
    funext k
    simpa using (hAct_add_smul X idx h z (fun a => pv X idx x (y a)) 1 k).symm
  rw [hT, mul_left_comm]
  refine congrArg (t * ·) (congrArg (· * _) (congrArg cexp (congrArg (fun s : ℂ => -((Real.pi : ℂ) * s)) ?_)))

  have hE : ∀ k, hAct X idx h z k + (1 / 2 : ℂ) • hAct X idx h (fun a => pv X idx x (y a)) k =
      hAct X idx h (fun a => z a + (1 / 2 : ℂ) • pv X idx x (y a)) k :=
    fun k => (hAct_add_smul X idx h z _ _ k).symm
  simp only [hE]
  exact sum_hx_hAct X bas idx x hadj h hh (fun a => z a + (1 / 2 : ℂ) • pv X idx x (y a))
    (fun a => pv X idx x (y a))
