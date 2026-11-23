import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOf
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MapNatActR

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G

theorem natAct_rat {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) {LL : Type} [Field LL] (e : LL →+* Kf) (A : ∀ v, GL (Fin (P.m + 1)) (P.Qq v))
    (g : ∀ v, Fin (P.n' v) → GL (Fin (P.m + 1)) LL)
    (hg : ∀ v s, Matrix.GeneralLinearGroup.map e (g v s) = gPosGL P v s (A v)) (Q : XR P LL) :
    MvPolynomial.map e (natActR P LL g Q) = P.natAct A (MvPolynomial.map e Q) := by
  have hinv : ∀ v s a b, e ((((g v s)⁻¹ : GL (Fin (P.m + 1)) LL) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL) a b) =
      P.gPos v s (((A v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) a b := by
    intro v s a b
    have h1 : Matrix.GeneralLinearGroup.map e ((g v s)⁻¹) = gPosGL P v s ((A v)⁻¹) := by
      rw [map_inv, map_inv, hg]
    have h2 := congrArg (fun M : GL (Fin (P.m + 1)) Kf => (M : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf) a b) h1
    exact h2
  have hdet : ∀ v s, e ((g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL).det) =
      (P.gPos v s (A v : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))).det := by
    intro v s
    rw [RingHom.map_det]
    congr 1
    have h2 := congrArg (fun M : GL (Fin (P.m + 1)) Kf => (M : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf)) (hg v s)
    exact h2
  have hsub : ∀ R : XR P LL, MvPolynomial.map e
      (substR P LL (fun v s => (((g v s)⁻¹ : GL (Fin (P.m + 1)) LL) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL)) R) =
      P.subst (fun v s => P.gPos v s (((A v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)) :
        Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))) (MvPolynomial.map e R) := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C a => simp [substR, Places.subst]
    | add f q hf hq => simp only [map_add, hf, hq]
    | mul_X f x hf =>
      simp only [map_mul, hf]
      congr 1
      simp only [substR, Places.subst, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.map_C,
        MvPolynomial.map_X, hinv]
  simp only [natActR, Places.natAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hsub]
  congr 2
  simp only [map_prod, map_zpow₀, hdet]
  rfl

variable {p : ℕ} (G : GAtP p) {LL : Type} [Field LL] (e : LL →+* G.Kf)

def RatLev : Prop :=
  (∀ (i : G.comp) (γ : (G.lev i).Γ) (v : Fin G.P.nV) (s : Fin (G.P.n' v)), ∃ g : GL (Fin (G.P.m + 1)) LL,
    Matrix.GeneralLinearGroup.map e g = gPosGL G.P v s ((G.lev i).act v γ)) ∧
  ∀ (i : G.comp) (γ : (G.lev i).Γ), ∃ a : LL, e a = algebraMap G.O G.Kf ((G.lev i).χ γ : G.O)

theorem ratActG_of (h : RatLev G e) : RatActG G e := by
  intro i γ ξ hξ
  obtain ⟨Q, hQ⟩ := hξ
  choose g hg using fun v s => h.1 i γ v s
  obtain ⟨a, ha⟩ := h.2 i γ
  refine ⟨a • natActR G.P LL g Q, ?_⟩
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
    natAct_rat G.P e (fun v => (G.lev i).act v γ) g hg Q, hQ, ← MvPolynomial.smul_eq_C_mul, ha,
    algebraMap_smul]
  rfl

end Formalism.L2.G.Cmp
