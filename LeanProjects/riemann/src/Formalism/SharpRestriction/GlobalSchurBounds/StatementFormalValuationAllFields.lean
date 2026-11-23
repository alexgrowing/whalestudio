import Formalism.SharpRestriction.GlobalSchurBounds.KernelEntryData
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.KernelEntryData

noncomputable section

namespace Formalism.MainNotions.KernelEntryData

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions Finset

section Numbers

variable {n' : ℕ}

def Fv (p rb : ℕ) (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) : ℝ :=
  (gam p - 1 / (p : ℝ)) * ∑ s : Fin n', (low rb TT nu s : ℝ)

end Numbers

section Val

variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)

theorem geV_zero (g : ℝ) : geV p Oc (0 : Kc) g := by
  intro a b hb _
  rw [zero_pow hb.ne', zero_mul]
  exact Oc.zero_mem

theorem geV_smul {c x : Kc} {g : ℝ} (hc : c ∈ Oc) (h : geV p Oc x g) : geV p Oc (c * x) g := by
  intro a b hb hab
  rw [mul_pow, mul_assoc]
  exact Oc.mul_mem (Oc.pow_mem hc b) (h a b hb hab)

theorem geV_neg {x : Kc} {g : ℝ} (h : geV p Oc x g) : geV p Oc (-x) g := by
  have := geV_smul p Oc (Oc.neg_mem Oc.one_mem) h
  simpa using this

theorem geV_add (hV : ValR p Oc) {x y : Kc} {g : ℝ} (hx : geV p Oc x g) (hy : geV p Oc y g) : geV p Oc (x + y) g := by
  intro a b hb hab
  by_cases hy0 : y = 0
  · subst hy0; simpa using hx a b hb hab
  by_cases hx0 : x = 0
  · subst hx0; simpa using hy a b hb hab
  rcases hV.val (x / y) with h | h
  · have e : x + y = (x / y + 1) * y := by field_simp
    rw [e, mul_pow, mul_assoc]
    exact Oc.mul_mem (Oc.pow_mem (Oc.add_mem h Oc.one_mem) _) (hy a b hb hab)
  · have h' : y / x ∈ Oc := by simpa [inv_div] using h
    have e : x + y = (1 + y / x) * x := by field_simp
    rw [e, mul_pow, mul_assoc]
    exact Oc.mul_mem (Oc.pow_mem (Oc.add_mem Oc.one_mem h') _) (hx a b hb hab)

end Val

section Core

variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc) (Sh : Shape)

def InMM (vp : Kc) (Th : MvPowerSeries Sh.ZV Kc) : Prop :=
  ∃ u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc, (∀ v s, u v s ∈ Oc) ∧
    Sh.InProd Oc p (fun v => Sh.hhV p v (u v)) (Sh.atPi vp Th)

def formalValuationLowerBound (rb : ℕ) (nu : Sh.Wt) (TT : ∀ v, Finset (Fin (Sh.n' v))) : ℝ :=
  ∑ v, (gsum p (TT v) (nu v) + Fv p rb (TT v) (nu v) - de p Sh.r0 Sh.r1 rb (TT v) (nu v))

def FormalValuationOneSeries (rb : ℕ) (nu : Sh.Wt) (Th : MvPowerSeries Sh.ZV Kc) : Prop :=
  ∀ (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh),
    gaussGe p Oc (FormalGroupSystem.applyD (Sh.PI rb nu I) Th) (formalValuationLowerBound p Sh rb nu TT)

def FormalValuationBoundInHidaSetting : Prop :=
  ∀ (rb : ℕ) (nu : Sh.Wt) (vp : Kc) (Th : MvPowerSeries Sh.ZV Kc), HidaSetting p Oc Sh rb nu vp →
    InMM p Oc Sh vp Th → FormalValuationOneSeries p Oc Sh rb nu Th

end Core

def StatementFormalValuationAllFields : Prop := ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape), FormalValuationBoundInHidaSetting p Oc Sh

section AtG

variable {p : ℕ} [Fact p.Prime]

def FL_G (_D : D7) (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X) : Prop :=
  ∀ j < X.mm, ∀ c : ℝ,
    (∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
      ∀ (φ : Y.Frm j La La') (I : (shX X j).ColCh),
        gaussGe p Y.Oc (FormalGroupSystem.applyD ((shX X j).PI (rbX X j) (nuX X j) I) (ThX Y j La La' φ)) c) →
    ∀ G ∈ X.Int j, X.vGe (j + 1) (X.Kz j G) (c - X.dG j)

end AtG

def TwoOrbitExponentialValuation : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (i0 : Fin 1) (t : Fin 1 → PowerSeries ℚ), IsLeaf p t → ∀ e : ℕ,
    padicValRat p (PowerSeries.coeff (p ^ 3 * p ^ e) ((-ze3 p t (posAdd i0 1)) ^ (p ^ e)) / ((p ^ e).factorial : ℚ)) =
      -(((p : ℤ) + 1) * (p : ℤ) ^ e + padicValNat p (p ^ e).factorial)

end Formalism.MainNotions.KernelEntryData

end
