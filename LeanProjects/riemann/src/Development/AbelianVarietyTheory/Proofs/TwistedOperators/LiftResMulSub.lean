import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.ColSubst

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem liftRes_mul_sub {A C : Type} [Fintype C] {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (T : A → C → Res k e)
    (N : Matrix C C 𝒪[k]) (i : A) (j : C) :
    valuation k ((liftRes (Matrix.of T * N.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e)) :
        A → C → Res k e) - liftRes T * N.map (fun x => (x : k))) i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
  set r : 𝒪[k] := Quotient.out ((Matrix.of T * N.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e))) i j) -
    ∑ l, Quotient.out (T i l) * N l j with hr
  have h1 : ((liftRes (Matrix.of T * N.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e)) :
        A → C → Res k e) - liftRes T * N.map (fun x => (x : k))) i j) = (r : k) := by
    simp [hr, liftRes, Matrix.mul_apply]
  rw [h1, ← GlobalTheory.SplitFlip.Model.val_le_iff_mem hϖ, ← Ideal.Quotient.eq_zero_iff_mem, hr, map_sub, map_sum]
  simp [Matrix.mul_apply, Ideal.Quotient.mk_out]

theorem sum_liftRes_mul {A C : Type} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ)
    (N N' : Matrix C C 𝒪[k]) (hN : N * N' = 1) (F : Matrix A C k → ℂ)
    (hF : ∀ T Z : Matrix A C k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) → F (T + Z) = F T) :
    ∑ T : A → C → Res k e, F (liftRes T * N.map (fun x => (x : k))) = ∑ T : A → C → Res k e, F (liftRes T) := by
  classical
  set π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) with hπ
  let φ : (A → C → Res k e) → (A → C → Res k e) := fun T => Matrix.of T * N.map π
  have hinj : Function.Injective φ := by
    intro T T' h
    have h2 := congrArg (fun M : Matrix A C (Res k e) => M * N'.map π) h
    simp only [φ, Matrix.mul_assoc, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero π) (map_one π),
      Matrix.mul_one] at h2
    exact h2
  have hbij : Function.Bijective φ := Finite.injective_iff_bijective.1 hinj
  rw [← hbij.sum_comp (fun T => F (liftRes T))]
  refine Finset.sum_congr rfl fun T _ => ?_
  symm
  rw [show liftRes (φ T) = liftRes T * N.map (fun x => (x : k)) +
    (liftRes (φ T) - liftRes T * N.map (fun x => (x : k))) by abel]
  exact hF _ _ fun i j => liftRes_mul_sub hϖ e T N i j

end GlobalTheory.ColSubst
