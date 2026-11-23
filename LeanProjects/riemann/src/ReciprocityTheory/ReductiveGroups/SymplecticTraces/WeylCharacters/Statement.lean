import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Branch
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.BlockCombStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
import Formalism.LocalRingCardinality.DataCoeff

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS.S7

def kChar {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) : ℂ :=
  LinearMap.trace ℂ T.V ((T.op k : T.V →L[ℂ] T.V) : T.V →ₗ[ℂ] T.V)

def SqCharStatement : Prop :=
  ∀ (N : ℕ) (lam : Formalism.BasicNotions.DomWeight N) (g : GL (Fin N) ℂ) (t : Fin N → ℂ),
    (g : Matrix (Fin N) (Fin N) ℂ) = Matrix.diagonal t →
    ∃ f : Formalism.BasicNotions.nablaSq ℂ N lam →ₗ[ℂ] Formalism.BasicNotions.nablaSq ℂ N lam,
      (∀ x, (f x : MvPolynomial (Fin N × Fin N) ℂ) = Formalism.BasicNotions.sqAct ℂ N lam g x) ∧
      LinearMap.trace ℂ _ f = gtChar N lam.w t

def UCharStatement : Prop :=
  ∀ (N : ℕ) (Λ : Fin N → ℤ), Antitone Λ →
    ∀ (T : KType (fun _ : Fin N => true) (fun a => (Λ a : ℝ))) (k : KG (fun _ : Fin N => true)) (t : Fin N → ℂ),
      toMK k = Matrix.diagonal t → kChar T k = gtChar N Λ t

def KCharGTStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℤ), (∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) →
    ∀ (T : KType ε (fun a => (Λ a : ℝ))) (k : KG ε) (t : Fin n → ℂ), toMK k = Matrix.diagonal t →
      kChar T k = gtChar (cnt ε true) (Λ ∘ blk ε true) (t ∘ blk ε true) *
        gtChar (cnt ε false) (Λ ∘ blk ε false) (t ∘ blk ε false)

def WeylStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℤ), (∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) →
    ∀ (T : KType ε (fun a => (Λ a : ℝ))) (k : KG ε) (t : Fin n → ℂ), toMK k = Matrix.diagonal t →
      wdenK ε t * kChar T k = numK ε (Λ + rhoK ε) t

theorem ne_zero_of_toMK_diag {n : ℕ} {ε : Fin n → Bool} (k : KG ε) {t : Fin n → ℂ}
    (hk : toMK k = Matrix.diagonal t) (i : Fin n) : t i ≠ 0 := by
  unfold toMK toM at hk
  have hu : IsUnit (Matrix.diagonal t) := by
    rw [← hk]
    first
    | exact Units.isUnit _
    | exact (unitary.toUnits _).isUnit
    | exact (Matrix.isUnit_iff_isUnit_det _).mpr (Units.isUnit _)
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hu
  rw [Matrix.det_diagonal] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet.ne_zero i (Finset.mem_univ i)

theorem antitone_blk {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℤ}
    (hdom : ∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) (b : Bool) : Antitone (Λ ∘ blk ε b) := by
  have hmem : ∀ r, ε (blk ε b r) = b := by
    intro r
    have hr := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl r
    show ε ((univ.filter fun i : Fin n => ε i = b).orderEmbOfFin rfl r) = b
    simpa using hr
  have hsm : StrictMono (blk ε b) :=
    (Finset.orderEmbOfFin (univ.filter fun i : Fin n => ε i = b) rfl).strictMono
  intro i j hij
  rcases hij.lt_or_eq with h | h
  · exact hdom _ _ (hsm h) ((hmem i).trans (hmem j).symm)
  · rw [h]

theorem weyl_of (hK : KCharGTStatement) (hB : BlockCombStatement) : WeylStatement := by
  have hW : WeylGTStatement := weylGT
  intro n ε Λ hdom T k t hk
  rw [hK n ε Λ hdom T k t hk]
  obtain ⟨hw, hnum, hrho⟩ := hB ℂ n ε (Λ + rhoK ε) t
  rw [hw, hnum]
  have hG : ∀ b : Bool, wden (cnt ε b) (t ∘ blk ε b) * gtChar (cnt ε b) (Λ ∘ blk ε b) (t ∘ blk ε b) =
      alt (cnt ε b) ((Λ + rhoK ε) ∘ blk ε b) (t ∘ blk ε b) := by
    intro b
    have hc : (Λ + rhoK ε) ∘ blk ε b = Λ ∘ blk ε b + delta (cnt ε b) := by
      rw [← hrho b]
      rfl
    rw [hc]
    exact hW ℂ _ _ (antitone_blk hdom b) _ (fun i => ne_zero_of_toMK_diag k hk _)
  rw [← hG true, ← hG false]
  ring

end ReciprocityTheory.ChartRestriction.TR.Weyl
