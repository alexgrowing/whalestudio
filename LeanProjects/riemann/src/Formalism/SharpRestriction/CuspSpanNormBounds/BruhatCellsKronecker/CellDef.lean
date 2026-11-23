import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S Matrix

section Mat

variable {K : Type} [Field K] {n : ℕ}

def StrictUp (A : Matrix (Fin n) (Fin n) K) : Prop := ∀ a b : Fin n, b ≤ a → A a b = 0

def supSum (A : Matrix (Fin n) (Fin n) K) : K :=
  ∑ a : Fin n, if h : a.val + 1 < n then A a ⟨a.val + 1, h⟩ else 0

def mono (σ : Fin n → Fin n) (t : Fin n → K) : Matrix (Fin n) (Fin n) K := fun a b => if a = σ b then t b else 0

def MatRel [StarRing K] (Z : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ A A' : Matrix (Fin n) (Fin n) K, StrictUp A → StrictUp A' → Aᴴ * Z + Z * A' = 0 → supSum A = star (supSum A')

end Mat

def RelevanceUnipotentInvariant : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : ℕ) (L Z U : Matrix (Fin n) (Fin n) K), IsLoUni L → IsUpUni U →
    MatRel (L * Z * U) → MatRel Z

def ColumnScalingBruhatShape : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (ε : Fin n → K) (L U : Matrix (Fin n) (Fin n) K) (σ : Fin n → Fin n) (t : Fin n → K),
    (∀ b, ε b ≠ 0) → IsUpUni U →
    ∃ U' : Matrix (Fin n) (Fin n) K, IsUpUni U' ∧
      (fun a b => ε b * (L * mono σ t * U) a b) = L * mono σ (fun b => ε b * t b) * U'

def BruhatDecomposition : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (Z : Matrix (Fin n) (Fin n) K), Z.det ≠ 0 →
    ∃ (L U : Matrix (Fin n) (Fin n) K) (σ : Fin n → Fin n) (t : Fin n → K), IsLoUni L ∧ IsUpUni U ∧
      Function.Bijective σ ∧ (∀ b, t b ≠ 0) ∧ Z = L * mono σ t * U

def RelevantMonomialConsecutive : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : ℕ) (σ : Fin n → Fin n) (t : Fin n → K), Function.Bijective σ →
    (∀ b, t b ≠ 0) → MatRel (mono σ t) →
    ∀ c b : Fin n, c < b → (σ c).val = (σ b).val + 1 → b.val = c.val + 1 ∧ t b = -t c

def MonomialMatrixIsPoint : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (σ : Fin n → Fin n) (τ : Fin n → K), Function.Bijective σ → (∀ b, τ b ≠ 0) →
    (∀ c b : Fin n, c < b → (σ c).val = (σ b).val + 1 → b.val = c.val + 1 ∧ τ b = τ c) →
    ∃ p : Point K n, ptMat p = mono σ τ

def SchurComplementCellExtension : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (p : Point K n),
    IsInCell (M.submatrix Fin.castSucc Fin.castSucc) p → (M.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 → M.det ≠ 0 →
      ∃ p' : Point K (n + 1), IsInCell M p'

def LeadingBlocksRelevant : Prop :=
  ∀ (K E : Type) [Field K] [Field E] [NumberField E] [StarRing E] [Algebra K E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ)
    (T T' : E) (F : FlagG S r T) (F' : FlagG S r T'),
    (∀ x : E, algebraMap K E (Algebra.trace K E x) = x + star x) →
    (∀ y : S.V, (∀ a, S.hT (F.fvec a) y = 0) → S.hT y y = 0 → y ∈ F.X) →
    (∀ y : S.V, (∀ a, S.hT (F'.fvec a) y = 0) → S.hT y y = 0 → y ∈ F'.X) →
    Relevant K F F' → ∀ (j : ℕ) (hj : j ≤ r + 1), ((j ≤ r ∧ Dl F F' j ≠ 0) ∨ (j = r + 1 ∧ Gflag F F' ≠ 0)) →
      MatRel ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))

theorem cell_of_matRel (h1 : RelevanceUnipotentInvariant) (h2 : ColumnScalingBruhatShape) (h3 : BruhatDecomposition) (h4 : RelevantMonomialConsecutive) (h5 : MonomialMatrixIsPoint)
    {K : Type} [Field K] [StarRing K] {n r : ℕ} (hn : n ≤ r + 1) (Z : Matrix (Fin n) (Fin n) K) (hdet : Z.det ≠ 0)
    (hrel : MatRel Z) : ∃ p : Point K n, IsInCell (fun a b => (-1 : K) ^ (r - b.val) * Z a b) p := by
  obtain ⟨L, U, σ, t, hL, hU, hσ, ht, hZ⟩ := h3 K n Z hdet
  have hm : MatRel (mono σ t) := h1 K n L (mono σ t) U hL hU (hZ ▸ hrel)
  have hc := h4 K n σ t hσ ht hm
  have hε : ∀ b : Fin n, ((-1 : K) ^ (r - b.val)) ≠ 0 := fun b => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  obtain ⟨U', hU', hE⟩ := h2 K n (fun b => (-1 : K) ^ (r - b.val)) L U σ t hε hU
  obtain ⟨p, hp⟩ := h5 K n σ (fun b => (-1 : K) ^ (r - b.val) * t b) hσ (fun b => mul_ne_zero (hε b) (ht b)) (by
    intro c b hcb hv
    obtain ⟨e1, e2⟩ := hc c b hcb hv
    refine ⟨e1, ?_⟩
    have hb : b.val < n := b.isLt
    have e3 : r - c.val = (r - b.val) + 1 := by omega
    rw [e2, e3, pow_succ]
    ring)
  refine ⟨p, L, U', hL, hU', ?_⟩
  rw [hp, ← hE, hZ]

end Formalism.MainNotions.BridgeLemma

end
