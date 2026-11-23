import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.NeglogPowMul
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestPlusOf

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM Formalism.MainNotions.G.SymmetricFormBlocks

abbrev setZ {N : ℕ} (G : M.BlockData N) (z : ℕ) : M.BlockData N := ⟨G.LL, G.T, G.uPos, G.B, z⟩

def lgN (p A r : ℕ) : ℕ := Nat.log p (8 * A + r) + 1

def x0N (p A r N t : ℕ) : ℕ := ((t + 1) * (r + 1) + ((N + 1) * r + (t + 1) * 2)) * lgN p A r

def JN {N : ℕ} (G : M.BlockData N) (jp : ℕ) : ℕ := min (G.LL.deg G.uPos - jp) (G.B - jp)

def WinLvl : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (G : M.BlockData N), G.BlockOK →
    ∀ (j : Fin G.T.t → ℕ) (jp : ℕ), G.LevelOK j jp → ∀ (A : ℕ), 1 ≤ A → (∀ x, G.LL.deg x ≤ 2 * A) → G.B ≤ 2 * A →
    (∀ i, G.T.z i ≤ 2 * A) →
    ∀ (n₁ : ℕ) (f : Fin n₁ → MvPolynomial (M.BVar N r G.T.t) ℚ_[p]),
      (∀ a, f a ∈ Ljj p (r := r) G j jp) → LinearIndependent ℤ_[p] f →
      (∀ a b, a ≠ b → bePhi p (r := r) G j jp (f a) (f b) = 0) →
      ∀ D : ℤ, (∀ a, bePhi p (r := r) G j jp (f a) (f a) ≠ 0 ∧ (bePhi p (r := r) G j jp (f a) (f a)).valuation ≤ D) →
      ∀ (z0 W h : ℕ) (k : ℤ), 0 ≤ k → 0 < W → W ≤ p ^ h → JN G jp + 1 ≤ p ^ h →
        (∑ i ∈ Finset.range W, (M.bad p (bejj p (r := r) (setZ G (z0 + i)) j jp)
            (Submodule.span ℤ_[p] (Set.range f)) k : ℝ)) ≤
          (W : ℝ) * ((n₁ : ℝ) * ((JN G jp : ℝ) / W +
            (((x0N p A r N G.T.t : ℝ) + D + lgN p A r) + (JN G jp : ℝ) * h / W) / ((k : ℝ) + 1)))

end Formalism.MainNotions.G.GramWindowAlt

end
