import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.JacFramePair

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pair_col (p : Place D k) {N ρ : ℕ} {κ : Type} [Fintype κ] (G : Matrix (Fin N) (Fin N) D.host.E)
    (X : Matrix (Fin N) κ D.host.E) (e : Matrix (Fin N) (Fin ρ) D.host.E) (j : κ) (i : Fin ρ) :
    ∑ r, p.pr (X r j) * p.pr (star ((G *ᵥ fun r => e r i) r)) = p.pr (star ((Xᴴ * G * e) j i)) := by
  have h : star ((Xᴴ * G * e) j i) = ∑ r, X r j * star ((G *ᵥ fun r => e r i) r) := by
    rw [Matrix.mul_assoc, Matrix.mul_apply, star_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hv : (G * e) r i = (G *ᵥ fun r => e r i) r := by simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [star_mul', Matrix.conjTranspose_apply, star_star, hv, mul_comm]
  rw [h]
  change _ = Witness.prH p _
  rw [map_sum]
  exact Finset.sum_congr rfl fun r _ => (map_mul (Witness.prH p) _ _).symm

theorem pair_scaled (p : Place D k) {N ρ : ℕ} {κ Z : Type} [Fintype κ] (G : Matrix (Fin N) (Fin N) D.host.E)
    (X : Matrix (Fin N) κ D.host.E) (e : Matrix (Fin N) (Fin ρ) D.host.E) (β : Matrix (Fin N) Z k) (m : Z) (j : κ)
    (t : k) (h : ∀ r, β r m = t * p.pr (X r j)) (i : Fin ρ) :
    ∑ r, β r m * p.pr (star ((G *ᵥ fun r => e r i) r)) = t * p.pr (star ((Xᴴ * G * e) j i)) := by
  simp_rw [h, mul_assoc, ← Finset.mul_sum, pair_col]

theorem pr_zero (p : Place D k) : p.pr 0 = 0 := map_zero (Witness.prH p)

theorem pr_one (p : Place D k) : p.pr 1 = 1 := map_one (Witness.prH p)

theorem pr_star_one (p : Place D k) {ρ : ℕ} (i' i : Fin ρ) :
    p.pr (star ((1 : Matrix (Fin ρ) (Fin ρ) D.host.E) i' i)) = if i' = i then 1 else 0 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp [pr_zero, pr_one]

theorem isJacFrame_pairing : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ρ : ℕ) (J : JacLev D ρ) (s hh : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)),
    p.IsJacFrame J s hh F₀ F → valuation k s = 1 → valuation k hh = 1 → valuation k p.xi = 1 → ∀ i : Fin ρ,
    ∃ (b : k) (m₀ : n ⊕ Fin c), valuation k b = 1 ∧ (∀ r, b * p.pr (J.d.e r i) = F.β r m₀) ∧
      (∀ m, ∑ r, F.β r m * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) ∈ 𝒪[k]) ∧
      ∃ m, valuation k (∑ r, F.β r m * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r))) = 1 := by
  intro D k _ _ _ _ p ρ J s hh n _ _ c F₀ F hJ hs hhh hx i
  obtain ⟨hc, h1, h2, h3⟩ := hJ
  subst hc
  have vt : ∀ l : ℕ, valuation k (s * (hh / p.xi) * (-1 / p.xi) ^ l) = 1 := fun l => by
    simp [map_mul, map_div₀, map_pow, Valuation.map_neg, hs, hhh, hx]
  have inrLo : ∀ (j : Fin (2 * ρ)) (hj : j.val < ρ),
      ∑ r, F.β r (Sum.inr j) * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) = 0 := fun j hj => by
    rw [pair_scaled p J.W.gram J.d.e J.d.e F.β (Sum.inr j) (⟨j.val, hj⟩ : Fin ρ) _ (h2 ⟨j.val, hj⟩ j rfl), J.d.ee]
    simp [pr_zero]
  have inrHi : ∀ (j : Fin (2 * ρ)) (hj : ρ ≤ j.val),
      ∑ r, F.β r (Sum.inr j) * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) =
        s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - 1 - j.val)) *
          (if (⟨2 * ρ - 1 - j.val, by omega⟩ : Fin ρ) = i then 1 else 0) := fun j hj => by
    rw [pair_scaled p J.W.gram J.d.e' J.d.e F.β (Sum.inr j) (⟨2 * ρ - 1 - j.val, by omega⟩ : Fin ρ) _
      (h3 ⟨2 * ρ - 1 - j.val, by omega⟩ j (by simp only; omega)), J.d.e'e, pr_star_one]
  refine ⟨s * p.xi ^ (ρ - i.val), Sum.inr ⟨i.val, by omega⟩, by simp [map_mul, map_pow, hs, hx],
    fun r => (h2 i _ rfl r).symm, ?_, Sum.inr ⟨2 * ρ - 1 - i.val, by omega⟩, ?_⟩
  · rintro (a | j)
    · have e0 : ∑ r, F.β r (Sum.inl a) * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) = 0 := by
        simp_rw [h1, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun b _ => ?_
        have := pair_col p J.W.gram J.d.i₀ J.d.e b i
        rw [J.d.i₀e, Matrix.zero_apply, star_zero, pr_zero] at this
        calc ∑ r, p.pr (J.d.i₀ r b) * F₀.β b a * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r))
            = F₀.β b a * ∑ r, p.pr (J.d.i₀ r b) * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
          _ = 0 := by rw [this, mul_zero]
      rw [e0]
      exact zero_mem _
    · by_cases hj : j.val < ρ
      · rw [inrLo j hj]
        exact zero_mem _
      · rw [inrHi j (by omega), Valuation.mem_integer_iff, map_mul, vt, one_mul]
        split_ifs <;> simp
  · rw [inrHi _ (by simp only; omega), map_mul, vt, one_mul, if_pos (Fin.ext (by simp only; omega)), map_one]

end GlobalTheory.JacFramePair
end
