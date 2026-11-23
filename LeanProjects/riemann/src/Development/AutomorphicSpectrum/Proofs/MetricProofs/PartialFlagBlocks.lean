import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

abbrev PartialFlagBlocks (M : FlagModel y Ψ N j) (p : Ψ × Fin N) : Type :=
  {k : K // (∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k}

instance (M : FlagModel y Ψ N j) (p : Ψ × Fin N) : Fintype (PartialFlagBlocks M p) := Fintype.ofFinite _

abbrev stepIdx (M : FlagModel y Ψ N j) (p : Ψ × Fin N) : PartialFlagBlocks M p → Type := fun k => ι k.1

def stepV (M : FlagModel y Ψ N j) (p : Ψ × Fin N) : (Σ k, stepIdx M p k) → Σ k, ι k :=
  fun q => ⟨q.1.1, q.2⟩

theorem isBlockMap_stepV (M : FlagModel y Ψ N j) (p : Ψ × Fin N) :
    IsBlockMap (Subtype.val : PartialFlagBlocks M p → K) (stepV M p) := by
  refine ⟨Subtype.val_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨⟨k, hk⟩, m⟩ ⟨⟨k', hk'⟩, m'⟩ h
    simp only [stepV, Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h2⟩ := h
    cases h2
    rfl
  · rintro ⟨k, m⟩ ⟨k', rfl⟩
    exact ⟨⟨k', m⟩, rfl⟩

theorem mem_range_step (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (k : K) :
    k ∈ Set.range (Subtype.val : PartialFlagBlocks M p → K) ↔
      ((∀ p', M.blk p' ≠ some k) ∨ ∃ p', p' = p ∧ M.blk p' = some k) := by
  constructor
  · rintro ⟨⟨k', hk'⟩, rfl⟩
    rcases hk' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨p, rfl, h⟩
  · rintro (h | ⟨p', rfl, h⟩)
    · exact ⟨⟨k, Or.inl h⟩, rfl⟩
    · exact ⟨⟨k, Or.inr h⟩, rfl⟩

def IsStepMember {M : FlagModel y Ψ N j} {n e : ℕ} (BM : BaseMetric M n) (R : AnLogRes (mCoordIdeal y) ⊤ e)
    (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (p : Ψ × Fin N) (ph : R.X → ℝ)
    (phT : ℝ → R.X → ℝ) (line : ℝ → HermLine ι) (C₅ C t₀ : ℝ) : Prop :=
  IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y))
      (potOf R (fsHerm ι (M.dy p))) ph C₅ ∧
    IsRegFamily R.A (potOf R (fsHerm ι fun _ => 1)) (BM.L.pullback pr hp.1)
      (fun x y => BM.s (pr x) (pr y)) (potOf R (fsHerm ι (M.dy p))) ph phT C t₀ ∧
    IsRegFamilyC2 R.A (fun x y => BM.s (pr x) (pr y)) ph phT ∧
    (∀ t, (line t).a = M.dy p) ∧
    (∀ t, M.OnStep p (line t)) ∧
    (∀ t, 0 < t → t ≤ t₀ → IsSmoothHerm (line t) ∧ ∀ x, Real.log ((line t).h (R.lift x x)) =
      Real.log ((fsHerm ι (M.dy p)).h (R.lift x x)) + phT t x) ∧
    (∀ x, pr x ∉ bdry BM.s → Real.log ((BM.hom p).h (R.lift x x)) =
      Real.log ((fsHerm ι (M.dy p)).h (R.lift x x)) + ph x) ∧
    (∀ x x', pr x = pr x' →
      (∀ k, M.blk p = some k → ∃ a : ℂ, ∀ m : ι k, R.lift x x ⟨k, m⟩ = a * R.lift x' x' ⟨k, m⟩) →
        ph x = ph x' ∧ ∀ t, phT t x = phT t x') ∧
    ((p.2 : ℕ) + 1 = N → ∀ t, IsPsh R.A ((potOf R (fsHerm ι (M.dy p)) + LocPot.ofFun (phT t)).rsmul (-1)) ∧
      IsPsh R.A (potOf R (fsHerm ι (M.dy p)) + LocPot.ofFun (phT t)) ∧ phT t = ph)

end GlobalTheory.CompanionTheory.Ar.PB.FA
