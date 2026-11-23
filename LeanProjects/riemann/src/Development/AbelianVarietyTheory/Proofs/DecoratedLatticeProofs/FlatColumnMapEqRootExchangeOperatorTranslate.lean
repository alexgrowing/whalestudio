import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousWittExtendByZero
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.LocFlat.ColTranslate
open GlobalTheory.RootEx.Exchange GlobalTheory.LocFlat

theorem colE_neg_inv {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (y : n → k) :
    ((colE c p (-y))⁻¹ : GL (n ⊕ Fin c) k).val = (colE c p y).val := by
  ext r s
  rcases r with r | r <;> rcases s with s | s <;>
    simp [colE, upU, -Matrix.coe_units_inv, Units.inv_mk, neg_ite]

theorem affPt_add_colAt {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} (q : Fin c) (y : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    affPt (q.val + 1) x₀ e + colAt n' c (q.val + 1) y = mat x₀ (ext0 (Free (q.val + 1)) e + gCol q y) := by
  classical
  ext r s
  rcases r with r | r <;> rcases s with s | s
  · simp [affPt_eq, mat, ext0, colAt, gCol, Free]
  · by_cases h : s = q.castSucc
    · subst h; simp [affPt_eq, mat, ext0, colAt, gCol, Free]
    · have h' : ¬ s.val = q.val := fun hh => h (Fin.ext (by simpa using hh))
      simp [affPt_eq, mat, ext0, colAt, gCol, h, h']
  · simp [affPt_eq, mat, ext0, colAt, gCol]
  · simp [affPt_eq, mat, ext0, colAt, gCol]

theorem ch_add_colAt {k : Type} [Field k] {n n' : Type} {c : ℕ} (p : ℕ) (y : n → k)
    (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (z + colAt n' c p y) = ch z := by
  simp [ch, colAt]

end GlobalTheory.LocFlat.ColTranslate

namespace GlobalTheory.LocFlat
open GlobalTheory.RootEx.Exchange GlobalTheory.LocFlat.ColTranslate

theorem flCol_eq_opE_colE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix n (n' ⊕ Unit) k, GlobalTheory.LocFlat.flCol ψ ν p Φ x = opE ψ ν p (fun z => Φ ((colE c p fun r => x r (Sum.inr ())).val * z)) x.toCols₁ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp1 hpc Φ hΦ x
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, p = q.val + 1 := ⟨⟨p - 1, by omega⟩, by simp; omega⟩
  have hcont : Continuous Φ := hΦ.1.continuous
  have h1 := opE_colE hψ ν 1 q q (χ := fun _ => (1 : ℂ)) continuous_const hcont x.toCols₁
    (-fun r => x r (Sum.inr ()))
  simp only [om_colE, colE_neg_inv, one_mul, neg_neg] at h1
  refine Eq.trans ?_ h1.symm
  rw [flCol]
  unfold opE
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  simp only
  rw [← affPt_add_colAt, big, ch_add_colAt, one_mul]

end GlobalTheory.LocFlat
