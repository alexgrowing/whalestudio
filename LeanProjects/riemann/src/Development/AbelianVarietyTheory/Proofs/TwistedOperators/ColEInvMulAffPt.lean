import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.ColumnSupport

theorem colE_inv_mul_affPt {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n]
    {c p : ℕ} (hp : p < c) (β : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (p + 1) rs} → k) (r : n) :
    (((colE c (p + 1) β)⁻¹).val * affPt (p + 1) x₀ e) (Sum.inl r) (Sum.inr ⟨p, by omega⟩) = -β r := by
  have hv : ((colE c (p + 1) β)⁻¹).val =
      fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p + 1 then β r else 0)) 0 1 := rfl
  have h1 : ∀ s : n, affPt (p + 1) x₀ e (Sum.inl s) (Sum.inr ⟨p, by omega⟩) = 0 := by
    intro s
    simp [affPt, basePt, Free]
  have h2 : affPt (p + 1) x₀ e (Sum.inr ⟨p, hp⟩) (Sum.inr ⟨p, by omega⟩) = 1 := by
    simp [affPt, basePt, Free]
  rw [hv, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [h1, mul_zero, Finset.sum_const_zero, zero_add, fromBlocks_apply₁₂]
  rw [Finset.sum_eq_single (⟨p, hp⟩ : Fin c)]
  · simp [h2]
  · intro j _ hj
    have : j.val ≠ p := fun e => hj (Fin.ext e)
    simp [this]
  · simp

open MeasureTheory ValuativeRel Matrix in

theorem _root_.GlobalTheory.RootEx.ColumnSupport.opE_colE_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : p < c) (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ), ∀ Φ ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∃ K : Set (n → k), IsCompact K ∧ ∀ β, β ∉ K → ∀ χ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ, _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => χ y * _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.colE c (p + 1) β) Φ y) = 0 := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp ψ ν μ Φ hΦ
  have hcs : HasCompactSupport Φ := (show IsLocallyConstant Φ ∧ HasCompactSupport Φ from hΦ).2
  let q : Fin (c + 1) := ⟨p, by omega⟩
  refine ⟨(fun z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => fun r => -z (Sum.inl r) (Sum.inr q)) '' tsupport Φ,
    hcs.isCompact.image (continuous_pi fun r => (continuous_apply_apply _ _).neg), ?_⟩
  intro β hβ χ
  funext x
  unfold _root_.GlobalTheory.RootEx.opE
  refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_)
  have hentry : ∀ r, ((((_root_.GlobalTheory.RootEx.colE c (p + 1) β)⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.affPt (p + 1) x e) (Sum.inl r) (Sum.inr q) = -β r := by
    intro r
    rw [_root_.GlobalTheory.RootEx.ExchangeSupport.colE_inv_val]
    simp [q, Matrix.mul_apply, Fintype.sum_sum_type, _root_.GlobalTheory.RootEx.affPt, _root_.GlobalTheory.RootEx.basePt, _root_.GlobalTheory.RootEx.Free, _root_.GlobalTheory.RootEx.ExchangeSupport.colM, Matrix.one_apply]
    rw [Finset.sum_eq_single ⟨p, hp⟩ (fun b _ hb => if_neg (fun h => hb (Fin.ext h))) (by simp)]
    simp
  have hzero : Φ ((((_root_.GlobalTheory.RootEx.colE c (p + 1) β)⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.affPt (p + 1) x e * ((1 : GL (n' ⊕ Fin (c + 1)) k) : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)) = 0 := by
    by_contra h
    apply hβ
    refine ⟨_, subset_tsupport _ h, ?_⟩
    funext r
    simp only [Units.val_one, Matrix.mul_one]
    rw [hentry r, neg_neg]
  unfold _root_.GlobalTheory.SplitWeil.om
  simp only [Pi.zero_apply]
  rw [hzero]
  simp

end GlobalTheory.RootEx.ColumnSupport
