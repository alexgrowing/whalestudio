import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LineRowFrame

variable {D : D7}

theorem half_mul {e : AE D} {l m n : ℕ} {u : Mx D l m} (hu : IsHalf e u) (v : Mx D m n) : IsHalf e (u ⬝ v) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hu i]

theorem mul_half {e : AE D} {l m n : ℕ} (u : Mx D l m) {v : Mx D m n} (hv : IsHalf e v) : IsHalf e (u ⬝ v) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [mul_left_comm, hv a j]

theorem adj_half {e : AE D} {m n : ℕ} {u : Mx D m n} (hu : IsHalf e u) : IsHalf (cA D e) (adj u) := fun i j => by
  change cA D e * cA D (u j i) = cA D (u j i)
  rw [← map_mul, hu j i]

theorem ofAdj_half {e : AE D} (S T : HSp D) {z : Mx D S.rank T.rank} (hz : IsHalf e z) :
    IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T z) := fun i j => by
  have h := mul_half (giA T) (half_mul (adj_half hz) (gA S)) i j
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj, Matrix.smul_apply, smul_eq_mul, mul_left_comm, h]

theorem xi_mul_hO (S T : HSp D) (x : WO S T) (z : Mx D S.rank T.rank) :
    incA D D.host.xi0 * hO S T x (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T z) = (z ⬝ x).trace := by
  conv_rhs => rw [← GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj_ofAdj S T z]
  rw [hO_eq_trace, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc,
    Matrix.mul_assoc]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem incA_mul_ι (a : D.host.E) (x : k) : incA D a * p.ι x = p.ι (p.pr a * x) := by
  conv_rhs => rw [← p.π_ι x, Place.pr, ← map_mul, p.ι_π, mul_left_comm, Witness.e_ι]

theorem pr_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (v : Fin n → D.host.E) (r : Fin m) :
    p.pr ((M *ᵥ v) r) = ∑ a, p.pr (M r a) * p.pr (v a) := by
  simp only [Place.pr, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem line_row : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (s : k), s ≠ 0 → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B s FA F₀ → p.IsCoreFrame B' (s * p.xi) FA' F₀' → ∀ u₀ : n → k, ∃ x : WO S B'.L, p.up FS F₀' (fromRows 0 (Matrix.of fun _ => u₀)) = (B'.o.resT S).symm (0, x) ∧ IsHalf (cA D p.e) ((B.o.resS S).symm (0, l.κ S x)) ∧ ∀ t : Matrix n (n' ⊕ Unit) k, ψ (symplO B.V₀ S (p.up F₀ FS t) ((B.o.resS S).symm (0, l.κ S x))) = ((ψk (-(u₀ ⬝ᵥ fun r => t r (Sum.inr ()))) : Circle) : ℂ) := by
  intro D k _ _ _ _ p ψ hψ ψk hk ρ σ B B' l S s hs n n' n'' _ _ _ _ _ _ FA F₀ FS FA' F₀' h₀ h₀' u₀
  have hxi : p.xi ≠ 0 := (GlobalTheory.LocChar.weil_char_split D k p ψ hψ).2.2.1
  obtain ⟨w, hw⟩ : ∃ w, w = u₀ ᵥ* FS.γ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : WO S B'.L, ∀ a c, x a c = p.ι (s * p.xi * p.pr (B'.ζ a) * w c) :=
    ⟨Matrix.of fun a c => p.ι (s * p.xi * p.pr (B'.ζ a) * w c), fun _ _ => rfl⟩
  have hxh : IsHalf p.e x := fun a c => by rw [hx, Witness.e_ι]
  have hy : (B.o.resS S).symm (0, l.κ S x) = l.κ S x ⬝ B.o.pB := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
  have hh : IsHalf (cA D p.e) ((B.o.resS S).symm (0, l.κ S x)) := by
    rw [hy]
    exact half_mul (ofAdj_half B.L S (mul_half _ hxh)) _
  refine ⟨x, ?_, hh, fun t => ?_⟩
  · rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    ext r c
    have e1 : (F₀'.β * (fromRows 0 (Matrix.of fun _ => u₀) : Matrix (n'' ⊕ Unit) n k) * FS.γ) r c = s * p.xi * p.pr (vecB B'.o B'.ζ r) * w c := by
      rw [Matrix.mul_assoc, fromRows_mul, Matrix.zero_mul, Matrix.mul_apply, Fintype.sum_sum_type, ← h₀'.2 r, hw]
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
    change p.ι ((F₀'.β * (fromRows 0 (Matrix.of fun _ => u₀) : Matrix (n'' ⊕ Unit) n k) * FS.γ) r c) = _
    rw [e1, vecB, pr_mulVec, Finset.mul_sum, Finset.sum_mul, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx]
    change _ = incA D (B'.o.iB r a) * _
    rw [incA_mul_ι]
    congr 1
    ring
  · rw [(GlobalTheory.LocSympl.halves_at_split D k p _ _ B.V₀ S F₀ FS ψ ψk hk).2.2.2.1 t _ hh]
    congr 2
    rw [B.o.hO_resS, AddEquiv.apply_symm_apply, hO_eq_trace B.A, adj_zero, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.trace_zero, zero_add]
    refine mul_left_cancel₀ hxi ?_
    have e2 : ∀ a c, p.π (((rat l.τ : Mx D B.L.rank B'.L.rank) ⬝ x) a c) = -(s * p.xi * w c) * p.pr (B.ζ a) := fun a c => by
      have h1 := pr_mulVec p l.τ B'.ζ a
      rw [l.map, Pi.neg_apply, Place.pr, map_neg, map_neg] at h1
      rw [Place.pr, neg_mul, ← mul_neg, h1, Matrix.mul_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, hx, p.π_ι]
      change p.pr (l.τ a b) * _ = _
      ring
    have e3 : ∀ c a, p.π ((p.up F₀ FS t ⬝ B.o.jB) c a) = ∑ r, (FS.β * t * F₀.γ) c r * p.pr (B.o.iB r a) := fun c a => by
      rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_mul]
      exact congrArg (· * _) (p.π_ι _)
    have e4 : ∀ c, ∑ r, (FS.β * t * F₀.γ) c r * F₀.β r (Sum.inr ()) = (FS.β * t) c (Sum.inr ()) := fun c => by
      rw [← Matrix.mul_apply, Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
    have e5 : ∑ c, w c * (FS.β * t) c (Sum.inr ()) = u₀ ⬝ᵥ fun r => t r (Sum.inr ()) := by
      change (w ᵥ* (FS.β * t)) (Sum.inr ()) = (u₀ ᵥ* t) (Sum.inr ())
      rw [hw, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, FS.γβ, Matrix.one_mul]
    change p.π (incA D D.host.xi0) * p.π (hO B.L S (p.up F₀ FS t ⬝ B.o.jB) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.L S _)) = _
    rw [← map_mul, xi_mul_hO, Matrix.trace_mul_comm, ← e5, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
      Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, map_sum, ← e4,
      Finset.sum_congr rfl fun a _ => (p.π.map_mul _ _).trans (congrArg₂ (· * ·) (e3 c a) (e2 a c))]
    generalize FS.β * t * F₀.γ = M
    simp only [h₀.2, vecB, pr_mulVec, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ => ?_
    ring

end GlobalTheory.LineRowFrame
