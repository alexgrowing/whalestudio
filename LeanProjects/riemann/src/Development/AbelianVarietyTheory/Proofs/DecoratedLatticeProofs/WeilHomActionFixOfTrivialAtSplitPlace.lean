import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceSectionAddComplementMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.OffFix

open scoped TensorProduct

variable {D : D7}

theorem idOff_mul_eq_zero {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {x y : AE D}
    (hx : x ∈ idOff D (· = v)) (hy : algebraMap (AF D.host.F) (AE D) ε * y = y) : x * y = 0 := by
  classical
  obtain ⟨α, hεα, hv, hw⟩ := hε
  obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D v ε α hεα
  have hc' : ∀ w, compAt D w (algebraMap (AF D.host.F) (AE D) ε) = if w = v then 1 else 0 := by
    intro w
    rw [hc w]
    by_cases h : w = v
    · subst h; rw [if_pos rfl, hv]; rfl
    · rw [if_neg h, hw w h, TensorProduct.zero_tmul]
  have hx0 := (SetCut.mem_idOff_iff_mul (· = v) _ h0 hc' x).1 hx
  rw [← hy, ← mul_assoc, mul_comm x, hx0, zero_mul]

theorem supp_of_mem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {ε : AF D.host.F} (hε : IsPlaceIdem D p.v ε)
    (hsum : p.e + cA D p.e = algebraMap (AF D.host.F) (AE D) ε) (S T : HSp D) (LS : Lat S) (LT : Lat T) (u : WO S T)
    (hu : u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) ∨
      IsHalf p.e u ∨ IsHalf (cA D p.e) u) :
    ∀ i j, algebraMap (AF D.host.F) (AE D) ε * u i j = u i j := by
  rcases hu with hu | hu | hu
  · intro i j
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, -, hα0, a, -, s, -, t, -, rfl⟩ := hw
      have hmem : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) ∈ idAt D (· = p.v) := by
        obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D p.v _ α rfl
        rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
        exact ⟨h0, fun w hw => by rw [hc w, hα0 w hw, TensorProduct.zero_tmul]⟩
      rw [Matrix.of_apply]
      have hfac : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) =
          algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) *
            ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hfac]
      exact ((placeIdem_acts D p.v ε hε).1 _).1 (Ideal.mul_mem_right _ _ hmem)
    | zero => simp
    | add x y _ _ hx hy => simp only [Matrix.add_apply, mul_add, hx, hy]
    | neg x _ hx => simp only [Matrix.neg_apply, mul_neg, hx]
  · intro i j
    have hce : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, p.split.1, mul_comm (cA D p.e), p.split.2.1, add_zero]
    rw [← hu i j, ← mul_assoc, hce]
  · intro i j
    have hce : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by
      rw [← hsum, add_mul, p.split.2.1, zero_add, ← map_mul, p.split.1]
    rw [← hu i j, ← mul_assoc, hce]

theorem actO_eq_of_grpOff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (LS : Lat S) (LT : Lat T) (g : GA D S) (h : GA D T),
    g ∈ grpOff S (· = p.v) → h ∈ grpOff T (· = p.v) → ∀ u : WO S T,
    (u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) ∨ IsHalf p.e u ∨
      IsHalf (cA D p.e) u) → actO S T g h u = u := by
  intro D k _ _ _ _ p S T LS LT g h hg hh u hu
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hsupp := supp_of_mem p hε hsum S T LS LT u hu
  have hA : ∀ i j, (Formalism.L2.Theta.mt T h - 1) i j ∈ idOff D (· = p.v) :=
    (SetCut.mem_congGrp_iff T (idOff D (· = p.v)) h).1 hh
  have hB : ∀ i j, (Formalism.L2.Theta.mt S g⁻¹ - 1) i j ∈ idOff D (· = p.v) :=
    (SetCut.mem_congGrp_iff S (idOff D (· = p.v)) g⁻¹).1 (inv_mem hg)
  let U : Matrix (Fin T.rank) (Fin S.rank) (AE D) := u
  have hU : ∀ i j, algebraMap (AF D.host.F) (AE D) ε * U i j = U i j := hsupp
  have h1 : HMul.hMul (Formalism.L2.Theta.mt T h - 1) U = (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun l _ => idOff_mul_eq_zero hε (hA i l) (hU l j)
  have h2 : HMul.hMul U (Formalism.L2.Theta.mt S g⁻¹ - 1) = (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun l _ => by rw [mul_comm]; exact idOff_mul_eq_zero hε (hB l j) (hU i l)
  have e1 : HMul.hMul (Formalism.L2.Theta.mt T h) U = U := by rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1; exact h1
  have e2 : HMul.hMul U (Formalism.L2.Theta.mt S g⁻¹) = U := by rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2; exact h2
  show HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) U) (Formalism.L2.Theta.mt S g⁻¹) = U
  rw [e1, e2]

end GlobalTheory.FinPl.OffFix

end
