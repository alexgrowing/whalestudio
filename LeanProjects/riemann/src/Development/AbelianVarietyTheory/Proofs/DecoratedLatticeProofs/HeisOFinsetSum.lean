import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisComb

variable {D : D7}

theorem heisO_finset_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) {ι : Type} (s : Finset ι)
    (a : ι → ℂ) (g : ι → WO S T → ℂ) :
    heisO ψ S T x (∑ i ∈ s, a i • g i) = ∑ i ∈ s, a i • heisO ψ S T x (g i) := by
  funext w
  simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem comb_eq_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = c.sum fun u a => a • heisO ψ S T u f := rfl

theorem comb_comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (comb ψ S T c' f) =
      ∑ x ∈ c.support, ∑ y ∈ c'.support, (c x * c' y) • heisO ψ S T x (heisO ψ S T y f) := by
  unfold comb
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [heisO_finset_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]

theorem symplO_half (S T : HSp D) (e e' : AE D) (x y : WO S T) (he : cA D e = e) (hee : e * e' = 0)
    (hx : IsHalf e x) (hy : IsHalf e' y) : symplO S T x y = 0 := by
  have h0 : e * cA D e' = 0 := by
    conv_lhs => rw [← he]
    rw [← map_mul, hee, map_zero]
  have hh : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    rw [← hy c b, ← hx d a, map_mul]
    calc incA D (S.gram⁻¹ a b) * (cA D e' * cA D (y c b)) * incA D (T.gram c d) * (e * x d a)
        = (e * cA D e') * (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) := by ring
      _ = 0 := by rw [h0, zero_mul]
  unfold symplO
  rw [hh, mul_zero, map_zero]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), (∀ c c' : WO S T →₀ ℂ, ∃ c'' : WO S T →₀ ℂ, (∀ w ∈ c''.support, ∃ x ∈ c.support, ∃ y ∈ c'.support, w = x + y) ∧ ∀ f, comb ψ S T c'' f = comb ψ S T c (comb ψ S T c' f)) ∧ (∀ c c' : WO S T →₀ ℂ, (∀ x ∈ c.support, ∀ y ∈ c'.support, symplO S T x y = 0) → ∀ f, comb ψ S T c (comb ψ S T c' f) = comb ψ S T c' (comb ψ S T c f)) ∧ (∀ (c : WO S T →₀ ℂ) f, IsThetaFunO ψ S T f → IsFinComb c → IsStdChar D ψ (-1) → IsThetaFunO ψ S T (comb ψ S T c f)) ∧ ∀ (e e' : AE D) (x y : WO S T), cA D e = e → e * e' = 0 → IsHalf e x → IsHalf e' y → symplO S T x y = 0 := by
  intro D ψ S T
  refine ⟨fun c c' => ?_, fun c c' h f => ?_, fun c f hf hc hψ => ?_,
    fun e e' x y he hee hx hy => symplO_half S T e e' x y he hee hx hy⟩
  · classical
    refine ⟨∑ x ∈ c.support, ∑ y ∈ c'.support, Finsupp.single (x + y) (c x * c' y * ψ (symplOH S T x y)), ?_,
      fun f => ?_⟩
    · intro w hw
      have h1 := Finsupp.support_finset_sum hw
      rw [Finset.mem_biUnion] at h1
      obtain ⟨x, hx, hw2⟩ := h1
      have h2 := Finsupp.support_finset_sum hw2
      rw [Finset.mem_biUnion] at h2
      obtain ⟨y, hy, hw3⟩ := h2
      have h3 := Finsupp.support_single_subset hw3
      rw [Finset.mem_singleton] at h3
      exact ⟨x, hx, y, hy, h3⟩
    · rw [comb_comb, comb_eq_sum]
      rw [← Finsupp.sum_finset_sum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finsupp.sum_finset_sum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T (x + y) f)), GlobalTheory.WeilVacMove.heisO_heisO, smul_smul]
  · rw [comb_comb, comb_comb, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
    have h0 : symplOH S T x y = 0 := by
      unfold symplOH
      rw [h x hx y hy, mul_zero]
    have h1 : symplOH S T y x = 0 := by
      rw [GlobalTheory.MixModel.symplOH_skew, h0, neg_zero]
    rw [GlobalTheory.WeilVacMove.heisO_heisO, GlobalTheory.WeilVacMove.heisO_heisO, h0, h1, add_comm x y, mul_comm (c x)]
  · exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 f hf (WO S T) c.support id (fun u => c u) hc

end GlobalTheory.HeisComb
