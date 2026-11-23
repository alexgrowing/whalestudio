import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdAdelicChar

theorem eq_of_psiInf_eq {F : Type} [Field F] [NumberField F] {ψ ψ' : AddChar (AF F) ℂ}
    (h : IsCharAF F ψ) (h' : IsCharAF F ψ') (e : ∀ x, psiInf F ψ x = psiInf F ψ' x) : ψ = ψ' := by
  have hrat : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) = ψ' (pairA F 0 (algebraMap F (Af F) x)) := fun x => by
    rw [GlobalTheory.StdRat.char_fin_rat ψ h, GlobalTheory.StdRat.char_fin_rat ψ' h', e]
  have hp : Continuous fun y : Af F => pairA F 0 y := Continuous.prodMk continuous_const continuous_id
  have hint : ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 α) = ψ' (pairA F 0 α) :=
    fun α hα => GlobalTheory.IntDense.mem_of_isClosed F (C := {y | ψ (pairA F 0 y) = ψ' (pairA F 0 y)})
      (isClosed_eq (h.1.comp hp) (h'.1.comp hp)) (fun a => hrat a) α hα
  have hfin : ∀ y : Af F, ψ (pairA F 0 y) = ψ' (pairA F 0 y) := fun y => by
    obtain ⟨a, s, hs, hy⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos y
    have e1 : pairA F 0 y = pairA F 0 (algebraMap F (Af F) a) + pairA F 0 s := by
      refine Prod.ext (add_zero _).symm ?_
      show y = algebraMap F (Af F) a + s
      simpa only [one_smul] using hy
    rw [e1, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hrat, hint s hs]
  refine AddChar.ext _ _ fun a => ?_
  have e2 : a = pairA F a.1 0 + pairA F 0 a.2 := Prod.ext (add_zero _).symm (zero_add _).symm
  rw [e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hfin]
  exact congrArg (· * _) (e a.1)

theorem isCharAF_inv {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ) :
    IsCharAF F ψ⁻¹ := by
  refine ⟨?_, fun x => ?_, fun a => ?_, ?_⟩
  · exact h.1.comp continuous_neg
  · exact h.2.1 (-x)
  · rw [AddChar.inv_apply, ← map_neg]; exact h.2.2.1 _
  · obtain ⟨x, hx⟩ := h.2.2.2
    exact ⟨-x, by rwa [AddChar.inv_apply, neg_neg]⟩

theorem isStdChar_inv {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {s : ℤ} (h : IsStdChar D ψ s) :
    IsStdChar D ψ⁻¹ (-s) := by
  refine ⟨isCharAF_inv h.1, h.2.1, fun θ hθ x => ?_⟩
  have e : psiInf D.host.F ψ⁻¹ x = psiInf D.host.F ψ (-x) := by
    rw [psiInf, psiInf, AddChar.inv_apply]
    exact congrArg ψ (Prod.ext rfl neg_zero)
  rw [e, h.2.2 θ hθ]
  simp only [TensorProduct.neg_tmul, map_neg, Finset.sum_neg_distrib]
  congr 1
  push_cast
  ring

theorem isStdChar_unique {D : D7} {ψ ψ' : AddChar (AF D.host.F) ℂ} {s : ℤ} (h : IsStdChar D ψ s)
    (h' : IsStdChar D ψ' s) : ψ = ψ' := by
  obtain ⟨θ, hθ⟩ := h.2.1
  exact eq_of_psiInf_eq h.1 h'.1 fun x => (h.2.2 θ hθ x).trans (h'.2.2 θ hθ x).symm

theorem existsUnique_isStdChar :
    ∀ (D : D7) (s : ℤ), s = 1 ∨ s = -1 → ∃! ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ s := by
  intro D s hs
  obtain ⟨ψ, hψ⟩ := exists_isStdChar D
  rcases hs with rfl | rfl
  · have h1 : IsStdChar D ψ⁻¹ 1 := by simpa using isStdChar_inv hψ
    exact ⟨ψ⁻¹, h1, fun ψ' h' => isStdChar_unique h' h1⟩
  · exact ⟨ψ, hψ, fun ψ' h' => isStdChar_unique h' hψ⟩

end GlobalTheory.StdAdelicChar

end
