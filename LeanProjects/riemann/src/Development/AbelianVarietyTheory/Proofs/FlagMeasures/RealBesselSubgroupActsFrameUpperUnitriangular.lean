import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabUMapEqOfRoots

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

namespace GlobalTheory.LoopAct

open scoped Classical

theorem exists_coeff_of_mem_span_image {r n : ℕ} (e : Fin r → Fin n → ℂ) (s : Set (Fin r)) (x : Fin n → ℂ)
    (hx : x ∈ Submodule.span ℂ (e '' s)) : ∃ c : Fin r → ℂ, (∀ b, b ∉ s → c b = 0) ∧ x = ∑ b, c b • e b := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  refine ⟨l, fun b hb => ?_, ?_⟩
  · by_contra h
    exact hb (hl (Finsupp.mem_support_iff.mpr h))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro b
    exact zero_smul ℂ (e b)

theorem exists_upUni_of_inS {r n : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : Formalism.L2.SG.HidaSetting.InS e z g) :
    ∃ M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, IsUpUni M ∧
      IsMatOn g (Fin.snoc (α := fun _ => Fin n → ℂ) e z) M := by
  set f : Fin (r + 1) → Fin n → ℂ := Fin.snoc (α := fun _ => Fin n → ℂ) e z with hf

  have hcol : ∀ b : Fin (r + 1), (g - 1) *ᵥ f b ∈ Submodule.span ℂ (e '' {c : Fin r | c.1 < b.1}) := by
    intro b
    refine Fin.lastCases ?_ (fun a => ?_) b
    · simpa [hf, Formalism.L2.SG.HidaSetting.spanLt] using hg.2
    · simpa [hf, Formalism.L2.SG.HidaSetting.spanLt] using hg.1 a
  choose D hD0 hDs using fun b => exists_coeff_of_mem_span_image e _ _ (hcol b)
  refine ⟨fun c b => (if c = b then 1 else 0) + (if h : c.1 < r then D b ⟨c.1, h⟩ else 0), ?_, ?_⟩
  · intro i j
    constructor
    · intro hji
      have hne : i ≠ j := fun h => (lt_irrefl j) (h ▸ hji)
      simp only [hne, if_false, zero_add]
      split_ifs with h
      · apply hD0
        simp only [Set.mem_setOf_eq, not_lt]
        exact le_of_lt hji
      · rfl
    · rintro rfl
      simp only [if_true]
      split_ifs with h
      · rw [hD0 i ⟨i.1, h⟩ (by simp)]
        ring
      · ring
  · intro b
    have hg1 : g *ᵥ f b = (g - 1) *ᵥ f b + f b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
    rw [hg1, hDs b]
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [add_comm, Fin.sum_univ_castSucc]
    simp [hf]

theorem sinfU_frame_upUni : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (y : X.B.I.Ginf), y ∈ X.SinfU u → ∀ v : NumberField.InfinitePlace X.B.I.F, ∃ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ, IsUpUni M ∧ GlobalTheory.LoopAct.IsMatOn (uMat (y v)) (Formalism.L2.SG.RealObj.frm X u 1 v) M := by
  intro D X u y hy v
  obtain ⟨M, hM, hMat⟩ := exists_upUni_of_inS _ _ _ (hy v)
  refine ⟨M, hM, ?_⟩
  have hfr : Formalism.L2.SG.RealObj.frm X u 1 v = Fin.snoc (α := fun _ => Fin X.B.I.n → ℂ)
      (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) := by
    funext a
    simp [Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc, Formalism.L2.SG.RealObj.fam]
  rw [hfr]
  exact hMat

end GlobalTheory.LoopAct

end
