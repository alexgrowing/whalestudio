import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.IdVOne

variable {D : D7}

def finIncl (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem finIncl_tmul (y : Af D.host.F) (x : D.host.E) :
    finIncl D (y ⊗ₜ[D.host.F] x) = pairA D.host.F 0 y ⊗ₜ[D.host.F] x := rfl

theorem mul_eq_mul_finIncl (v : Pl D) (b : AE D) :
    algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * b =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * finIncl D (finPart D b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul x c =>
    have h : finPart D (x ⊗ₜ[D.host.F] c) = sndA D.host.F x ⊗ₜ[D.host.F] c := rfl
    rw [h, finIncl_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    congr 1
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) * x.1 = 0 * 0
      rw [zero_mul, zero_mul]
    · rfl
  | add x y hx hy => rw [mul_add, hx, hy, RingHom.map_add, LinearMap.map_add, mul_add]

theorem mul_finIncl_mem (v : Pl D) (t : Af D.host.F ⊗[D.host.F] D.host.E) (ht : t ∈ intAE D) :
    algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * finIncl D t ∈ idV (1 : FI D) v := by
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨GlobalTheory.SelfDualAt.indP (· = v) * α, ?_, ?_, (x : D.host.E), ?_, ?_⟩
    · intro w
      rw [map_mul]
      refine mul_mem ?_ (hα w)
      rw [GlobalTheory.SelfDualAt.evalV_indP]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro w hw
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP, if_neg hw, zero_mul]
    · exact (FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩
    · rw [finIncl_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      refine Prod.ext ?_ ?_
      · show (0 : Ainf D.host.F) * 0 = 0
        rw [zero_mul]
      · rfl
  | zero => rw [map_zero, mul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add, mul_add]; exact add_mem h1 h2
  | neg x _ h => rw [map_neg, mul_neg]; exact neg_mem h

end GlobalTheory.SeeSaw.IdVOne

open GlobalTheory.SeeSaw.IdVOne in

theorem GlobalTheory.SeeSaw.idV_one_eq_intAt :
    ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v) := by
  intro D v a
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, hv, x, hx, rfl⟩ := hy
      obtain ⟨x', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      refine ⟨?_, ?_⟩
      · rw [idAt, Ideal.mem_inf, Ideal.mem_iInf]
        refine ⟨?_, fun w => ?_⟩
        · rw [RingHom.mem_ker]
          show fstA D.host.F (pairA D.host.F 0 α) ⊗ₜ[D.host.F] _ = 0
          exact TensorProduct.zero_tmul _ _
        · rw [RingHom.mem_ker]
          show evalV D.host.F w.1 (sndA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] _ = 0
          have : evalV D.host.F w.1 α = 0 := hv w.1 w.2
          rw [show sndA D.host.F (pairA D.host.F 0 α) = α from rfl, this]
          exact TensorProduct.zero_tmul _ _
      · exact AddSubgroup.subset_closure ⟨α, hα, x', rfl⟩
    | zero => exact ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
    | add x y _ _ h1 h2 => exact ⟨add_mem h1.1 h2.1, by rw [RingHom.map_add]; exact add_mem h1.2 h2.2⟩
    | neg x _ h => exact ⟨neg_mem h.1, by rw [RingHom.map_neg]; exact neg_mem h.2⟩
  · rintro ⟨ha, hf⟩
    rw [← GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul (· = v) a ha, mul_eq_mul_finIncl]
    exact mul_finIncl_mem v _ hf

example : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v) :=
  GlobalTheory.SeeSaw.idV_one_eq_intAt

end
