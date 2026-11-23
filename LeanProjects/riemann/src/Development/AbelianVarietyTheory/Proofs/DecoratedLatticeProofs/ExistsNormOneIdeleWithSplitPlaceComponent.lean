import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

set_option maxHeartbeats 2000000 in
open GlobalTheory.FinPl.FrameLat in

theorem exists_normOneAt_pr (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (c₀ : k) (hc₀ : c₀ ≠ 0) :
    ∃ c : AE D, NormOneAt p.v c ∧ p.pr c = c₀ := by
  have hf : ∀ x : k, (p.e + cA D p.e) * p.sec x = p.sec x := fun x => (idem_iff p _).1 (sec_mem_idAt p x)
  have hcf : ∀ x : k, (p.e + cA D p.e) * cA D (p.sec x) = cA D (p.sec x) :=
    fun x => (idem_iff p _).1 (csec_mem_idAt (p := p) x)
  have hee : p.e * cA D p.e = 0 := p.split.2.1
  have hce : cA D p.e * p.e = 0 := cAe_mul_e p
  have hecs : ∀ x : k, p.e * cA D (p.sec x) = 0 := by
    intro x
    rw [← e_mul_sec p x, map_mul, ← mul_assoc, hee, zero_mul]
  have hsc : ∀ x y : k, p.sec x * cA D (p.sec y) = 0 := by
    intro x y
    rw [← e_mul_sec p x, mul_comm p.e, mul_assoc, hecs, mul_zero]
  have hprc : ∀ x : k, p.pr (cA D (p.sec x)) = 0 := by
    intro x
    have h1 : p.sec (p.pr (cA D (p.sec x))) = 0 := by rw [p.sec_pr, hecs]
    have h2 := congrArg p.pr h1
    rwa [p.pr_sec, map_zero] at h2
  have hcc : ∀ z : AE D, cA D (cA D z) = z := fun z => cA_cA z
  have he1 : p.sec 1 = p.e := sec_one p
  obtain ⟨f, hfdef⟩ : ∃ f : AE D, f = p.e + cA D p.e := ⟨_, rfl⟩
  have hfm : f ∈ idAt D (· = p.v) := hfdef ▸ sum_mem_idAt p
  have hff : f * f = f := by
    have := (idem_iff p f).1 hfm; rwa [← hfdef] at this
  have hf' : ∀ x : k, f * p.sec x = p.sec x := fun x => hfdef ▸ hf x
  have hcf' : ∀ x : k, f * cA D (p.sec x) = cA D (p.sec x) := fun x => hfdef ▸ hcf x

  obtain ⟨u, hu⟩ : ∃ u : AE D, u = 1 - f := ⟨_, rfl⟩
  have huf : u * f = 0 := by rw [hu, sub_mul, one_mul, hff, sub_self]
  have hus : ∀ x : k, u * p.sec x = 0 := by intro x; rw [← hf' x, ← mul_assoc, huf, zero_mul]
  have hucs : ∀ x : k, u * cA D (p.sec x) = 0 := by intro x; rw [← hcf' x, ← mul_assoc, huf, zero_mul]
  have huu : u * u = u := by nth_rewrite 2 [hu]; rw [mul_sub, mul_one, huf, sub_zero]
  have hcu : cA D u = u := by
    rw [hu, hfdef, map_sub, map_one, map_add, hcc, add_comm]
  refine ⟨u + p.sec c₀ + cA D (p.sec c₀⁻¹), ⟨?_, ?_⟩, ?_⟩
  · have hconj : cA D (u + p.sec c₀ + cA D (p.sec c₀⁻¹)) = u + cA D (p.sec c₀) + p.sec c₀⁻¹ := by
      rw [map_add, map_add, hcu, hcc]
    show _ * cA D _ = 1
    rw [hconj]
    have e1 : p.sec c₀ * p.sec c₀⁻¹ = p.e := by rw [← sec_mul p, mul_inv_cancel₀ hc₀, he1]
    have e2 : cA D (p.sec c₀⁻¹) * cA D (p.sec c₀) = cA D p.e := by
      rw [← map_mul (cA D), ← sec_mul p, inv_mul_cancel₀ hc₀, he1]
    have s1 : p.sec c₀ * u = 0 := by rw [mul_comm (p.sec c₀) u]; exact hus _
    have s2 : cA D (p.sec c₀⁻¹) * u = 0 := by rw [mul_comm (cA D (p.sec c₀⁻¹)) u]; exact hucs _
    have s3 : cA D (p.sec c₀⁻¹) * p.sec c₀⁻¹ = 0 := by rw [mul_comm (cA D (p.sec c₀⁻¹)) (p.sec c₀⁻¹)]; exact hsc _ _
    have s4 : p.sec c₀ * cA D (p.sec c₀) = 0 := hsc _ _
    have expand : (u + p.sec c₀ + cA D (p.sec c₀⁻¹)) * (u + cA D (p.sec c₀) + p.sec c₀⁻¹)
        = u * u + u * cA D (p.sec c₀) + u * p.sec c₀⁻¹ + p.sec c₀ * u + p.sec c₀ * cA D (p.sec c₀)
          + p.sec c₀ * p.sec c₀⁻¹ + cA D (p.sec c₀⁻¹) * u + cA D (p.sec c₀⁻¹) * cA D (p.sec c₀)
          + cA D (p.sec c₀⁻¹) * p.sec c₀⁻¹ := by ring
    rw [expand, huu, hucs, hus, s1, s4, e1, s2, e2, s3, hu, hfdef]
    ring
  · have : u + p.sec c₀ + cA D (p.sec c₀⁻¹) - 1 = -f + p.sec c₀ + cA D (p.sec c₀⁻¹) := by rw [hu]; ring
    rw [this]
    refine add_mem (add_mem (neg_mem hfm) (sec_mem_idAt p _)) (csec_mem_idAt (p := p) _)
  · rw [map_add, map_add, hprc, add_zero, hu, hfdef, map_sub, map_one, map_add, ← he1, hprc, p.pr_sec, p.pr_sec]
    ring

end GlobalTheory.Core.Mi.LatMatch
