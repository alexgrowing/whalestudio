import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal

theorem mem_prime_iff_pr_inv_notMem {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E))
    (h : Formalism.L2.NTheta.IsIdemAt p.e P) (x : 𝓞 D.host.E) (hx : x ≠ 0) :
    x ∈ P.asIdeal ↔ p.pr (incA D ((x : D.host.E)⁻¹)) ∉ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr]
  exact h.2 x hx

theorem exists_denom_notMem_of_pr_int : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ a : D.host.E, p.pr (incA D a) ∈ 𝒪[k] →
    ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ c : 𝓞 D.host.E,
      algebraMap (𝓞 D.host.E) D.host.E c = algebraMap (𝓞 D.host.E) D.host.E s * a := by
  intro D k _ _ _ _ p P h a ha
  obtain ⟨n, ⟨d, hd⟩, hnd | hnd⟩ := P.exists_primeCompl_mul_eq_or_mul_eq (K := D.host.E) a
  · exact ⟨d, hd, n, by rw [← hnd, mul_comm]⟩
  · have hd' : d ∉ P.asIdeal := hd
    have hd0 : d ≠ 0 := fun h0 => hd' (h0 ▸ P.asIdeal.zero_mem)
    have hnd' : a * (n : D.host.E) = (d : D.host.E) := hnd
    have hdE : (d : D.host.E) ≠ 0 := fun h0 => hd0 (RingOfIntegers.coe_eq_zero_iff.mp h0)
    have hnE : (n : D.host.E) ≠ 0 := fun h0 => hdE (by rw [← hnd', h0, mul_zero])
    have hn0 : n ≠ 0 := fun h0 => hnE (by rw [h0]; rfl)
    refine ⟨n, fun hn => ?_, d, by rw [mul_comm]; exact hnd.symm⟩
    have h1 := (mem_prime_iff_pr_inv_notMem p P h n hn0).1 hn
    have h2 := not_not.1 (mt (mem_prime_iff_pr_inv_notMem p P h d hd0).2 hd')
    apply h1
    have h3 : (n : D.host.E)⁻¹ = a * (d : D.host.E)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hdE, ← hnd', mul_comm a, inv_mul_cancel_left₀ hnE]
    rw [h3, map_mul, map_mul]
    exact mul_mem ha h2

end GlobalTheory.PhiOneVal

end
