import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointComponentMemSpanOfLatticeGenerators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal

theorem residue_pr_int_eq_zero_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ c : 𝓞 D.host.E,
    ∃ h : p.pr (incA D (algebraMap (𝓞 D.host.E) D.host.E c)) ∈ 𝒪[k], (residue 𝒪[k] ⟨_, h⟩ = 0 ↔ c ∈ P.asIdeal) := by
  intro D k _ _ _ _ p P hP c
  have h : p.pr (incA D (c : D.host.E)) ∈ 𝒪[k] := GlobalTheory.LocMod.FullLatFrame.pr_int_mem p c
  refine ⟨h, ?_⟩
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  by_cases hc : c = 0
  · subst hc
    have h0 : (⟨_, h⟩ : 𝒪[k]) = 0 := by
      apply Subtype.ext
      simp
    refine ⟨fun _ => zero_mem _, fun _ hu => ?_⟩
    exact not_isUnit_zero (h0 ▸ hu)
  have hc' : (c : D.host.E) ≠ 0 := fun h0 => hc (Subtype.ext h0)
  have hinv : p.pr (incA D (c : D.host.E)) * p.pr (incA D (c : D.host.E)⁻¹) = 1 := by
    rw [← RingHom.map_mul, ← map_mul (incA D), mul_inv_cancel₀ hc', map_one, map_one]
  rw [hP.2 c hc, ← p.sec_pr, ← p.int_iff]
  apply not_congr
  constructor
  · intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have hy' : p.pr (incA D (c : D.host.E)) * (y : k) = 1 := congrArg Subtype.val hy
    have hne : p.pr (incA D (c : D.host.E)) ≠ 0 := left_ne_zero_of_mul_eq_one hinv
    have : p.pr (incA D (c : D.host.E)⁻¹) = y := mul_left_cancel₀ hne (hinv.trans hy'.symm)
    rw [this]; exact y.2
  · intro hi
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : 𝒪[k]) (Subtype.ext hinv)

end GlobalTheory.PhiOneVal
