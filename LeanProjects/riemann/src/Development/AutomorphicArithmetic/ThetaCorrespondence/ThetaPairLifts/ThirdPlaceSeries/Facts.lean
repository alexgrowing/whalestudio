import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceOfLocalAdmissible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
noncomputable section
namespace GlobalTheory.HeightCounting.FirstFacts
theorem facts_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : GlobalTheory.Mem.Top.Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : GlobalTheory.Mem.Top.TwDat B} {w : GlobalTheory.Mem.Top.Bl.ColW B f T}, K.Over B.toPre → GlobalTheory.Mem.Top.Bl.Start K B f T w → ∀ {P : GlobalTheory.Mem.R3.Rw.Pre2 K w} (x : GlobalTheory.Mem.R3.Rw.St P) (l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x), IsChoice (D := GlobalTheory.HeightCounting.Up.Dof x) (Set.range l.Pq) ∧ (∀ t, ∀ Q ∈ x.m.z.R.Q t, Q ∈ Set.range l.Pq) ∧ (∀ j, FWT.VStd (GlobalTheory.HeightCounting.Up.Dof x) j) ∧ x.m.z.R.C = GlobalTheory.HeightCounting.Up.cfOf x ∧ ∀ (k : Fin 2) (z : ℂ), z ^ ((GlobalTheory.HeightCounting.Up.Dof x).host.g k * ((GlobalTheory.HeightCounting.Up.Dof x).host.g k - 1)) = 1 → z ∈ (embLL0 (GlobalTheory.HeightCounting.Up.Dof x)).fieldRange := by
  intro hL K B f T w hK hS P x l
  obtain ⟨⟨c⟩, -⟩ := hS
  refine ⟨⟨pair_of_over _ l.Pq_over, ?_⟩, ?_, vstd_of_over (w.st x.o.Z) hK, x.m.z.lev.C, fun k z hz => ?_⟩
  · rw [l.sel]
    rintro _ ⟨v, rfl⟩ _ ⟨v', rfl⟩ ⟨p, hp, h1, h2⟩
    have key : ∀ u : HeightOneSpectrum (𝓞 B.host.F), (p : 𝓞 B.host.E) ∈ (w.I.sel u).asIdeal → (p : 𝓞 B.host.F) ∈ u.asIdeal := by
      intro u hu
      have e : (w.I.sel u).asIdeal.under (𝓞 B.host.F) = u.asIdeal := w.ok.sel_ok u
      rw [← e, Ideal.mem_comap, map_natCast]
      exact hu
    exact congrArg HeightOneSpectrum.asIdeal (c.half v v' p hp (key v h1) (key v' h2))
  · intro t Q hQ
    rw [x.m.z.lev.Q] at hQ
    rw [l.sel]
    exact mem_range_of_mem_QE hQ
  · have h0 : B.host.g k * (B.host.g k - 1) ≠ 0 :=
      mul_ne_zero (B.host.g_prime k).ne_zero (by have := (B.host.g_prime k).two_le; omega)
    obtain ⟨y, hy, e⟩ := B.roots_Ks (B.host.g k * (B.host.g k - 1)) (by fin_cases k <;> simp)
    obtain ⟨u, hu⟩ := GlobalTheory.Mem.Col2.InEx.root_mem (embLL0 (GlobalTheory.HeightCounting.Up.Dof x)) h0 ⟨⟨y, B.Ks_le hy⟩, e⟩ hz
    exact ⟨u, hu⟩
end GlobalTheory.HeightCounting.FirstFacts
end
end
