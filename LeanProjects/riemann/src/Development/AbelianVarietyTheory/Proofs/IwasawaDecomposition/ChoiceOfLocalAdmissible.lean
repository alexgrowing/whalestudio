import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapRealSubfieldEqIffEqOrIsConjPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSpacesOfOver
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotVstdOfGramOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.HeightCounting.FirstFacts

theorem pair_of_over (D : D7) {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host}
    (hPq : ∀ v, NG.OverPl (Pq v) v) (P P' : PlE D.host) (hc : IsConjPl D.host P P') (hne : P ≠ P') :
    P ∈ Set.range Pq ↔ P' ∉ Set.range Pq := by
  have e := (GlobalTheory.PlacePair.comap_eq_iff D P P').2 (Or.inr hc)
  constructor
  · rintro ⟨v, rfl⟩ ⟨v', rfl⟩
    obtain rfl : v = v' := HeightOneSpectrum.ext ((hPq v).symm.trans (e.trans (hPq v')))
    exact hne rfl
  · intro h
    let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := P.under _
    have hv : NG.OverPl P v := rfl
    rcases (GlobalTheory.PlacePair.comap_eq_iff D P (Pq v)).1 (hv.trans (hPq v).symm) with e1 | e1
    · exact ⟨v, e1.symm⟩
    · exact absurd ⟨v, GlobalTheory.GalChar.isConjPl_unique e1 hc⟩ h

theorem vstd_of_over {K : GlobalTheory.Mem.Top.Ctx} (X : GlobalTheory.Mem.Stages) (hX : K.Over X.B.toPre) (i : Fin X.toD7.R.m) :
    FWT.VStd X.toD7 i := by
  obtain ⟨-, -, -, -, -, hVf, -⟩ := GlobalTheory.Mem.HostFrames.frames_of_over K X hX
  obtain ⟨h1, h2⟩ := hVf i
  rw [GlobalTheory.StdFrameCounterexample.vstd_iff]
  refine ⟨Matrix.ext fun a b => ?_, fun x => ?_⟩
  · rw [HSpace.gram, h1, Matrix.one_apply]
  · rw [h2, Module.Basis.mem_span_iff_repr_mem, Module.Basis.repr_sum_self]
    refine forall_congr' fun a => ?_
    constructor
    · rintro ⟨y, hy⟩
      rw [← hy]; exact y.2
    · intro h
      exact ⟨⟨x a, h⟩, rfl⟩

theorem mem_range_of_mem_QE {X : Col.Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {Q : HeightOneSpectrum (𝓞 X.E)} : ∀ {ξ}, Q ∈ Col.QE sel ξ → Q ∈ Set.range sel := by
  classical
  intro ξ h
  unfold Col.QE at h
  split_ifs at h
  · obtain ⟨v, -, e⟩ := Finset.mem_image.1 h
    exact ⟨v, e⟩
  · exact absurd h (Finset.notMem_empty _)

theorem facts : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : GlobalTheory.Mem.Top.Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : GlobalTheory.Mem.Top.TwDat B} {w : GlobalTheory.Mem.Top.Bl.ColW B f T}, K.Over B.toPre → GlobalTheory.Mem.Top.Bl.Start K B f T w → ∀ {P : GlobalTheory.Mem.R3.Rw.Pre2 K w} (x : GlobalTheory.Mem.R3.Rw.St P) (l : GlobalTheory.HeightCounting.Up.LA hL x), IsChoice (D := GlobalTheory.HeightCounting.Up.Dof x) (Set.range l.Pq) ∧ (∀ t, ∀ Q ∈ x.m.z.R.Q t, Q ∈ Set.range l.Pq) ∧ (∀ j, FWT.VStd (GlobalTheory.HeightCounting.Up.Dof x) j) ∧ x.m.z.R.C = GlobalTheory.HeightCounting.Up.cfOf x ∧ ∀ (k : Fin 2) (z : ℂ), z ^ ((GlobalTheory.HeightCounting.Up.Dof x).host.g k * ((GlobalTheory.HeightCounting.Up.Dof x).host.g k - 1)) = 1 → z ∈ (embLL0 (GlobalTheory.HeightCounting.Up.Dof x)).fieldRange := by
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
