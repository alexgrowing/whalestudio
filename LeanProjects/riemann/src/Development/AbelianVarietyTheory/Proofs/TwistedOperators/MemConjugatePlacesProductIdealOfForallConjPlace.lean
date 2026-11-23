import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLevel.InfMem

theorem conjI_eq_comap (D : D7) (P : Ideal (𝓞 D.host.E)) : conjI P = P.comap GlobalTheory.SW.Lev.bar := by
  ext a; rw [GlobalTheory.SW.Lev.mem_conjI, Ideal.mem_comap]

theorem bar_surj (D : D7) : Function.Surjective (GlobalTheory.SW.Lev.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
  fun a => ⟨GlobalTheory.SW.Lev.bar a, GlobalTheory.SW.Lev.bar_bar a⟩

theorem conjI_isMaximal (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E) : (conjI PP.asIdeal).IsMaximal := by
  rw [conjI_eq_comap]
  haveI := PP.isMaximal
  exact Ideal.comap_isMaximal_of_surjective _ (bar_surj D)

theorem conjI_inj (D : D7) {PP PP' : Formalism.L2.DIV.Pl D.host.E} (h : conjI PP.asIdeal = conjI PP'.asIdeal) : PP = PP' := by
  apply HeightOneSpectrum.ext
  ext a
  have := congrArg (fun I => GlobalTheory.SW.Lev.bar a ∈ I) h
  simp only [GlobalTheory.SW.Lev.mem_conjI, GlobalTheory.SW.Lev.bar_bar] at this
  exact Iff.of_eq this

theorem mem_liftI (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : 𝓞 D.host.E)
    (hx : ∀ PP ∈ Pg ∪ Q, x ∈ conjI PP.asIdeal) : x ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
  unfold GlobalTheory.LiftLevel.liftI
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp only [Submodule.mem_iInf]
    exact hx
  · intro PP _ PP' _ hne
    have hne' : conjI PP.asIdeal ≠ conjI PP'.asIdeal := fun h => hne (conjI_inj D h)
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne (conjI_isMaximal D PP) (conjI_isMaximal D PP') hne'

theorem main : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : 𝓞 D.host.E), (∀ PP ∈ Pg ∪ Q, x ∈ conjI PP.asIdeal) → x ∈ GlobalTheory.LiftLevel.liftI Pg Q := fun D Pg Q x hx => mem_liftI D Pg Q x hx

end GlobalTheory.LiftLevel.InfMem
