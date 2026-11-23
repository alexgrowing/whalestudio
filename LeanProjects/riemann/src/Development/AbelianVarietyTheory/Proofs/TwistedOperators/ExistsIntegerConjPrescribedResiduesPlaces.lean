import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SW.Lev

theorem exists_bar_mk_eq_at_places : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (b : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Formalism.L2.DIV.kP PP), ∃ c : 𝓞 D.host.E, ∀ PP ∈ P, Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) = b PP := by
  intro D P b
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := P) (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal) (fun _ => 1)
    (fun PP _ => PP.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun PP => Classical.choose (Ideal.Quotient.mk_surjective (b PP.1)))
  refine ⟨GlobalTheory.SW.Lev.bar y, fun PP hPP => ?_⟩
  rw [GlobalTheory.SW.Lev.bar_bar]
  have h := hy PP hPP
  rw [pow_one] at h
  have hc := Classical.choose_spec (Ideal.Quotient.mk_surjective (b PP))
  rw [← hc]
  exact Ideal.Quotient.eq.2 h

end GlobalTheory.SW.Lev
