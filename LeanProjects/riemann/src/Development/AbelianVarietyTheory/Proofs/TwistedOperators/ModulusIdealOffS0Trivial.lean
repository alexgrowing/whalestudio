import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMemLatOIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentPowCompletionTrivialAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JZeroMulMemLatticeIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ModulUnit

open GlobalTheory.ChiGrid

theorem exists_int_mem_modul {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D)
    (hv : v ∉ P.S0) : ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modul sc := by
  have hne : ∀ v' ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal := by
    intro v' hv'
    by_contra hc
    push_neg at hc
    have hle : v'.asIdeal ≤ v.asIdeal := fun t ht => hc t ht
    have heq : v'.asIdeal = v.asIdeal := v'.isMaximal.eq_of_le v.isPrime.ne_top hle
    have : v' = v := HeightOneSpectrum.ext heq
    exact hv (this ▸ hv')
  choose! f hf using hne
  refine ⟨∏ v' ∈ P.S0, f v' ^ P.depth sc v', ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨v', hv', h⟩
    exact (hf v' hv').2 (v.isPrime.mem_of_pow_mem _ h)
  · rw [map_prod, Places.modul]
    refine Ideal.prod_mem_prod fun v' hv' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have e : ((P.w v').under (𝓞 D.host.F)).asIdeal = v'.asIdeal := by rw [P.under_w hv']
    have h1 : f v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := e ▸ (hf v' hv').1
    exact h1

end GlobalTheory.ModulUnit

theorem GlobalTheory.ModulUnit.idV_modul_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D), v ∉ P.S0 → GlobalTheory.SeeSaw.idV ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) v = GlobalTheory.SeeSaw.idV 1 v := by
  intro D T L P sc v hv
  obtain ⟨t, ht, htm⟩ := GlobalTheory.ModulUnit.exists_int_mem_modul P sc v hv
  apply le_antisymm
  · exact GlobalTheory.SeeSaw.idV_mono FractionalIdeal.coeIdeal_le_one v
  · rw [GlobalTheory.SeeSaw.idV, AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hαv, a, ha, rfl⟩
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [GlobalTheory.IdVGen.tmul_eq ht α]
    obtain ⟨h1, h2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht hα hαv
    refine AddSubgroup.subset_closure ⟨_, h1, h2, _, ?_, rfl⟩
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t * o, Ideal.mul_mem_right _ _ htm, by rw [map_mul]; rfl⟩
