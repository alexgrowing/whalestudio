import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TmulOneMemIntAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentPowCompletionTrivialAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Pointwise

namespace GlobalTheory.ModulUnit

variable {D : D7}

theorem exists_sep {v v' : GlobalTheory.FinPl.Pl D} (h : v' ≠ v) :
    ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal := by
  by_contra hc
  push_neg at hc
  exact h (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hc))

theorem idV_eq_one_of_mem {v : GlobalTheory.FinPl.Pl D} {I : Ideal (𝓞 D.host.E)} {t : 𝓞 D.host.F} (ht : t ∉ v.asIdeal)
    (hI : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ I) :
    GlobalTheory.SeeSaw.idV ((I : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 1 v := by
  refine le_antisymm (GlobalTheory.SeeSaw.idV_mono FractionalIdeal.coeIdeal_le_one v) ?_
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, h0, a, ha, rfl⟩
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
  obtain ⟨h1, h2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht hα h0
  rw [GlobalTheory.IdVGen.tmul_eq ht α]
  refine AddSubgroup.subset_closure ⟨_, h1, h2, _, ?_, rfl⟩
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨_, I.mul_mem_right o hI, ?_⟩
  rw [map_mul]
  rfl

theorem idV_mul_of_eq_one {𝔞 I : GlobalTheory.SeeSaw.FI D} {v : GlobalTheory.FinPl.Pl D}
    (h : GlobalTheory.SeeSaw.idV I v = GlobalTheory.SeeSaw.idV 1 v) : GlobalTheory.SeeSaw.idV (𝔞 * I) v = GlobalTheory.SeeSaw.idV 𝔞 v := by
  rcases eq_or_ne 𝔞 0 with rfl | h0
  · rw [zero_mul]
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞 h0
  have := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 I x 1 hx0 one_ne_zero hx
    (GlobalTheory.Core.Mi.LatMatch.DiUnit.eq_one_iff.1 h)
  rw [mul_one] at this
  ext s
  rw [this, hx]

variable {T : Type} {L : LevCh D T}

theorem exists_mem_modul (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ s : 𝓞 D.host.F, s ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ P.modul sc := by
  classical
  have hsep : ∀ v' ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal :=
    fun v' hv' => exists_sep fun e => hv (e ▸ hv')
  choose! t ht using hsep
  refine ⟨∏ v' ∈ P.S0, t v' ^ P.depth sc v', fun hm => ?_, ?_⟩
  · obtain ⟨v', hv', hm'⟩ := (haveI := v.isPrime; Ideal.IsPrime.prod_mem_iff.1 hm)
    exact (ht v' hv').2 (v.isPrime.mem_of_pow_mem _ hm')
  · rw [map_prod]
    refine Ideal.prod_mem_prod fun v' hv' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have h : t v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := by rw [P.under_w hv']; exact (ht v' hv').1
    exact h
end GlobalTheory.ModulUnit

namespace GlobalTheory.ModulUnit

variable {D : D7} {T : Type} {L : LevCh D T}

theorem conj_smul_algebraMap (s : 𝓞 D.host.F) :
    D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s := by
  apply RingOfIntegers.ext
  show D.host.conj ((s : D.host.F) : D.host.E) = ((s : D.host.F) : D.host.E)
  exact (D.host.conjE_mem_hostF_iff _).1 (s : D.host.F).2

theorem exists_mem_modulBar (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ s : 𝓞 D.host.F, s ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ P.modulBar sc := by
  obtain ⟨s, hs, hm⟩ := exists_mem_modul P sc hv
  refine ⟨s, hs, ?_⟩
  have := Ideal.smul_mem_pointwise_smul D.host.conj _ _ hm
  rwa [conj_smul_algebraMap] at this

end GlobalTheory.ModulUnit

open GlobalTheory.ModulUnit in

theorem GlobalTheory.ChiGrid.Places.idV_mul_modul : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : GlobalTheory.ChiGrid.Consts) (v : GlobalTheory.FinPl.Pl D), v ∉ P.S0 → ∀ 𝔞 : GlobalTheory.SeeSaw.FI D, GlobalTheory.SeeSaw.idV (𝔞 * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 𝔞 v ∧ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 𝔞 v := by
  intro D T L P sc v hv 𝔞
  obtain ⟨s, hs, hm⟩ := exists_mem_modul P sc hv
  obtain ⟨s', hs', hm'⟩ := exists_mem_modulBar P sc hv
  exact ⟨idV_mul_of_eq_one (idV_eq_one_of_mem hs hm), idV_mul_of_eq_one (idV_eq_one_of_mem hs' hm')⟩
