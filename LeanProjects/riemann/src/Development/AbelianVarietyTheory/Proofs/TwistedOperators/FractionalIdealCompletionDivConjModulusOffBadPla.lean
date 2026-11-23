import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ModBarOff

theorem idV_mul_inv_iff {D : D7} {v : GlobalTheory.FinPl.Pl D} (I : Ideal (𝓞 D.host.E)) (t : 𝓞 D.host.F) (ht : t ∉ v.asIdeal)
    (hI : algebraMap D.host.F D.host.E (t : D.host.F) ∈ (I : GlobalTheory.SeeSaw.FI D))
    (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D) :
    s ∈ GlobalTheory.SeeSaw.idV (𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  have ht0 : t ≠ 0 := fun h => ht (h ▸ v.asIdeal.zero_mem)
  have hF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  have hI0 : (I : GlobalTheory.SeeSaw.FI D) ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hI
    exact hF ((map_eq_zero _).1 hI)
  have e : 𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹ * (I : GlobalTheory.SeeSaw.FI D) = 𝔞 := by
    rw [mul_assoc, inv_mul_cancel₀ hI0, mul_one]
  constructor
  · revert s
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, h1, h2, a, ha, rfl⟩
    obtain ⟨g1, g2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht h1 h2
    refine AddSubgroup.subset_closure ⟨_, g1, g2, _, ?_, GlobalTheory.IdVGen.tmul_eq ht α a⟩
    rw [← e, mul_comm (algebraMap D.host.F D.host.E (t : D.host.F)) a]
    exact FractionalIdeal.mul_mem_mul ha hI
  · refine fun h => GlobalTheory.SeeSaw.idV_mono ?_ v h
    calc 𝔞 = 𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹ * (I : GlobalTheory.SeeSaw.FI D) := e.symm
      _ ≤ 𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹ * 1 := by
        gcongr
        exact FractionalIdeal.coeIdeal_le_one
      _ = _ := mul_one _

theorem exists_mem_modul {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D}
    (hv : v ∉ P.S0) : ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modul sc := by
  have h : ∀ u : HeightOneSpectrum (𝓞 D.host.F), ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ (u ∈ P.S0 → t ∈ u.asIdeal) := by
    intro u
    by_cases hu : u ∈ P.S0
    · have hne : ¬ u.asIdeal ≤ v.asIdeal := fun hle =>
        hv ((HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top hle)) ▸ hu)
      obtain ⟨t, h1, h2⟩ := SetLike.not_le_iff_exists.1 hne
      exact ⟨t, h2, fun _ => h1⟩
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, fun h => absurd h hu⟩
  choose t ht1 ht2 using h
  refine ⟨∏ u ∈ P.S0, t u ^ P.depth sc u, ?_, ?_⟩
  · have := v.isPrime
    exact prod_mem (S := v.asIdeal.primeCompl) fun u _ => pow_mem (show t u ∈ v.asIdeal.primeCompl from ht1 u) _
  · rw [map_prod]
    refine Ideal.prod_mem_prod fun u hu => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have h1 := ht2 u hu
    have h2 : t u ∈ ((P.w u).under (𝓞 D.host.F)).asIdeal := by rw [P.under_w hu]; exact h1
    exact h2

theorem idV_mul_modulBar_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D}, v ∉ P.S0 → ∀ (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D), s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  intro D T L P sc v hv 𝔞 s
  obtain ⟨t, ht, hm⟩ := exists_mem_modul P sc hv
  refine idV_mul_inv_iff _ t ht ?_ 𝔞 s
  have h1 : algebraMap D.host.F D.host.E (t : D.host.F) ∈ ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, hm, rfl⟩
  have h2 := (GlobalTheory.ChiGrid.StairConj.mem_coe_iff D _ _).1 h1
  have h3 : D.host.conj (algebraMap D.host.F D.host.E (t : D.host.F)) = algebraMap D.host.F D.host.E (t : D.host.F) :=
    (D.host.conjE_mem_hostF_iff _).1 (t : D.host.F).2
  rw [h3] at h2
  exact h2

end GlobalTheory.ModBarOff
