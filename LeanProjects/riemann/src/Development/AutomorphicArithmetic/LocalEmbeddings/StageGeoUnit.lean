import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoDefs
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.AdelicU (splitPrime)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StageGeo

private theorem cond_notMem {D : D7} {large₂ : SizeData₂ D} (hR : Rec large₂) {T : Type} {Lc : LevCh D T} {μ₀ : T} (hL : Lc.Is μ₀)
    {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T) :
    ∀ w ∈ locPl G t, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  classical
  obtain ⟨⟨P, -, -⟩, -⟩ := hR.size
  have lev : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hpp (P.level_split p hp)
  intro w hw
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨p, hpv, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧ Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := by
      rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
      · refine ⟨q0 D, G.pl.basePlace_over_qZero, ?_⟩
        have hs := (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
        have hM : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
          rw [Nat.Coprime, Nat.gcd_rec, hs, Nat.gcd_one_left]
        have hdv : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by
          unfold LevelStarExponents.condE
          exact Dvd.dvd.mul_left dvd_rfl _
        exact (hM.coprime_dvd_left hdv).symm
      · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
        · exact ⟨_, h, lev _ (D.host.g_level 0) (D.host.g_prime 0)⟩
        · exact ⟨_, h, lev _ (D.host.g_level 1) (D.host.g_prime 1)⟩
        · exact ⟨_, h, lev _ D.host.pde_level.1 D.host.pde_prime⟩
        · exact ⟨_, h, lev _ D.host.pde_level.2 D.host.pde'_prime⟩
    have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
      rw [← G.pl.under_w hv, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hpv
      exact hpv
    exact UpperTheory.Ram.natCast_notMem_of_coprime (G.pl.w v).isPrime.ne_top hpw hcop.symm
  · intro hmem
    apply (hL.Q_off t w hw).1
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem

theorem aUnit_locPl : GBig fun {D} T _ _ G _ _ _ _ => ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F))
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ ∈ GlobalTheory.FunObj.locPl G t → AUnit τ := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro t v τ hw
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h1 : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ (splitPrime τ).asIdeal := fun h =>
    cond_notMem hR hL G t _ hw (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
  haveI := (splitPrime τ).isPrime
  obtain ⟨z, hz, hzP⟩ := Set.not_subset.1 (UpperTheory.Ram.half_not_le D.host _ h1)
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (UpperTheory.Ram.half_ne_bot D.host)
  have hA : D.host.AA = ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
    unfold Host.AA Host.ccE Host.AA0
    rw [hcc, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]
  refine ⟨⟨1, ?_, by rw [map_one, map_one]⟩, (z : D.host.E), ?_, ?_⟩
  · rw [hA, FractionalIdeal.mem_inv_iff hB]
    intro y hy
    rw [one_mul]
    exact FractionalIdeal.coeIdeal_le_one hy
  · rw [hA, inv_inv]
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩
  · exact le_antisymm (GlobalTheory.AdelicU.apply_coe_mem τ z) (not_lt.1 fun h => hzP ((GlobalTheory.AdelicU.mem_splitPrime τ z).2 h))

end GlobalTheory.StageGeo
