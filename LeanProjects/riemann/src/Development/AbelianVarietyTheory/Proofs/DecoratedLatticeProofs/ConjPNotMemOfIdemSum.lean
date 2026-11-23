import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.LeadingConstantNeZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerLift

theorem conjP_notMem_of_isIdemSum {D : D7} {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e SS) :
    ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  intro P hP hP'
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  have horth := Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_conj_orth hes hsum hc P hP (Formalism.L2.Col.conjPrime₂ P) hP'
  have h1 : Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.Col.conjPrime₂ P))) P := by
    refine GlobalTheory.MovedIdem.isIdemAt_conj (hes _ hP') fun x => ?_
    show x ∈ P.asIdeal ↔ Formalism.L2.Col.cO D.host.E (Formalism.L2.Col.cO D.host.E x) ∈ P.asIdeal
    have : Formalism.L2.Col.cO D.host.E (Formalism.L2.Col.cO D.host.E x) = x := by
      apply RingOfIntegers.ext
      simp [Formalism.L2.Col.cO]
    rw [this]
  have heq : cA D (es (Formalism.L2.Col.conjPrime₂ P)) = es P :=
    (GlobalTheory.ExportSeries.idemAt_eq h1).symm.trans (GlobalTheory.ExportSeries.idemAt_eq (hes P hP))
  rw [heq, (hes P hP).1.1] at horth
  have hI := hes P hP
  rw [horth] at hI
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have := (hI.2 x hx0).1 hxP
  rw [zero_mul, map_zero] at this
  exact this (zero_mem _)

theorem natCast_smul_inv_smul {E : Type} [Field E] [NumberField E] {a b : ℕ} (c : ℕ) (hc : 0 < c)
    (y : Formalism.L2.Col.HomE E a b) : ((c : 𝓞 E)) • ((c : E)⁻¹ • y) = y := by
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Nat.cast_smul_eq_nsmul (𝓞 E), ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hc0, one_smul]

set_option maxHeartbeats 800000 in

theorem exists_rep_add_mem : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ c : ℕ, 0 < c → ∀ (SX : Finset (VV D.what₂.Tau S.rank T.rank)), Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) SX → ∀ (px : VV D.what₂.Tau S.rank T.rank → Formalism.L2.Col.HomE D.host.E S.rank T.rank), (∀ x ∈ SX, px x ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c ∧ embH (tauE D) δ (px x) = x) → ∀ g : Formalism.L2.Col.HomE D.host.E S.rank T.rank, (∀ P ∈ SS, (c : D.host.E) • g ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) → ∃ x ∈ SX, ∀ P ∈ SS, g + px x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T δ sc hP e SS he N N' hN hN' c hc SX hSX px hpx g hg
  have hSS := conjP_notMem_of_isIdemSum he
  have hAA : (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ≠ ⊥ := fun h =>
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.leading_constant_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 h)
  have hspan : ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, ∃ n : ℕ, 0 < n ∧ (n : D.host.E) • x ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' :=
    Formalism.L2.Ker.lf_span _ hAA N N' hN.1.fg hN'.1.span_eq_top
  have hneg : ∀ P ∈ SS, (c : D.host.E) • (-g) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := fun P hP' => by
    rw [smul_neg]; exact neg_mem (hg P hP')
  have hL := Formalism.L2.Ker.lift_exists_alt D.host.E S.rank T.rank SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c hc hSS hspan (-g) hneg
  obtain ⟨hsA, hsP⟩ := hL
  generalize Formalism.L2.Ker.liftS SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c (-g) = s at hsA hsP
  have hmem : embH (tauE D) δ s ∈ AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c :=
    ⟨s, hsA, rfl⟩
  obtain ⟨x, hxS, hxL⟩ := hSX.2.2 _ hmem
  obtain ⟨β, hβ, hβe⟩ := hxL
  have hne : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hβs : β = s - px x := by
    apply Formalism.L2.Ker.embH_inj (tauE D) hP.ne
    rw [map_sub, (hpx x hxS).2]
    exact hβe
  refine ⟨x, hxS, fun P hPS => ?_⟩
  have h1 : s + g ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
    have h2 := hsP P hPS
    rw [sub_neg_eq_add] at h2
    have h3 : ((c : 𝓞 D.host.E)) • ((c : D.host.E)⁻¹ • (s + g)) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :=
      Submodule.smul_mem _ _ h2
    have e3 := natCast_smul_inv_smul c hc (s + g)
    rwa [e3] at h3
  have h4 : β ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hβ⟩
  have e5 : g + px x = (s + g) - β := by rw [hβs]; abel
  rw [e5]
  exact sub_mem h1 h4

end GlobalTheory.PerLift
