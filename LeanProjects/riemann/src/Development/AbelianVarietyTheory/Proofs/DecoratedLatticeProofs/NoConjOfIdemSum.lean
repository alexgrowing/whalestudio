import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslate
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
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemFin
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AltENsmulLeft
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CocRZeroLeft
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfSplit

theorem noConj_of_idemSum : ∀ (D : D7) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  intro D e SS hI P hP hP'
  obtain ⟨⟨es, hes, he⟩, hc⟩ := hI
  have h1 : ∀ i ∈ SS, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ SS, ∀ j ∈ SS, es i * cA D (es j) = 0 := by
    subst he
    exact GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es SS h1 hc
  have hcj : Lev.IsConjPl (D := D) (Formalism.L2.Col.conjPrime₂ P) P := by
    intro c hc'
    exact ⟨Formalism.L2.Col.cO D.host.E c, (Formalism.L2.Col.mem_conjP P c).1 hc', rfl⟩
  have heq : es P = cA D (es (Formalism.L2.Col.conjPrime₂ P)) :=
    Formalism.IndefR.Fin.conj_idem_eq (hes _ hP') (hes P hP) hcj
  apply Formalism.IndefR.Fin.idemAt_ne_zero (hes P hP)
  have := hcross P hP _ hP'
  rw [← heq, h1 P hP] at this
  exact this

theorem splitHyp_halves : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → IsSelfDualC S N → IsSelfDualC T N' → SplitHyp (HV sc) (alV D.host.d sc) (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T δ sc hP e SS hI N N' c hc hcS h2 hL hN hN'
  have hSS : ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := noConj_of_idemSum D e SS hI
  have hT : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hconj : ∀ τ (x : D.host.E), tauE D τ (star x) = starRingEnd ℂ (tauE D τ x) := fun τ x =>
    GlobalTheory.FockCompare.tauE_star τ x
  have he1 : ∀ Q, expS SS Q = 1 ∨ expS SS Q = 0 ∨ expS SS Q = -1 := by
    intro Q; unfold expS; split_ifs <;> simp
  have hc1 : ∀ Q, expS SS (Formalism.L2.Col.conjPrime₂ Q) = -expS SS Q := exponent_set_conjugate D.host.E SS hSS
  have hfg : N.FG := hN.1.fg
  have tw : ∀ f : HeightOneSpectrum (𝓞 D.host.E) → ℤ, (∀ Q, f (Formalism.L2.Col.conjPrime₂ Q) = -f Q) →
      (∀ Q, f Q = 1 ∨ f Q = 0 ∨ f Q = -1) →
      LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N (twist₂ N' c f) := by
    intro f hf1 hf2
    unfold LaFacts LamC
    rw [← twist_homomorphism D.host.E _ _ _ N N' c f hfg hc]
    exact ⟨GlobalTheory.TwPerSelfDual.twO_selfDual D.host.E D.what₂.Tau _ _ (tauE D) δ D.host.d sc _ c f hP.ne hconj hc hf1 hf2 hL.1 hL.2,
      GlobalTheory.SemiTwist.semiChar_twO D.host.E D.what₂.Tau _ _ (tauE D) δ D.host.d sc _ c f hP.ne hconj hc hf1 hf2 hL.1 hL.2⟩
  exact half_periods_of_lattice D.host.E D.what₂.Tau _ _ (tauE D) δ D.host.d sc _ SS N N' c hP.ne hc hSS hfg hL
    (tw _ hc1 he1) (tw (fun Q => -expS SS Q) (fun Q => by simp [hc1])
      (fun Q => by rcases he1 Q with h | h | h <;> simp [h]))

end GlobalTheory.HalfSplit
