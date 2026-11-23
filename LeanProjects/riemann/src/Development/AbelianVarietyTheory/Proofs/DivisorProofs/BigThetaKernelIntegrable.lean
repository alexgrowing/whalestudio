import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelIntegrableOnUnitaryQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStandingStatement
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastNotMemOfCoprime

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.SquareConv

theorem natCast_not_mem {Rg : Type*} [CommRing Rg] {P : Ideal Rg} (hP : P ≠ ⊤) {p n : ℕ} (hpn : Nat.Coprime p n)
    (hp : (p : Rg) ∈ P) : (n : Rg) ∉ P :=
  _root_.GlobalTheory.CoprimeNatNotMem.natCast_not_mem_of_coprime hP hpn hp

theorem coprime_two_q_d {p q d : ℕ} (hp : p.Prime) (hq : q.Prime) (hd : d.Prime) (h2 : p ≠ 2) (h3 : p ≠ q) (h4 : p ≠ d) :
    Nat.Coprime p (2 * q * d) :=
  Nat.Coprime.mul_right (Nat.Coprime.mul_right ((Nat.coprime_primes hp Nat.prime_two).2 h2) ((Nat.coprime_primes hp hq).2 h3))
    ((Nat.coprime_primes hp hd).2 h4)

theorem standing {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D}
    (hS : HidaSetting large₂ R F) (hx : 11 ≤ D.host.splitBound) {sc : Consts} (G : GridData R.toLevCh sc) (t : T) :
    SquareStanding G t := by
  classical
  obtain ⟨hq, hd, -⟩ := D.host.hyp
  have hcc : D.host.ccK = ⊤ := hS.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨P, -, -⟩, -⟩ := hS.size
  have lev : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hpp (P.level_split p hp)
  refine ⟨hx, fun w hw => ?_⟩
  have e1 : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) = ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) := by
    rw [hcc, Ideal.absNorm_top, mul_one]
  rw [e1]
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
    exact natCast_not_mem (G.pl.w v).isPrime.ne_top hcop hpw
  · intro hmem
    apply (hS.core.lev.Q_off t w hw).1
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem

theorem splitBound_ge {D : D7} {large₂ : SizeData₂ D} {ε : ℝ} (_he : large₂.sc.eps = ε) (_hx : (12 : ℝ) ^ (5 / ε) ≤ large₂.sc.x)
    {Γ : Type} {_ : Group Γ} {_ : Fintype Γ} {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} {_ : Field Ks} {_ : NumberField Ks} {_ : Algebra Ks D.what₂.LL} {R : RealDat D A Ks} {F : Face D A}
    (hS : HidaSetting large₂ R F := by assumption) : 11 ≤ D.host.splitBound :=
  hS.size.2.1.eleven_le

theorem bigConv : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t (M : Vol ch.G), M.Is t → ∀ Θ Θ', IsMatched ch.S.B t ch.rm i j Θ Θ' → ∀ g g₁,
    IntegrableOn (kerBig ch.W Θ g g₁) (M.fd _) (M.ν _) := by
  intro _ _ hWC _ _
  refine ⟨0, fun ε CF _ => ⟨(12:ℝ) ^ (5/ε), fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩⟩
  intro i j t M hM Θ Θ' hΘ g g₁
  have hst : SquareStanding ch.G t := standing hS (splitBound_ge he hx) ch.G t
  exact GlobalTheory.T.bigRoute_kernel_integrableOn_unitary_quotient hWC hS.core.lev ch.W ch.S.B ch.rm t i j (GlobalTheory.T.squareThetaTripleHypotheses_of_standing hS.core.lev ch.W t i j hst) M hM Θ Θ' hΘ g₁ g

end GlobalTheory.SquareConv
