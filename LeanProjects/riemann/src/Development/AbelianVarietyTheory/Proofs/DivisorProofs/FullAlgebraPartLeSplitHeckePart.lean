import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.HeckeSplitPart

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem goodPl (R : RealDat D A Ks) (F : Face D A) (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam)
    {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hSF : IsSF R SF) {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ} (hβ : IsSDFrame V β Λ N)
    (hN : N = 1 ∨ N = D.host.g 0 * D.host.g 1) :
    GlobalTheory.HeckeParts.GoodPl V β R.Pg (A.ok A.μ0) R.pl A.q SF := by
  obtain ⟨hQ, h2, h3, h4⟩ := GlobalTheory.GoodPrimes.good_primes R F hL
  intro P hP
  obtain ⟨hg, hc, hq⟩ := h4 hF _ P hP
  refine ⟨?_, (h3 SF hSF _).2 hg, ?_, fun L hLP hLQ e f hef => ?_⟩
  · rw [hq, Nat.cast_ne_zero]
    exact fun h => (R.pl P).ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
    exact fun h => hc (HeightOneSpectrum.ext h)
  · obtain ⟨c, hcB⟩ := hβ
    refine (GlobalTheory.LevSplit.lev_split V β Λ _ L hcB).2 (R.pl P) e f hef ?_ ?_
    · intro h
      rw [Nat.cast_pow] at h
      have h' := (R.pl P).isPrime.mem_of_pow_mem _ h
      rcases hN with rfl | rfl
      · exact (R.pl P).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h'))
      · exact (h2 _ _ hg).1 h'
    · rw [hLP, hLQ]
      rintro PP (h | h)
      · exact hg PP (Or.inl h)
      · simp at h

theorem parts_in_hPart : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ SF, IsSF R SF → ∀ (c : Pl D.host.E → List ℤ → ℂ) (Sg : Pl0 → ℂ[X]), ((∀ P ∈ A.ok A.μ0, Sg P = Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (dualLab (splitLab D.R.r k))) → ∀ x ∈ EEc R SF c, R.HE.e x ∈ hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q Sg) ∧ ∀ i, (∀ P ∈ A.ok A.μ0, Sg P = Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (splitLab D.R.r k)) → ∀ x ∈ Wcc R SF i c, (R.HW i _).e x ∈ hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q Sg := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _ hC SF hSF c Sg
  have hY := goodPl R F hC.lev hC.fam hSF (hC.lev.βY 0 (by have := D.R.two_le_m; omega)) (Or.inr rfl)
  have hW := fun i => goodPl R F hC.lev hC.fam hSF (hC.lev.βW i) (Or.inl rfl)
  refine ⟨fun hSg x hx => ?_, fun i hSg x hx => ?_⟩
  · exact GlobalTheory.HeckeParts.mem_hPart_of_partFull (V := Yc D 0) (β := R.βY 0) (r := D.R.r) (t := D.R.t) (hr := r_le_Y 0)
      (Pg := R.Pg) (χ := R.chi) (ξ := fun _ => 1) (c := fun P d => c P (dualLab d)) hY R.triv hx
      (fun P hP => by rw [hSg P hP, GlobalTheory.HeckeParts.rank_zeroth_component_eq])
  · exact GlobalTheory.HeckeParts.mem_hPart_of_partFull (V := Wc D i) (β := R.βW i) (r := D.R.r) (t := D.R.t) (hr := r_le_rank_Wc i)
      (Pg := R.Pg) (χ := fun _ _ => 1) (ξ := fun _ => 1) (c := c) (hW i) R.triv hx.2
      (fun P hP => by rw [hSg P hP, GlobalTheory.HeckeParts.rank_weight_component_eq])

end GlobalTheory.HeckeSplitPart

end
