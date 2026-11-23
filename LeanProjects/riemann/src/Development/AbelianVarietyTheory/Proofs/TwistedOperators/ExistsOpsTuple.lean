import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdjoinSplitHeckeGeneratorsDualsSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeConjPlaceEqDualLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorAdjointIntertwinerNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.OpsRowsTuple

theorem offS_badPl_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) (w : Pl D.host.E) :
    OffS D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) w ↔ GlobalTheory.Hk3.Good R t w := by
  classical
  rw [GlobalTheory.GoodPrimes.offS_iff]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl
  simp only [Finset.mem_image, Finset.mem_union, not_exists, not_and]
  refine forall₂_congr fun PP _ => ⟨fun h => ⟨fun e => h (by rw [e]), fun e => h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e)⟩, fun h e => ?_⟩
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with h1 | h1
  · exact h.1 h1.symm
  · exact h.2 (GlobalTheory.GoodPrimes.isConjPl_iff.2 h1)

theorem exists_ops_tuple : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → ∀ t : T, ∃ h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H, (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) ∧ GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R t) h ∧ (∀ (c : Pl D.host.E → List ℤ → ℂ) P, GlobalTheory.Hk3.Good R t P → ∀ cc, ∀ x ∈ GlobalTheory.Hk3.EEc R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c, h P cc x = GlobalTheory.Hk3.evC (Yc D 0) P (fun d => c P (dualLab d)) cc • x) ∧ ∀ (c : Pl D.host.E → List ℤ → ℂ) x, (∀ P d, GlobalTheory.Hk3.Good R t P → GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) x = c P (dualLab d) • x) → x ∈ GlobalTheory.Hk3.EEc R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS t
  have hgp := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hg := hgp.2.1
  have hoff := offS_badPl_iff R t
  have h0 : ∀ P, Good R t P → Good R A.μ0 P := fun P hP => (hg t P hP).2.2
  have hβ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  cases hβ with
  | intro n hβ =>
  have lev := fun P (hP : Good R t P) => GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβ P
    (by rw [Nat.cast_pow]; exact fun hm => (hg _ P (h0 P hP)).1 (P.isPrime.mem_of_pow_mem n hm))
    (fun PP hPP => h0 P hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  have H := GlobalTheory.Hk3.OpsRows.exists_ops (θ := R.θ) (M := R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv))
    (levChi _ (R.βY 0) (R.dat0 R.triv)) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) R.ν0 R.fd0 hC.models.inf hC.models.ν0.1.1 hC.models.ν0.2
    hS.2.1 R.HE _ hC.models.HE (goodPart_le _ _ _ _ _) (Good R t)
    (fun P d B => ⟨fun hB => by
        have hP : Good R t P := by
          obtain ⟨_, _, _, _, hO, -⟩ := hB
          exact (hoff P).1 hO
        exact ⟨hP, (((lev P hP).2.1 _ d B).1 hB).2⟩,
      fun hB => ((lev P hB.1).2.1 _ d B).2 ⟨(hoff P).2 hB.1, hB.2⟩⟩)
    (fun P hP => (lev P hP).1)
    (fun P hP c U hU => by
      obtain ⟨hU1, hU2⟩ := (mem_goodPart _ _ _ _ _ _).1 hU
      refine (mem_goodPart _ _ _ _ _ _).2 ⟨(lev P hP).2.2.2.2 _ _ _ c hC.models.inf U hU1, fun v => ?_⟩
      have hfix : ∀ k ∈ hyp (Yc D 0) P, ∀ g, U v (g * k) = U v g := fun k hk g => by
        rw [GlobalTheory.Hk3.OpsRows.mult_lev hU1 v k ((lev P hP).1 k hk).1 g, ((lev P hP).1 k hk).2, one_mul]
      rw [postOn_apply]
      conv_rhs => rw [← hU2 v]
      simp only [RealDat.e0, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      exact (lev P hP).2.2.2.1 c _ _ hfix)
  cases H with
  | intro h H2 =>
  exact ⟨h, H2.1, H2.2.1, fun c => H2.2.2.2.1 _, fun c => H2.2.2.2.2 _⟩

end GlobalTheory.Hk3.OpsRowsTuple

end
