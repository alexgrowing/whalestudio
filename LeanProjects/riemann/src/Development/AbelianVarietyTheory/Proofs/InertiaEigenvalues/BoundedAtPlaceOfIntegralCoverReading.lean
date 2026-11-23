import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntValuationPrimeBack
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtensionIntegralFramedPointLiftCove
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvROfFrMapFromTest
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddAllOfThetaSumOnCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCoverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadingsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralValuesAlgebraicPointsIffValueNonnegStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverLocInt

theorem rd_sum {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {m : ℕ} (s : Fin m → C.d.c₂.F) (g : Fin m → Rul C.d.Xo₂ C.d.c₂) :
    C.rd a (∑ b, s b • g b) = ∑ b, C.σ₂ (s b) • C.rd a (g b) := by
  unfold Cover.rd
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smulₛₗ, map_smul, smul_comm]

theorem rd_sub {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (g h : Rul C.d.Xo₂ C.d.c₂) : C.rd a (g - h) = C.rd a g - C.rd a h := by
  unfold Cover.rd
  rw [map_sub, map_sub, smul_sub]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem bddAll_of_mem_intForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (la' : HeightOneSpectrum (𝓞 C.c'.F)), (∀ y : C.c'.F, la'.valuation C.c'.F y = la.valuation C.d.c₂.F (C.d.eF y)) → ∀ (m : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → (∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b)) ∈ C.intForms a n {la} → GlobalTheory.GoodPts.BddAll (T.Q.Xo j) C.c' la' 1 (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) := by
  intro D T hL j hj σ hσ C hU a n hdom hPin la la' hval m x f hf hmem
  obtain ⟨g₂, ⟨hcs, hint⟩, hrd⟩ := hmem
  choose f₂ hf₂ using fun b => GlobalTheory.T.exists_pullback_section_to_levelCover D T hL j hj σ hσ C hU.1 a n (f b) (hf b)
  have hpin : ∀ b, C.rd a (f₂ b) = T.phiJ j σ a (f b) := fun b => hPin.2 (f b) (hf b) (f₂ b) (hf₂ b).1 (hf₂ b).2
  have hG : g₂ = ∑ b, C.d.eF (x b) • f₂ b := by
    by_contra hne
    have h0 : g₂ - ∑ b, C.d.eF (x b) • f₂ b ≠ 0 := sub_ne_zero.2 hne
    have hsec : g₂ - ∑ b, C.d.eF (x b) • f₂ b ∈ sec C.d.Xo₂ C.d.c₂ a n :=
      sub_mem hcs.1 (sum_mem fun b _ => Submodule.smul_mem _ _ (hf₂ b).1)
    have hli : LinearIndependent C.d.c₂.F ![g₂ - ∑ b, C.d.eF (x b) • f₂ b] :=
      linearIndependent_unique_iff.2 h0
    have hli2 := GlobalTheory.T.coverSections_linearIndependent_adelicReadings D T hL j hj σ hσ C hU hPin.1 a n hdom 1 ![g₂ - ∑ b, C.d.eF (x b) • f₂ b]
      (fun i => by fin_cases i; exact hsec) hli
    have hz : C.rd a (g₂ - ∑ b, C.d.eF (x b) • f₂ b) = 0 := by
      rw [rd_sub, rd_sum, hrd]
      simp only [hpin, sub_self]
    exact hli2.ne_zero 0 (by simpa using hz)
  intro Tv io e ho y hy
  obtain ⟨T', iT, e', y', io₂, y₂, hext, hfin', hio₂, hover⟩ :=
    GlobalTheory.CoverPoint.exists_ext_lift_to_cover _ _ _ _ (T.Q.Xo j) C.c' 0 C.d hU.1 Tv io y hy
  have ho₂ : OverLa la T'.V io₂ (e' * e) := by
    refine ⟨Nat.mul_pos hext.1 ho.1, fun z => ?_⟩
    have h1 := hio₂ (C.d.eF.symm z)
    rw [C.d.eF.apply_symm_apply] at h1
    have h2 : vLa la z = vLa la' (C.d.eF.symm z) := by
      simp only [vLa, hval, C.d.eF.apply_symm_apply]
    rw [h1, hext.2.1, ho.2, h2]
    push_cast
    ring
  have hB := (GlobalTheory.T.integral_values_algebraic_points_iff_value_nonneg _ _ _ _ C.d.Xo₂ C.d.c₂ la g₂).2 (hint la (Set.mem_singleton la)) T' io₂ (e' * e) ho₂
    y₂ hfin'
  rw [map_one, one_mul] at hB
  have laws := GlobalTheory.firstFiveLaws.1
  letI a1 : Algebra C.c'.F T'.Fr := (iT.comp io).toAlgebra
  letI a2 : Algebra C.d.c₂.F T'.Fr := io₂.toAlgebra
  letI a0 : Algebra T.Q.c.F T'.Fr := ((iT.comp io).comp (incF T.Q.c C.c' C.hle)).toAlgebra
  have hAO : AlgOver T.Q.c C.c' C.hle T'.Fr := fun _ => rfl
  have hcomp : ∀ z : C.c'.F, algebraMap C.d.c₂.F T'.Fr (C.d.eF z) = algebraMap C.c'.F T'.Fr z := hio₂
  have e1 : ∀ b, evI y₂ (f₂ b) = evR (T.Q.Xo j) T.Q.c (f b) (y'.1.res C.hle hAO) := fun b =>
    (hf₂ b).2 T'.Fr hAO hcomp y₂.1 y'.1 hover
  have e2 : ∀ b, evI y' (GlobalTheory.FieldBC.rulBC C.hle (f b)) = evR (T.Q.Xo j) T.Q.c (f b) (y'.1.res C.hle hAO) := fun b =>
    GlobalTheory.FieldBCModel.evR_rulBC C.hle (hf b).1 hAO y'.1
  have e3 : evI y₂ g₂ = evI y' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) := by
    rw [hG, GlobalTheory.GalSup.evI_sum, GlobalTheory.GalSup.evI_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [e1, e2, hio₂]
    rfl
  have hgs : (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) ∈ sec (T.Q.Xo j) C.c' a n :=
    sum_mem fun b _ => Submodule.smul_mem _ _ (GlobalTheory.FieldBCModel.rulBC_mem_sec C.hle (hf b))
  obtain ⟨φ, hφ, hm⟩ := hext.2.2
  letI a3 : Algebra C.c'.F Tv.Fr := io.toAlgebra
  have e4 : evI y' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) =
      iT (evI y (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b))) := by
    have := GlobalTheory.PlaceInt.evR_of_frMap_fromTest
      (GlobalTheory.Frames.algebraic_laws laws.secBaseChange _ _ _ _ (T.Q.Xo j) C.c').2.2.1 _ hgs.1 φ y.1 y.2.1 y'.1 hm
    exact this.trans (congrArg (fun r : Tv.Fr →+* T'.Fr => r (evR (T.Q.Xo j) C.c' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) y.1)) hφ)
  rw [map_one, one_mul, ← GlobalTheory.CoverBound.inV_map_iff iT hext.1 hext.2.1, ← e4, ← e3]
  exact hB

end GlobalTheory.CoverLocInt
