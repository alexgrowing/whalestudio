import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabelThetaLiftSpaceIffDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePolynomialsOfCarriedEigensystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertValuesIffInertLabelsCarriedEigensystems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPartnerCombinationGoodInertLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.Hk3.LabDetRows

open GlobalTheory.Hk3 GlobalTheory.Hk3.LabDet

theorem dual_eq_of_split : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (c c' : Pl D.host.E → List ℤ → ℂ), GlobalTheory.Hk3.EEc R SF c ≠ ⊥ → GlobalTheory.Hk3.EEc R SF c' ≠ ⊥ → (∀ P, GlobalTheory.Hk3.Good R A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∀ k ≤ (Yc D 0).rank, c P (dualLab (splitLab (Yc D 0).rank k)) = c' P (dualLab (splitLab (Yc D 0).rank k))) → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∀ d, GlobalTheory.Hk3.IsLab (Yc D 0) P d → c P (dualLab d) = c' P (dualLab d) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF c c' hc hc' hs P hP hcP
  obtain ⟨-, hgood, hoff, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  obtain ⟨n, hβ⟩ := hC.lev.βY 0 (by have := D.R.two_le_m; omega)
  have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
    GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) ((D.host.g 0 * D.host.g 1) ^ n) (R.dat0 R.triv) hβ P
      (by
        rw [Nat.cast_pow]
        exact fun h => (hgood A.μ0 P hP).1 (P.isPrime.mem_of_pow_mem _ h))
      (by
        intro PP hPP
        refine hP PP (hPP.imp id ?_)
        intro h
        exact absurd h (Finset.notMem_empty _))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  obtain ⟨x', hx', hx0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc'
  have inj : Function.Injective R.HE.e := hC.models.HE.1
  have hu : R.HE.e x ≠ 0 := fun h => hx0 (inj (by rw [h, map_zero]))
  have hu' : R.HE.e x' ≠ 0 := fun h => hx0' (inj (by rw [h, map_zero]))
  have hp := (LabDet.mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_comap.1 hx)
  have hp' := (LabDet.mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_comap.1 hx')
  have hP' : Good R A.μ0 (Formalism.DivisionValues.conjPl P) := (hgood _ P hP).2.1
  have hcc : Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P) = P := Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl P
  exact eq_of_split (rRep (R.MY 0)) P hcP _ _ hu hu'
    (fun k hk => mult_lev _ _ _ _ _ hp.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2)
    (fun k hk => mult_lev _ _ _ _ _ hp'.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2)
    (fun d => c P (dualLab d)) (fun d => c' P (dualLab d))
    (fun d => c (Formalism.DivisionValues.conjPl P) (dualLab d)) (fun d => c' (Formalism.DivisionValues.conjPl P) (dualLab d))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp'.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp'.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩))
    (hs P hP hcP) (hs _ hP' (by rw [hcc]; exact fun h => hcP h.symm))

end GlobalTheory.Hk3.LabDetRows

end
