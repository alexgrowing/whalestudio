import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

private theorem algSat_prod_eq (a q : ℕ) (B : Multiset ℂˣ) (hB : B.card = a) :
    (algSat a q B).prod = ((B.prod : ℂˣ) : ℂ) * (q : ℂ) ^ (a.choose 2) := by
  have hq : (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) ^ a : ℝ) = (q : ℝ) ^ (a.choose 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q), ← Real.rpow_natCast (q : ℝ) (a.choose 2),
      Nat.cast_choose_two]
    congr 1
    ring
  have hu : ((B.prod : ℂˣ) : ℂ) = (B.map fun α : ℂˣ => (α : ℂ)).prod :=
    map_multiset_prod (Units.coeHom ℂ) B
  have hm := Multiset.prod_map_mul (m := B) (f := fun _ : ℂˣ => (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ))
    (g := fun α : ℂˣ => (α : ℂ))
  have hl : algSat a q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
    unfold algSat
    change Multiset.map _ (Multiset.bind B fun α : ℂˣ => {(α : ℂ)}) = _
    rw [Multiset.bind_singleton, Multiset.map_map]
    rfl
  rw [hl, hm, Multiset.map_const', Multiset.prod_replicate, hB, hu, mul_comm]
  congr 1
  exact_mod_cast hq

theorem UpperTheory.Gal.Int.Div.detEx_of :
    CentU → DetEx := by
  classical
  intro hC E Ω _ _ _ _ _ _ l _ ι a ha U hU
  obtain ⟨χ, n, hχ, hval⟩ := hC E a ha U hU
  obtain ⟨L, hL, -⟩ := UpperTheory.Gal.TP.Sub.charEx E Ω l ι
  obtain ⟨ν, hν⟩ : ∃ ν : HChar E, ν.IsAbsPow ((-((a.choose 2 : ℕ) : ℤ) : ℤ) : ℝ) :=
    ⟨_, GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow _⟩
  have hνa : IsAlgPos ν (fun _ => -((a.choose 2 : ℕ) : ℤ)) :=
    AlgExpo.isAlgPos_of_expo E ν _ fun τ => by
      rw [(InfType.expo_of_infType E ν).2.1 _ hν τ]
      push_cast
      rfl
  have hA := GlobalTheory.GoodCsdTwist.isAlgPos_mul hχ hνa
  refine ⟨L (χ * ν) (n + fun _ => -((a.choose 2 : ℕ) : ℤ)), (hL _ _ hA).1, fun w hw B hB => ?_⟩
  obtain ⟨hu, hv⟩ := hval w hw B hB
  have hcl := (hL _ _ hA).2 w (GlobalTheory.GoodCsdTwist.unrAt_mul hu (hν.1 w))
  have hcard : B.card = a := by
    obtain ⟨σ, -, hs⟩ := hB
    exact hs.card
  have hvalue : (((χ * ν).val w : ℂˣ) : ℂ) = (algSat a (normV w) B).prod := by
    have e : (χ * ν).val w = χ.val w * ν.val w := rfl
    have h2 : ((ν.val w : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ) ^ (a.choose 2) := by
      rw [hν.2.1 w]
      have e2 : -(((((-((a.choose 2 : ℕ) : ℤ) : ℤ) : ℝ)) : ℂ)) = ((a.choose 2 : ℕ) : ℂ) := by
        push_cast
        ring
      rw [e2, Complex.cpow_natCast]
      rfl
    rw [e, Units.val_mul, hv, h2, algSat_prod_eq a _ B hcard]
  rw [hvalue] at hcl
  exact ⟨_, hcl⟩
