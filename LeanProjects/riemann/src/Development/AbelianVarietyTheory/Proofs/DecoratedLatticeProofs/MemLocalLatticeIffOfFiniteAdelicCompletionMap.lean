import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.LocFromGlob

open scoped TensorProduct

theorem mem_latLoc_iff_of_latHat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L L' : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (hL' : L'.FG) (b : GL (Fin n) (TensorProduct F (Af F) E))
    (hb : ∀ w, w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔
      b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L' : Set (Fin n → E)))
    (v : HeightOneSpectrum (𝓞 F)) (z : Fin n → TensorProduct F (Fv F v) E) :
    z ∈ latLoc F L v ↔
      (Formalism.UG.bc (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom b).val *ᵥ z ∈ latLoc F L' v := by

  let ext : (Fin n → Fv F v ⊗[F] E) → (Fin n → Af F ⊗[F] E) :=
    fun z i => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v) (z i)
  have hself : ∀ z, GlobalTheory.AdelicU.vecLoc v (ext z) = z := fun z =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_self _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_self v) _
  have hne : ∀ z u, u ≠ v → GlobalTheory.AdelicU.vecLoc u (ext z) = 0 := fun z u hu =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_ne hu) _
  have hmul : ∀ (g : GL (Fin n) (TensorProduct F (Af F) E)) u y, GlobalTheory.AdelicU.vecLoc u (g.val *ᵥ y) =
      (Formalism.UG.bc (Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E)).toRingHom g).val *ᵥ
        GlobalTheory.AdelicU.vecLoc u y := fun g u y => funext fun i =>
    RingHom.map_mulVec (Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E)).toRingHom _ y i
  have hext : ∀ (M : Submodule (𝓞 E) (Fin n → E)), M.FG → ∀ z, z ∈ latLoc F M v →
      ext z ∈ Formalism.MainNotions.StandardLattice.latHat F E (M : Set (Fin n → E)) := fun M hM z hz => by
    rw [GlobalTheory.AdelicU.mem_latHat_iff hM]
    intro u
    by_cases e : u = v
    · subst e; rw [hself]; exact hz
    · rw [hne z u e]; exact zero_mem _
  constructor
  · intro hz
    have h1 := (GlobalTheory.AdelicU.mem_latHat_iff hL' _).1 ((hb _).1 (hext L hL z hz)) v
    rwa [hmul, hself] at h1
  · intro hz
    have h1 := hext L' hL' _ hz
    set y := ext ((Formalism.UG.bc (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom b).val *ᵥ z)
    have h2 : b.val *ᵥ ((b⁻¹).val *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have h3 := (GlobalTheory.AdelicU.mem_latHat_iff hL _).1 ((hb _).2 (h2 ▸ h1)) v
    rw [hmul, hself, Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec] at h3
    exact h3

end GlobalTheory.Core.LocFromGlob
