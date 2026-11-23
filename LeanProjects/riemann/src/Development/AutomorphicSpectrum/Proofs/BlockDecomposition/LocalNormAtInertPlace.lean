import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

namespace GlobalTheory.CompanionTheory.FexTheta

theorem local_norm_eq_of_unique_place : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal],
  (∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) → ∀ ξ : K,
    Algebra.norm (Qv v) (algebraMap K (Kv K w) ξ) = ((Algebra.norm ℚ ξ : ℚ) : Qv v) := by
  intro K _ _ _ v w i hu ξ
  haveI : Unique (SemiLocal.PlacesOver K v) := ⟨⟨⟨w, i⟩⟩, fun x => Subtype.ext (hu x.1 x.2)⟩
  have h := SemiLocal.algebraMap_norm_eq_prod (K := ℚ) (L := K) v ξ
  rw [Fintype.prod_unique] at h
  have hd : (default : SemiLocal.PlacesOver K v) = ⟨w, i⟩ := Subsingleton.elim _ _
  rw [hd] at h
  refine h.symm.trans ?_
  exact eq_ratCast (@algebraMap ℚ (Qv v) _ _ (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v)) _

end GlobalTheory.CompanionTheory.FexTheta
