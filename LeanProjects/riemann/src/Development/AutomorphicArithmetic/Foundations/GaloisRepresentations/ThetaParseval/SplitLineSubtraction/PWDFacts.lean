import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationOperations

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem scaleRoots_X_sub_C' (a d : ℂ) : (X - C a : ℂ[X]).scaleRoots d = X - C (a * d) := by
  rw [sub_eq_add_neg, ← C_neg, X_add_C_scaleRoots, neg_mul, C_neg, ← sub_eq_add_neg]

private theorem scaleRoots_unrPol (S : Multiset ℂ) (m : ℤ) (c : ℂ) :
    (unrPol S m).scaleRoots (c ^ (-m)) = unrPol (S.map (· * c)) m := by
  unfold unrPol
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, mul_scaleRoots_of_noZeroDivisors, ih,
      scaleRoots_X_sub_C', mul_zpow]

theorem UpperTheory.Gal.TP.Sub.wDFacts_holds :
    WDFacts := by
  intro E Ω _ _ _ _ _ A w h x y
  induction x using WD.ind with | _ n a => ?_
  induction y using WD.ind with | _ m b => ?_
  refine ⟨?_, fun g => WD.charPol_lpSum _ _ g, ?_, ?_⟩
  · rw [WD.lpSum_mk, WD.unr_mk, WD.unr_mk]
    unfold WDRep.Unr
    simp only [WDRep.sum]
    rintro ⟨hN, hρ⟩
    refine ⟨?_, fun σ => ?_⟩
    · apply LinearMap.ext
      intro v
      have hv := congrArg (fun f => (f (v, 0)).1) hN
      simpa using hv
    · apply LinearMap.ext
      intro v
      have hv := congrArg (fun f => (f (v, 0)).1) (hρ σ)
      simpa [Representation.prod] using hv
  · rw [WD.lpChar_mk, WD.unr_mk, WD.unr_mk, WD.unr_mk]
    unfold WDRep.Unr
    simp only [WDRep.tensor]
    rintro ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by simp [ha, hb], fun σ => ?_⟩
    rw [Representation.tprod_apply, ha' σ, hb' σ]
    simp
  · intro g S c hx hy
    rw [WD.charPol_mk] at hx hy
    rw [WD.lpChar_mk, WD.charPol_mk, WDRep.tensor_ρ]
    have hm : m = 1 := by
      have hd := congrArg Polynomial.natDegree hy
      rw [LinearMap.charpoly_natDegree] at hd
      unfold unrPol at hd
      simpa using hd
    subst hm
    have hb : b.ρ g = c ^ (-deg g) • (1 : Module.End ℂ (Fin 1 → ℂ)) := by
      have hct := LinearMap.aeval_self_charpoly (b.ρ g)
      rw [hy] at hct
      unfold unrPol at hct
      simp only [Multiset.map_singleton, Multiset.prod_singleton, map_sub, aeval_X, aeval_C] at hct
      rw [sub_eq_zero] at hct
      rw [hct, Algebra.algebraMap_eq_smul_one]
    have ht : c ^ (-deg g) ≠ 0 := by
      intro ht0
      have h0 : b.ρ g = 0 := by
        rw [hb, ht0, zero_smul]
      have h1 : b.ρ (g * g⁻¹) = 1 := by
        rw [mul_inv_cancel, map_one]
      rw [map_mul, h0, zero_mul] at h1
      exact zero_ne_one h1
    rw [hb, TensorProduct.map_smul_right, GlobalTheory.CompanionTheory.RelOpsLeaf.charpoly_smul_eq_scaleRoots _ ht,
      GlobalTheory.CompanionTheory.RelOpsLeaf.charpoly_map_one (by simp), hx, scaleRoots_unrPol]
