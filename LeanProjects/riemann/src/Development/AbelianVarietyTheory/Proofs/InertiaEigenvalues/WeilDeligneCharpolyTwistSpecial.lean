import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.SpCharpoly

theorem charpoly_blockDiag {m o R : Type*} [Fintype m] [DecidableEq m] [Fintype o]
    [DecidableEq o] [CommRing R] (B : o → Matrix m m R) :
    (Matrix.blockDiagonal B).charpoly = ∏ k, (B k).charpoly := by
  have e : Matrix.charmatrix (Matrix.blockDiagonal B) =
      Matrix.blockDiagonal (fun k => Matrix.charmatrix (B k)) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply,
      Prod.mk.injEq]
    split_ifs <;> simp_all
  rw [Matrix.charpoly, e, Matrix.det_blockDiagonal]
  rfl

theorem charpoly_map_diagEnd {n m : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (c : Fin m → ℂ) :
    LinearMap.charpoly (TensorProduct.map f (diagEnd c)) = ∏ i, LinearMap.charpoly (c i • f) := by
  classical
  set b := Pi.basisFun ℂ (Fin n)
  have e : LinearMap.toMatrix (Pi.basisFun ℂ (Fin m)) (Pi.basisFun ℂ (Fin m)) (diagEnd c) =
      Matrix.diagonal c := by
    ext i j
    simp [LinearMap.toMatrix_apply, Matrix.diagonal_apply, Pi.single_apply]
  rw [← LinearMap.charpoly_toMatrix _ (b.tensorProduct (Pi.basisFun ℂ (Fin m))),
    TensorProduct.toMatrix_map, e]
  have e2 : Matrix.kroneckerMap (· * ·) (LinearMap.toMatrix b b f) (Matrix.diagonal c) =
      Matrix.blockDiagonal fun i => LinearMap.toMatrix b b (c i • f) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply,
      map_smul, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [mul_comm]
  rw [e2, charpoly_blockDiag]
  exact Finset.prod_congr rfl fun i _ => LinearMap.charpoly_toMatrix _ _

end GlobalTheory.WeilDeligne.SpCharpoly

namespace GlobalTheory.WeilDeligne

theorem charPol_lpTw_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), (x.lpTw 0).lpChar (WD.lpSp h 1) = x ∧ ∀ (l : ℕ) (σ : Weil h), ((x.lpTw (((l : ℝ) - 1) / 2)).lpChar (WD.lpSp h l)).charPol σ = ((Multiset.range l).map fun j : ℕ => (x.lpTw j).charPol σ).prod := by
  intro E Ω _ _ _ _ _ A w h x
  refine ⟨?_, fun l σ => ?_⟩
  · rw [WD.lpTw_zero]
    induction x using WD.ind with
    | hP n a =>
      rw [WD.lpSp, WD.lpChar_mk]
      refine WD.sound (WDRep.Iso.symm ⟨(TensorProduct.rid ℂ (Fin n → ℂ)).symm ≪≫ₗ
        TensorProduct.congr (LinearEquiv.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm,
        fun σ v => ?_, fun v => ?_⟩)
      · have : (WDRep.sp h 1).ρ σ = 1 := by
          refine LinearMap.ext fun v => funext fun i => ?_
          simp [WDRep.spEig]
        rw [WDRep.tensor_ρ, this]
        simp
      · have : (WDRep.sp h 1).N = 0 := by
          refine LinearMap.ext fun v => funext fun i => ?_
          simp [shiftEnd_apply]
        rw [WDRep.tensor_N, this]
        simp
  · induction x using WD.ind with
    | hP n a =>
      have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
      rw [WD.lpSp, WD.lpTw_mk, WD.lpChar_mk, WD.charPol_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
        SpCharpoly.charpoly_map_diagEnd]
      change _ = ∏ j ∈ Finset.range l, ((WD.mk a).lpTw (j : ℕ)).charPol σ
      rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => ((WD.mk a).lpTw (j : ℕ)).charPol σ)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.tw_ρ, smul_smul, ← mul_zpow, WDRep.spEig,
        coe_qPow, ← Complex.cpow_add _ _ hq, ← Complex.ofReal_add, sub_add_cancel]

end GlobalTheory.WeilDeligne
