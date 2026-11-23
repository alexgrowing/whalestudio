import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocAdMul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.UnipEmbAct

theorem glue_glue {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {m : Type} [Fintype m] [DecidableEq m]
    (j₁ : B →ₙ+* A) (j₂ : C →ₙ+* B) (M : Matrix m m C) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.glue j₁ 1 (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.glue j₂ 1 M) = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.glue (j₁.comp j₂) 1 M := by
  have h1 : ∀ y, j₁ y * j₁ 1 = j₁ y := fun y => by rw [← map_mul, mul_one]
  ext r s
  by_cases h : r = s
  · subst h
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.glue, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Matrix.one_apply_eq, mul_one, map_add, map_mul, map_sub, NonUnitalRingHom.comp_apply]
    ring
  · simp [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.glue, h]

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem locAd_mul_eq (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (b : AF F) :
    GlobalTheory.UnipEmb.locAd F v a * b = GlobalTheory.UnipEmb.locAd F v (a * evFin F v b) := by
  refine Prod.ext (zero_mul _) ?_
  show singleFin v a * b.2 = singleFin v (a * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v b.2)
  refine af_ext fun u => ?_
  by_cases h : u = v
  · subst h
    rw [map_mul, evalV_singleFin_self, evalV_singleFin_self]
  · rw [map_mul, evalV_singleFin_ne h, evalV_singleFin_ne h, zero_mul]

theorem locInc_mul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v ⊗[F] E) (z : AF F ⊗[F] E) :
    GlobalTheory.UnipEmb.locInc F E v a * z = GlobalTheory.UnipEmb.locInc F E v (a * compFin F E v z) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, add_mul, hx, hy]
  | tmul a e =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
    | tmul b e' =>
      show (GlobalTheory.UnipEmb.locAd F v a ⊗ₜ[F] e) * (b ⊗ₜ[F] e') =
        GlobalTheory.UnipEmb.locInc F E v ((a ⊗ₜ[F] e) * (evFin F v b ⊗ₜ[F] e'))
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, locAd_mul_eq]
      rfl

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem mat_emb (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) :
    (matHom (AF F) σ J (emb σ J v x)).1 =
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.glue (GlobalTheory.UnipEmb.locInc F E v) 1 (matHom (Fv F v) σ J x).1 := by
  show GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.glue _ 1 (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.glue _ 1 (matHom (Fv F v) σ J x).1) = _
  rw [glue_glue]
  congr 1
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, hx, hy]; exact (map_add _ x y).symm
  | tmul a e => rfl

theorem emb_mulVec (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) (y : Fin n → AF F ⊗[F] E) :
    (matHom (AF F) σ J (emb σ J v x)).1 *ᵥ y =
      y + fun k => GlobalTheory.UnipEmb.locInc F E v ((((matHom (Fv F v) σ J x).1 - 1) *ᵥ fun i => compFin F E v (y i)) k) := by
  rw [mat_emb]
  set M := (matHom (Fv F v) σ J x).1
  set L := GlobalTheory.UnipEmb.locInc F E v
  have e2 : ∀ k, (M.map L *ᵥ y) k = L ((M *ᵥ fun i => compFin F E v (y i)) k) := fun k => by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, L, locInc_mul]
  funext k
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.glue, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, e2, Matrix.sub_mulVec, Pi.sub_apply, map_sub]
  have e3 : L 1 * y k = L (compFin F E v (y k)) := by rw [locInc_mul, one_mul]
  have e4 : (((1 - L 1) • (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) *ᵥ y) k = (1 - L 1) * y k := by
    simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply, ite_mul]
  rw [e4, sub_mul, one_mul, e3]
  ring

end GlobalTheory.UnipEmbAct

end
