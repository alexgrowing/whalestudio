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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.ThetaLocalBridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField F] [NumberField E] in

theorem smul_extH_extH_sub_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {R R' R'' : Type} [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] [CommRing R''] [Algebra F R''] (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)
    (j' : R' →ₗ[F] R'') (hj' : ∀ a b, j' (a * b) = j' a * j' b) (u : R'') (hu : ∀ b, u * j' (j b) = 0)
    (x : HA R σ J) :
    u • ((HA.mat R'' σ J (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extH σ J j' hj' (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extH σ J j hj x))).1 - 1) = 0 := by
  have key : ∀ z : R ⊗[F] E, u • GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) j' hj' (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU j hj z) = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, smul_add, hx, hy, add_zero]
    | tmul b e =>
      rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul, TensorProduct.smul_tmul', smul_eq_mul, hu,
        TensorProduct.zero_tmul]
  ext r s
  have e := key ((HA.mat R σ J x).1 r s - (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) r s)
  rw [Matrix.smul_apply, Matrix.zero_apply, ← e]
  congr 1
  rw [Matrix.sub_apply, GlobalTheory.AutFunCompare.mat_extH, GlobalTheory.AutFunCompare.mat_extH]
  by_cases h : r = s
  · subst h
    simp only [Matrix.one_apply_eq, mul_one, map_add, map_sub]
    ring
  · simp only [Matrix.one_apply_ne h, mul_zero, zero_add, sub_zero]

theorem at_emb_sub_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) :
    At (evFin F v) ((matHom _ σ J (emb σ J v x)).1 - 1) := by
  intro u hu
  refine smul_extH_extH_sub_one (R'' := AF F) (singleFin v) (singleFin_mul v) (LinearMap.inr F (Ainf F) (Af F))
    (fun _ _ => Prod.ext (mul_zero _).symm rfl) u (fun b => ?_) x
  refine Prod.ext (show u.1 * (0 : Ainf F) = 0 from mul_zero _) ?_
  change u.2 * singleFin v b = 0
  refine af_ext fun w => ?_
  rw [map_mul, map_zero]
  by_cases h : w = v
  · subst h
    have : evalV F w u.2 = 0 := hu
    rw [this, zero_mul]
  · rw [evalV_singleFin_ne h, mul_zero]

theorem emb_mem_uAt_piW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (d : ℕ) (W : Spc F E d) (c : E) (hc : c ≠ 0) (v : Pl F) (t : E →ₐ[F] Fv F v)
    (g : GL (Fin d) (Fv F v)) (x : GLoc σ (c • W.J.map σ) v), IsCompAt σ (c • W.J.map σ) t 1 g x →
    (toGAd hσ W.J hc).symm (GlobalTheory.AdelicU.emb σ (c • W.J.map σ) v x) ∈ UAt σ W (evFin F v) ∧
      (mat ((toGAd hσ W.J hc).symm (GlobalTheory.AdelicU.emb σ (c • W.J.map σ) v x))).map (piW t) = g.1 := by
  intro F E _ _ _ _ _ σ hσ d W c hc v t g x hx
  set y := (toGAd hσ W.J hc).symm (GlobalTheory.AdelicU.emb σ (c • W.J.map σ) v x) with hy
  have hm : mat y = (matHom _ σ _ (GlobalTheory.AdelicU.emb σ (c • W.J.map σ) v x)).1 := by
    have := toGAd_mat hσ W.J hc y
    rw [hy, MulEquiv.apply_symm_apply] at this
    rw [mat, ← this]
    rfl
  refine ⟨?_, ?_⟩
  · change At _ (mat y - 1)
    rw [hm]
    exact at_emb_sub_one v x
  · have hpi : (mat y).map (piW t) = ((mat y).map (compFin F E v)).map (splitProj t) := by
      rw [Matrix.map_map]; rfl
    rw [hpi, hm]
    have h2 : (matHom _ σ _ (GlobalTheory.AdelicU.emb σ (c • W.J.map σ) v x)).1.map (compFin F E v) =
        (matHom _ σ _ x).1 := by
      rw [← proj_emb_self σ (c • W.J.map σ) v x, matHom_proj, proj_emb_self]
      rfl
    rw [h2]
    have h3 := hx
    unfold IsCompAt at h3
    rw [h3]
    simp

end GlobalTheory.ThetaLocalBridge
