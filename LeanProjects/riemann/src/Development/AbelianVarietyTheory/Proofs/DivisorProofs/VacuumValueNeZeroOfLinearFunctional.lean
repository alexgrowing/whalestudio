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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisWittModelEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinBarUnique
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

noncomputable section

namespace GlobalTheory.LinBarVacZero

def sandwich {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n d : ℕ} (A : GL (Fin n) k) (C : GL (Fin d) k) :
    Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun Y := A.val * Y * C.val
  invFun Y := (A⁻¹).val * Y * (C⁻¹).val
  left_inv Y := by
    simp only [← Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv Y := by
    simp only [← Matrix.mul_assoc]
    rw [Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem sandwich_apply {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n d : ℕ} (A : GL (Fin n) k)
    (C : GL (Fin d) k) (Y : Matrix (Fin n) (Fin d) k) : sandwich A C Y = A.val * Y * C.val := rfl

theorem comp_homeo_mem_SB {Z : Type} [TopologicalSpace Z] (T : Z ≃ₜ Z) {f : Z → ℂ} (hf : f ∈ GlobalTheory.WeilM.SB Z) :
    f ∘ T ∈ GlobalTheory.WeilM.SB Z := ⟨hf.1.comp_continuous T.continuous, hf.2.comp_homeomorph T⟩

theorem isLinBar_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {v : Pl F} (t : E →ₐ[F] Fv F v) (b bt : GL (Fin n) (Fv F v)) (hbt : bt.val = b.valᵀ)
    (c : GL (Fin d) (Fv F v)) (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ))
    (h : M.IsLinBar ψ t b c ι) : M.IsLinBar ψ t 1 1 ((LinearMap.funLeft ℂ ℂ (sandwich bt c)).comp ι) := by
  have hco : ∀ u : Matrix (Fin n) (Fin d) (AE F E),
      sandwich bt c (-((1 : GL (Fin n) (Fv F v)).1ᵀ * Y.J.map t * u.map (piW (t.comp σ)) * (Wd.J.map t)ᵀ *
        (1 : GL (Fin d) (Fv F v)).1)) =
      -(b.1ᵀ * Y.J.map t * u.map (piW (t.comp σ)) * (Wd.J.map t)ᵀ * c.1) := fun u => by
    rw [sandwich_apply, hbt]
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc]
  have hadd : ∀ Z Z' : Matrix (Fin n) (Fin d) (Fv F v), sandwich bt c (Z + Z') = sandwich bt c Z + sandwich bt c Z' :=
    fun Z Z' => by
      simp only [sandwich_apply, Matrix.mul_add, Matrix.add_mul]
  have hb : Set.BijOn (LinearMap.funLeft ℂ ℂ (sandwich bt c)) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _)
      (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _) := by
    refine ⟨fun f hf => comp_homeo_mem_SB _ hf, fun f _ f' _ e => ?_,
      fun f hf => ⟨f ∘ (sandwich bt c).symm, comp_homeo_mem_SB _ hf, ?_⟩⟩
    · funext Z
      have := congrFun e ((sandwich bt c).symm Z)
      simpa [LinearMap.funLeft_apply] using this
    · funext Z
      simp [LinearMap.funLeft_apply]
  refine ⟨hb.comp h.bij, fun u hu h0 φ hφ φ₁ hφ₁ ha Z => ?_, fun u hu h0 φ hφ φ₁ hφ₁ ha x hx hx0 => ?_⟩
  · simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
    rw [hadd, hco]
    exact h.trans u hu h0 φ hφ φ₁ hφ₁ ha _
  · simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
    rw [hco]
    exact h.mult u hu h0 φ hφ φ₁ hφ₁ ha x hx hx0

theorem linBar_vac_zero_ne : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → ι (G.M'.vac B.v₁) 0 ≠ 0 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT ι hι
  haveI := hT.geo.hV'.lat
  haveI := hT.geo.hW.lat
  obtain ⟨b', hb'⟩ := exists_isSplitBasis B.τ₁ G.V'.L hT.base.cm
  obtain ⟨c, hc⟩ := exists_isSplitBasis B.τ₁ G.W.L hT.base.cm
  obtain ⟨b₁, -, ι', hι', hvac'⟩ :=
    GlobalTheory.SplitBarVac.linBar_vac_indicator hP F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT) B.v₁ B.τ₁ b' c hb' hc
  let Q : GL (Fin a') (Fv F B.v₁) := Matrix.GeneralLinearGroup.mkOfDetNeZero b₁.valᵀ (by
    rw [Matrix.det_transpose]; exact b₁.isUnit.map Matrix.detMonoidHom |>.ne_zero)
  have h₁ := isLinBar_std G.M' B.ψ B.τ₁ b₁ Q rfl c ι' hι'
  obtain ⟨l, hl⟩ := GlobalTheory.LinModelUniq.linBar_unique F E σ B a a' G X om om' hT _ ι h₁ hι
  have hv := hT.geo.hM'.vac B.v₁
  have e := hl _ hv.1
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_smul] at e
    exact hv.2.1 (hι.bij.injOn hv.1 (Submodule.zero_mem _) (e.trans (map_zero ι).symm))
  rw [e]
  simp only [Pi.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, smul_eq_mul]
  rw [hvac', sandwich_apply, Matrix.mul_zero, Matrix.zero_mul,
    Set.indicator_of_mem (by intro i j; exact zero_mem _)]
  simpa using hl0

end GlobalTheory.LinBarVacZero
