import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.SplitWeil NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.AutomorphicL2Unitary (conv starFn IsTopIrreducible)
open scoped TensorProduct Topology Pointwise ComplexConjugate ContDiff Matrix

noncomputable section

namespace GlobalTheory.Orb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

instance fintypeEmbOver (w : InfinitePlace F) : Fintype (EmbOver E w) := Fintype.ofFinite _

def archMat {w : InfinitePlace F} (τ : EmbOver E w) : GArch σ J w →* Matrix (Fin n) (Fin n) ℂ :=
  (infEmb τ).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (matHom _ σ J))

def archCoord (w : InfinitePlace F) (g : GArch σ J w) : EmbOver E w → Fin n → Fin n → ℂ :=
  fun τ => matCoord (archMat σ J τ) g

def infCoord (g : GInf σ J) : ∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin n → ℂ :=
  fun w => archCoord σ J w (projInfArch σ J w g)

omit [NumberField E] in

theorem archMat_apply {w : InfinitePlace F} (τ : EmbOver E w) (g : GArch σ J w) :
    archMat σ J τ g = (matHom _ σ J g).1.map (infEmb τ) := rfl

theorem archMat_eq_archEquiv {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w)
    (g : GArch σ J w) : archMat σ J τ g = (archEquiv J h τ g).1.1 := rfl

theorem continuous_infEmb {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (infEmb τ) := by
  have : IsModuleTopology w.Completion (w.Completion ⊗[F] E) := ⟨rfl⟩
  letI : Algebra w.Completion ℂ := (InfinitePlace.Completion.extensionEmbedding w).toAlgebra
  have : ContinuousSMul w.Completion ℂ :=
    ⟨((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp continuous_fst).mul continuous_snd⟩
  let L : w.Completion ⊗[F] E →ₗ[w.Completion] ℂ :=
    { toFun := infEmb τ
      map_add' := map_add _
      map_smul' := fun c y => by
        have : c • y = (c ⊗ₜ[F] (1 : E)) * y := by rw [Algebra.smul_def]; rfl
        rw [this, map_mul, infEmb_tmul, map_one, mul_one]; rfl }
  exact IsModuleTopology.continuous_of_linearMap L

theorem continuous_archMat {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (archMat σ J τ) :=
  (Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous).matrix_map (continuous_infEmb τ)

theorem continuous_archCoord (w : InfinitePlace F) : Continuous (archCoord σ J w) :=
  continuous_pi fun τ => continuous_archMat σ J τ

theorem continuous_infCoord : Continuous (infCoord σ J) :=
  continuous_pi fun w => (continuous_archCoord σ J w).comp (continuous_projInfArch σ J w)

variable {σ} in

theorem isEmbedding_archMat (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) :
    Topology.IsEmbedding (matCoord (archMat σ J τ)) := by
  let e := RingEquiv.ofBijective _ (infEmb_bijective h τ)
  have hb : ∀ {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] (φ : A →+* B),
      Continuous φ → Continuous (Formalism.UG.bc (n := Fin n) φ) := fun φ hφ =>
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map hφ, Units.continuous_coe_inv.matrix_map hφ⟩
  have h1 : Topology.IsEmbedding (Formalism.UG.bc (n := Fin n) (infEmb τ)) :=
    Function.LeftInverse.isEmbedding (f := Formalism.UG.bc (n := Fin n) e.symm.toRingHom)
      (fun x => Units.ext (Matrix.ext fun i j => e.symm_apply_apply _))
      (hb _ (Frames.continuous_infEmb_symm h τ)) (hb _ (continuous_infEmb τ))
  have h2 : Topology.IsEmbedding (Units.val : (Matrix (Fin n) (Fin n) ℂ)ˣ → Matrix (Fin n) (Fin n) ℂ) := by
    refine Units.isEmbedding_val_mk' (f := fun A => A⁻¹) (fun A hA => ?_) fun u => by simp
    have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
    exact (continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd)).continuousWithinAt
  exact h2.comp (h1.comp (isEmbedding_matHom _ σ J))

abbrev CcLoc (v : HeightOneSpectrum (𝓞 F)) : Submodule ℂ (GLoc σ J v → ℂ) := SB (GLoc σ J v)

abbrev CcArch (w : InfinitePlace F) : Submodule ℂ (GArch σ J w → ℂ) := CcSmooth (archCoord σ J w)

abbrev CcInf : Submodule ℂ (GInf σ J → ℂ) := CcSmooth (infCoord σ J)

abbrev CcFin : Submodule ℂ (GFin σ J → ℂ) := SB (GFin σ J)

def infFin (a : GInf σ J → ℂ) (b : GFin σ J → ℂ) : GAd σ J → ℂ := fun g => a (projInf σ J g) * b (projFin σ J g)

def CcAd : Submodule ℂ (GAd σ J → ℂ) :=
  Submodule.span ℂ {f | ∃ a ∈ CcInf σ J, ∃ b ∈ CcFin σ J, f = infFin σ J a b}

def tensorInf (fa : ∀ w, GArch σ J w → ℂ) : GInf σ J → ℂ := fun g => ∏ w, fa w (projInfArch σ J w g)

def tensorFin (ff : ∀ v, GLoc σ J v → ℂ) : GFin σ J → ℂ := fun g => ∏ᶠ v, ff v (projFinLoc σ J v g)

def tensor (fa : ∀ w, GArch σ J w → ℂ) (ff : ∀ v, GLoc σ J v → ℂ) : GAd σ J → ℂ :=
  fun g => (∏ w, fa w (projArch σ J w g)) * ∏ᶠ v, ff v (proj σ J v g)

variable (L : Submodule (𝓞 E) (Fin n → E))

def unitLoc (v : HeightOneSpectrum (𝓞 F)) : GLoc σ J v → ℂ := (stabLoc σ J L v : Set (GLoc σ J v)).indicator 1

def IsFinFamily (ff : ∀ v, GLoc σ J v → ℂ) : Prop :=
  (∀ v, ff v ∈ CcLoc σ J v) ∧ ∀ᶠ v in cofinite, ff v = unitLoc σ J L v

def IsPureTensor (f : GAd σ J → ℂ) : Prop :=
  ∃ fa ff, (∀ w, fa w ∈ CcArch σ J w) ∧ IsFinFamily σ J L ff ∧ f = tensor σ J fa ff

variable {σ J L} {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}

theorem ccArch_eq (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) :
    CcArch σ J w = CcMat (archMat σ J τ) := by
  classical
  refine le_antisymm (ccSmooth_le (p := fun y τ' i j => if infEmb τ' = infEmb τ then y i j else conj (y i j)) ?_ ?_)
    (ccSmooth_le (p := fun y => y τ) (by fun_prop) fun _ => rfl)
  · refine contDiff_pi.2 fun τ' => contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    split_ifs
    · fun_prop
    · exact Complex.conjCLE.contDiff.comp (by fun_prop)
  · intro g
    funext τ' i j
    change infEmb τ' _ = if _ then infEmb τ _ else conj (infEmb τ _)
    split_ifs with e
    · rw [e]
    · rw [(infEmb_eq_or_conj h τ τ').resolve_left e]; rfl

omit [NumberField E] in

theorem tensor_eq_infFin : tensor σ J fa ff = infFin σ J (tensorInf σ J fa) (tensorFin σ J ff) := by
  funext g
  simp [tensor, infFin, tensorInf, tensorFin]

theorem infFin_mem_ccAd {a : GInf σ J → ℂ} {b : GFin σ J → ℂ} (ha : a ∈ CcInf σ J) (hb : b ∈ CcFin σ J) :
    infFin σ J a b ∈ CcAd σ J := Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

theorem continuous_of_mem_ccAd {f : GAd σ J → ℂ} (h : f ∈ CcAd σ J) : Continuous f ∧ HasCompactSupport f := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hf
    refine ⟨((continuous_of_mem_ccSmooth (continuous_infCoord σ J) ha).comp (continuous_projInf σ J)).mul
      (hb.1.continuous.comp (continuous_projFin σ J)), .intro
      ((infFinEquiv σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (IsCompact.prod ha.1 hb.2)) fun g hg => ?_⟩
    by_contra hne
    exact hg ⟨subset_tsupport a (left_ne_zero_of_mul hne), subset_tsupport b (right_ne_zero_of_mul hne)⟩
  | zero => exact ⟨continuous_zero, HasCompactSupport.zero⟩
  | add f f' _ _ h h' => exact ⟨h.1.add h'.1, h.2.add h'.2⟩
  | smul a f _ h => exact ⟨h.1.const_smul a, h.2.smul_left (f := fun _ => a)⟩

theorem tensorInf_mem (h : ∀ w, fa w ∈ CcArch σ J w) : tensorInf σ J fa ∈ CcInf σ J := by
  choose Φ hΦ e using fun w => (h w).2
  refine ⟨.intro ((infContEquivPi σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage
    (isCompact_univ_pi fun w => (h w).1)) fun g hg => ?_, fun y => ∏ w, Φ w (y w),
    contDiff_prod fun w _ => (hΦ w).comp (contDiff_pi.1 contDiff_id w), fun g => Finset.prod_congr rfl fun w _ => e w _⟩
  by_contra hne
  exact hg fun w _ => subset_tsupport _ (Finset.prod_ne_zero_iff.1 hne w (Finset.mem_univ w))

variable [Submodule.IsLattice E L]

theorem unitLoc_mem (v : HeightOneSpectrum (𝓞 F)) : unitLoc σ J L v ∈ CcLoc σ J v :=
  indicator_mem_SB (isOpen_stabLoc σ J L v) (isCompact_stabLoc σ J L v)

theorem isFinFamily_unit : IsFinFamily σ J L (unitLoc σ J L) := ⟨unitLoc_mem, .of_forall fun _ => rfl⟩

theorem IsFinFamily.of_lattice (h : IsFinFamily σ J L ff) (L' : Submodule (𝓞 E) (Fin n → E))
    [Submodule.IsLattice E L'] : IsFinFamily σ J L' ff :=
  ⟨h.1, (h.2.and (eventually_stabLoc_eq σ J L L')).mono fun v hv => by rw [hv.1, unitLoc, unitLoc, hv.2]⟩

theorem IsFinFamily.finite_mulSupport (h : IsFinFamily σ J L ff) (g : GFin σ J) :
    (Function.mulSupport fun v => ff v (projFinLoc σ J v g)).Finite :=
  (h.2.and (eventually_projFinLoc_mem_stabLoc σ J L g)).mono (q := fun v => ff v (projFinLoc σ J v g) = 1)
    fun v hv => by rw [hv.1, unitLoc, indicator_of_mem hv.2, Pi.one_apply]

theorem IsFinFamily.tensorFin_ne_zero_iff (h : IsFinFamily σ J L ff) (g : GFin σ J) :
    tensorFin σ J ff g ≠ 0 ↔ ∀ v, ff v (projFinLoc σ J v g) ≠ 0 := by
  refine ⟨fun hne v hv => hne (finprod_eq_zero _ v hv (h.finite_mulSupport g)), fun hne => ?_⟩
  rw [tensorFin, finprod_eq_prod _ (h.finite_mulSupport g)]
  exact Finset.prod_ne_zero_iff.2 fun v _ => hne v

theorem IsFinFamily.tensorFin_mem (h : IsFinFamily σ J L ff) : tensorFin σ J ff ∈ CcFin σ J := by
  let S := (eventually_cofinite.1 h.2).toFinset
  have hS : ∀ v ∉ S, ff v = unitLoc σ J L v := fun v hv => by simpa [S] using hv
  choose U hU hf using fun v => exists_biinvariant (h.1 v)
  have ho : IsOpen ({k | ∀ v, projFinLoc σ J v k ∈ stabLoc σ J L v} ∩ ⋂ v ∈ S, projFinLoc σ J v ⁻¹' U v) :=
    (isRestrGroup_GFin σ J L).isOpen_all.inter
      (isOpen_biInter_finset fun v _ => (hU v).preimage (continuous_projFinLoc σ J v))
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun g => ⟨_, ho.preimage (continuous_const_mul g⁻¹),
    by simp, fun x hx => finprod_congr fun v => ?_⟩,
    .intro ((isRestrGroup_GFin σ J L).isCompact_cyl S (fun _ => univ) (fun v => tsupport (ff v)) (fun e => e.elim)
      fun v _ => (h.1 v).2) fun g hg => ?_⟩
  · rw [← mul_inv_cancel_left g x, map_mul]
    by_cases hv : v ∈ S
    · exact (hf v _ (mem_iInter₂.1 hx.2 v hv) _).2
    · rw [hS v hv, unitLoc]
      by_cases hg : projFinLoc σ J v g ∈ stabLoc σ J L v
      · rw [indicator_of_mem hg, indicator_of_mem (mul_mem hg (hx.1 v))]; rfl
      · rw [indicator_of_notMem hg, indicator_of_notMem fun e => hg ((Subgroup.mul_mem_cancel_right _ (hx.1 v)).1 e)]
  · by_contra hne
    have := (h.tensorFin_ne_zero_iff g).1 hne
    refine hg ⟨fun e => e.elim, fun v _ => subset_tsupport _ (this v), fun v hv => ?_⟩
    by_contra hn
    exact this v (by rw [hS v hv, unitLoc, indicator_of_notMem hn])

theorem tensor_mem_ccAd (ha : ∀ w, fa w ∈ CcArch σ J w) (hf : IsFinFamily σ J L ff) : tensor σ J fa ff ∈ CcAd σ J :=
  by rw [tensor_eq_infFin]; exact infFin_mem_ccAd (tensorInf_mem ha) hf.tensorFin_mem

theorem IsPureTensor.mem_ccAd {f : GAd σ J → ℂ} (h : IsPureTensor σ J L f) : f ∈ CcAd σ J := by
  obtain ⟨fa, ff, ha, hf, rfl⟩ := h
  exact tensor_mem_ccAd ha hf

theorem IsFinFamily.starFn_tensor (h : IsFinFamily σ J L ff) :
    IsFinFamily σ J L (fun v => starFn (ff v)) ∧
      starFn (tensor σ J fa ff) = tensor σ J (fun w => starFn (fa w)) fun v => starFn (ff v) := by
  refine ⟨⟨fun v => starFn_mem_SB (h.1 v), h.2.mono fun v hv => funext fun g => ?_⟩, funext fun g => ?_⟩
  · by_cases hg : g ∈ stabLoc σ J L v <;> simp [hv, starFn, unitLoc, indicator, hg]
  · have := h.finite_mulSupport (projFin σ J g⁻¹)
    simp only [projFinLoc_projFin, map_inv] at this
    simp only [starFn, tensor, map_mul, map_prod, map_inv]
    rw [map_finprod _ this]

theorem integral_tensor {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)} {μ : Measure (GAd σ J)}
    (hμ : IsRestrictedProd σ J L μa μf μ) (ha : ∀ w, fa w ∈ CcArch σ J w) (hf : IsFinFamily σ J L ff) :
    ∫ g, tensor σ J fa ff g ∂μ = (∏ w, ∫ y, fa w y ∂μa w) * ∏ᶠ v, ∫ y, ff v y ∂μf v := by
  have := hμ.haar_arch
  have := hμ.haar_loc
  let S := (eventually_cofinite.1 (hf.2.and hμ.eventually_eq_one)).toFinset
  have hS : ∀ v ∉ S, ff v = unitLoc σ J L v ∧ μf v (stabLoc σ J L v) = 1 := fun v hv => by
    simpa only [S, Finite.mem_toFinset, mem_setOf_eq, not_not] using hv
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ fun v hv => by_contra fun h => hv (by
    rw [(hS v h).1, unitLoc]
    refine (integral_indicator_const _ (isOpen_stabLoc σ J L v).measurableSet).trans ?_
    rw [Measure.real, (hS v h).2, ENNReal.toReal_one, one_smul]; rfl)]
  exact (((hμ.euler_product S fun v hv => (hS v hv).2).1 fa ff fun w =>
    (continuous_of_mem_ccSmooth (continuous_archCoord σ J w) (ha w)).integrable_of_hasCompactSupport (ha w).1).2.1
    (fun v hv => (hS v hv).1) fun v _ => (hf.1 v).1.continuous.integrable_of_hasCompactSupport (hf.1 v).2).2

variable (J L) in

theorem exists_isPureTensor (h : IsCMExt F E σ) : ∃ f, IsPureTensor σ J L f ∧ f 1 = 1 := by
  choose φ h1 h2 _ _ using fun w => exists_bump (isEmbedding_archMat J h (Classical.arbitrary (EmbOver E w))).isInducing
    (g := 1) univ_mem
  refine ⟨_, ⟨fun w x => φ w x, _, fun w => ccArch_eq h _ ▸ h1 w, isFinFamily_unit, rfl⟩, ?_⟩
  simp [tensor, h2, unitLoc]

variable (σ J L) in

structure SplitAt (v : HeightOneSpectrum (𝓞 F)) where

  emb : E →ₐ[F] Fv F v

  basis : GL (Fin n) (Fv F v)

  cm : IsCMExt F E σ

  herm : IsHermND σ J

  selfDual : IsSelfDualAt σ J L v

  isBasis : IsSplitBasis emb L basis

abbrev ResF (v : HeightOneSpectrum (𝓞 F)) : Type := IsLocalRing.ResidueField (v.adicCompletionIntegers F)

instance finite_GL_resF (v : HeightOneSpectrum (𝓞 F)) : Finite (GL (Fin n) (ResF v)) :=
  have : Finite (ResF v) := Formalism.UG.P.glint_finite_residueField v
  have : Finite (Matrix (Fin n) (Fin n) (ResF v)) := inferInstanceAs (Finite (Fin n → Fin n → ResF v))
  inferInstance

def IsUnif {v : HeightOneSpectrum (𝓞 F)} (ϖ : (Fv F v)ˣ) : Prop := Valued.v (ϖ : Fv F v) = WithZero.exp (-1 : ℤ)

def strictTorus {k : Type} [Field k] (n : ℕ) (ϖ : kˣ) : Set (Fin n → kˣ) :=
  {t | ∃ a : Fin n → ℤ, StrictAnti a ∧ t = fun i => ϖ ^ a i}

theorem strictTorus_nonempty {k : Type} [Field k] (n : ℕ) (ϖ : kˣ) : (strictTorus n ϖ).Nonempty :=
  ⟨_, fun i => -(i : ℤ), fun _ _ h => neg_lt_neg (by exact_mod_cast h), rfl⟩

theorem exists_isUnif (v : HeightOneSpectrum (𝓞 F)) : ∃ ϖ : (Fv F v)ˣ, IsUnif ϖ := by
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ))
  exact ⟨Units.mk0 p fun e => WithZero.exp_ne_zero (hp.symm.trans ((congrArg _ e).trans (map_zero _))), hp⟩

open ValuativeRel in

theorem IsUnif.valuation_eq {v : HeightOneSpectrum (𝓞 F)} {ϖ : (Fv F v)ˣ} (h : IsUnif ϖ) :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    valuation (Fv F v) (ϖ : Fv F v) = uniformizer (Fv F v) := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  apply le_antisymm
  · rw [le_uniformizer_iff, he.lt_one_iff_lt_one, h, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer (Fv F v))
    have h1 : valuation (Fv F v) y < 1 := hy ▸ uniformizer_lt_one
    rw [← hy, he.le_iff_le, h]
    rw [he.lt_one_iff_lt_one] at h1
    by_cases h0 : Valued.v y = 0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega

namespace SplitAt

omit [Submodule.IsLattice E L]

variable {v : HeightOneSpectrum (𝓞 F)} (s : SplitAt σ J L v)

def equiv : GLoc σ J v ≃ₜ* GL (Fin n) (Fv F v) := splitEquivIn s.cm s.herm s.emb s.basis

def red : stabLoc σ J L v →* GL (Fin n) (ResF v) := splitRed s.cm s.herm s.selfDual s.isBasis

def iwahori : Subgroup (GLoc σ J v) :=
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  (GlobalTheory.SmGL.iwahori (Fv F v) (Fin n)).comap (s.equiv : GLoc σ J v →* GL (Fin n) (Fv F v))

def diag (t : Fin n → (Fv F v)ˣ) : GLoc σ J v := s.equiv.symm (GlobalTheory.SmGL.diagT _ _ t)

def iwahoriCoset (t : Fin n → (Fv F v)ˣ) : Set (GLoc σ J v) := DoubleCoset.doubleCoset (s.diag t) s.iwahori s.iwahori

def cosetFn (t : Fin n → (Fv F v)ˣ) : GLoc σ J v → ℂ := (s.iwahoriCoset t).indicator 1

def idem {W : Type} [AddCommGroup W] [Module ℂ W] (μ : Measure (GLoc σ J v))
    (τ : Representation ℂ (GL (Fin n) (ResF v)) W) : GLoc σ J v → ℂ := typeIdem μ s.red τ

theorem red_surjective : Function.Surjective s.red := splitRed_surjective _ _ _ _

theorem red_eq_one_iff (k : stabLoc σ J L v) : s.red k = 1 ↔ k.1 ∈ stabLocOne σ J s.emb L := splitRed_eq_one_iff _ _ _ _ k

theorem mem_stabLoc_iff {g : GLoc σ J v} :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    g ∈ stabLoc σ J L v ↔ s.equiv g ∈ KO (Fv F v) (Fin n) := by
  rw [← (GLint_eq_KO_and_princ_eq_KOne v n).1]
  exact mem_stabLoc_iff_GLint s.cm s.herm s.selfDual s.isBasis

theorem mem_iwahori {g : GLoc σ J v} :
    g ∈ s.iwahori ↔ g ∈ stabLoc σ J L v ∧ ∀ i j, j < i → Valued.v ((s.equiv g).1 i j) < 1 := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (Fv F v))
    (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  refine GlobalTheory.SmGL.mem_iwahori.trans (and_congr s.mem_stabLoc_iff.symm ?_)
  simp only [he.lt_one_iff_lt_one]
  rfl

theorem iwahori_le : s.iwahori ≤ stabLoc σ J L v := fun _ h => (s.mem_iwahori.1 h).1

theorem mem_iwahoriCoset {t : Fin n → (Fv F v)ˣ} {g : GLoc σ J v} :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    g ∈ s.iwahoriCoset t ↔ ∃ a ∈ GlobalTheory.SmGL.iwahori (Fv F v) (Fin n), ∃ b ∈ GlobalTheory.SmGL.iwahori (Fv F v) (Fin n),
      s.equiv g = a * GlobalTheory.SmGL.diagT _ _ t * b := by
  rw [iwahoriCoset, DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, ha, _, hb, by simp [diag]⟩
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨s.equiv.symm a, ?_, s.equiv.symm b, ?_, s.equiv.injective (by simp [diag, e])⟩
    · exact Subgroup.mem_comap.2 ((s.equiv.apply_symm_apply a).symm ▸ ha :)
    · exact Subgroup.mem_comap.2 ((s.equiv.apply_symm_apply b).symm ▸ hb :)

theorem isOpen_iwahori : IsOpen (s.iwahori : Set (GLoc σ J v)) :=
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (Fv F v) (Fin n)).preimage (map_continuous s.equiv)

theorem isCompact_iwahori : IsCompact (s.iwahori : Set (GLoc σ J v)) :=
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  s.equiv.toHomeomorph.isClosedEmbedding.isCompact_preimage (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (Fv F v) (Fin n))

theorem cosetFn_mem (t : Fin n → (Fv F v)ˣ) : s.cosetFn t ∈ CcLoc σ J v :=
  indicator_mem_SB s.isOpen_iwahori.mul_left ((s.isCompact_iwahori.mul isCompact_singleton).mul s.isCompact_iwahori)

theorem cosetFn_diag (t : Fin n → (Fv F v)ˣ) : s.cosetFn t (s.diag t) = 1 :=
  indicator_of_mem (DoubleCoset.mem_doubleCoset_self _ _ _) _

variable {W : Type} [AddCommGroup W] [Module ℂ W] (μ : Measure (GLoc σ J v))
  (τ : Representation ℂ (GL (Fin n) (ResF v)) W)

theorem idem_mem [Submodule.IsLattice E L] : s.idem μ τ ∈ CcLoc σ J v := by
  refine typeIdem_mem_SB μ _ τ (isOpen_stabLoc σ J L v) (isCompact_stabLoc σ J L v) ?_
  rw [show (s.red.ker : Set (stabLoc σ J L v)) = (↑) ⁻¹' (stabLocOne σ J s.emb L : Set (GLoc σ J v)) from
    Set.ext s.red_eq_one_iff]
  exact (isOpen_stabLocOne J s.emb L s.cm).preimage continuous_subtype_val

theorem starFn_idem [FiniteDimensional ℂ W] : starFn (s.idem μ τ) = s.idem μ τ := starFn_typeIdem μ _ τ

end SplitAt

variable (σ J L) in

structure TypeData where

  S : Finset (HeightOneSpectrum (𝓞 F))

  frame : ∀ v : S, SplitAt σ J L v

  W : S → Type
  [acg : ∀ v, AddCommGroup (W v)]
  [mod : ∀ v, Module ℂ (W v)]
  [fd : ∀ v, FiniteDimensional ℂ (W v)]

  τ : ∀ v : S, Representation ℂ (GL (Fin n) (ResF v.1)) (W v)

  irred : ∀ v, (τ v).IsIrreducible

attribute [instance] TypeData.acg TypeData.mod TypeData.fd

variable (σ J L) in

structure UnitaryAuxiliaryPlaceData where

  u : HeightOneSpectrum (𝓞 F)

  frame : SplitAt σ J L u

  ϖ : (Fv F u)ˣ

  unif : IsUnif ϖ

def TypeData.idem (T : TypeData σ J L) (μf : ∀ v, Measure (GLoc σ J v)) (v : T.S) : GLoc σ J v → ℂ :=
  (T.frame v).idem (μf v) (T.τ v)

def IsTestFin (T : TypeData σ J L) (U : UnitaryAuxiliaryPlaceData σ J L) (μf : ∀ v, Measure (GLoc σ J v))
    (ff : ∀ v, GLoc σ J v → ℂ) : Prop :=
  U.u ∉ T.S ∧
  (∀ v : T.S, ∃ h ∈ CcLoc σ J v, ff v = conv (μf v) (conv (μf v) (T.idem μf v) h) (T.idem μf v)) ∧
  (∃ t ∈ strictTorus n U.ϖ, ff U.u = U.frame.cosetFn t) ∧
  (∀ v ∉ T.S, v ≠ U.u → ff v ∈ CcLoc σ J v) ∧
  ∀ᶠ v in cofinite, ff v = unitLoc σ J L v

section ArchFamily

variable {Hs : InfinitePlace F → Type} [∀ w, NormedAddCommGroup (Hs w)] [∀ w, InnerProductSpace ℂ (Hs w)]
  [∀ w, CompleteSpace (Hs w)]

def IsTestArch (Ψ : ∀ w : InfinitePlace F, EmbOver E w) (D : ∀ w, GArch σ J w →* (Hs w →L[ℂ] Hs w)) (μa : ∀ w, Measure (GArch σ J w))
    (fa : ∀ w, GArch σ J w → ℂ) : Prop := ∀ w, IsPseudoCoeff (archMat σ J (Ψ w)) (μa w) (D w) (fa w)

def IsTestFn (Ψ : ∀ w : InfinitePlace F, EmbOver E w) (D : ∀ w, GArch σ J w →* (Hs w →L[ℂ] Hs w)) (T : TypeData σ J L)
    (U : UnitaryAuxiliaryPlaceData σ J L) (μa : ∀ w, Measure (GArch σ J w)) (μf : ∀ v, Measure (GLoc σ J v)) (f : GAd σ J → ℂ) : Prop :=
  ∃ fa ff, IsTestArch Ψ D μa fa ∧ IsTestFin T U μf ff ∧ f = tensor σ J fa ff

variable {Ψ : ∀ w : InfinitePlace F, EmbOver E w} {D : ∀ w, GArch σ J w →* (Hs w →L[ℂ] Hs w)} {T : TypeData σ J L} {U : UnitaryAuxiliaryPlaceData σ J L}
  {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)}

theorem IsTestFin.isFinFamily (h : IsTestFin T U μf ff) : IsFinFamily σ J L ff := by
  obtain ⟨-, h1, ⟨t, -, h2⟩, h3, h4⟩ := h
  refine ⟨fun v => ?_, h4⟩
  by_cases hv : v ∈ T.S
  · obtain ⟨φ, hφ, e⟩ := h1 ⟨v, hv⟩
    have := (T.frame ⟨v, hv⟩).idem_mem (μf v) (T.τ ⟨v, hv⟩)
    exact e ▸ conv_mem_SB (conv_mem_SB this hφ) this
  · by_cases hu : v = U.u
    · subst hu; exact h2 ▸ U.frame.cosetFn_mem t
    · exact h3 v hv hu

theorem IsTestFn.isPureTensor {f : GAd σ J → ℂ} (h : IsTestFn Ψ D T U μa μf f) : IsPureTensor σ J L f := by
  obtain ⟨fa, ff, ha, hf, rfl⟩ := h
  exact ⟨fa, ff, fun w => ccArch_eq U.frame.cm (Ψ w) ▸ (ha w).mem, hf.isFinFamily, rfl⟩

open Classical in
omit [Submodule.IsLattice E L] in

theorem exists_isTestFin (hu : U.u ∉ T.S) (μf : ∀ v, Measure (GLoc σ J v)) (h : ∀ v : T.S, GLoc σ J v → ℂ)
    (hh : ∀ v : T.S, h v ∈ CcLoc σ J v) {t : Fin n → (Fv F U.u)ˣ} (ht : t ∈ strictTorus n U.ϖ)
    {rest : ∀ v, GLoc σ J v → ℂ} (hr : IsFinFamily σ J L rest) :
    ∃ ff, IsTestFin T U μf ff ∧ (∀ v : T.S, ff v = conv (μf v) (conv (μf v) (T.idem μf v) (h v)) (T.idem μf v)) ∧
      ff U.u = U.frame.cosetFn t ∧ ∀ v ∉ T.S, v ≠ U.u → ff v = rest v := by
  let ff : ∀ v, GLoc σ J v → ℂ := fun v =>
    if hv : v ∈ T.S then conv (μf v) (conv (μf v) (T.idem μf ⟨v, hv⟩) (h ⟨v, hv⟩)) (T.idem μf ⟨v, hv⟩)
    else Function.update rest U.u (U.frame.cosetFn t) v
  have h1 : ∀ v : T.S, ff v = conv (μf v) (conv (μf v) (T.idem μf v) (h v)) (T.idem μf v) := fun v => dif_pos v.2
  have h2 : ff U.u = U.frame.cosetFn t := (dif_neg hu).trans (Function.update_self ..)
  have h3 : ∀ v ∉ T.S, v ≠ U.u → ff v = rest v := fun v hv hv' => (dif_neg hv).trans (Function.update_of_ne hv' ..)
  refine ⟨ff, ⟨hu, fun v => ⟨_, hh v, h1 v⟩, ⟨t, ht, h2⟩, fun v hv hv' => h3 v hv hv' ▸ hr.1 v, ?_⟩, h1, h2, h3⟩
  filter_upwards [hr.2, T.S.eventually_cofinite_notMem, eventually_cofinite_ne U.u] with v e hv hv'
  rw [h3 v hv hv', e]

end ArchFamily

def transfer {n' : ℕ} {J' : Matrix (Fin n') (Fin n') E} (j : ∀ v, GLoc σ J v ≃ₜ* GLoc σ J' v)
    (ff : ∀ v, GLoc σ J v → ℂ) : ∀ v, GLoc σ J' v → ℂ := fun v => ff v ∘ (j v).symm

omit [Submodule.IsLattice E L] in

theorem IsFinFamily.transfer {n' : ℕ} {J' : Matrix (Fin n') (Fin n') E} {L' : Submodule (𝓞 E) (Fin n' → E)}
    (h : IsFinFamily σ J L ff) (j : ∀ v, GLoc σ J v ≃ₜ* GLoc σ J' v)
    (hj : ∀ᶠ v in cofinite, ∀ g, j v g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v) :
    IsFinFamily σ J' L' (transfer j ff) := by
  refine ⟨fun v => comp_mem_SB (h.1 v) (j v).symm.toHomeomorph, (h.2.and hj).mono fun v hv => funext fun g => ?_⟩
  obtain ⟨g, rfl⟩ := (j v).surjective g
  by_cases hg : g ∈ stabLoc σ J L v <;> simp [Orb.transfer, hv.1, unitLoc, indicator, hv.2 g, hg]

omit [Submodule.IsLattice E L] in

theorem exists_split_place_notMem (h : IsCMExt F E σ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ v ∉ S, Nonempty (E →ₐ[F] Fv F v) := by
  obtain ⟨a₀, ha₀, ha₁⟩ := exists_integer_conj_eq_neg h
  choose m hm hm0 using fun v : HeightOneSpectrum (𝓞 F) => Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  set a := algebraMap (𝓞 F) (𝓞 E) (∏ v ∈ S, m v) * a₀ with ha_def
  have ha0 : a ≠ 0 := mul_ne_zero ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2
    (Finset.prod_ne_zero_iff.2 fun v _ => hm0 v)) ha₀
  obtain ⟨s, hs⟩ : ∃ s : 𝓞 E →+* 𝓞 E, ∀ x, (s x : E) = σ x := ⟨RingOfIntegers.mapRingHom (σ : E →+* E), fun _ => rfl⟩
  have hc : ∀ c, s (algebraMap (𝓞 F) (𝓞 E) c) = algebraMap (𝓞 F) (𝓞 E) c := fun c =>
    RingOfIntegers.ext ((hs _).trans (σ.commutes (c : F)))
  have hsa : s a = -a := by
    rw [ha_def, map_mul, hc, show s a₀ = -a₀ from RingOfIntegers.ext ((hs a₀).trans ha₁), mul_neg]
  have ha : σ a = -a := (hs a).symm.trans (congrArg Subtype.val hsa)
  have hlt : ∀ w : InfinitePlace E, 1 < w ((1 + 2 * a : 𝓞 E) : E) :=
    one_lt_infinitePlace h (RingOfIntegers.coe_ne_zero_iff.2 ha0) ha
  obtain ⟨P, hP, hle⟩ := exists_max_ideal_of_mem_nonunits (not_isUnit_of_one_lt hlt)
  have h0 : (1 + 2 * a : 𝓞 E) ≠ 0 := fun e => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have := hlt w
    rw [e] at this
    norm_num at this
  have hs1 : s (1 - 2 * a) = 1 + 2 * a := by rw [map_sub, map_one, map_mul, map_ofNat, hsa]; ring
  have hm' : 1 - 2 * a ∈ P.comap s := by rwa [Ideal.mem_comap, hs1]
  have := hP.isPrime
  have hb : P ≠ ⊥ := fun e => h0 (by rwa [e, Ideal.mem_bot] at hle)
  have hb' : P.comap s ≠ ⊥ := fun e => h0 (by rw [e, Ideal.mem_bot] at hm'; rw [← hs1, hm', map_zero])
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq h (w := ⟨P, hP.isPrime, hb⟩) (w' := ⟨P.comap s, inferInstance, hb'⟩)
    (fun e => hP.ne_top ((Ideal.eq_top_iff_one _).2 (by
      have e' : P = P.comap s := congrArg HeightOneSpectrum.asIdeal e
      rw [← e'] at hm'
      convert sub_mem hle (P.mul_mem_right a (add_mem hle hm')) using 1
      ring))) rfl
    (HeightOneSpectrum.ext (Ideal.ext fun c => by
      change s (algebraMap (𝓞 F) (𝓞 E) c) ∈ P ↔ algebraMap (𝓞 F) (𝓞 E) c ∈ P
      rw [hc]))
  refine ⟨_, fun hv => hP.ne_top ((Ideal.eq_top_iff_one _).2 ?_), ⟨τ⟩⟩
  have h1 : algebraMap (𝓞 F) (𝓞 E) (∏ v ∈ S, m v) ∈ P :=
    Ideal.mem_of_dvd _ (map_dvd _ (Finset.dvd_prod_of_mem m hv)) (hm (HeightOneSpectrum.under (𝓞 F) ⟨P, hP.isPrime, hb⟩))
  convert sub_mem hle (P.mul_mem_left 2 (P.mul_mem_right a₀ h1)) using 1
  ring

theorem exists_auxiliaryPlace_not_mem_finset (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : ∀ v, IsSelfDualAt σ J L v)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ∃ U : UnitaryAuxiliaryPlaceData σ J L, U.u ∉ S := by
  obtain ⟨u, hu, ⟨τ⟩⟩ := exists_split_place_notMem h S
  obtain ⟨β, hβ⟩ := exists_isSplitBasis τ L h
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif u
  exact ⟨⟨u, ⟨τ, β, h, hJ, hL u, hβ⟩, ϖ, hϖ⟩, hu⟩

theorem exists_testData (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : ∀ v, IsSelfDualAt σ J L v)
    (μf : ∀ v, Measure (GLoc σ J v)) :
    ∃ (T : TypeData σ J L) (U : UnitaryAuxiliaryPlaceData σ J L) (ff : ∀ v, GLoc σ J v → ℂ), T.S.Nonempty ∧ IsTestFin T U μf ff := by
  obtain ⟨U₀, -⟩ := exists_auxiliaryPlace_not_mem_finset h hJ hL ∅
  obtain ⟨U, hU⟩ := exists_auxiliaryPlace_not_mem_finset h hJ hL {U₀.u}
  let T : TypeData σ J L :=
    { S := {U₀.u}
      frame := fun v => (Finset.mem_singleton.1 v.2).symm ▸ U₀.frame
      W := fun _ => ℂ
      τ := fun _ => GlobalTheory.SmGL.ofChar 1
      irred := fun _ => GlobalTheory.SmGL.isIrreducible_ofChar 1 }
  obtain ⟨t, ht⟩ := strictTorus_nonempty n U.ϖ
  obtain ⟨ff, hff, -⟩ := exists_isTestFin (T := T) hU μf (fun v => unitLoc σ J L v) (fun v => unitLoc_mem v.1) ht isFinFamily_unit
  exact ⟨T, U, ff, Finset.singleton_nonempty _, hff⟩

theorem exists_isTestFn_ne_zero (h : IsCMExt F E σ) (μa : ∀ w, Measure (GArch σ (1 : Matrix (Fin n) (Fin n) E) w))
    (μf : ∀ v, Measure (GLoc σ (1 : Matrix (Fin n) (Fin n) E) v)) [∀ w, (μa w).IsHaarMeasure]
    [∀ v, (μf v).IsHaarMeasure] (Ψ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ (T : TypeData σ 1 (stdLattice E n)) (U : UnitaryAuxiliaryPlaceData σ 1 (stdLattice E n)) (f : GAd σ 1 → ℂ), T.S.Nonempty ∧
      IsTestFn Ψ (fun _ => charRep 1) T U μa μf f ∧ f ≠ 0 := by
  have := isLattice_stdLattice (E := E) (n := n)
  have hJ := isHermND_one σ n
  have hL := isSelfDualAt_stdLattice_one (n := n) σ
  obtain ⟨U₀, -⟩ := exists_auxiliaryPlace_not_mem_finset h hJ hL ∅
  obtain ⟨U, hU⟩ := exists_auxiliaryPlace_not_mem_finset h hJ hL {U₀.u}
  let T : TypeData σ 1 (stdLattice E n) :=
    { S := {U₀.u}
      frame := fun v => (Finset.mem_singleton.1 v.2).symm ▸ U₀.frame
      W := fun _ => ℂ
      τ := fun _ => GlobalTheory.SmGL.ofChar 1
      irred := fun _ => GlobalTheory.SmGL.isIrreducible_ofChar 1 }
  obtain ⟨t, ht⟩ := strictTorus_nonempty n U.ϖ
  obtain ⟨ff, hff, h1, h2, h3⟩ := exists_isTestFin (T := T) hU μf (fun v => unitLoc σ 1 (stdLattice E n) v)
    (fun v => unitLoc_mem v.1) ht isFinFamily_unit
  have hc : ∀ w, CompactSpace (GArch σ (1 : Matrix (Fin n) (Fin n) E) w) := fun w => ⟨by
    rw [(isEmbedding_matHom _ σ _).isCompact_iff]
    convert Frames.isCompact_UJ_one (n := n) h w using 1
    have e : JR (F := F) w.Completion (1 : Matrix (Fin n) (Fin n) E) = 1 := by simp [JR]
    ext x
    exact ⟨fun ⟨g, _, hg⟩ => hg ▸ e ▸ g.2, fun hx => ⟨(⟨x, (e.symm ▸ hx :)⟩ : HR _ σ 1), trivial, rfl⟩⟩⟩
  refine ⟨T, U, _, Finset.singleton_nonempty _, ⟨_, ff, fun w => isPseudoCoeff_char (χ := 1)
    (continuous_archMat σ _ _) ⟨(isClosed_tsupport _).isCompact, fun _ => 1, contDiff_const, fun _ => by simp⟩,
    hff, rfl⟩, fun h0 => ?_⟩
  have hvol : ∀ v, ((μf v).real (stabLoc σ 1 (stdLattice E n) v) : ℂ) ≠ 0 := fun v => by
    exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨((isOpen_stabLoc σ 1 _ v).measure_pos _ ⟨1, one_mem _⟩).ne',
      (isCompact_stabLoc σ 1 _ v).measure_ne_top⟩
  have hconv : ∀ v (a b : ℂ), conv (μf v) (a • unitLoc σ 1 (stdLattice E n) v) (b • unitLoc σ 1 (stdLattice E n) v) =
      (a * b * (μf v).real (stabLoc σ 1 (stdLattice E n) v)) • unitLoc σ 1 (stdLattice E n) v := fun v a b => by
    funext y
    have : ∀ x, (a • unitLoc σ 1 (stdLattice E n) v) x * (b • unitLoc σ 1 (stdLattice E n) v) (x⁻¹ * y) =
        (stabLoc σ 1 (stdLattice E n) v : Set _).indicator (fun _ => a * b * unitLoc σ 1 (stdLattice E n) v y) x :=
      fun x => by
        by_cases hx : x ∈ stabLoc σ 1 (stdLattice E n) v
        · by_cases hy : y ∈ stabLoc σ 1 (stdLattice E n) v <;>
            simp [unitLoc, hx, hy, Subgroup.mul_mem_cancel_left _ (inv_mem hx)]
        · simp [unitLoc, hx]
    rw [conv, integral_congr_ae (.of_forall this), integral_indicator_const _ (isOpen_stabLoc σ 1 _ v).measurableSet]
    simp only [Complex.real_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hid : ∀ v : T.S, T.idem μf v =
      ((μf v).real (stabLoc σ 1 (stdLattice E n) v) : ℂ)⁻¹ • unitLoc σ 1 (stdLattice E n) v := fun v => by
    funext g
    by_cases hg : g ∈ stabLoc σ 1 (stdLattice E n) v
    · refine (typeIdem_coe _ _ _ ⟨g, hg⟩).trans ?_
      have : ∀ q, (T.τ v).character q = 1 := fun q => by
        rw [Representation.character, show T.τ v q = LinearMap.id from LinearMap.ext fun x => one_mul x]
        simp [T]
      simp [this, unitLoc, hg, T]
    · exact (typeIdem_of_notMem _ _ _ hg).trans (by simp [unitLoc, hg])
  have h4 := congrFun h0 (emb σ 1 U.u (U.frame.diag t))
  rw [tensor_eq_infFin] at h4
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => div_ne_zero (by simp) ?_)
    ((hff.isFinFamily.tensorFin_ne_zero_iff _).2 fun v => ?_) h4
  · exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨(isOpen_univ.measure_pos _ univ_nonempty).ne', measure_ne_top _ _⟩
  · rw [projFinLoc_projFin]
    by_cases hu : v = U.u
    · subst hu
      rw [proj_emb_self, h2, SplitAt.cosetFn_diag]
      exact one_ne_zero
    · rw [proj_emb_ne σ 1 hu]
      by_cases hv : v ∈ T.S
      · rw [h1 ⟨v, hv⟩, hid, ← one_smul ℂ (unitLoc σ 1 (stdLattice E n) v), smul_smul, hconv, hconv]
        simp [unitLoc, hvol]
      · simp [h3 v hv hu, unitLoc]

section Cent

def centMap {H H' : Type} [Group H] [Group H'] (φ : H →* H') (γ : H) : cent γ →* cent (φ γ) :=
  (φ.comp (cent γ).subtype).codRestrict _ fun t => mem_cent.2 (by
    change φ t * φ γ = φ γ * φ t
    rw [← map_mul, ← map_mul, mem_cent.1 t.2])

variable (L) in

def IsCentProd (γ : GAd σ J) (dta : ∀ w, Measure (cent (projArch σ J w γ))) (dtf : ∀ v, Measure (cent (proj σ J v γ)))
    (dt : Measure (cent γ)) : Prop :=
  GlobalTheory.RestrMeas.IsHaarProd (fun w => centMap (projArch σ J w) γ) (fun v => centMap (proj σ J v) γ)
    (fun v => (stabLoc σ J L v).subgroupOf (cent (proj σ J v γ))) dta dtf dt

variable (L) in

theorem restrGroup_cent (γ : GAd σ J) :
    GlobalTheory.RestrMeas.IsRestrGroup (fun w => centMap (projArch σ J w) γ) (fun v => centMap (proj σ J v) γ)
      fun v => (stabLoc σ J L v).subgroupOf (cent (proj σ J v γ)) := by
  have h := restrGroup_GAd σ J L
  refine ⟨fun w => ((h.continuous_pa w).comp continuous_subtype_val).subtype_mk _,
    fun v => ((h.continuous_pf v).comp continuous_subtype_val).subtype_mk _,
    fun v => (h.isOpen_K v).preimage continuous_subtype_val,
    fun v => (isClosed_cent _).isClosedEmbedding_subtypeVal.isCompact_preimage (h.isCompact_K v),
    fun x y ha hf => Subtype.ext (h.ext _ _ (fun w => congrArg Subtype.val (ha w)) fun v => congrArg Subtype.val (hf v)),
    fun x => h.eventually_mem x, fun a y hy => ?_, h.isOpen_level.preimage continuous_subtype_val, fun C hC => ?_⟩
  · obtain ⟨x, h1, h2⟩ := h.exists_eq (fun w => a w) (fun v => y v) hy
    exact ⟨⟨x, mem_cent.2 (h.ext _ _ (fun w => by simpa only [map_mul, h1] using mem_cent.1 (a w).2)
      fun v => by simpa only [map_mul, h2] using mem_cent.1 (y v).2)⟩, fun w => Subtype.ext (h1 w),
      fun v => Subtype.ext (h2 v)⟩
  · refine (congrArg IsCompact (Set.ext fun x => ?_)).mpr
      ((isClosed_cent γ).isClosedEmbedding_subtypeVal.isCompact_preimage
        (h.isCompact_level (fun w => Subtype.val '' C w) fun w => (hC w).image continuous_subtype_val))
    exact and_congr_left fun _ => forall_congr' fun w => (Subtype.val_injective.mem_set_image).symm

theorem existsUnique_isCentProd (γ : GAd σ J) (dta : ∀ w, Measure (cent (projArch σ J w γ)))
    (dtf : ∀ v, Measure (cent (proj σ J v γ))) [∀ w, (dta w).IsHaarMeasure] [∀ v, (dtf v).IsHaarMeasure]
    (h : ∀ᶠ v in cofinite, dtf v ((stabLoc σ J L v).subgroupOf (cent (proj σ J v γ))) = 1) :
    ∃! dt, IsCentProd L γ dta dtf dt := by
  have : LocallyCompactSpace (cent γ) := (isClosed_cent _).locallyCompactSpace
  have : ∀ w, LocallyCompactSpace (cent (projArch σ J w γ)) := fun _ => (isClosed_cent _).locallyCompactSpace
  have : ∀ v, LocallyCompactSpace (cent (proj σ J v γ)) := fun _ => (isClosed_cent _).locallyCompactSpace
  exact (restrGroup_cent L γ).existsUnique_isHaarProd dta dtf h

end Cent

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S

def ujMat {m : ℕ} (ε : Fin m → Bool) : Formalism.REAL.UJ ε →* Matrix (Fin m) (Fin m) ℂ :=
  (Units.coeHom _).comp (Formalism.REAL.UJ ε).subtype

def repVia {H X : Type} [Group H] [NormedAddCommGroup X] [InnerProductSpace ℂ X] {m : ℕ}
    {G : Set (Matrix (Fin m) (Fin m) ℂ)} {ρ : Matrix (Fin m) (Fin m) ℂ → (X →L[ℂ] X)} (h : IsURepOn G ρ)
    (ι : H →* Matrix (Fin m) (Fin m) ℂ) (hι : ∀ g, ι g ∈ G) : H →* (X →L[ℂ] X) where
  toFun g := ρ (ι g)
  map_one' := by rw [map_one, h.1.1]
  map_mul' a b := by rw [map_mul, h.1.2 _ (hι a) _ (hι b)]; rfl

theorem isUnitaryRep_repVia {H X : Type} [Group H] [TopologicalSpace H] [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)}
    {ρ : Matrix (Fin m) (Fin m) ℂ → (X →L[ℂ] X)} (h : IsURepOn G ρ) {ι : H →* Matrix (Fin m) (Fin m) ℂ}
    (hι : ∀ g, ι g ∈ G) (hc : Continuous ι) : IsUnitaryRep (repVia h ι hι) :=
  ⟨fun g => h.2.1 _ (hι g), fun v => (h.2.2 v).comp_continuous hc hι⟩

theorem isTopIrreducible_repVia {H X : Type} [Group H] [NormedAddCommGroup X] [InnerProductSpace ℂ X] [Nontrivial X]
    {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {ρ : Matrix (Fin m) (Fin m) ℂ → (X →L[ℂ] X)} (h : IsURepOn G ρ)
    {ι : H →* Matrix (Fin m) (Fin m) ℂ} (hι : ∀ g, ι g ∈ G) (hs : ∀ x ∈ G, ∃ g, ι g = x) (hi : IsIrredOn G ρ) :
    IsTopIrreducible (repVia h ι hι) :=
  ⟨inferInstance, fun W hW => hi W hW.1 fun x hx => by obtain ⟨g, rfl⟩ := hs x hx; exact hW.2 g⟩

def ujRep {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {m : ℕ} {ε : Fin m → Bool}
    {ρ : Matrix (Fin m) (Fin m) ℂ → (X →L[ℂ] X)} (h : IsURepOn (UJset ε) ρ) : Formalism.REAL.UJ ε →* (X →L[ℂ] X) :=
  repVia h (ujMat ε) fun g => g.2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (V : HSp D)

theorem isHermND_gram : IsHermND D.sp.cm.sig V.gram :=
  ⟨fun i j => V.herm.eq (V.frame j) (V.frame i), (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero⟩

instance isLattice_frameLat : Submodule.IsLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V

abbrev CcGA : Submodule ℂ (GA D V → ℂ) := CcAd D.sp.cm.sig V.gram

abbrev TypeDataG : Type 1 := TypeData D.sp.cm.sig V.gram (frameLat V)

abbrev AuxiliaryPlaceHermitianSpace : Type := UnitaryAuxiliaryPlaceData D.sp.cm.sig V.gram (frameLat V)

abbrev matAt (ρ : D.what₂.Tau) : GArch D.sp.cm.sig V.gram (placeOf D ρ) →* Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  archMat D.sp.cm.sig V.gram (embOverOf D ρ)

theorem exists_splitAt {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    ∃ s : SplitAt D.sp.cm.sig V.gram (frameLat V) v, s.emb = τ := by
  obtain ⟨β, hβ⟩ := exists_isSplitBasis τ (frameLat V) (isCMExt_host D)
  exact ⟨⟨τ, β, isCMExt_host D, isHermND_gram V, SelfDual.isSelfDualAt_frameLat D V v, hβ⟩, rfl⟩

theorem exists_testDataG (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) :
    ∃ (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
      T.S.Nonempty ∧ IsTestFin T U μf ff :=
  exists_testData (isCMExt_host D) (isHermND_gram V) (SelfDual.isSelfDualAt_frameLat D V) μf

variable {V} {S : D.what₂.Tau → SPar} (M : DSModel V S)

def frameMat (ρ : D.what₂.Tau) : GArch D.sp.cm.sig V.gram (placeOf D ρ) →* Matrix (Fin V.rank) (Fin V.rank) ℂ where
  toFun g := M.fr ρ * matAt V ρ g * (M.fr ρ)⁻¹
  map_one' := by
    rw [map_one, mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ))]
  map_mul' a b := by
    simp only [map_mul, mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ))]

theorem conj_mem_UJset_iff (ρ : D.what₂.Tau) (x : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    M.fr ρ * x * (M.fr ρ)⁻¹ ∈ UJset (M.ε ρ) ↔ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
  obtain ⟨a, ha⟩ := M.fr_unit ρ
  have hb : IsUnit (a⁻¹ : (Matrix _ _ ℂ)ˣ).1ᴴ := (a⁻¹).isUnit.star
  have h1 : (a⁻¹ : (Matrix _ _ ℂ)ˣ).1ᴴ * a.1ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  change _ᴴ * _ * _ = _ ↔ _ᴴ * _ * _ = _
  rw [← M.fr_gram ρ, ← ha, ← Matrix.coe_units_inv, ← hb.mul_right_inj (b := xᴴ * _ * x),
    ← (a⁻¹).isUnit.mul_left_inj (b := _ * (xᴴ * _ * x))]
  refine Eq.congr (by simp only [Matrix.conjTranspose_mul, mul_assoc]) ?_
  rw [← mul_assoc, ← mul_assoc, h1, one_mul, mul_assoc, Units.mul_inv, mul_one]

theorem frameMat_mem (ρ : D.what₂.Tau) (g : GArch D.sp.cm.sig V.gram (placeOf D ρ)) :
    frameMat M ρ g ∈ UJset (M.ε ρ) := (conj_mem_UJset_iff M ρ _).2 (archEquiv_mem_UH V _ rfl g)

def dsRep (ρ : D.what₂.Tau) : GArch D.sp.cm.sig V.gram (placeOf D ρ) →* (M.H ρ →L[ℂ] M.H ρ) :=
  repVia (M.ds ρ).2.2.1 (frameMat M ρ) (frameMat_mem M ρ)

theorem dsRep_apply (ρ : D.what₂.Tau) (g : GArch D.sp.cm.sig V.gram (placeOf D ρ)) :
    dsRep M ρ g = M.rep ρ (matAt V ρ g) := rfl

theorem isUnitaryRep_dsRep (ρ : D.what₂.Tau) : IsUnitaryRep (dsRep M ρ) :=
  isUnitaryRep_repVia _ _ ((continuous_const.mul (continuous_archMat _ _ _)).mul continuous_const)

theorem isTopIrreducible_dsRep (ρ : D.what₂.Tau) : IsTopIrreducible (dsRep M ρ) := by
  have := (M.ds ρ).2.1
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
  refine isTopIrreducible_repVia _ _ (fun x hx => ?_) (M.ds ρ).2.2.2.1
  have e : M.fr ρ * ((M.fr ρ)⁻¹ * x * M.fr ρ) * (M.fr ρ)⁻¹ = x := by
    rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hd, mul_one]
  obtain ⟨g, hg⟩ := exists_archEquiv_eq V (embOverOf D ρ) rfl ((conj_mem_UJset_iff M ρ _).1 (e.symm ▸ hx))
  exact ⟨g, (congrArg (M.fr ρ * · * (M.fr ρ)⁻¹) hg).trans e⟩

def IsTestArchG (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) : Prop :=
  ∀ ρ, haveI := (M.ds ρ).1
    IsPseudoCoeff (matAt V ρ) (μa (placeOf D ρ)) (dsRep M ρ) (fa (placeOf D ρ))

def IsTestFnG (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (f : GA D V → ℂ) : Prop :=
  ∃ fa ff, IsTestArchG M μa fa ∧ IsTestFin T U μf ff ∧ f = tensor D.sp.cm.sig V.gram fa ff

variable {M} {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}

theorem IsTestArchG.mem {fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ} (h : IsTestArchG M μa fa)
    (w : InfinitePlace D.host.F) : fa w ∈ CcArch D.sp.cm.sig V.gram w := by
  obtain ⟨ρ, rfl⟩ := (placeOf_bijective D).2 w
  have := (M.ds ρ).1
  exact ccArch_eq (isCMExt_host D) (embOverOf D ρ) ▸ (h ρ).mem

theorem IsTestFnG.isPureTensor {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {f : GA D V → ℂ} (h : IsTestFnG M T U μa μf f) :
    IsPureTensor D.sp.cm.sig V.gram (frameLat V) f ∧ f ∈ CcGA V := by
  obtain ⟨fa, ff, ha, hf, rfl⟩ := h
  exact ⟨⟨fa, ff, ha.mem, hf.isFinFamily, rfl⟩, tensor_mem_ccAd ha.mem hf.isFinFamily⟩

end Record

omit [Submodule.IsLattice E L] in

example {v : HeightOneSpectrum (𝓞 F)} {ϖ : (Fv F v)ˣ} (h : IsUnif ϖ) :
    ![ϖ, 1] ∈ strictTorus 2 ϖ ∧ ![1, ϖ] ∉ strictTorus 2 ϖ := by
  refine ⟨⟨![1, 0], Fin.strictAnti_iff_succ_lt.2 fun i => by fin_cases i; simp, funext fun i => by fin_cases i <;> simp⟩,
    fun ⟨a, ha, e⟩ => ?_⟩
  have key : ∀ m : ℤ, Valued.v ((ϖ ^ m : (Fv F v)ˣ) : Fv F v) = WithZero.exp (-m) := fun m => by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, h, ← WithZero.exp_zsmul]; simp
  have h0 := key (a 0)
  have h1 := key (a 1)
  rw [← show (1 : (Fv F v)ˣ) = ϖ ^ a 0 from congrFun e 0, Units.val_one, map_one, ← WithZero.exp_zero,
    WithZero.exp_inj] at h0
  rw [← show ϖ = ϖ ^ a 1 from congrFun e 1, h, WithZero.exp_inj] at h1
  have := ha (show (0 : Fin 2) < 1 by decide)
  omega

example (g : GFin σ J) : tensorFin σ J (unitLoc σ J L) g ≠ 0 ↔ g ∈ levelOffFin σ J L ∅ := by
  simp [isFinFamily_unit.tensorFin_ne_zero_iff, unitLoc, mem_levelOffFin]

end GlobalTheory.Orb
