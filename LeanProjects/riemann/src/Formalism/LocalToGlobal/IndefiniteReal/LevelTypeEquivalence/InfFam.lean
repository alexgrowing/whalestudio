import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.BaseSt
import Formalism.LocalToGlobal.UnitaryNorms.RealPl
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InfEmbUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField NumberField.InfinitePlace.Completion
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem infEmb_unique {τ : E →+* ℂ} {θ θ' : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmb τ θ) (h' : IsInfEmb τ θ') : θ = θ' := by
  first | exact UpperTheory.Reformulated.B.Qf27.infEmb_unique .. | (apply UpperTheory.Reformulated.B.Qf27.infEmb_unique <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qf27.infEmb_unique <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf27.infEmb_unique <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qf27.infEmb_unique <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf27.infEmb_unique <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qf27.infEmb_unique F E ‹_› ‹_› ‹_› ‹_› τ θ θ' h h' | exact @UpperTheory.Reformulated.B.Qf27.infEmb_unique F E ‹_› ‹_› ‹_› ‹_› τ θ θ' h | exact @UpperTheory.Reformulated.B.Qf27.infEmb_unique F E ‹_› ‹_› ‹_› ‹_› τ θ θ' | exact @UpperTheory.Reformulated.B.Qf27.infEmb_unique F E ‹_› ‹_› ‹_› ‹_› τ θ | exact @UpperTheory.Reformulated.B.Qf27.infEmb_unique F E ‹_› ‹_› ‹_› ‹_› τ | exact @UpperTheory.Reformulated.B.Qf27.infEmb_unique F E ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qf27.infEmb_unique F E ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qf27.infEmb_unique F E ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qf27.infEmb_unique F E ‹_› | exact @UpperTheory.Reformulated.B.Qf27.infEmb_unique F E | exact @UpperTheory.Reformulated.B.Qf27.infEmb_unique F

end General

variable (D : D7)

def fEmb (τ : D.what₂.Tau) : D.host.F →+* ℂ := (tauE D τ).comp (algebraMap D.host.F D.host.E)

theorem star_algebraMapF (x : D.host.F) : star (algebraMap D.host.F D.host.E x) = algebraMap D.host.F D.host.E x :=
  (D.sp.cm.fixed _).mpr ⟨x, rfl⟩

theorem tauE_star (τ : D.what₂.Tau) (a : D.host.E) : tauE D τ (star a) = starRingEnd ℂ (tauE D τ a) :=
  D.sp.cm.cmUnram.2.1 _ a

theorem fEmb_isReal (τ : D.what₂.Tau) : ComplexEmbedding.IsReal (fEmb D τ) := by
  rw [ComplexEmbedding.isReal_iff]
  refine RingHom.ext fun x => ?_
  rw [ComplexEmbedding.conjugate_coe_eq]
  simp only [fEmb, RingHom.comp_apply]
  rw [← tauE_star, star_algebraMapF]

def plW (τ : D.what₂.Tau) : InfinitePlace D.host.F := InfinitePlace.mk (fEmb D τ)

theorem plW_embedding (τ : D.what₂.Tau) : (plW D τ).embedding = fEmb D τ :=
  InfinitePlace.embedding_mk_eq_of_isReal (fEmb_isReal D τ)

theorem isReal_place (w : InfinitePlace D.host.F) : w.IsReal :=
  @IsTotallyReal.isReal _ _ D.sp.cm.totReal w

theorem plW_eq_tauPl (τ : D.what₂.Tau) : plW D τ = Formalism.L2.Host.tauPl D τ := rfl

theorem plW_symm (w : InfinitePlace D.host.F) : plW D ((Formalism.L2.Host.tauPl D).symm w) = w := by
  rw [plW_eq_tauPl]; exact (Formalism.L2.Host.tauPl D).apply_symm_apply w

theorem symm_plW (τ : D.what₂.Tau) : (Formalism.L2.Host.tauPl D).symm (plW D τ) = τ := by
  rw [plW_eq_tauPl]; exact (Formalism.L2.Host.tauPl D).symm_apply_apply τ

def gW (w : InfinitePlace D.host.F) : Ainf D.host.F →+* ℂ :=
  (extensionEmbedding w).comp (Pi.evalRingHom (fun v : InfinitePlace D.host.F => v.Completion) w)

theorem gW_apply (w : InfinitePlace D.host.F) (a : Ainf D.host.F) : gW D w a = extensionEmbedding w (a w) := rfl

theorem continuous_gW (w : InfinitePlace D.host.F) : Continuous (gW D w) :=
  (isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

theorem gW_real (w : InfinitePlace D.host.F) (a : Ainf D.host.F) :
    gW D w a = ((isometryEquivRealOfIsReal (isReal_place D w) (a w) : ℝ) : ℂ) := by
  rw [gW_apply, ← extensionEmbeddingOfIsReal_apply (isReal_place D w)]
  rfl

theorem gW_symm (w : InfinitePlace D.host.F) (t : ℝ) :
    extensionEmbedding w ((isometryEquivRealOfIsReal (isReal_place D w)).symm t) = (t : ℂ) := by
  rw [← extensionEmbeddingOfIsReal_apply (isReal_place D w)]
  congr 1
  exact (isometryEquivRealOfIsReal (isReal_place D w)).apply_symm_apply t

theorem gW_algebraMap (τ : D.what₂.Tau) (x : D.host.F) :
    gW D (plW D τ) (algebraMap D.host.F (Ainf D.host.F) x) = fEmb D τ x := by
  rw [gW_apply, InfiniteAdeleRing.algebraMap_apply, extensionEmbedding_coe, plW_embedding D τ]
  rfl

def thetaC (τ : D.what₂.Tau) : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ :=
  letI : Algebra D.host.F ℂ := (fEmb D τ).toAlgebra
  (Algebra.TensorProduct.productMap
    ({ gW D (plW D τ) with commutes' := fun x => gW_algebraMap D τ x } : Ainf D.host.F →ₐ[D.host.F] ℂ)
    ({ tauE D τ with commutes' := fun _ => rfl } : D.host.E →ₐ[D.host.F] ℂ)).toRingHom

theorem thetaC_tmul (τ : D.what₂.Tau) (a : Ainf D.host.F) (x : D.host.E) :
    thetaC D τ (a ⊗ₜ[D.host.F] x) = gW D (plW D τ) a * tauE D τ x := by
  let _ : Algebra D.host.F ℂ := (fEmb D τ).toAlgebra
  exact Algebra.TensorProduct.productMap_apply_tmul _ _ a x

theorem isInfFam_thetaC : IsInfFam (D := D) (thetaC D) := by
  intro τ
  refine ⟨fun x => ?_, ?_⟩
  · rw [thetaC_tmul, map_one, one_mul]
  · have : (fun a : Ainf D.host.F => thetaC D τ (a ⊗ₜ[D.host.F] (1 : D.host.E))) = gW D (plW D τ) := by
      funext a; rw [thetaC_tmul, map_one, mul_one]
    rw [this]; exact continuous_gW D _

theorem infFamExists_holds : InfFamExists D := ⟨thetaC D, isInfFam_thetaC D⟩

theorem infFamUnique_holds : InfFamUnique D := fun _ _ h h' => funext fun τ => infEmb_unique (h τ) (h' τ)

theorem eq_thetaC {θ : Datum.InfFam D} (hθ : IsInfFam θ) : θ = thetaC D :=
  infFamUnique_holds D θ _ hθ (isInfFam_thetaC D)

theorem exists_alpha : ∃ α : D.host.E, star α = -α ∧ α ≠ 0 := by
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  have hb : ∃ b : D.host.E, b ∉ (algebraMap D.host.F D.host.E).range := by
    by_contra hc
    push Not at hc
    have : Module.finrank D.host.F D.host.E ≤ 1 := finrank_le_one (1 : D.host.E) fun w => by
      obtain ⟨c, hc⟩ := hc w
      exact ⟨c, by rw [Algebra.smul_def, mul_one, hc]⟩
    omega
  obtain ⟨b, hb⟩ := hb
  refine ⟨b - star b, by simp [star_sub, star_star], fun h0 => hb ?_⟩
  have : star b = b := (sub_eq_zero.mp h0).symm
  exact (D.sp.cm.fixed b).mp this

def alphaE : D.host.E := (exists_alpha D).choose

theorem star_alphaE : star (alphaE D) = -alphaE D := (exists_alpha D).choose_spec.1

theorem alphaE_ne : alphaE D ≠ 0 := (exists_alpha D).choose_spec.2

theorem linInd_alpha : LinearIndependent D.host.F ![(1 : D.host.E), alphaE D] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ht : t = 0 := by
    by_contra ht
    have e1 : alphaE D = algebraMap D.host.F D.host.E (-(s / t)) := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have ht' : algebraMap D.host.F D.host.E t ≠ 0 := by
        rwa [ne_eq, map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective]
      rw [map_neg, map_div₀]
      field_simp
      linear_combination hst
    have e2 := star_alphaE D
    rw [e1, star_algebraMapF] at e2
    have e3 : algebraMap D.host.F D.host.E (-(s / t)) = 0 := by
      have := e2; rw [← e1] at this
      have h2 : (2 : D.host.E) * alphaE D = 0 := by linear_combination this
      rw [← e1]
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
    exact alphaE_ne D (e1.trans e3)
  subst ht
  refine ⟨?_, rfl⟩
  rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
  exact (map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective).mp hst

def basE : Module.Basis (Fin 2) D.host.F D.host.E :=
  basisOfLinearIndependentOfCardEqFinrank (linInd_alpha D) (by rw [Fintype.card_fin]; exact D.sp.cm.deg2.symm)

theorem basE_zero : basE D 0 = 1 := by simp [basE]

theorem basE_one : basE D 1 = alphaE D := by simp [basE]

def basA : Module.Basis (Fin 2) (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
  Algebra.TensorProduct.basis (Ainf D.host.F) (basE D)

theorem decomp (x : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    x = (basA D).repr x 0 ⊗ₜ[D.host.F] (1 : D.host.E) + (basA D).repr x 1 ⊗ₜ[D.host.F] alphaE D := by
  conv_lhs => rw [← (basA D).sum_repr x]
  rw [Fin.sum_univ_two]
  simp only [basA, Algebra.TensorProduct.basis_apply, basE_zero, basE_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

def betaT (τ : D.what₂.Tau) : ℂ := tauE D τ (alphaE D)

theorem conj_betaT (τ : D.what₂.Tau) : starRingEnd ℂ (betaT D τ) = -betaT D τ := by
  rw [betaT, ← tauE_star, star_alphaE, map_neg]

theorem betaT_re (τ : D.what₂.Tau) : (betaT D τ).re = 0 := by
  have h := congrArg Complex.re (conj_betaT D τ)
  rw [Complex.conj_re, Complex.neg_re] at h
  linarith

theorem betaT_im_ne (τ : D.what₂.Tau) : (betaT D τ).im ≠ 0 := by
  intro h
  have : betaT D τ = 0 := Complex.ext (betaT_re D τ) h
  exact alphaE_ne D ((map_eq_zero_iff _ (tauE D τ).injective).mp this)

theorem thetaC_decomp (τ : D.what₂.Tau) (x : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    thetaC D τ x = gW D (plW D τ) ((basA D).repr x 0) + gW D (plW D τ) ((basA D).repr x 1) * betaT D τ := by
  conv_lhs => rw [decomp D x]
  rw [map_add, thetaC_tmul, thetaC_tmul, map_one, mul_one]
  rfl

theorem thetaC_inj (x : Ainf D.host.F ⊗[D.host.F] D.host.E) (h : ∀ τ, thetaC D τ x = 0) : x = 0 := by
  have hc : ∀ i : Fin 2, (basA D).repr x i = 0 := by
    have key : ∀ τ, gW D (plW D τ) ((basA D).repr x 0) = 0 ∧ gW D (plW D τ) ((basA D).repr x 1) = 0 := by
      intro τ
      have h0 := h τ
      rw [thetaC_decomp, gW_real, gW_real] at h0
      set r0 := isometryEquivRealOfIsReal (isReal_place D (plW D τ)) ((basA D).repr x 0 (plW D τ))
      set r1 := isometryEquivRealOfIsReal (isReal_place D (plW D τ)) ((basA D).repr x 1 (plW D τ))
      have hre := congrArg Complex.re h0
      have him := congrArg Complex.im h0
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero,
        betaT_re, mul_zero, Complex.zero_re, Complex.add_im, Complex.mul_im, zero_add, Complex.zero_im, add_zero] at hre him
      have h1 : r1 = 0 := by
        rcases mul_eq_zero.mp him with h | h
        · exact h
        · exact absurd h (betaT_im_ne D τ)
      rw [gW_real, gW_real]
      exact ⟨Complex.ofReal_eq_zero.mpr hre, Complex.ofReal_eq_zero.mpr h1⟩
    have hz : ∀ i : Fin 2, (∀ τ, gW D (plW D τ) ((basA D).repr x i) = 0) → (basA D).repr x i = 0 := by
      intro i hi
      funext w
      obtain ⟨τ, rfl⟩ : ∃ τ, plW D τ = w := ⟨_, plW_symm D w⟩
      apply (extensionEmbedding (plW D τ)).injective
      rw [← gW_apply, hi τ]
      exact (map_zero (extensionEmbedding (plW D τ))).symm
    intro i
    fin_cases i
    · exact hz 0 fun τ => (key τ).1
    · exact hz 1 fun τ => (key τ).2
  have : (basA D).repr x = 0 := Finsupp.ext hc
  simpa using congrArg (basA D).repr.symm this

def preA (y : D.what₂.Tau → ℂ) (k : Fin 2) : Ainf D.host.F := fun w =>
  (isometryEquivRealOfIsReal (isReal_place D w)).symm
    (if k = 0 then (y ((Formalism.L2.Host.tauPl D).symm w)).re
      else (y ((Formalism.L2.Host.tauPl D).symm w)).im / (betaT D ((Formalism.L2.Host.tauPl D).symm w)).im)

def splitInv (y : D.what₂.Tau → ℂ) : Ainf D.host.F ⊗[D.host.F] D.host.E :=
  preA D y 0 ⊗ₜ[D.host.F] (1 : D.host.E) + preA D y 1 ⊗ₜ[D.host.F] alphaE D

theorem archimedean_image_real (y : D.what₂.Tau → ℂ) (τ : D.what₂.Tau) :
    gW D (plW D τ) (preA D y 0) = ((y τ).re : ℂ) := by
  rw [gW_apply]
  dsimp only [preA]
  rw [if_pos rfl, gW_symm, symm_plW]

theorem archimedean_image_imaginary (y : D.what₂.Tau → ℂ) (τ : D.what₂.Tau) :
    gW D (plW D τ) (preA D y 1) = (((y τ).im / (betaT D τ).im : ℝ) : ℂ) := by
  rw [gW_apply]
  dsimp only [preA]
  rw [if_neg (by decide), gW_symm, symm_plW]

theorem thetaC_splitInv (y : D.what₂.Tau → ℂ) (τ : D.what₂.Tau) : thetaC D τ (splitInv D y) = y τ := by
  rw [splitInv, map_add, thetaC_tmul, thetaC_tmul, map_one, mul_one, archimedean_image_real, archimedean_image_imaginary,
    show tauE D τ (alphaE D) = betaT D τ from rfl]
  apply Complex.ext
  · simp [Complex.mul_re, betaT_re]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add, betaT_re, mul_zero, add_zero]
    field_simp [betaT_im_ne D τ]

def splitHom : Ainf D.host.F ⊗[D.host.F] D.host.E →+* (D.what₂.Tau → ℂ) := RingHom.pi fun τ => thetaC D τ

theorem splitHom_bij : Function.Bijective (splitHom D) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => thetaC_inj D x fun τ => congrFun hx τ, fun y =>
    ⟨splitInv D y, funext fun τ => thetaC_splitInv D y τ⟩⟩

def splitEquiv : (Ainf D.host.F ⊗[D.host.F] D.host.E) ≃+* (D.what₂.Tau → ℂ) := RingEquiv.ofBijective _ (splitHom_bij D)

theorem splitEquiv_apply (x : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : D.what₂.Tau) : splitEquiv D x τ = thetaC D τ x := rfl

theorem splitEquiv_symm : ⇑(splitEquiv D).symm = splitInv D := by
  funext y
  apply (splitEquiv D).injective
  rw [RingEquiv.apply_symm_apply]
  funext τ
  rw [splitEquiv_apply, thetaC_splitInv]

instance isModuleTopology_ainfE : IsModuleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩

theorem continuous_repr (k : Fin 2) : Continuous fun x : Ainf D.host.F ⊗[D.host.F] D.host.E => (basA D).repr x k :=
  IsModuleTopology.continuous_of_linearMap ((basA D).coord k)

theorem continuous_preA (k : Fin 2) : Continuous fun y : D.what₂.Tau → ℂ => preA D y k := by
  refine continuous_pi fun w => (isometryEquivRealOfIsReal (isReal_place D w)).symm.continuous.comp ?_
  fin_cases k
  · exact Complex.continuous_re.comp (continuous_apply _)
  · exact (Complex.continuous_im.comp (continuous_apply _)).div_const _

theorem continuous_splitEquiv_symm : Continuous (splitEquiv D).symm := by
  rw [splitEquiv_symm]
  have e : splitInv D = fun y => preA D y 0 • ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) +
      preA D y 1 • ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] alphaE D) := by
    funext y; simp only [splitInv, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e]
  have c1 : Continuous fun _ : D.what₂.Tau → ℂ => ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) := continuous_const
  have c2 : Continuous fun _ : D.what₂.Tau → ℂ => ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] alphaE D) := continuous_const
  have : ContinuousAdd (Ainf D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.toContinuousAdd (Ainf D.host.F) _
  exact ((continuous_preA D 0).smul c1).add ((continuous_preA D 1).smul c2)

end Formalism.IndefR.Eqv

end
