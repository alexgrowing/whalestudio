import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemKFinOfIsLocallyConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsotropicComplGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCompactUnderWittChart
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocallyConstantLinOm
import Development.AbelianVarietyTheory.Definitions.Divisors.EventuallyMemIntMatIff
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStdMulShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlace

noncomputable section

open scoped Matrix NNReal TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.WeilM GlobalTheory.LocIntw

namespace GlobalTheory.LocSW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

theorem exists_isQuad_conjR (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] : ∃ δ, IsQuad (conjR R σ) δ := by
  obtain ⟨a, ha, hξ⟩ := exists_integer_conj_eq_neg h
  have hξ0 : (a : E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ha
  generalize (a : E) = ξ at hξ hξ0
  have hli : LinearIndependent F ![(1 : E), ξ] := by
    rw [LinearIndependent.pair_iff]
    intro s u hsu
    simp only [Algebra.smul_def, mul_one] at hsu
    have h2 := congrArg σ hsu
    simp only [map_add, map_mul, AlgHom.commutes, hξ, map_zero] at h2
    have h3 : algebraMap F E u * ξ = 0 := by linear_combination (hsu - h2) / 2
    obtain rfl : u = 0 := (map_eq_zero (algebraMap F E)).mp ((mul_eq_zero.mp h3).resolve_right hξ0)
    exact ⟨(map_eq_zero (algebraMap F E)).mp (by simpa using hsu), rfl⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [h.2.2.1]; rfl)
  have hb : ∀ i, b i = ![(1 : E), ξ] i := fun i => by simp [b]
  refine ⟨(1 : R) ⊗ₜ[F] ξ, (IsUnit.mk0 ξ hξ0).map (inclR (F := F) R), ?_, Algebra.TensorProduct.basis R b, ?_, ?_⟩
  · rw [conjR_tmul, hξ, TensorProduct.tmul_neg]
  · rw [Algebra.TensorProduct.basis_apply, hb]; rfl
  · rw [Algebra.TensorProduct.basis_apply, hb]; rfl

theorem continuous_psiAt {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (LatVac.psiAt ψ v) := hψ.comp (continuous_const.prodMk (continuous_singleFin v))

theorem psiAt_ne_one (hF : IsTotallyReal F) {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (v : HeightOneSpectrum (𝓞 F)) :
    LatVac.psiAt ψ v ≠ 1 := fun h => by
  obtain ⟨a, -, ha⟩ := StdRescale.exists_isStd_mulShift F hF ψ hψ
  obtain ⟨t, ht⟩ := PsiNontrivAt.exists_psiAt_ne_one _ ha v
  refine ht ?_
  have h1 := DFunLike.congr_fun h (a • t)
  change ψ (LatVac.liftV v (a • t)) = 1 at h1
  change ψ (algebraMap F (AF F) a * LatVac.liftV v t) = 1
  rwa [map_smul, Algebra.smul_def] at h1

def pureT {κ : Type} (φi : ∀ w : InfinitePlace F, (κ → w.Completion) → ℂ)
    (φf : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ) : (κ → AF F) → ℂ :=
  fun x => (∏ w, φi w fun i => evInf F w (x i)) * ∏ᶠ v, φf v fun i => evFin F v (x i)

def unitFun (κ : Type) (v : HeightOneSpectrum (𝓞 F)) : (κ → Fv F v) → ℂ :=
  Set.indicator {y | ∀ i, y i ∈ v.adicCompletionIntegers F} 1

def AlmostUnit {κ : Type} (φf : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ) : Prop :=
  ∀ᶠ v in Filter.cofinite, φf v = unitFun κ v

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem exists_mem_secFin_hyperbolic (hc : IsCMExt F E σ) (hQ : Q = StdUnn.blk4 0 1 (-1) 0) {ψ : AddChar (AF F) ℂ}
    (hψ : IsCharAF F ψ) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ f ∈ secFin σ hQ ψ 1 !![0, 1; 1, 0] v, f 1 ≠ 0 ∧
      f ∈ psUp _ σ Q (absEv F E v) (KUpFin σ Q v) (charAt 1 v) ((((2 : ℕ) : ℂ) - n) / 2) := by
  letI := invTwo F (Fv F v)
  obtain ⟨δ, hq⟩ := exists_isQuad_conjR hc (Fv F v)
  obtain ⟨d, co, om, l, h1, h2, ⟨φ, hφ, h0⟩, h3⟩ :=
    Lin.exists_model hq (continuous_psiAt hψ.1 v) (psiAt_ne_one hc.1 hψ v) hQ
  have e : JR (F := F) (Fv F v) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) = !![0, 1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [JR]
  have h4 := (h3 φ hφ).comp_continuous (continuous_toUG hQ)
  have hf : coefMap (om.comp (toUG _ σ hQ).toMonoidHom) l φ ∈ secFin σ hQ ψ 1 !![0, 1; 1, 0] v := by
    rw [secFin_eq, e]
    exact secOf_le_secLoc h1 h2 ⟨φ, mem_kFin_of_isLocallyConstant (isCompact_KUpFin v) hφ h4, rfl⟩
  exact ⟨_, hf, by simpa using h0, mem_psUp_fin hf (h4.comp l).continuous⟩

example : IsHermND σ !![0, 1; 1, 0] :=
  ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp, by simp⟩

example (hσ : ∀ x, σ (σ x) = x) (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (f : GLoc σ Q v → ℂ) (hf : f ∈ secFin σ hQ ψ 1 !![0, 1; 1, 0] v) (a : GL (Fin n) (Fv F v ⊗[F] E)) :
    f (mLoc _ σ hσ hQ a) = (absEv F E v (Matrix.GeneralLinearGroup.det a) : ℝ) * f 1 := by
  simpa [charAt, npow] using law_of_mem_secFin hf ⟨_, mLoc_mem_upP _ σ hσ hQ a⟩ 1

example (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (ψ : AddChar (AF F) ℂ) (χ : (AF F ⊗[F] E)ˣ →* Circle)
    (JA : Matrix (Fin m) (Fin m) E) (w : InfinitePlace F) (hw : w.IsReal) (f : GArch σ Q w → ℂ)
    (hf : f ∈ secArch σ hQ ψ χ JA w hw) (b : HermR w.Completion σ n) (g : GArch σ Q w) : f (nLoc _ σ hQ b * g) = f g := by
  simpa using law_of_mem_secArch hf ⟨_, nLoc_mem_upP hQ b⟩ g

end GlobalTheory.LocSW

end
