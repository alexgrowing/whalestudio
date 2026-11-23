import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

namespace GlobalTheory.DiagNonvan

open scoped Classical
open GlobalTheory.DiagForm GlobalTheory.StdCharFromIsStd

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem eq_zero_of_psi_mul {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (b : AF F) (h : ∀ y : AF F, ψ (b * y) = 1) :
    b = 0 := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have h1 : b.1 = 0 := by
    refine e.injective ?_
    rw [map_zero]
    refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun s => ?_
    by_contra hT
    set T := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (e b.1 * s) with hTdef
    have h2 := h (pairA F (e.symm ((1 / (2 * T)) • s)) 0)
    have e1 : b * pairA F (e.symm ((1 / (2 * T)) • s)) 0 = pairA F (b.1 * e.symm ((1 / (2 * T)) • s)) 0 := by
      show ((b.1 * _, b.2 * 0) : Ainf F × Af F) = (_, 0)
      rw [mul_zero]
      rfl
    have e2 : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (e (b.1 * e.symm ((1 / (2 * T)) • s))) = 1 / 2 := by
      rw [map_mul, RingEquiv.apply_symm_apply, mul_smul_comm, map_smul, ← hTdef, smul_eq_mul]
      field_simp
    rw [e1, psi_pairA hψ] at h2
    change Complex.exp (_ * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (e (b.1 * e.symm ((1 / (2 * T)) • s))) : ℝ) : ℂ)) = 1 at h2
    have e3 : -(2 * (Real.pi : ℂ) * Complex.I) * ((1 / 2 : ℝ) : ℂ) = -(Real.pi * Complex.I) := by push_cast; ring
    rw [e2, e3, Complex.exp_neg, Complex.exp_pi_mul_I] at h2
    norm_num at h2
  have h2 : b.2 = 0 := by
    refine af_ext fun v => ?_
    rw [map_zero]
    by_contra hv
    apply GlobalTheory.PsiNontriv.psiV_ne_one ψ hψ v
    ext t
    rw [GlobalTheory.VacAny.psiV_apply, AddChar.one_apply, ← h (pairA F 0 (singleFin v ((evalV F v b.2)⁻¹ * t)))]
    congr 1
    show ((0, singleFin v t) : Ainf F × Af F) = (b.1 * 0, b.2 * singleFin v ((evalV F v b.2)⁻¹ * t))
    rw [mul_zero]
    congr 1
    refine af_ext fun u => ?_
    by_cases hu : u = v
    · subst hu
      rw [map_mul, evalV_singleFin_self, evalV_singleFin_self, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    · rw [map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, mul_zero]
  exact Prod.ext h1 h2

theorem continuous_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_glue : Continuous (glue : Vi F κ × Vf F κ → κ → AdeleRing (𝓞 F) F) :=
  continuous_pi fun i =>
    (continuous_symm.comp ((continuous_apply i).comp ((eI F κ).continuous.comp continuous_fst))).prodMk
      ((continuous_apply i).comp continuous_snd)

theorem glue_add (p q : Vi F κ × Vf F κ) : glue (p + q) = glue p + glue q := by
  funext i
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ (p.1 + q.1) i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i) +
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ q.1 i)
  rw [map_add, Pi.add_apply, map_add]

theorem glue_zero : glue (0 : Vi F κ × Vf F κ) = 0 := by
  have h := glue_add (0 : Vi F κ × Vf F κ) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem eq_zero_of_glue {p : Vi F κ × Vf F κ} (h : glue p = 0) : p = 0 := by
  refine Prod.ext ?_ (funext fun i => congrArg Prod.snd (congrFun h i))
  refine (eI F κ).injective ?_
  rw [Prod.fst_zero, map_zero]
  funext i
  refine (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.injective ?_
  rw [Pi.zero_apply, map_zero]
  exact congrArg Prod.fst (congrFun h i)

theorem continuous_resD {φ : (κ ⊕ κ → AdeleRing (𝓞 F) F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) :
    Continuous (resD F κ φ) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    have hd : Continuous fun v : Vf F κ => (Sum.elim v v : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
      continuous_pi fun i => by cases i <;> exact continuous_apply _
    rw [show resD F κ (pureA F f g) = fun p => compD F κ f p.1 * g (Sum.elim p.2 p.2) from funext (resD_pureA f g)]
    exact ((compD F κ f).continuous.comp continuous_fst).mul ((hg.1.continuous.comp hd).comp continuous_snd)
  | zero => rw [map_zero]; exact continuous_zero
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | smul c x _ hx => rw [map_smul]; exact hx.const_smul c

instance mu_haar : (mu F κ).IsAddHaarMeasure := by unfold mu; infer_instance

theorem dot_left (a c : κ → AF F) : Sum.elim a a ⬝ᵥ Sum.elim c (0 : κ → AF F) = a ⬝ᵥ c := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem exists_lDiag_schr_ne {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {f : (κ ⊕ κ → AF F) → ℂ}
    (hf : f ∈ schA F (κ ⊕ κ)) (hf0 : f ≠ 0) : ∃ w, lDiag F κ (schr ψ w f) ≠ 0 := by
  obtain ⟨p, hp⟩ := Function.ne_iff.1 hf0
  by_contra hcon
  push_neg at hcon
  have hmem := fun w => GlobalTheory.HeisSchA.schr_mem_schA ψ hψ w f hf
  let N : Vi F κ × Vf F κ → ℂ := resD F κ (schr ψ (p, 0) f)
  have hN : ∀ q, N q = f (Sum.elim (glue q) (glue q) + p) := fun q => by
    show ψ (_ ⬝ᵥ 0 + _ * (p ⬝ᵥ 0)) * _ = _
    rw [dotProduct_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
  let χ : (κ → AF F) → Vi F κ × Vf F κ → ℂ := fun c q => ψ (glue q ⬝ᵥ c)
  have key : N = 0 := by
    refine GlobalTheory.CharFourierInj.eq_zero χ (fun c => hψ.1.comp (continuous_glue.dotProduct continuous_const))
      (fun c q q' => ?_) (fun c c' q => ?_) (fun q => ?_) (fun c q => norm_psi hψ _) (fun q hq => ?_) (mu F κ) N
      (continuous_resD (hmem _)) (integrable_resD (hmem _)) fun c => ?_
    · simp only [χ, glue_add, add_dotProduct, AddChar.map_add_eq_mul]
    · simp only [χ, dotProduct_add, AddChar.map_add_eq_mul]
    · simp only [χ, dotProduct_zero, AddChar.map_zero_eq_one]
    · refine eq_zero_of_glue (funext fun i => eq_zero_of_psi_mul hψ _ fun y => ?_)
      have := hq (Pi.single i y)
      simp only [χ] at this
      rwa [dotProduct_single] at this
    · have h1 := hcon (p, Sum.elim c 0)
      rw [lDiag, LinearMap.comp_apply, Lext_apply _ (integrable_resD (hmem _))] at h1
      have e : ∀ q, resD F κ (schr ψ (p, Sum.elim c 0) f) q =
          ψ (⅟(2 : AF F) * (p ⬝ᵥ Sum.elim c 0)) * (χ c q * N q) := fun q => by
        rw [hN]
        show ψ (Sum.elim (glue q) (glue q) ⬝ᵥ Sum.elim c 0 + ⅟(2 : AF F) * (p ⬝ᵥ Sum.elim c 0)) *
          f (Sum.elim (glue q) (glue q) + p) = _
        rw [dot_left, AddChar.map_add_eq_mul]
        simp only [χ]
        ring
      simp only [e] at h1
      rw [integral_const_mul] at h1
      refine (mul_eq_zero.1 h1).resolve_left fun h0 => ?_
      have := norm_psi hψ (⅟(2 : AF F) * (p ⬝ᵥ Sum.elim c 0))
      rw [h0, norm_zero] at this
      exact zero_ne_one this
  have h0 := hN 0
  rw [key, glue_zero, Sum.elim_zero_zero, zero_add] at h0
  exact hp h0.symm

theorem exists_invForm_rho_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)),
    IsStd ψ → IsDblCoord (cA σ) (-1) JA JB d dd →
    ∀ f ∈ schA F (κ ⊕ κ), f ≠ 0 →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (AE F E), ∀ φ ∈ schA F (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ) = l φ) ∧
      ∃ w : Matrix α (β ⊕ β) (AE F E), l (dd.rho ψ w f) ≠ 0 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d dd hψ hdd f hf hf0
  refine ⟨lDiag F κ, lDiag_adm, fun z φ hφ => ?_, ?_⟩
  · have hz : z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.mul_fromCols, Matrix.mul_one]
    rw [hz, Darboux.rho, hdd z z, lDiag_schr ψ _ _ hφ]
  · obtain ⟨w, hw⟩ := exists_lDiag_schr_ne hψ hf hf0
    exact ⟨dd.e.symm w, by rwa [Darboux.rho, LinearEquiv.apply_symm_apply]⟩

end GlobalTheory.DiagNonvan

end
