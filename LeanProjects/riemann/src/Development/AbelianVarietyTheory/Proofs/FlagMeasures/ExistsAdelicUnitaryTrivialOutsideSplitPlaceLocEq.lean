import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
open NumberField ReciprocityTheory.Aut IsDedekindDomain TensorProduct

noncomputable section

namespace GlobalTheory.SplitLift
open GlobalTheory.InertUmax

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

theorem sgl_mul (v : HeightOneSpectrum (𝓞 L⁺)) (a b : v.adicCompletion L⁺) :
    sgl L v a * sgl L v b = sgl L v (a * b) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change sgl L v a w * sgl L v b w = sgl L v (a * b) w
  rcases eq_or_ne w v with rfl | hw
  · simp only [sgl_same]
  · simp only [sgl_ne L _ _ hw, mul_zero]

theorem sgl_add (v : HeightOneSpectrum (𝓞 L⁺)) (a b : v.adicCompletion L⁺) :
    sgl L v a + sgl L v b = sgl L v (a + b) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change sgl L v a w + sgl L v b w = sgl L v (a + b) w
  rcases eq_or_ne w v with rfl | hw
  · simp only [sgl_same]
  · simp only [sgl_ne L _ _ hw, add_zero]

theorem alg_mul_sgl (v : HeightOneSpectrum (𝓞 L⁺)) (d : L⁺) (a : v.adicCompletion L⁺) :
    algebraMap L⁺ (AFplus L) d * sgl L v a = sgl L v (algebraMap L⁺ _ d * a) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change algebraMap L⁺ (AFplus L) d w * sgl L v a w = sgl L v (algebraMap L⁺ _ d * a) w
  rcases eq_or_ne w v with rfl | hw
  · simp only [sgl_same]; rfl
  · simp only [sgl_ne L _ _ hw, mul_zero]

theorem proj_tmul (s : SplitPlace L) (x : L) (a : AFplus L) : s.proj (x ⊗ₜ[L⁺] a) = s.i x * a s.v := by
  simp [SplitPlace.proj, Algebra.TensorProduct.lift_tmul]; left; rfl

theorem conjAL_tmul (x : L) (a : AFplus L) :
    conjAL L (x ⊗ₜ[L⁺] a) = IsCMField.complexConj L x ⊗ₜ[L⁺] a := by
  simp [conjAL, Algebra.TensorProduct.map_tmul]

def ιs (s : SplitPlace L) (a : s.v.adicCompletion L⁺) : AL L := (1 : L) ⊗ₜ[L⁺] sgl L s.v a

def tt (δ : L) : AL L := δ ⊗ₜ[L⁺] (1 : AFplus L)

theorem ιs_mul (s : SplitPlace L) (a b : s.v.adicCompletion L⁺) : ιs s a * ιs s b = ιs s (a * b) := by
  simp only [ιs, Algebra.TensorProduct.tmul_mul_tmul, mul_one, sgl_mul]

theorem ιs_add (s : SplitPlace L) (a b : s.v.adicCompletion L⁺) : ιs s a + ιs s b = ιs s (a + b) := by
  simp only [ιs, ← TensorProduct.tmul_add, sgl_add]

theorem ιs_zero (s : SplitPlace L) : ιs s 0 = 0 := by
  have h := ιs_add s 0 0
  rw [add_zero] at h
  simpa using h

theorem tt_tt (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d)
    (a : s.v.adicCompletion L⁺) : tt δ * tt δ * ιs s a = ιs s (s.i δ * s.i δ * a) := by
  simp only [tt, ιs, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hd]
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def, alg_mul_sgl]
  congr 2
  rw [← map_mul, hd, AlgHom.commutes]

theorem proj_ιs (s : SplitPlace L) (a : s.v.adicCompletion L⁺) : s.proj (ιs s a) = a := by
  rw [ιs, proj_tmul, map_one, one_mul, sgl_same]

theorem proj_tt (s : SplitPlace L) (δ : L) : s.proj (tt δ) = s.i δ := by
  rw [tt, proj_tmul]; change s.i δ * 1 = s.i δ; exact mul_one _

theorem compAt_ιs (s : SplitPlace L) (a : s.v.adicCompletion L⁺) {w : HeightOneSpectrum (𝓞 L⁺)}
    (hw : w ≠ s.v) : compAt L w (ιs s a) = 0 := by
  rw [ιs, compAt_tmul, sgl_ne L _ _ hw, TensorProduct.tmul_zero]

theorem conj_ιs (s : SplitPlace L) (a : s.v.adicCompletion L⁺) : conjAL L (ιs s a) = ιs s a := by
  rw [ιs, conjAL_tmul, map_one]

theorem conj_tt (δ : L) (hδ : IsCMField.complexConj L δ = -δ) : conjAL L (tt δ) = -tt δ := by
  rw [tt, conjAL_tmul, hδ, TensorProduct.neg_tmul]

end GlobalTheory.SplitLift

namespace GlobalTheory.SplitLift
open GlobalTheory.InertUmax

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

def Ep (s : SplitPlace L) (δ : L) : AL L := ιs s (1 / 2) + tt δ * ιs s (1 / (2 * s.i δ))

def Em (s : SplitPlace L) (δ : L) : AL L := ιs s (1 / 2) - tt δ * ιs s (1 / (2 * s.i δ))

section Idem

theorem two_ne (s : SplitPlace L) : (2 : s.v.adicCompletion L⁺) ≠ 0 := by
  haveI : CharZero (s.v.adicCompletion L⁺) := algebraRat.charZero _
  exact two_ne_zero

theorem F1 (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0) : ιs s (1 / 2) * ιs s (1 / 2) + tt δ * tt δ * (ιs s (1 / (2 * s.i δ)) * ιs s (1 / (2 * s.i δ)))
    = ιs s (1 / 2) := by
  have h2 := two_ne s
  rw [ιs_mul, ιs_mul, tt_tt s δ d hd, ιs_add]
  congr 1
  field_simp
  ring

theorem F2 (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0) : ιs s (1 / 2) * ιs s (1 / (2 * s.i δ)) + ιs s (1 / 2) * ιs s (1 / (2 * s.i δ))
    = ιs s (1 / (2 * s.i δ)) := by
  have h2 := two_ne s
  rw [ιs_mul, ιs_add]
  congr 1
  field_simp
  ring

theorem F3 (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0) : ιs s (1 / 2) * ιs s (1 / 2) = tt δ * tt δ * (ιs s (1 / (2 * s.i δ)) * ιs s (1 / (2 * s.i δ))) := by
  have h2 := two_ne s
  rw [ιs_mul, ιs_mul, tt_tt s δ d hd]
  congr 1
  field_simp

theorem F4 (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0) : ιs s (1 / 2) + ιs s (1 / 2) = ιs s 1 := by
  have h2 := two_ne s
  rw [ιs_add]
  congr 1
  field_simp
  norm_num

theorem Ep_mul_Ep (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0) : Ep s δ * Ep s δ = Ep s δ := by
  unfold Ep; linear_combination F1 s δ d hd hr + tt δ * F2 s δ d hd hr

theorem Em_mul_Em (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0) : Em s δ * Em s δ = Em s δ := by
  unfold Em; linear_combination F1 s δ d hd hr - tt δ * F2 s δ d hd hr

theorem Ep_mul_Em (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0) : Ep s δ * Em s δ = 0 := by
  unfold Ep Em; linear_combination F3 s δ d hd hr

theorem Ep_add_Em (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0) : Ep s δ + Em s δ = ιs s 1 := by
  unfold Ep Em; linear_combination F4 s δ d hd hr

theorem Ep_mul_P (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0) : Ep s δ * ιs s 1 = Ep s δ := by
  linear_combination (-(Ep s δ)) * Ep_add_Em s δ d hd hr + Ep_mul_Ep s δ d hd hr + Ep_mul_Em s δ d hd hr

theorem Em_mul_P (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0) : Em s δ * ιs s 1 = Em s δ := by
  linear_combination (-(Em s δ)) * Ep_add_Em s δ d hd hr + Em_mul_Em s δ d hd hr + Ep_mul_Em s δ d hd hr

theorem proj_Ep (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0) : s.proj (Ep s δ) = 1 := by
  have h2 := two_ne s
  rw [Ep, map_add, map_mul, proj_ιs, proj_ιs, proj_tt]
  field_simp
  ring

theorem proj_Em (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0) : s.proj (Em s δ) = 0 := by
  have h2 := two_ne s
  rw [Em, map_sub, map_mul, proj_ιs, proj_ιs, proj_tt]
  field_simp
  ring

end Idem

theorem conj_Ep (s : SplitPlace L) (δ : L) (hδ : IsCMField.complexConj L δ = -δ) :
    conjAL L (Ep s δ) = Em s δ := by
  rw [Ep, Em, map_add, map_mul, conj_ιs, conj_ιs, conj_tt δ hδ]; ring

theorem conj_Em (s : SplitPlace L) (δ : L) (hδ : IsCMField.complexConj L δ = -δ) :
    conjAL L (Em s δ) = Ep s δ := by
  rw [Ep, Em, map_sub, map_mul, conj_ιs, conj_ιs, conj_tt δ hδ]; ring

theorem compAt_Ep (s : SplitPlace L) (δ : L) {w : HeightOneSpectrum (𝓞 L⁺)} (hw : w ≠ s.v) :
    compAt L w (Ep s δ) = 0 := by
  rw [Ep, map_add, map_mul, compAt_ιs s _ hw, compAt_ιs s _ hw]; ring

theorem compAt_Em (s : SplitPlace L) (δ : L) {w : HeightOneSpectrum (𝓞 L⁺)} (hw : w ≠ s.v) :
    compAt L w (Em s δ) = 0 := by
  rw [Em, map_sub, map_mul, compAt_ιs s _ hw, compAt_ιs s _ hw]; ring

end GlobalTheory.SplitLift

namespace GlobalTheory.SplitLift
open GlobalTheory.InertUmax

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

def θ (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0) :
    s.v.adicCompletion L⁺ × s.v.adicCompletion L⁺ × AL L →+* AL L where
  toFun q := Ep s δ * ιs s q.1 + Em s δ * ιs s q.2.1 + (1 - ιs s 1) * q.2.2
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, mul_one]
    rw [Ep_mul_P s δ d hd hr, Em_mul_P s δ d hd hr, ← Ep_add_Em s δ d hd hr]; ring
  map_mul' q q' := by
    simp only [Prod.fst_mul, Prod.snd_mul, ← ιs_mul]
    have hP : ιs s 1 * ιs s 1 = ιs s 1 := by rw [ιs_mul, mul_one]
    linear_combination -(ιs s q.1 * ιs s q'.1) * Ep_mul_Ep s δ d hd hr
      - (ιs s q.2.1 * ιs s q'.2.1) * Em_mul_Em s δ d hd hr
      - (ιs s q.1 * ιs s q'.2.1 + ιs s q.2.1 * ιs s q'.1) * Ep_mul_Em s δ d hd hr
      + (ιs s q.1 * q'.2.2 + q.2.2 * ιs s q'.1) * Ep_mul_P s δ d hd hr
      + (ιs s q.2.1 * q'.2.2 + q.2.2 * ιs s q'.2.1) * Em_mul_P s δ d hd hr
      - (q.2.2 * q'.2.2) * hP
  map_zero' := by simp [ιs_zero]
  map_add' q q' := by
    simp only [Prod.fst_add, Prod.snd_add, ← ιs_add]; ring

end GlobalTheory.SplitLift

namespace GlobalTheory.SplitLift
open GlobalTheory.InertUmax

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

theorem θ_apply (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0)
    (q : s.v.adicCompletion L⁺ × s.v.adicCompletion L⁺ × AL L) :
    θ s δ d hd hr q = Ep s δ * ιs s q.1 + Em s δ * ιs s q.2.1 + (1 - ιs s 1) * q.2.2 := rfl

theorem proj_θ (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0)
    (q : s.v.adicCompletion L⁺ × s.v.adicCompletion L⁺ × AL L) : s.proj (θ s δ d hd hr q) = q.1 := by
  rw [θ_apply, map_add, map_add, map_mul, map_mul, map_mul, map_sub, map_one, proj_Ep s δ d hd hr,
    proj_Em s δ d hd hr, proj_ιs, proj_ιs, proj_ιs]
  ring

theorem compAt_θ (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0)
    (q : s.v.adicCompletion L⁺ × s.v.adicCompletion L⁺ × AL L) {w : HeightOneSpectrum (𝓞 L⁺)}
    (hw : w ≠ s.v) : compAt L w (θ s δ d hd hr q) = compAt L w q.2.2 := by
  rw [θ_apply, map_add, map_add, map_mul, map_mul, map_mul, map_sub, map_one, compAt_Ep s δ hw,
    compAt_Em s δ hw]
  simp only [compAt_ιs s _ hw]
  ring

theorem conj_θ (s : SplitPlace L) (δ : L) (d : L⁺) (hd : δ * δ = algebraMap L⁺ L d) (hr : s.i δ ≠ 0)
    (hδ : IsCMField.complexConj L δ = -δ)
    (q : s.v.adicCompletion L⁺ × s.v.adicCompletion L⁺ × AL L) :
    conjAL L (θ s δ d hd hr q) = θ s δ d hd hr (q.2.1, q.1, conjAL L q.2.2) := by
  rw [θ_apply, θ_apply, map_add, map_add, map_mul, map_mul, map_mul, map_sub, map_one,
    conj_Ep s δ hδ, conj_Em s δ hδ, conj_ιs, conj_ιs, conj_ιs]
  ring

theorem matrix_prod_ext {n : ℕ} {R₁ R₂ R₃ : Type*} (A B : Matrix (Fin n) (Fin n) (R₁ × R₂ × R₃))
    (h₁ : A.map Prod.fst = B.map Prod.fst) (h₂ : A.map (fun q => q.2.1) = B.map (fun q => q.2.1))
    (h₃ : A.map (fun q => q.2.2) = B.map (fun q => q.2.2)) : A = B := by
  refine Matrix.ext fun i j => ?_
  exact Prod.ext (congrFun (congrFun h₁ i) j)
    (Prod.ext (congrFun (congrFun h₂ i) j) (congrFun (congrFun h₃ i) j))

theorem exists_trivOutside_loc_eq : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (s : ReciprocityTheory.Aut.SplitPlace L)
    (M : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))),
    ∃ x : Formalism.AUTREP.GAf L n, ReciprocityTheory.Aut.TrivOutside {s.v} x ∧ s.loc n x = M := by
  intro L _ _ _ n s M
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  set δ : L := y - IsCMField.complexConj L y with hδdef
  have hδ : IsCMField.complexConj L δ = -δ := by
    rw [hδdef, map_sub, IsCMField.complexConj_apply_apply]; ring
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hfix : IsCMField.complexConj L (δ * δ) = δ * δ := by rw [map_mul, hδ]; ring
  let d : maximalRealSubfield L := ⟨δ * δ, (IsCMField.complexConj_eq_self_iff L _).1 hfix⟩
  have hd : δ * δ = algebraMap (maximalRealSubfield L) L d := rfl
  have hr : s.i δ ≠ 0 := (map_ne_zero _).2 hδ0
  let Z : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L) ×
      s.v.adicCompletion (maximalRealSubfield L) × AL L) :=
    fun i j => ((M : Matrix _ _ _) i j, ((M⁻¹ : GL _ _) : Matrix _ _ _) j i, (1 : Matrix (Fin n) (Fin n) (AL L)) i j)
  let W : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L) ×
      s.v.adicCompletion (maximalRealSubfield L) × AL L) :=
    fun i j => (((M⁻¹ : GL _ _) : Matrix _ _ _) i j, (M : Matrix _ _ _) j i, (1 : Matrix (Fin n) (Fin n) (AL L)) i j)
  have hZW : Z * W = 1 := by
    apply matrix_prod_ext
    · have e := Matrix.map_mul (L := Z) (M := W)
        (f := RingHom.fst (s.v.adicCompletion (maximalRealSubfield L))
          (s.v.adicCompletion (maximalRealSubfield L) × AL L))
      refine e.trans ?_
      rw [Matrix.map_one _ rfl rfl]
      exact Units.mul_inv M
    · have e := Matrix.map_mul (L := Z) (M := W)
        (f := (RingHom.fst (s.v.adicCompletion (maximalRealSubfield L)) (AL L)).comp
          (RingHom.snd (s.v.adicCompletion (maximalRealSubfield L))
          (s.v.adicCompletion (maximalRealSubfield L) × AL L)))
      refine e.trans ?_
      rw [Matrix.map_one _ rfl rfl]
      have h := congrArg Matrix.transpose (Units.mul_inv M)
      rw [Matrix.transpose_mul, Matrix.transpose_one] at h
      exact h
    · have e := Matrix.map_mul (L := Z) (M := W)
        (f := (RingHom.snd (s.v.adicCompletion (maximalRealSubfield L)) (AL L)).comp
          (RingHom.snd (s.v.adicCompletion (maximalRealSubfield L))
          (s.v.adicCompletion (maximalRealSubfield L) × AL L)))
      refine e.trans ?_
      rw [Matrix.map_one _ rfl rfl]
      exact Matrix.mul_one _
  let X : Matrix (Fin n) (Fin n) (AL L) := Z.map (θ s δ d hd hr)
  have hconj : conjT (conjAL L) X = W.map (θ s δ d hd hr) := by
    refine Matrix.ext fun i j => ?_
    simp only [conjT, X, Matrix.transpose_apply, Matrix.map_apply]
    rw [conj_θ s δ d hd hr hδ]
    congr 1
    refine Prod.ext rfl (Prod.ext rfl ?_)
    simp only [Z, W, Matrix.one_apply, eq_comm]
    split_ifs <;> simp
  have hX : X * conjT (conjAL L) X = 1 := by
    rw [hconj]
    show Z.map (θ s δ d hd hr) * W.map (θ s δ d hd hr) = 1
    rw [← Matrix.map_mul, hZW, Matrix.map_one _ (map_zero _) (map_one _)]
  let g : GL (Fin n) (AL L) := ⟨X, conjT (conjAL L) X, hX, mul_eq_one_comm.mp hX⟩
  refine ⟨⟨g, hX⟩, ?_, ?_⟩
  · intro w hw
    have hw' : w ≠ s.v := hw
    refine Matrix.ext fun i j => ?_
    change compAt L w (θ s δ d hd hr (Z i j)) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [compAt_θ s δ d hd hr _ hw']
    simp only [Z, Matrix.one_apply]
    split_ifs <;> simp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change s.proj (θ s δ d hd hr (Z i j)) = _
    rw [proj_θ]

end GlobalTheory.SplitLift
