import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GalSplit

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.L1

private theorem pi_factor {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ι → Type*} [∀ i, Field (k i)]
    {K : Type*} [Field K] (φ : (∀ i, k i) →+* K) : ∃ w, ∀ b : ∀ i, k i, b w = 0 → φ b = 0 := by
  have h1 : ∑ i, φ (Pi.single i 1) = 1 := by
    have h : (∑ x, Pi.single x 1 : ∀ i, k i) = 1 := Finset.univ_sum_single (1 : ∀ i, k i)
    rw [← map_sum, h, map_one]
  obtain ⟨w, hw⟩ : ∃ w, φ (Pi.single w 1) ≠ 0 := by
    by_contra! h
    simp [h] at h1
  refine ⟨w, fun b hb => ?_⟩
  have h0 : b * Pi.single w 1 = 0 := by
    ext i
    by_cases h : i = w
    · subst h
      simp [hb]
    · simp [Pi.single_eq_of_ne h]
  have h2 := congrArg φ h0
  rw [map_mul, map_zero] at h2
  exact (mul_eq_zero.1 h2).resolve_right hw

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem comp_eq (v : HeightOneSpectrum (𝓞 F)) (φ : CompletionsOver E v →+* v.adicCompletion F)
    (hφ : ∀ a, φ (incFin E v a) = a)
    (hs : ∀ w : PlacesOver E v, Function.Surjective (completionMap v w.1)) :
    ∃ w : PlacesOver E v, ∀ b, completionMap v w.1 (φ b) = b w := by
  classical
  obtain ⟨w, hw⟩ := pi_factor φ
  refine ⟨w, fun b => ?_⟩
  obtain ⟨a, ha⟩ := hs w (b w)
  have h : φ (b - incFin E v a) = 0 := hw _ (by
    change b w - completionMap v w.1 a = 0
    rw [ha, sub_self])
  rw [map_sub, hφ, sub_eq_zero] at h
  rw [h, ha]

private noncomputable def pt (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v)
    (hs : Function.Surjective (completionMap v w.1)) : E →ₐ[F] v.adicCompletion F where
  toRingHom := (RingEquiv.ofBijective (completionMap v w.1)
    ⟨(completionMap v w.1).injective, hs⟩).symm.toRingHom.comp (algebraMap E (w.1.adicCompletion E))
  commutes' r := by
    change (RingEquiv.ofBijective (completionMap v w.1) _).symm _ = _
    rw [RingEquiv.symm_apply_eq]
    change _ = completionMap v w.1 _
    rw [completionMap_algebraMap, ← IsScalarTower.algebraMap_apply]

private theorem completionMap_pt (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v)
    (hs : Function.Surjective (completionMap v w.1)) (x : E) :
    completionMap v w.1 (pt v w hs x) = algebraMap E (w.1.adicCompletion E) x :=
  (RingEquiv.ofBijective (completionMap v w.1) ⟨(completionMap v w.1).injective, hs⟩).apply_symm_apply _

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.finSplit :
    UpperTheory.ConvolutionTheory.L1.FinSplit := by
  intro F E _ _ _ _ _ _ σ hσ m hm v w₀ hs
  classical
  obtain ⟨e, he, hshift⟩ := UpperTheory.ConvolutionTheory.L1.galSplit F E σ hσ m hm (v.adicCompletion F)
    (CompletionsOver E v) (tensorEquiv' E v) (pt v w₀ (hs w₀))
  have hinc : ∀ r, incFin E v r = tensorEquiv' E v (1 ⊗ₜ r) := fun r => by
    rw [tensorEquiv'_tmul, map_one, one_mul]
    rfl
  have hdiag : ∀ r i, e (incFin E v r) i = r := fun r i => by
    rw [hinc, he, map_one, map_one, one_mul]
  have hsmul : ∀ (a : v.adicCompletion F) (b : CompletionsOver E v), e (a • b) = a • e b := by
    intro a b
    funext i
    rw [Algebra.smul_def, map_mul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    exact congrArg (· * e b i) (hdiag a i)
  let L : CompletionsOver E v ≃ₗ[v.adicCompletion F] (Fin (m + 1) → v.adicCompletion F) :=
    { e.toAddEquiv with map_smul' := hsmul }
  let D : Split (incFin E v) (galFin σ v) m :=
    { e := e
      cont := IsModuleTopology.continuous_of_linearMap L.toLinearMap
      cont_symm := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap
      map_diag := hdiag
      map_shift := hshift }
  have hcomp : ∀ i, ∃ w : PlacesOver E v, ∀ b, completionMap v w.1 (e b i) = b w := fun i =>
    comp_eq v ((Pi.evalRingHom _ i).comp e.toRingHom) (fun a => hdiag a i) hs
  choose w hw using hcomp
  have hne : ∀ i u, e (Pi.single u 1) i ≠ 0 → w i = u := by
    intro i u h
    by_contra hu
    apply h
    apply (completionMap v (w i).1).injective
    rw [hw, map_zero, Pi.single_eq_of_ne hu]
  have hinj : Function.Injective w := by
    intro i j h
    by_contra hij
    have key : ∀ u, u = w j → ∀ b, completionMap v u.1 (e b i) = b u → e b i = e b j := by
      intro u hu b h3
      subst hu
      exact (completionMap v (w j).1).injective (h3.trans (hw j b).symm)
    have h4 := key _ h (e.symm (Pi.single i 1)) (hw i _)
    rw [RingEquiv.apply_symm_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] at h4
    exact one_ne_zero h4
  have hsurj : Function.Surjective w := by
    intro u
    have h1 : e (Pi.single u 1) ≠ 0 := fun h => by
      have h2 := congrFun ((map_eq_zero_iff e e.injective).1 h) u
      rw [Pi.single_eq_same] at h2
      exact one_ne_zero h2
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h1
    exact ⟨i, hne i u hi⟩
  have h0 : ∀ b : CompletionsOver E v, completionMap v w₀.1 (e b 0) = b w₀ := by
    intro b
    obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective b
    induction t with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, map_add, Pi.add_apply, map_add, hx, hy, Pi.add_apply]
    | tmul x a =>
      rw [he, map_mul]
      simp only [Fin.val_zero, pow_zero]
      rw [show ((1 : E ≃ₐ[F] E) x) = x from rfl, completionMap_pt, tensorEquiv'_tmul]
      rfl
  have hw0 : w 0 = w₀ := by
    refine hne 0 w₀ fun h => ?_
    have h1 := h0 (Pi.single w₀ 1)
    rw [h, map_zero, Pi.single_eq_same] at h1
    exact zero_ne_one h1
  exact ⟨D, Equiv.ofBijective w ⟨hinj, hsurj⟩, hw0, fun b i => hw i b⟩
