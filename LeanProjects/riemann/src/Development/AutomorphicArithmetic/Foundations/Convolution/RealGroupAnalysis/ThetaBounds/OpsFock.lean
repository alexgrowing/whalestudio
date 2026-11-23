import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private lemma infiniteProjection_placeEmbed (w : InfinitePlace F) (t : ℝ) : TR.pInf F (Fo.at1 w t) = Pi.single w t := by
  change (TR.infEq F).symm (TR.infEq F (Pi.single w t)) = _
  exact RingEquiv.symm_apply_apply _ _

private lemma placeEmbedReal_zero (w : InfinitePlace F) : Fo.at1 w 0 = 0 := by
  simp [Fo.at1]

private lemma placeEmbedReal_finitePart (w : InfinitePlace F) (t : ℝ) : (Fo.at1 w t).2 = 0 := rfl

private lemma shift_zero (w : InfinitePlace F) (i : Fin 4) (v : V4 F) :
    v + Pi.single i (Fo.at1 w 0) = v := by
  simp [placeEmbedReal_zero]

private lemma finPart_shift (w : InfinitePlace F) (i : Fin 4) (v : V4 F) (t : ℝ) :
    finPartPi (v + Pi.single i (Fo.at1 w t)) = finPartPi v := by
  funext j
  by_cases h : j = i
  · subst h
    simp [finPartPi, placeEmbedReal_finitePart]
  · simp [finPartPi, Pi.single_eq_of_ne h]

private lemma coord_shift (w w' : InfinitePlace F) (i j : Fin 4) (v : V4 F) (t : ℝ) :
    ((TR.pInf F ((v + Pi.single i (Fo.at1 w t) : V4 F) j) w' : ℝ) : ℂ) =
      ((TR.pInf F (v j) w' : ℝ) : ℂ) + (if j = i ∧ w' = w then 1 else 0) * (t : ℂ) := by
  by_cases h : j = i
  · subst h
    by_cases h' : w' = w
    · subst h'
      simp [map_add, infiniteProjection_placeEmbed]
    · simp [map_add, infiniteProjection_placeEmbed, h', Pi.single_eq_of_ne h']
  · simp [h, Pi.single_eq_of_ne h]

private lemma lin_der (a c : ℂ) : HasDerivAt (fun t : ℝ => a + c * (t : ℂ)) c 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul c).const_add a
  simpa using h

private lemma coord_mem (j : Fin 4) (w : InfinitePlace F) :
    (fun v : V4 F => ((TR.pInf F (v j) w : ℝ) : ℂ)) ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F) :=
  Algebra.subset_adjoin ⟨j, w, rfl⟩

private lemma poly_der (w : InfinitePlace F) (i : Fin 4) {p : V4 F → ℂ}
    (hp : p ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F)) :
    ∃ p' ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∀ v,
      HasDerivAt (fun t : ℝ => p (v + Pi.single i (Fo.at1 w t))) (p' v) 0 := by
  unfold UpperTheory.ConvolutionTheory.R2.polyFn at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, w', rfl⟩ := hx
    refine ⟨algebraMap ℂ _ (if j = i ∧ w' = w then 1 else 0), Subalgebra.algebraMap_mem _ _, fun v => ?_⟩
    have e : (fun t : ℝ => ((TR.pInf F ((v + Pi.single i (Fo.at1 w t) : V4 F) j) w' : ℝ) : ℂ)) =
        fun t : ℝ => ((TR.pInf F (v j) w' : ℝ) : ℂ) + (if j = i ∧ w' = w then 1 else 0) * (t : ℂ) :=
      funext fun t => coord_shift w w' i j v t
    rw [e]
    exact lin_der _ _
  | algebraMap r =>
    exact ⟨0, zero_mem _, fun v => hasDerivAt_const _ _⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    exact ⟨x' + y', add_mem hxm hym, fun v => (hx v).add (hy v)⟩
  | mul x y hxa hya hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    refine ⟨x' * y + x * y', add_mem (mul_mem hxm hya) (mul_mem hxa hym), fun v => ?_⟩
    have h := (hx v).mul (hy v)
    simp only [shift_zero] at h
    exact h

private noncomputable def Qf (δ : F) (v : V4 F) : ℂ :=
  ((∑ w, TR.pInf F (v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)) w : ℝ) : ℂ)

private lemma Qf_mem (δ : F) : Qf δ ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F) := by
  have e : Qf δ = ∑ w, ((fun v : V4 F => ((TR.pInf F (v 0) w : ℝ) : ℂ)) ^ 2 +
      (fun v : V4 F => ((TR.pInf F (v 1) w : ℝ) : ℂ)) ^ 2 +
      algebraMap ℂ (V4 F → ℂ) 2 * ((fun v : V4 F => ((TR.pInf F (v 2) w : ℝ) : ℂ)) ^ 2 -
        algebraMap ℂ (V4 F → ℂ) ((TR.pInf F (rt δ) w : ℝ) : ℂ) *
          (fun v : V4 F => ((TR.pInf F (v 3) w : ℝ) : ℂ)) ^ 2)) := by
    funext v
    have h2 : ∀ x, TR.pInf F (2 : A F) x = 2 := fun x => by
      rw [map_ofNat]; rfl
    simp [Qf, Finset.sum_apply, map_add, map_mul, map_sub, map_pow, h2]
  rw [e]
  refine sum_mem fun w _ => ?_
  exact add_mem (add_mem (pow_mem (coord_mem 0 w) 2) (pow_mem (coord_mem 1 w) 2))
    (mul_mem (Subalgebra.algebraMap_mem _ _) (sub_mem (pow_mem (coord_mem 2 w) 2)
      (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem (coord_mem 3 w) 2))))

private lemma gauss_der (δ : F) (w : InfinitePlace F) (i : Fin 4) :
    ∃ q ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∀ v, HasDerivAt
      (fun t : ℝ => UpperTheory.ConvolutionTheory.R2.gauss δ (v + Pi.single i (Fo.at1 w t)))
      (UpperTheory.ConvolutionTheory.R2.gauss δ v * q v) 0 := by
  obtain ⟨q, hq, hd⟩ := poly_der w i (Qf_mem δ)
  refine ⟨algebraMap ℂ _ (-(Real.pi : ℂ)) * q, mul_mem (Subalgebra.algebraMap_mem _ _) hq, fun v => ?_⟩
  have h := ((hd v).const_mul (-(Real.pi : ℂ))).cexp
  simp only [shift_zero] at h
  exact h

private def Gen (δ : F) : Set (V4 F → ℂ) :=
  {φ : V4 F → ℂ | ∃ p ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
    φ = fun v => p v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v)}

private lemma cw_coord_mul_mem_span_gen_of_mem (δ : F) (w : InfinitePlace F) (i : Fin 4) {f : V4 F → ℂ}
    (hf : f ∈ Submodule.span ℂ (Gen δ)) :
    (fun v => Fo.cw w (v i) * f v) ∈ Submodule.span ℂ (Gen δ) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨(fun v : V4 F => ((TR.pInf F (v i) w : ℝ) : ℂ)) * p,
      mul_mem (coord_mem i w) hp, g, hg, ?_⟩
    funext v
    simp [Fo.cw, mul_assoc]
  | zero =>
    have : (fun v : V4 F => Fo.cw w (v i) * (0 : V4 F → ℂ) v) = 0 := by
      funext v; simp
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    have : (fun v : V4 F => Fo.cw w (v i) * (x + y) v) =
        (fun v => Fo.cw w (v i) * x v) + fun v => Fo.cw w (v i) * y v := by
      funext v; simp [mul_add]
    rw [this]; exact add_mem hx hy
  | smul c x _ hx =>
    have : (fun v : V4 F => Fo.cw w (v i) * (c • x) v) = c • fun v => Fo.cw w (v i) * x v := by
      funext v; simp [mul_left_comm]
    rw [this]; exact Submodule.smul_mem _ _ hx

private lemma span_d (δ : F) (w : InfinitePlace F) (i : Fin 4) {f : V4 F → ℂ}
    (hf : f ∈ Submodule.span ℂ (Gen δ)) :
    ∃ f' ∈ Submodule.span ℂ (Gen δ), ∀ v,
      HasDerivAt (fun t : ℝ => f (v + Pi.single i (Fo.at1 w t))) (f' v) 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, g, hg, rfl⟩ := hx
    obtain ⟨p', hp', hdp⟩ := poly_der w i hp
    obtain ⟨q, hq, hdq⟩ := gauss_der δ w i
    refine ⟨fun v => (p' + p * q) v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v),
      Submodule.subset_span ⟨p' + p * q, add_mem hp' (mul_mem hp hq), g, hg, rfl⟩, fun v => ?_⟩
    have h := ((hdp v).mul (hdq v)).mul_const (g (finPartPi v))
    simp only [shift_zero] at h
    simp only [finPart_shift]
    have e : (p' + p * q) v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v) =
        (p' v * UpperTheory.ConvolutionTheory.R2.gauss δ v + p v * (UpperTheory.ConvolutionTheory.R2.gauss δ v * q v)) * g (finPartPi v) := by
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    rw [e]
    exact h
  | zero => exact ⟨0, zero_mem _, fun v => hasDerivAt_const _ _⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    exact ⟨x' + y', add_mem hxm hym, fun v => (hx v).add (hy v)⟩
  | smul c x _ hx =>
    obtain ⟨x', hxm, hx⟩ := hx
    exact ⟨c • x', Submodule.smul_mem _ _ hxm, fun v => (hx v).const_mul c⟩

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.R2.Ff.opsFock :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F), OpsFock D O := by
  intro F E _ _ _ _ _ _ _ D O w i φ hφ
  have hs : φ.1 ∈ Submodule.span ℂ (Gen D.δ) := hφ
  refine ⟨?_, ?_⟩
  · have e : (O.x w i φ).1 = fun v => Fo.cw w (v i) * φ.1 v := funext fun v => O.x_apply w i φ v
    change (O.x w i φ).1 ∈ Submodule.span ℂ (Gen D.δ)
    rw [e]
    exact cw_coord_mul_mem_span_gen_of_mem D.δ w i hs
  · obtain ⟨f', hf', hd⟩ := span_d D.δ w i hs
    have e : (O.d w i φ).1 = f' := funext fun v => (O.d_spec w i φ v).unique (hd v)
    change (O.d w i φ).1 ∈ Submodule.span ℂ (Gen D.δ)
    rw [e]
    exact hf'
