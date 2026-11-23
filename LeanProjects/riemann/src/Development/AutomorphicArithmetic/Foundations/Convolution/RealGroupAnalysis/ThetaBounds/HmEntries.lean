import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ActInf
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ExValCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open UpperTheory.ConvolutionTheory.R2.Fo (pl)
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldDerivatives

private theorem herm_der (P : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (P' H : Matrix (Fin 2) (Fin 2) ℂ) (h0 : P 0 = 1)
    (hP : ∀ i j, HasDerivAt (fun t => P t i j) (P' i j) 0) (i j : Fin 2) :
    HasDerivAt (fun t => (P t * H * (P t)ᴴ) i j) ((P' * H + H * P'ᴴ) i j) 0 := by
  have hval : ∀ i j : Fin 2,
      P' i 0 * H 0 0 * star ((1 : Matrix (Fin 2) (Fin 2) ℂ) j 0) + (1 : Matrix (Fin 2) (Fin 2) ℂ) i 0 * H 0 0 * star (P' j 0) +
        (P' i 1 * H 1 0 * star ((1 : Matrix (Fin 2) (Fin 2) ℂ) j 0) + (1 : Matrix (Fin 2) (Fin 2) ℂ) i 1 * H 1 0 * star (P' j 0)) +
      (P' i 0 * H 0 1 * star ((1 : Matrix (Fin 2) (Fin 2) ℂ) j 1) + (1 : Matrix (Fin 2) (Fin 2) ℂ) i 0 * H 0 1 * star (P' j 1) +
        (P' i 1 * H 1 1 * star ((1 : Matrix (Fin 2) (Fin 2) ℂ) j 1) + (1 : Matrix (Fin 2) (Fin 2) ℂ) i 1 * H 1 1 * star (P' j 1))) =
      (P' * H + H * P'ᴴ) i j := by
    simp only [Fin.forall_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring
  have hc : ∀ a b, HasDerivAt (fun t => star (P t a b)) (star (P' a b)) 0 := fun a b => (hP a b).star
  have hh : ∀ a b, HasDerivAt (fun t => P t i a * H a b * star (P t j b))
      (P' i a * H a b * star (P 0 j b) + P 0 i a * H a b * star (P' j b)) 0 :=
    fun a b => ((hP i a).mul_const (H a b)).mul (hc j b)
  have hs := (((hh 0 0).add (hh 1 0)).add ((hh 0 1).add (hh 1 1)))
  refine (hs.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  · rw [h0]
    exact hval i j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    ring

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem hm_entries {s : ℂ} {w : InfinitePlace F} (u : Fin 4 → TR.Rinf F) :
    Hm s w u 0 0 = (u 1 w : ℝ) ∧ Hm s w u 1 1 = (u 0 w : ℝ) ∧ Hm s w u 0 1 = (u 2 w : ℝ) + s * (u 3 w : ℝ) ∧
      Hm s w u 1 0 = (u 2 w : ℝ) - s * (u 3 w : ℝ) := by
  simp [Hm]

private theorem coord_der {s : ℂ} (hs : s ≠ 0) (w : InfinitePlace F) (a : ℝ → Fin 4 → TR.Rinf F)
    (Q : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : ∀ t, Hm s w (a t) = Q t)
    (hq : ∀ i j, HasDerivAt (fun t => Q t i j) (q i j) 0) (i : Fin 4) :
    ∃ d : ℝ, HasDerivAt (fun t => a t i w) d 0 := by
  have e00 : ∀ t, Q t 0 0 = (a t 1 w : ℝ) := fun t => by rw [← hQ]; exact (hm_entries _).1
  have e11 : ∀ t, Q t 1 1 = (a t 0 w : ℝ) := fun t => by rw [← hQ]; exact (hm_entries _).2.1
  have e01 : ∀ t, Q t 0 1 = (a t 2 w : ℝ) + s * (a t 3 w : ℝ) := fun t => by rw [← hQ]; exact (hm_entries _).2.2.1
  have e10 : ∀ t, Q t 1 0 = (a t 2 w : ℝ) - s * (a t 3 w : ℝ) := fun t => by rw [← hQ]; exact (hm_entries _).2.2.2
  suffices h : ∃ c : ℂ, HasDerivAt (fun t => ((a t i w : ℝ) : ℂ)) c 0 by
    obtain ⟨c, hc⟩ := h
    refine ⟨c.re, ?_⟩
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => by simp)
  fin_cases i
  · exact ⟨_, (hq 1 1).congr_of_eventuallyEq (Eventually.of_forall fun t => (e11 t).symm)⟩
  · exact ⟨_, (hq 0 0).congr_of_eventuallyEq (Eventually.of_forall fun t => (e00 t).symm)⟩
  · refine ⟨_, (((hq 0 1).add (hq 1 0)).const_mul (2⁻¹ : ℂ)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)⟩
    simp only [Pi.add_apply, e01, e10]
    change ((a t 2 w : ℝ) : ℂ) = _
    ring
  · refine ⟨_, (((hq 0 1).sub (hq 1 0)).const_mul ((2 * s)⁻¹ : ℂ)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)⟩
    simp only [Pi.sub_apply, e01, e10]
    change ((a t 3 w : ℝ) : ℂ) = _
    field_simp
    ring

private theorem hm_der {s : ℂ} (w : InfinitePlace F) (a : ℝ → Fin 4 → TR.Rinf F) (d : Fin 4 → TR.Rinf F)
    (Q : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : ∀ t, Hm s w (a t) = Q t)
    (hq : ∀ i j, HasDerivAt (fun t => Q t i j) (q i j) 0)
    (hd : ∀ i, HasDerivAt (fun t => a t i w) (d i w) 0) : Hm s w d = q := by
  have hc : ∀ i, HasDerivAt (fun t => ((a t i w : ℝ) : ℂ)) ((d i w : ℝ) : ℂ) 0 := fun i => (hd i).ofReal_comp
  have e00 : (fun t => Q t 0 0) = fun t => ((a t 1 w : ℝ) : ℂ) :=
    funext fun t => by rw [← hQ]; exact (hm_entries _).1
  have e11 : (fun t => Q t 1 1) = fun t => ((a t 0 w : ℝ) : ℂ) :=
    funext fun t => by rw [← hQ]; exact (hm_entries _).2.1
  have e01 : (fun t => Q t 0 1) = (fun t => ((a t 2 w : ℝ) : ℂ)) + fun t => s * ((a t 3 w : ℝ) : ℂ) :=
    funext fun t => by rw [← hQ]; exact (hm_entries _).2.2.1
  have e10 : (fun t => Q t 1 0) = (fun t => ((a t 2 w : ℝ) : ℂ)) - fun t => s * ((a t 3 w : ℝ) : ℂ) :=
    funext fun t => by rw [← hQ]; exact (hm_entries _).2.2.2
  have h00 := hq 0 0
  have h11 := hq 1 1
  have h01 := hq 0 1
  have h10 := hq 1 0
  rw [e00] at h00
  rw [e11] at h11
  rw [e01] at h01
  rw [e10] at h10
  obtain ⟨f00, f11, f01, f10⟩ := hm_entries (s := s) (w := w) d
  ext i j
  revert i j
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [f00]; exact (hc 1).unique h00
  · rw [f01]; exact ((hc 2).add ((hc 3).const_mul s)).unique h01
  · rw [f10]; exact ((hc 2).sub ((hc 3).const_mul s)).unique h10
  · rw [f11]; exact (hc 0).unique h11

end UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldDerivatives

open UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldDerivatives in
theorem UpperTheory.ConvolutionTheory.R2.Ff.vfDer :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), VfDer D := by
  intro F E _ _ _ _ _ _ _ D Y v
  obtain ⟨hadd, -, hder, -, -⟩ := exPar E Y
  have hA := actInf F E D
  have hex0 : ex Y 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hinv : ∀ t, (ex Y t)⁻¹ = ex Y (-t) := fun t => by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hadd, add_neg_cancel, hex0]
  let a : ℝ → Fin 4 → TR.Rinf F := fun t i => TR.pInf F (D.act (infGL E 2 (ex Y t))⁻¹ v i)
  let a0 : Fin 4 → TR.Rinf F := fun i => TR.pInf F (v i)
  let P : (E →+* ℂ) → ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun τ t => (ex Y (-t)).val.map (coord τ)
  have hHm : ∀ τ t, Hm (τ D.θ) (pl F τ) (a t) = P τ t * Hm (τ D.θ) (pl F τ) a0 * (P τ t)ᴴ := fun τ t => by
    have h := (hA (ex Y (-t)) v).2 τ
    simp only [a, P]
    rw [← map_inv, hinv]
    exact h
  have hP0 : ∀ τ, P τ 0 = 1 := fun τ => by
    simp only [P, neg_zero, hex0]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hPd : ∀ τ i j, HasDerivAt (fun t => P τ t i j) ((-(Matrix.of Y).map (coord τ)) i j) 0 := fun τ i j => by
    let c : Cinf E →L[ℝ] ℂ := LinearMap.mkContinuous
      { toFun := coord τ, map_add' := map_add _, map_smul' := UpperTheory.V.FieldIso.coord_smul τ } 1
      (fun x => by simpa using UpperTheory.V.FieldIso.norm_coord_le τ x)
    have h1 : HasDerivAt (fun t => (ex Y t).val i j) (Y i j) 0 := hasDerivAt_pi.1 (hasDerivAt_pi.1 hder i) j
    have h2 : HasDerivAt (fun t => c ((ex Y t).val i j)) (c (Y i j)) (-(0 : ℝ)) := by
      rw [neg_zero]
      exact c.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    have h3 := HasDerivAt.scomp (0 : ℝ) h2 (hasDerivAt_neg (0 : ℝ))
    refine (h3.congr_deriv ?_)
    simp [c]
  have hQ := fun τ => herm_der (P τ) (-(Matrix.of Y).map (coord τ)) (Hm (τ D.θ) (pl F τ) a0) (hP0 τ) (hPd τ)
  have hs : ∀ τ : E →+* ℂ, τ D.θ ≠ 0 := fun τ => (map_ne_zero τ).2 D.θ_ne_zero
  have hex : ∀ (w : InfinitePlace F) i, ∃ d : ℝ, HasDerivAt (fun t => a t i w) d 0 := by
    intro w i
    have : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
    obtain ⟨W, rfl⟩ := InfinitePlace.comap_surjective (k := F) (K := E) w
    have hw : pl F W.embedding = W.comap (algebraMap F E) := by
      rw [pl, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
    beta_reduce
    rw [← hw]
    exact coord_der (hs _) _ a _ _ (hHm _) (hQ _) i
  choose d hd using hex
  have hact1 : D.act 1 v = v := by
    funext i
    fin_cases i <;> simp [Dat.act, Dat.unherm, Dat.herm, D.co_mkE]
  refine ⟨fun t i => a t i - a0 i, fun i w => d w i, ?_, ?_, ?_, ?_⟩
  · funext i
    simp only [a, a0, hex0, map_one, inv_one, hact1, sub_self]
    rfl
  · rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro w
    exact (hd w i).sub_const _
  · intro t
    have hf := (hA (ex Y t)⁻¹ v).1
    rw [map_inv] at hf
    funext i
    have hi := congrFun hf i
    refine TR.ad_ext ?_ ?_
    · have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
      rw [map_add, h]
      simp [a, a0]
    · have h0 : ∀ x, pFin F (TR.sInf F x) = 0 := fun _ => rfl
      rw [map_add, h0, add_zero]
      exact hi
  · intro τ
    rw [hm_der (pl F τ) a (fun i w => d w i) _ _ (hHm τ) (hQ τ) (fun i => hd _ i)]
    simp only [Matrix.conjTranspose_neg, neg_mul, mul_neg, neg_add]
    rfl
