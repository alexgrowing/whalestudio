import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.AtLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem quadraticForm_add_expand (δ : F) (v : V4 F) (i : Fin 4) (a : A F) :
    q4 δ (v + Pi.single i a) = q4 δ v + a * (B4 δ v (Pi.single i 1) + a * q4 δ (Pi.single i 1)) := by
  fin_cases i <;> simp [q4, B4, Pi.single_apply] <;> ring

private theorem psi_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp [ψ, (adelicChar F).map_add_eq_mul]

private theorem cw_mul (w : InfinitePlace F) (a b : A F) : cw w (a * b) = cw w a * cw w b := by
  simp [cw, map_mul]

private theorem psi_curve (w : InfinitePlace F) (b : A F) (δ : F) (i : Fin 4) (v : V4 F) :
    ∃ g : ℝ → ℂ, (∀ t, ψ (b * q4 δ (v + Pi.single i (at1 w t))) = ψ (b * q4 δ v) * g t) ∧ g 0 = 1 ∧
      HasDerivAt g (cc * (cw w b * cw w (B4 δ v (Pi.single i 1)))) 0 := by
  obtain ⟨hψ, -, hp, -, -, hm, -, -⟩ := atLaws F w
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = TR.pInf F b w * TR.pInf F (B4 δ v (Pi.single i 1)) w := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = TR.pInf F b w * TR.pInf F (q4 δ (Pi.single i 1)) w := ⟨_, rfl⟩
  refine ⟨fun t => Complex.exp (cc * ((t * (β + t * κ) : ℝ) : ℂ)), ?_, by simp, ?_⟩
  · intro t
    have h0 : at1 w t * (b * (B4 δ v (Pi.single i 1) + at1 w t * q4 δ (Pi.single i 1))) =
        at1 w (t * (β + t * κ)) := by
      rw [hm]
      congr 2
      have : TR.pInf F (at1 w t) w = t := by rw [hp]; simp
      simp only [map_mul, map_add, Pi.mul_apply, Pi.add_apply, this, hβ, hκ]
      ring
    have h1 : b * q4 δ (v + Pi.single i (at1 w t)) = b * q4 δ v + at1 w (t * (β + t * κ)) := by
      rw [quadraticForm_add_expand, ← h0]
      ring
    rw [h1, psi_add, hψ]
  · have hu : HasDerivAt (fun t : ℝ => t * (β + t * κ)) β 0 := by
      have := (hasDerivAt_id' (0 : ℝ)).fun_mul (((hasDerivAt_id' (0 : ℝ)).mul_const κ).const_add β)
      simpa using this
    have h2 := (hu.ofReal_comp.const_mul cc).cexp
    convert h2 using 1
    simp [hβ, cw]

private theorem p_apply (O : Ops F) (δ : F) (w : InfinitePlace F) (i : Fin 4) (φ : S4 F) (v : V4 F) :
    (O.p δ w i φ).1 v = cc * cw w (B4 δ v (Pi.single i 1)) * φ.1 v := by
  have hs : ∀ (c : ℂ) (T : Module.End ℂ (S4 F)), ((c • T) φ).1 v = c * (T φ).1 v := fun _ _ => rfl
  have hn : ∀ a : A F, cw w (-a) = -cw w a := fun a => by simp [cw]
  have h2 : cw w (2 : A F) = 2 := by
    have : TR.pInf F (2 : A F) = 2 := map_ofNat _ 2
    simp [cw, this]
  fin_cases i
  · have : B4 δ v (Pi.single 0 1) = -v 1 := by simp [B4, Pi.single_apply]
    simp only [Fin.zero_eta, this, hn, Ops.p]
    simp [hs, O.x_apply]
    ring
  · have : B4 δ v (Pi.single 1 1) = -v 0 := by simp [B4, Pi.single_apply]
    simp only [Fin.mk_one, this, hn, Ops.p]
    simp [hs, O.x_apply]
    ring
  · have : B4 δ v (Pi.single 2 1) = 2 * v 2 := by simp [B4, Pi.single_apply]
    simp only [Fin.reduceFinMk, this, cw_mul, h2, Ops.p]
    simp [hs, O.x_apply]
    ring
  · have : B4 δ v (Pi.single 3 1) = (-2 * rt δ) * v 3 := by simp [B4, Pi.single_apply]; ring
    simp only [Fin.reduceFinMk, this, cw_mul, hn, h2, Ops.p]
    simp [hs, O.x_apply]
    ring

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Fo.dN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) w i b, O.d w i * W.Om (nU b) = W.Om (nU b) * (O.d w i + cw w b • O.p D.δ w i) ∧
    O.x w i * W.Om (nU b) = W.Om (nU b) * O.x w i := by
  intro F E _ _ _ _ _ _ _ D W O w i b
  refine ⟨?_, ?_⟩
  · refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    obtain ⟨g, hg, hg0, hgd⟩ := psi_curve w b D.δ i v
    have hφ := O.d_spec w i φ v
    have h1 := O.d_spec w i (W.Om (nU b) φ) v
    have hz : v + Pi.single i (at1 w 0) = v := by
      rw [(atLaws F w).2.2.2.2.1]; simp
    have hfun : (fun t : ℝ => (W.Om (nU b) φ).1 (v + Pi.single i (at1 w t))) =
        fun t => (ψ (b * q4 D.δ v) * g t) * φ.1 (v + Pi.single i (at1 w t)) := by
      funext t
      rw [W.Om_n, hg]
    rw [hfun] at h1
    have h2 := (hgd.const_mul (ψ (b * q4 D.δ v))).mul hφ
    have h3 := h1.unique h2
    change (O.d w i (W.Om (nU b) φ)).1 v = (W.Om (nU b) ((O.d w i + cw w b • O.p D.δ w i) φ)).1 v
    rw [h3, W.Om_n]
    change _ = _ * ((O.d w i φ).1 v + cw w b * (O.p D.δ w i φ).1 v)
    rw [p_apply, hg0, hz]
    ring
  · refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    change (O.x w i (W.Om (nU b) φ)).1 v = (W.Om (nU b) (O.x w i φ)).1 v
    rw [O.x_apply, W.Om_n, W.Om_n, O.x_apply]
    ring
