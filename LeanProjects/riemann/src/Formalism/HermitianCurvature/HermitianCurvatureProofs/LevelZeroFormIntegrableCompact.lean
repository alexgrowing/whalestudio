import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualCptOfStepParts2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.JCx2

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem level_zero_form_integrable (D : B.RealPlaceData k r Wp Wq) (μ : Measure (Mt k r))
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (x x' : Ix S → B.Mat k r → (Wq →L[ℂ] Wp))
    (Φ Φ' : Ix S → RadSp k r D.z D.z' D.π D.π')
    (hx : ∀ a, ∀ (A : ℝ) (m : ℕ), B.InCC A m (x a)) (hx' : ∀ a, ∀ (A : ℝ) (m : ℕ), B.InCC A m (x' a))
    (hΦ : ∀ a, ∀ y ∈ DomR k r D.z D.z',
      (Φ a : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF D (x a)) y.1 y.2)
    (hΦ' : ∀ a, ∀ y ∈ DomR k r D.z D.z',
      (Φ' a : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF D (x' a)) y.1 y.2) :
    Integrable (fun c : Fin r → ℂ => ((∏ a : Fin r, ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (Φ b) (Φ' b) c) := by
  obtain ⟨C1, -, hpair⟩ := rb_pairAt D μ hμ
  let f : Ix S → (Fin r → ℂ) × ℂ → ℂ := fun a q =>
    (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D (x' a) (B.gq D q))) (B.hsVec (B.JF D (x a) (B.gq D q)))
  have hint : ∀ a, Integrable (f a) := fun a => rb_int_pair D (x a) (x' a) (hx a) (hx' a)
  have hae : (fun c : Fin r → ℂ => ((∏ a : Fin r, ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (Φ b) (Φ' b) c)
      =ᵐ[volume] fun c => ∑ b, (C1 : ℂ) * ∫ ζ, f b (c, ζ) := by
    filter_upwards [rb_ae_OmX] with c hc
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hpair (x b) (x' b) (Φ b) (Φ' b) (hΦ b) (hΦ' b) c hc, mul_left_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    dsimp only
    rw [rb_weight hc]
    rfl
  refine Integrable.congr ?_ hae.symm
  exact integrable_finset_sum _ fun b _ => ((hint b).integral_prod_left).const_mul _

theorem level_zero_form_integrable_compact (D : B.RealPlaceData k r Wp Wq) (μ : Measure (Mt k r))
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (x x' : Ix S → B.Mat k r → (Wq →L[ℂ] Wp))
    (Φ Φ' : Ix S → RadSp k r D.z D.z' D.π D.π')
    (hx : ∀ a, ∀ (A : ℝ) (m : ℕ), B.InCC A m (x a)) (hx' : ∀ a, ∀ (A : ℝ) (m : ℕ), B.InCC A m (x' a))
    (hΦ : ∀ a, ∀ y ∈ DomR k r D.z D.z',
      (Φ a : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF D (x a)) y.1 y.2)
    (hΦ' : ∀ a, ∀ y ∈ DomR k r D.z D.z',
      (Φ' a : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF D (x' a)) y.1 y.2) (c : Fin r → ℂ) :
    Integrable (fun c' : Cf r 0 => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (Φ b) (Φ' b) (glue 0 c c')) := by
  have h := level_zero_form_integrable D μ hμ x x' Φ Φ' hx hx' hΦ hΦ'
  let e : {l : Fin r // (0 : Fin (r + 1)).val ≤ l.val} ≃ Fin r := Equiv.subtypeUnivEquiv (fun l => Nat.zero_le _)
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin r => ℂ) e
  have hv : ∀ (c' : Cf r 0) (l : {l : Fin r // (0 : Fin (r + 1)).val ≤ l.val}),
      (MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ) e c') (e l) = c' l := fun c' l =>
    Equiv.piCongrLeft_apply_apply _ _ _ _
  have hg : ∀ c' : Cf r 0, glue 0 c c' = MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ) e c' := by
    intro c'
    funext l
    have h1 := hv c' ⟨l, Nat.zero_le _⟩
    simp only [glue]
    exact h1.symm
  have hfun : (fun c' : Cf r 0 => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (Φ b) (Φ' b) (glue 0 c c')) =
      (fun c : Fin r → ℂ => ((∏ a : Fin r, ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (Φ b) (Φ' b) c) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ) e) := by
    funext c'
    simp only [Function.comp, hg]
    congr 2
    exact Fintype.prod_equiv e (fun l => ‖c' l‖ ^ (-2 : ℤ))
      (fun a => ‖(MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ) e c') a‖ ^ (-2 : ℤ)) (fun l => by rw [hv])
  rw [hfun]
  exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 h

end Formalism.FourierDecayAlt.P5.HerC
