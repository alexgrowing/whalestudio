import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeanLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UILaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.IILaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ExValCont
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointL2

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc UpperTheory.ConvolutionTheory.R2.Ff
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem vol_lt (N : MeasE E) : N.μ N.D < ⊤ := by
  have hb : Bd (fun _ : GL (Fin 2) (A E) => (1 : ℂ)) :=
    ⟨continuous_const, fun _ _ => rfl, fun _ _ => ⟨1, fun _ _ _ => by simp⟩⟩
  have h := (meanLaws E N _ hb).1 1
  have h' : IntegrableOn (fun _ : G1 E => (1 : ℂ)) N.D N.μ := h
  exact (integrableOn_const_iff (by simp)).1 h' |>.resolve_left (by simp)

private theorem inner_der (N : MeasE E) {Ψ Q : GL (Fin 2) (A E) → ℂ} (hΨ : Bd Ψ) (hQ : Bd Q)
    {g : ℝ → GL (Fin 2) (A E)} (hg : Continuous g)
    (hd : ∀ y s, HasDerivAt (fun u => Ψ (y * g u)) (Q (y * g s)) s) (y : GL (Fin 2) (A E)) (s : ℝ) :
    HasDerivAt (fun u => mean N fun x => Ψ (x * (y * g u))) (mean N fun x => Q (x * (y * g s))) s := by
  obtain ⟨B, hB⟩ := hQ.bdd ((fun u => y * g u) '' Metric.closedBall s 1)
    ((isCompact_closedBall s 1).image (continuous_const.mul hg))
  haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using vol_lt N⟩
  have hm : ∀ {P : GL (Fin 2) (A E) → ℂ}, Continuous P → ∀ k,
      AEStronglyMeasurable (fun h : G1 E => P (gl h * k)) (N.μ.restrict N.D) := fun hP k =>
    (hP.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const)).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := N.μ.restrict N.D)
    (F := fun u h => Ψ (gl h * (y * g u))) (F' := fun u h => Q (gl h * (y * g u)))
    (x₀ := s) (s := Metric.ball s 1) (bound := fun _ => B)
    (Metric.ball_mem_nhds _ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun u => hm hΨ.cont _
  · exact (meanLaws E N Ψ hΨ).1 _
  · exact hm hQ.cont _
  · exact ae_of_all _ fun h u hu => hB h _ ⟨u, Metric.ball_subset_closedBall hu, rfl⟩
  · exact integrable_const _
  · refine ae_of_all _ fun h u _ => ?_
    have := hd (gl h * y) u
    simpa only [mul_assoc] using this

private theorem outer_der (N : MeasE E) {Ψ Q : GL (Fin 2) (A E) → ℂ} (hΨ : Bd Ψ) (hQ : Bd Q)
    {g : ℝ → GL (Fin 2) (A E)} (hg : Continuous g) (g0 : g 0 = 1)
    (hd : ∀ y s, HasDerivAt (fun u => Ψ (y * g u)) (Q (y * g s)) s) :
    HasDerivAt (fun s => II N fun x => Ψ (x * g s)) (II N Q) 0 := by
  set Mp : GL (Fin 2) (A E) → ℂ := fun y => mean N fun x => Ψ (x * y) with hMp
  set Mq : GL (Fin 2) (A E) → ℂ := fun y => mean N fun x => Q (x * y) with hMq
  have cp : Continuous Mp := (meanLaws E N Ψ hΨ).2.1
  have cq : Continuous Mq := (meanLaws E N Q hQ).2.1
  have ip : ∀ γ y, Mp (ratGL E 2 γ * y) = Mp y := (meanLaws E N Ψ hΨ).2.2.2
  have iq : ∀ γ y, Mq (ratGL E 2 γ * y) = Mq y := (meanLaws E N Q hQ).2.2.2
  have inv : ∀ (M : GL (Fin 2) (A E) → ℂ), (∀ γ y, M (ratGL E 2 γ * y) = M y) → ∀ k (e : Eˣ) t,
      M (aE (IdeleGroup.diagonal E e * t) * k) = M (aE t * k) := by
    intro M hM k e t
    obtain ⟨γ, hγ⟩ := exists_ratGL_aE (F := E) e
    rw [aE_mul, ← hγ, mul_assoc, hM]
  have hK : IsCompact (Metric.closedBall (0 : ℝ) 1) := isCompact_closedBall 0 1
  set b : (A E)ˣ → ℝ := fun t => sSup ((fun s => ‖Mq (aE t * g s)‖) '' Metric.closedBall (0 : ℝ) 1) with hb
  have cb : Continuous b := IsCompact.continuous_sSup (f := fun t s => ‖Mq (aE t * g s)‖) hK
    (cq.comp ((continuous_aE.comp continuous_fst).mul (hg.comp continuous_snd))).norm
  have ib : ∀ (e : Eˣ) t, b (IdeleGroup.diagonal E e * t) = b t := fun e t => by
    simp only [hb, inv Mq iq]
  obtain ⟨-, ⟨B, hB⟩, -⟩ := uiLaws E (fun t => (b t : ℂ)) (Complex.continuous_ofReal.comp cb)
    (fun e t => by simp only [ib])
  have hbd : ∀ z : IdeleGroup.normOneSubgroup E, ∀ s ∈ Metric.closedBall (0 : ℝ) 1,
      ‖Mq (aE (z : IdeleGroup E) * g s)‖ ≤ B := by
    intro z s hs
    have hab : ab (z : IdeleGroup E) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 z.2)
    have h1 : ‖Mq (aE (z : IdeleGroup E) * g s)‖ ≤ b z :=
      le_csSup (hK.image (cq.comp (continuous_const.mul hg)).norm).bddAbove ⟨s, hs, rfl⟩
    calc _ ≤ b z := h1
      _ ≤ ‖(b z : ℂ)‖ := by rw [Complex.norm_real]; exact le_abs_self _
      _ ≤ B := hB _ hab
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) :=
    ⟨by simpa using normOneMeasure_normOneFundamentalDomain_lt_top E⟩
  have hint : ∀ (M : GL (Fin 2) (A E) → ℂ), Continuous M → (∀ γ y, M (ratGL E 2 γ * y) = M y) → ∀ k,
      IntegrableOn (fun z : IdeleGroup.normOneSubgroup E => M (aE (z : IdeleGroup E) * k))
        (normOneFundamentalDomain E) (normOneMeasure E) := fun M cM iM k =>
    (uiLaws E (fun t => M (aE t * k)) (cM.comp (continuous_aE.mul continuous_const)) (inv M iM k)).1
  have e1 : ∀ s, (II N fun x => Ψ (x * g s)) =
      ∫ z in normOneFundamentalDomain E, Mp (aE (z : IdeleGroup E) * g s) ∂normOneMeasure E := by
    intro s
    simp only [II, UI, hMp, mul_assoc]
  have e2 : II N Q = ∫ z in normOneFundamentalDomain E, Mq (aE (z : IdeleGroup E) * g 0) ∂normOneMeasure E := by
    simp only [II, UI, hMq, g0, mul_one]
  simp only [e1]
  rw [e2]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (μ := (normOneMeasure E).restrict (normOneFundamentalDomain E))
    (F := fun s z => Mp (aE (z : IdeleGroup E) * g s)) (F' := fun s z => Mq (aE (z : IdeleGroup E) * g s))
    (x₀ := 0) (s := Metric.ball (0 : ℝ) 1) (bound := fun _ => B)
    (Metric.ball_mem_nhds _ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun s => (hint Mp cp ip (g s)).aestronglyMeasurable
  · exact hint Mp cp ip (g 0)
  · exact (hint Mq cq iq (g 0)).aestronglyMeasurable
  · exact ae_of_all _ fun z s hs => hbd z s (Metric.ball_subset_closedBall hs)
  · exact integrable_const _
  · exact ae_of_all _ fun z s _ => inner_der N hΨ hQ hg hd _ s

variable [IsTotallyComplex E]

private theorem ex_zero' (X : Lie E 2) : ex X 0 = 1 := by
  have h := (exPar E X).1 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

private theorem der_curve (Φ : Sm E 2) (X : Lie E 2) (y : GL (Fin 2) (A E)) (s : ℝ) :
    HasDerivAt (fun u => Φ.1 (y * infGL E 2 (ex X u))) ((act (.lie X) Φ).1 (y * infGL E 2 (ex X s))) s := by
  have h1 := GlobalTheory.CuspRep.hasDerivAt_curve Φ (y * infGL E 2 (ex X s)) (ex X) X (ex_zero' X) (exPar E X).2.2.1
  have h2 : HasDerivAt (fun u => Φ.1 (y * infGL E 2 (ex X s) * infGL E 2 (ex X (u - s))))
      ((act (.lie X) Φ).1 (y * infGL E 2 (ex X s))) s :=
    HasDerivAt.comp_sub_const s s (by simpa using h1)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
  show Φ.1 (y * infGL E 2 (ex X u)) = Φ.1 (y * infGL E 2 (ex X s) * infGL E 2 (ex X (u - s)))
  rw [mul_assoc, ← map_mul, ← (exPar E X).1, add_sub_cancel]

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.iiLie :
    IILie := by
  intro E _ _ _ N Φ φ X h0 hP h1 h2
  have hg : Continuous fun s => infGL E 2 (ex X s) :=
    (GlobalTheory.CompanionTheory.LieSkew.continuous_infGL_map E 2).comp (exPar E X).2.1
  have g0 : infGL E 2 (ex X 0) = 1 := by rw [ex_zero', map_one]
  have hQ : Bd fun x => (act (.lie X) Φ).1 x * φ.1 x + (1 : ℂ) * (Φ.1 x * (act (.lie X) φ).1 x) := by
    refine ⟨h1.cont.add (continuous_const.mul h2.cont), fun γ g => ?_, fun C hC => ?_⟩
    · exact congrArg₂ (fun p q => p + (1 : ℂ) * q) (h1.left γ g) (h2.left γ g)
    · obtain ⟨B₁, hB₁⟩ := h1.bdd C hC
      obtain ⟨B₂, hB₂⟩ := h2.bdd C hC
      refine ⟨B₁ + B₂, fun h k hk => ?_⟩
      have a := hB₁ h k hk
      have b := hB₂ h k hk
      rw [one_mul]
      exact (norm_add_le _ _).trans (add_le_add a b)
  have hd : ∀ y s, HasDerivAt (fun u => Φ.1 (y * infGL E 2 (ex X u)) * φ.1 (y * infGL E 2 (ex X u)))
      ((act (.lie X) Φ).1 (y * infGL E 2 (ex X s)) * φ.1 (y * infGL E 2 (ex X s)) +
        (1 : ℂ) * (Φ.1 (y * infGL E 2 (ex X s)) * (act (.lie X) φ).1 (y * infGL E 2 (ex X s)))) s := by
    intro y s
    rw [one_mul]
    exact (der_curve Φ X y s).mul (der_curve φ X y s)
  have hD := outer_der N h0 hQ hg g0 hd
  have hc : (fun s => II N fun x => Φ.1 (x * infGL E 2 (ex X s)) * φ.1 (x * infGL E 2 (ex X s))) =
      fun _ => II N fun x => Φ.1 x * φ.1 x :=
    funext fun s => (iiLaws E N _ h0).2 hP (infGL E 2 (ex X s))
  rw [hc] at hD
  have hz := hD.unique (hasDerivAt_const (0 : ℝ) _)
  rw [(iiLaws E N _ h1).1 _ h2 1, one_mul] at hz
  exact hz
