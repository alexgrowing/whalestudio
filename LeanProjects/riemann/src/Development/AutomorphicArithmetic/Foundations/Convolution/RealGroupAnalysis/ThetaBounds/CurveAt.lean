import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThBoundH
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Vol
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ParCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.UnitsCpt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem curve_at {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (f : TR.Sm F 2) (x : GL (Fin 2) (A F)) {c : ℝ → GL (Fin 2) (TR.Rinf F)} {Y : TR.Lie F 2}
    (hc : Par c Y) (c0 : c 0 = 1) (t : ℝ) :
    HasDerivAt (fun s => f.1 (x * TR.infGL F 2 (c s))) ((TR.lie F 2 Y f).1 (x * TR.infGL F 2 (c t))) t := by
  have h1 := TR.hasDerivAt_curve f (x * TR.infGL F 2 (c t)) c Y c0 hc.2
  have h2 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h1' : HasDerivAt (fun u => f.1 (x * TR.infGL F 2 (c t) * TR.infGL F 2 (c u)))
      (TR.lieD Y f.1 (x * TR.infGL F 2 (c t))) ((fun s : ℝ => s - t) t) := by simpa using h1
  have h3 : HasDerivAt ((fun u => f.1 (x * TR.infGL F 2 (c t) * TR.infGL F 2 (c u))) ∘ (fun s : ℝ => s - t))
      ((1 : ℝ) • TR.lieD Y f.1 (x * TR.infGL F 2 (c t))) t := HasDerivAt.scomp t h1' h2
  have e : (fun s => f.1 (x * TR.infGL F 2 (c s))) =
      (fun u => f.1 (x * TR.infGL F 2 (c t) * TR.infGL F 2 (c u))) ∘ (fun s : ℝ => s - t) := by
    funext s
    simp only [Function.comp_apply]
    rw [mul_assoc, ← map_mul, ← hc.1, add_sub_cancel]
  rw [e]
  simpa using h3

theorem UpperTheory.ConvolutionTheory.R2.Ff.derF :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), DerF W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ c Y hc h
  obtain ⟨hinf, hcc⟩ := parCont F
  obtain ⟨c0, ccont, -⟩ := hcc c Y hc
  have hf' : TR.lie F 2 Y f ∈ π.V := π.stable (.lie Y) f hf
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using vol F M⟩
  obtain ⟨m1, -⟩ := thMeas F E D W (W.L h φ)
  set T : G1 F → ℂ := fun g => Th (W.Om g (W.L h φ)).1 with hT
  set x₀ := dM (nu F h) with hx₀
  have cf : ∀ (u : TR.Sm F 2), u ∈ π.V → ∀ a : GL (Fin 2) (A F), Continuous fun g : G1 F => u.1 (gl g * a) :=
    fun u hu a => (decay F π u hu).1.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const)
  have hone : ∀ y ∈ ({1} : Set (GL (Fin 2) (Cinf E))), One F y := by
    rintro _ rfl; simp [Ff.One, nu]
  set C : Set (GL (Fin 2) (A F)) :=
    (fun t => x₀ * TR.infGL F 2 (c t)) '' Metric.closedBall (0 : ℝ) 1 with hC
  have Cc : IsCompact C := (isCompact_closedBall (0 : ℝ) 1).image
    (continuous_const.mul (hinf.comp ccont))
  obtain ⟨B, hB⟩ := thBoundH F E D W π _ hf' φ hφ h C Cc {1} isCompact_singleton hone
  obtain ⟨B₀, hB₀⟩ := thBoundH F E D W π f hf φ hφ h C Cc {1} isCompact_singleton hone
  have bd : ∀ (u : TR.Sm F 2) (B : ℝ), (∀ g, ∀ x ∈ C, ∀ y ∈ ({1} : Set (GL (Fin 2) (Cinf E))),
      ‖u.1 (gl g * x) * Th (W.Om g (W.L (h * infGL E 2 y) φ)).1‖ ≤ B) →
      ∀ t ∈ Metric.closedBall (0 : ℝ) 1, ∀ g, ‖u.1 (gl g * x₀ * TR.infGL F 2 (c t)) * T g‖ ≤ B := by
    intro u B hb t ht g
    have := hb g _ ⟨t, ht, rfl⟩ 1 rfl
    simpa [hT, mul_assoc] using this
  have ms : ∀ u ∈ π.V, ∀ a : GL (Fin 2) (A F),
      AEStronglyMeasurable (fun g => u.1 (gl g * x₀ * a) * T g) (M.μ.restrict M.D) := by
    intro u hu a
    have e : (fun g => u.1 (gl g * x₀ * a) * T g) = (fun g => u.1 (gl g * (x₀ * a))) * T := by
      funext g
      simp only [Pi.mul_apply, mul_assoc]
    rw [e]
    exact ((cf u hu (x₀ * a)).measurable.mul m1).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := M.μ.restrict M.D)
    (F := fun t g => f.1 (gl g * x₀ * TR.infGL F 2 (c t)) * T g)
    (F' := fun t g => (TR.lie F 2 Y f).1 (gl g * x₀ * TR.infGL F 2 (c t)) * T g)
    (x₀ := (0 : ℝ)) (s := Metric.closedBall (0 : ℝ) 1) (bound := fun _ => B)
    (Metric.closedBall_mem_nhds _ one_pos)
    (Eventually.of_forall fun t => ?_) ?_ ?_ (ae_of_all _ fun g t ht => bd _ B hB t ht g)
    (integrable_const _) (ae_of_all _ fun g t _ => ?_)
  · simpa [lift, Function.comp_def, c0, mul_assoc] using key.2
  · exact ms f hf _
  · have h0 : ∀ g, ‖f.1 (gl g * x₀ * TR.infGL F 2 (c 0)) * T g‖ ≤ B₀ := bd _ B₀ hB₀ 0 (by simp)
    exact Integrable.of_bound (ms f hf _) B₀ (ae_of_all _ h0)
  · exact ms _ hf' _
  · exact (curve_at f _ hc c0 t).mul_const _
