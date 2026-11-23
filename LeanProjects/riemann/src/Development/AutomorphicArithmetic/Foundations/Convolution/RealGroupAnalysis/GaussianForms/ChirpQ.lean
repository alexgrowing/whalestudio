import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ChirpInf
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C
open GroundTheory.Heights₂.Theta

section ChirpQ

variable {F : Type} [Field F] [NumberField F]

private theorem eval_map_hom {R S ι : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : MvPolynomial ι R) (v : ι → R) :
    MvPolynomial.eval (fun i => f (v i)) (p.map f) = f (MvPolynomial.eval v p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

private theorem continuous_eval_poly {R ι : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (p : MvPolynomial ι R) :
    Continuous fun v : ι → R => MvPolynomial.eval v p := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.mul (continuous_apply i)

variable (F) in

private noncomputable def lT : mixedEmbedding.mixedSpace F →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (-((mixedTraceForm F).flip 1))

private theorem psi_split (x : A F) :
    ψ x = ((Real.fourierChar (lT F (adeleInfHom x)) : Circle) : ℂ) *
      ((finiteAdelicChar F (adeleFinHom x) : Circle) : ℂ) := by
  have h := adelicChar_mul_eq (K := F) x 1
  rw [mul_one] at h
  have h1 : homeomorphMixedSpace F (1 : A F).1 = 1 := by
    exact map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  rw [h1] at h
  have h2 : x.2 * (1 : A F).2 = adeleFinHom x := by
    change x.2 * 1 = x.2
    rw [mul_one]
  rw [h2] at h
  exact h

private theorem chirp_poly (p : MvPolynomial (Fin 4) (A F)) (φ : V4 F → ℂ)
    (hφ : φ ∈ schwartzBruhatPi F (Fin 4)) :
    (fun v => ψ (MvPolynomial.eval v p) * φ v) ∈ schwartzBruhatPi F (Fin 4) := by
  refine Submodule.span_induction
    (p := fun f _ => (fun v => ψ (MvPolynomial.eval v p) * f v) ∈ schwartzBruhatPi F (Fin 4))
    ?_ ?_ ?_ ?_ hφ
  · rintro _ ⟨φ0, g, hg, rfl⟩
    have hT := chirpInf F (Fin 4) (p.map adeleInfHom) (lT F)
    have hloc : IsLocallyConstant fun w : Fin 4 → FiniteAdeleRing (𝓞 F) F =>
        ((finiteAdelicChar F (MvPolynomial.eval w (p.map adeleFinHom)) : Circle) : ℂ) := by
      have h1 := (isLocallyConstant_finiteAdelicChar_mul (K := F) 1).comp_continuous
        (continuous_eval_poly (p.map (adeleFinHom (K := F))))
      simpa [Function.comp_def] using h1
    have hg' : (fun w => ((finiteAdelicChar F (MvPolynomial.eval w (p.map adeleFinHom)) : Circle) : ℂ) * g w)
        ∈ finiteSchwartzBruhatPi F (ι := Fin 4) :=
      ⟨hloc.mul hg.1, hg.2.mul_left⟩
    convert schwartzBruhatTensorPi_mem (SchwartzMap.smulLeftCLM ℂ (fun x : Fin 4 → mixedEmbedding.mixedSpace F =>
      ((Real.fourierChar (lT F (MvPolynomial.eval x (p.map adeleInfHom))) : Circle) : ℂ)) φ0) hg' using 1
    funext v
    simp only [schwartzBruhatTensorPi]
    rw [SchwartzMap.smulLeftCLM_apply_apply hT, psi_split]
    simp only [smul_eq_mul, infPartPi_eq_adeleInfHom, finPartPi_eq_adeleFinHom, eval_map_hom]
    ring
  · convert (schwartzBruhatPi F (Fin 4)).zero_mem using 1
    funext v
    simp
  · intro f g _ _ hf hg
    convert (schwartzBruhatPi F (Fin 4)).add_mem hf hg using 1
    funext v
    simp [mul_add]
  · intro a f _ hf
    convert (schwartzBruhatPi F (Fin 4)).smul_mem a hf using 1
    funext v
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end ChirpQ

theorem UpperTheory.ConvolutionTheory.R2.C.chirpQ :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (b : A F) (y : V4 F) (φ : V4 F → ℂ), φ ∈ schwartzBruhatPi F (Fin 4) →
    (fun v => ψ (b * q4 δ v + B4 δ v y) * φ v) ∈ schwartzBruhatPi F (Fin 4) := by
  intro F _ _ δ b y φ hφ
  open MvPolynomial in
  have h := chirp_poly (F := F)
    (C b * (X 2 ^ 2 - C (rt δ) * X 3 ^ 2 - X 1 * X 0) +
      (2 * (X 2 * C (y 2) - C (rt δ) * (X 3 * C (y 3))) - X 1 * C (y 0) - X 0 * C (y 1))) φ hφ
  convert h using 3 with v
  simp [q4, B4]
