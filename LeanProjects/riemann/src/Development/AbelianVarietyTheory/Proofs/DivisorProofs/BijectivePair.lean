import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HilbFam.EBasis

theorem bijective_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : E →+* ℂ) (θ : E),
    (ψ θ).im ≠ 0 → Function.Bijective (fun x : Fin 2 → FR E ↦ (x 0 : E) * θ + (x 1 : E)) := by
  intro E _ _ _ ψ θ hθ
  let f : (Fin 2 → FR E) →ₗ[FR E] E :=
    { toFun := fun x ↦ (x 0 : E) * θ + (x 1 : E)
      map_add' := fun x y ↦ by simp only [Pi.add_apply, Subfield.coe_add]; ring
      map_smul' := fun c x ↦ by
        simp only [Pi.smul_apply, smul_eq_mul, Subfield.coe_mul, RingHom.id_apply, Subfield.smul_def]
        ring }
  have hreal : ∀ a : FR E, (ψ (a : E)).im = 0 := fun a ↦ by
    have h : star (ψ (a : E)) = ψ (a : E) := a.2 ψ
    have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have e : (x 0 : E) * θ + (x 1 : E) = 0 := hx
    have e2 := congrArg ψ e
    rw [map_add, map_mul, map_zero] at e2
    have him := congrArg Complex.im e2
    simp only [Complex.add_im, Complex.mul_im, hreal, mul_zero, zero_mul, add_zero, Complex.zero_im] at him
    have h0re : (ψ (x 0 : E)).re = 0 := (mul_eq_zero.1 him).resolve_right hθ
    have h0 : ψ (x 0 : E) = 0 := Complex.ext h0re (hreal _)
    have hx0 : x 0 = 0 := Subtype.ext ((map_eq_zero ψ).1 h0)
    have hx1 : x 1 = 0 := by
      rw [hx0] at e
      simpa using e
    funext i
    fin_cases i
    · exact hx0
    · exact hx1
  have hdim : Module.finrank (FR E) (Fin 2 → FR E) = Module.finrank (FR E) E := by
    rw [Module.finrank_fin_fun, Algebra.IsQuadraticExtension.finrank_eq_two (FR E) E]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩

end GlobalTheory.HilbFam.EBasis

example : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : E →+* ℂ) (θ : E), (ψ θ).im ≠ 0 → Function.Bijective (fun x : Fin 2 → FR E ↦ (x 0 : E) * θ + (x 1 : E)) := GlobalTheory.HilbFam.EBasis.bijective_pair
