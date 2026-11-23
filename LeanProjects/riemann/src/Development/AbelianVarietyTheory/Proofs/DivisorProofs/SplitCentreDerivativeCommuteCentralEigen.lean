import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.OfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem zc_eq_scL {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) :
    zc E N = lie E N (Central.scL N 1) := by
  unfold zc
  congr 1

theorem splitCentre_eq_scalar {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (t : ℝ) :
    splitCentre E N t = Matrix.GeneralLinearGroup.scalar (Fin N) (infId E (expU (t • (1 : Cinf E)))) := by
  have e : (fun _ : InfinitePlace E => (t : ℂ)) = t • (1 : Cinf E) := by
    funext w; simp
  unfold splitCentre
  rw [e]
  exact cornerGL_scalar _ _

theorem zc_comm_mem_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), (∀ o : Op E N, zc E N * act o = act o * zc E N) ∧ zc E N ∈ Zalg E N ∧ ∀ (φ : Sm E N) (c : ℂ), zc E N φ = c • φ ↔ ∀ (t : ℝ) (g : GA E N), φ.1 (splitCentre E N t * g) = Complex.exp (c * t) * φ.1 g := by
  intro E _ _ _ N
  rw [zc_eq_scL]
  refine ⟨fun o => (Central.lie_act 1 o).eq, Central.lie_mem_Zalg 1, fun φ c => ⟨fun h t g => ?_, fun h => ?_⟩⟩
  · have e : Central.scL N (t • (1 : Cinf E)) = t • Central.scL N (1 : Cinf E) := by
      funext i j
      change Matrix.diagonal (fun _ => t • (1 : Cinf E)) i j = t • Matrix.diagonal (fun _ => (1 : Cinf E)) i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.diagonal_apply_ne _ hij]
    have h1 : lie E N (Central.scL N (t • (1 : Cinf E))) φ = (c * t) • φ := by
      rw [e, map_smul, LinearMap.smul_apply, h, mul_comm, mul_smul, Complex.coe_smul]
    have h2 := congrFun (congrArg Subtype.val (Central.rs_exp _ _ φ h1)) g
    rw [splitCentre_eq_scalar, scalar_comm]
    exact h2
  · refine Subtype.ext <| funext fun g => ?_
    have h1 := Central.hasDerivAt_scalar (1 : Cinf E) φ g
    have e : ∀ t : ℝ, φ.1 (g * Matrix.GeneralLinearGroup.scalar (Fin N) (infId E (expU (t • (1 : Cinf E))))) =
        Complex.exp (c * t) * φ.1 g := fun t => by rw [← scalar_comm, ← splitCentre_eq_scalar, h]
    simp only [e] at h1
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * t) * φ.1 g) (c * φ.1 g) 0 := by
      simpa using (((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul c).cexp).mul_const (φ.1 g)
    exact h1.unique h2

end GlobalTheory.ResW
