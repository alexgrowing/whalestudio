import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicNormDegreeEqPadicNormDetTateModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetAevalEqProdArootsCharpolyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNormProdAevalEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativePolynomialFunctionEqNormFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDimStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

theorem map_eq_charpoly_vmap : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) [Module.Finite ℚ_[l] (Vl l A)] (f : End A) (P : Polynomial ℚ), P.Monic → P.natDegree = 2 * A.dim → (∀ n : ℤ, P.eval (n : ℚ) = (deg (A := A) (B := A) ((n : End A) - f) : ℚ)) → P.map (algebraMap ℚ ℚ_[l]) = (vmap l (A := A) (B := A) f).charpoly := by
  intro K _ l _ hl A _ f P hPm hPd hP
  obtain ⟨hfree, hfin, -, -, hrkV⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  let δ : Polynomial ℤ → ℚ := fun F => (deg (A := A) (B := A) (Polynomial.aeval f F) : ℚ)
  have hmul : ∀ F G, δ (F * G) = δ F * δ G := by
    intro F G
    simp only [δ, map_mul]
    rw [End.mul_def, (GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K A A A _ _ rfl rfl).2]
    push_cast; ring
  have hpoly : ∀ (n : ℕ) (u : Fin n → Polynomial ℤ), ∃ Φ : MvPolynomial (Fin n) ℚ, Φ.IsHomogeneous (2 * A.dim) ∧
      ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) Φ = δ (∑ i, m i • u i) := by
    intro n u
    obtain ⟨Φ, hΦ, hΦe⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl n (fun i => Polynomial.aeval f (u i))
    refine ⟨Φ, hΦ, fun m => ?_⟩
    rw [hΦe m]
    simp only [δ, map_sum, map_zsmul]
  have hPn : ∀ n : ℤ, P.eval (n : ℚ) = δ (Polynomial.C n - Polynomial.X) := by
    intro n
    rw [hP n]
    simp only [δ, map_sub, map_intCast, Polynomial.aeval_C, Polynomial.aeval_X, algebraMap_int_eq, eq_intCast]
  have hroots := GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm (PadicAlgCl l) A.dim δ P hmul hpoly hPm hPd hPn
  apply GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq l
  · exact hPm.map _
  · exact LinearMap.charpoly_monic _
  · rw [Polynomial.natDegree_map, hPd, LinearMap.charpoly_natDegree, hrkV]
  · intro F
    have h1 : (P.map (algebraMap ℚ ℚ_[l])).aroots (PadicAlgCl l) = P.aroots (PadicAlgCl l) := by
      simp only [Polynomial.aroots, Polynomial.map_map]
      congr 2
    rw [h1]
    refine (congrArg norm (hroots F)).symm.trans ?_
    have h2 := GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' ℚ_[l] (PadicAlgCl l) (Vl l A) (vmap l f) (F.map (algebraMap ℤ ℚ_[l]))
    simp only [Polynomial.aeval_map_algebraMap] at h2
    rw [← h2]
    let ψ : End A →+* Module.End ℚ_[l] (Vl l A) :=
      (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)).toRingHom.comp (tend l A)
    have hψ : vmap l (A := A) (B := A) f = ψ f := rfl
    have hev : ∀ G : Polynomial ℤ, Polynomial.aeval (ψ f) G = ψ (Polynomial.aeval f G) := by
      intro G
      induction G using Polynomial.induction_on with
      | C a => simp
      | add p q hp hq => simp only [map_add, hp, hq]
      | monomial n a _ => simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, algebraMap_int_eq, eq_intCast, map_intCast]
    rw [hψ, hev F]
    have h3 : ψ (Polynomial.aeval f F) = (tend l A (Polynomial.aeval f F)).baseChange ℚ_[l] := rfl
    rw [h3, LinearMap.det_baseChange, PadicAlgCl.norm_extends]
    have h4 := GlobalTheory.T.padicNorm_degree_eq_padicNorm_det_tateModule K l hl A (Polynomial.aeval f F)
    have h5 : algebraMap ℚ (PadicAlgCl l) (δ F) = algebraMap ℚ_[l] (PadicAlgCl l) ((deg (A := A) (B := A) (Polynomial.aeval f F) : ℕ) : ℚ_[l]) := by
      simp only [δ, map_natCast]
    rw [h5, PadicAlgCl.norm_extends]
    rw [PadicInt.norm_def] at h4
    simpa using h4

end GlobalTheory.AV.AbVar
