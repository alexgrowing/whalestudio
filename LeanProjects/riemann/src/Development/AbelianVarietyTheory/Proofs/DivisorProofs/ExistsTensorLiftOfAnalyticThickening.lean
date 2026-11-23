import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem exists_tensorLift_of_DObj {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R]
    [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (S : K₀.DObj (et : Hol F₀.V →+* R) M) :
    ∃ ψ : R ⊗[ℂ] Hol (K₀.W S.T.k) →+* S.T.C, ∀ (d : R) (h : Hol (K₀.W S.T.k)),
      ψ (d ⊗ₜ[ℂ] h) = algebraMap R S.T.C d * S.T.ρ h := by
  letI : Algebra ℂ S.T.C := ((algebraMap R S.T.C).comp (algebraMap ℂ R)).toAlgebra
  let fR : R →ₐ[ℂ] S.T.C := { algebraMap R S.T.C with commutes' := fun _ ↦ rfl }
  let fH : Hol (K₀.W S.T.k) →ₐ[ℂ] S.T.C :=
    { S.T.ρ with
      commutes' := fun a ↦ by
        have h1 : algebraMap ℂ (Hol (K₀.W S.T.k)) a = K₀.cst S.T.k (algebraMap ℂ (Hol F₀.V) a) :=
          ((Hol.comap Prod.fst (fun _ _ ↦ analyticAt_fst) (K₀.base S.T.k)).commutes a).symm
        change S.T.ρ (algebraMap ℂ (Hol (K₀.W S.T.k)) a) = algebraMap R S.T.C (algebraMap ℂ R a)
        rw [h1, S.T.ρ_cst, S.compat]
        change algebraMap R S.T.C (et (algebraMap ℂ (Hol F₀.V) a)) = _
        rw [et.commutes] }
  refine ⟨(Algebra.TensorProduct.lift fR fH (fun _ _ ↦ Commute.all _ _)).toRingHom, fun d h ↦ ?_⟩
  exact Algebra.TensorProduct.lift_tmul _ _ _ d h

end GlobalTheory.AnPer
