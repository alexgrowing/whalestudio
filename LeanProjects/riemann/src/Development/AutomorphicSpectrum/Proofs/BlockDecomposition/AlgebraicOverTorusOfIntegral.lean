import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoTorus

theorem isAlgebraic_unit_inv {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    (A : Subalgebra K R) (u : Rˣ) (hu : (u : R) ∈ A) : IsAlgebraic A ((u⁻¹ : Rˣ) : R) := by
  refine ⟨Polynomial.C (⟨u, hu⟩ : A) * Polynomial.X - 1, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun p => Polynomial.coeff p 0) h
    simp at h1
  · simp [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_mul]

theorem isAlgebraic_unit_zpow {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    (A : Subalgebra K R) (u : Rˣ) (hu : (u : R) ∈ A) (m : ℤ) : IsAlgebraic A ((u ^ m : Rˣ) : R) := by
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · have h : IsAlgebraic A (u : R) := isAlgebraic_algebraMap (⟨u, hu⟩ : A)
    simpa using h.pow n
  · simpa using (isAlgebraic_unit_inv A u hu).pow n

theorem isAlgebraic_tpow {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ}
    (t : Fin d → Rˣ) (m : Fin d → ℤ) :
    IsAlgebraic (Algebra.adjoin K (Set.range fun k => (t k : R))) (tpow t m) := by
  set A := Algebra.adjoin K (Set.range fun k => (t k : R))
  have hmem : ∀ k, (t k : R) ∈ A := fun k => Algebra.subset_adjoin ⟨k, rfl⟩
  have key : ∀ s : Finset (Fin d), IsAlgebraic A (((∏ k ∈ s, t k ^ m k : Rˣ)) : R) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (isAlgebraic_one : IsAlgebraic A (1 : R))
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Units.val_mul]
      exact (isAlgebraic_unit_zpow A (t a) (hmem a) (m a)).mul ih
  exact key Finset.univ

theorem isAlgebraic_of_integral_torusS : ∀ {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ} (t : Fin d → Rˣ), (∀ r : R, IsIntegral (torusS K t Finset.univ) r) → Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun k => (t k : R))) R := by
  intro K R _ _ _ _ d t hint
  set A := Algebra.adjoin K (Set.range fun k => (t k : R)) with hA
  let S : Subalgebra A R := Subalgebra.algebraicClosure A R
  have hle : ∀ b : torusS K t Finset.univ, (b : R) ∈ S := by
    rintro ⟨b, hb⟩
    have : torusS K t Finset.univ ≤ S.restrictScalars K := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨m, -, rfl⟩
      exact (Subalgebra.mem_algebraicClosure A R).2 (isAlgebraic_tpow t m)
    exact this hb
  let φ : torusS K t Finset.univ →+* S :=
    { toFun := fun b => ⟨b, hle b⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨fun r => ?_⟩
  obtain ⟨p, hm, hp⟩ := hint r
  have hS : IsIntegral S r := by
    refine ⟨p.map φ, hm.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp
  exact hS.isAlgebraic.restrictScalars A

end GlobalTheory.CompanionTheory.GeoTorus
