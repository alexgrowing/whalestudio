import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReducedFiniteTypeIffTestRing
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem exists_testRing_universal_partially_invertible (K : Type) [Field K] (σ : Type) [Finite σ]
    (D : σ → Prop) (p : TRing K) :
    ∃ (A : TRing K) (π : p.R →ₐ[K] A.R) (x : σ → A.R), (∀ i, D i → IsUnit (x i)) ∧
      ∀ (T : Type) [CommRing T] [Algebra K T] (ψ : p.R →ₐ[K] T) (t : σ → T), (∀ i, D i → IsUnit (t i)) →
        ∃! k : A.R →ₐ[K] T, k.comp π = ψ ∧ ∀ i, k (x i) = t i := by
  classical
  have := Fintype.ofFinite σ
  obtain ⟨hft, hred⟩ := (reduced_finiteType_iff_testRing K).2 p
  let P := MvPolynomial σ p.R
  let f : P := ∏ i ∈ Finset.univ.filter D, MvPolynomial.X i
  let B := Localization.Away f
  have hPred : _root_.IsReduced P := ⟨fun q hq => by
    ext i
    exact IsReduced.eq_zero _ (MvPolynomial.isNilpotent_iff.1 hq i)⟩
  have hBred : _root_.IsReduced B := isReduced_localizationPreserves (Submonoid.powers f) B hPred
  have hPft : Algebra.FiniteType K P := Algebra.FiniteType.trans hft inferInstance
  have hBft : Algebra.FiniteType K B :=
    Algebra.FiniteType.trans hPft (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) B)
  obtain ⟨A, ⟨e⟩⟩ := (reduced_finiteType_iff_testRing K).1 B hBft hBred
  let emb : P →ₐ[K] B := IsScalarTower.toAlgHom K P B
  let c : p.R →ₐ[K] P := IsScalarTower.toAlgHom K p.R P
  refine ⟨A, (e.symm : B →ₐ[K] A.R).comp (emb.comp c), fun i => e.symm (emb (MvPolynomial.X i)), ?_, ?_⟩
  · intro i hi
    refine IsUnit.map e.symm ?_
    have hf : IsUnit (emb f) := IsLocalization.Away.algebraMap_isUnit f
    refine isUnit_of_dvd_unit (map_dvd emb ?_) hf
    exact Finset.dvd_prod_of_mem _ (by simp [hi])
  · intro T _ _ ψ t ht
    let φ : P →ₐ[K] T := MvPolynomial.aevalTower ψ t
    have hφ : IsUnit (φ f) := by
      simp only [f, map_prod]
      refine IsUnit.prod_iff.2 fun i hi => ?_
      simp only [φ, P, MvPolynomial.aevalTower_X]
      exact ht i (by simpa using hi)
    have hφ' : ∀ y : Submonoid.powers f, IsUnit (φ y) := by
      rintro ⟨_, n, rfl⟩
      simpa using hφ.pow n
    let k₀ : B →ₐ[K] T := IsLocalization.liftAlgHom (M := Submonoid.powers f) hφ'
    have hk₀ : ∀ q, k₀ (emb q) = φ q := fun q => IsLocalization.lift_eq hφ' q
    refine ⟨k₀.comp (e : A.R →ₐ[K] B), ⟨?_, ?_⟩, ?_⟩
    · refine AlgHom.ext fun r => ?_
      change k₀ (e (e.symm (emb (c r)))) = ψ r
      rw [AlgEquiv.apply_symm_apply, hk₀]
      exact MvPolynomial.aevalTower_algebraMap ψ t r
    · intro i
      change k₀ (e (e.symm (emb (MvPolynomial.X i)))) = t i
      rw [AlgEquiv.apply_symm_apply, hk₀]
      exact MvPolynomial.aevalTower_X ψ t i
    · rintro k ⟨h1, h2⟩
      have h3 : ∀ q, k (e.symm (emb q)) = φ q := by
        intro q
        induction q using MvPolynomial.induction_on with
        | C r =>
          have := AlgHom.congr_fun h1 r
          exact this.trans (MvPolynomial.aevalTower_algebraMap ψ t r).symm
        | add a b ha hb => simp only [map_add, ha, hb]
        | mul_X a i ha =>
          simp only [map_mul, ha, h2]
          rw [show φ (MvPolynomial.X i) = t i from MvPolynomial.aevalTower_X ψ t i]
      have h4 : (k.comp (e.symm : B →ₐ[K] A.R)).toRingHom = k₀.toRingHom :=
        IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun q => (h3 q).trans (hk₀ q).symm)
      refine AlgHom.ext fun a => ?_
      have := RingHom.congr_fun h4 (e a)
      simpa using this

theorem exists_testRing_triRing :
    ∀ (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) (p : TRing K), ∃ (A : TRing K) (π : p.R →ₐ[K] A.R) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A.R) (s : (A.R)ˣ), TriRing m π X s := by
  intro K _ J _ m p
  classical
  obtain ⟨A, π, x, hx, hu⟩ := exists_testRing_universal_partially_invertible K
    (Option (Σ τ : J, {q : Fin (m τ) × Fin (m τ) // q.2 ≤ q.1}))
    (fun o => o.elim True fun z => z.2.1.1 = z.2.1.2) p
  refine ⟨A, π, fun τ => Matrix.of fun i j => if h : j ≤ i then x (some ⟨τ, ⟨(i, j), h⟩⟩) else 0,
    (hx none trivial).unit, ?_, ?_, ?_⟩
  · intro τ i
    simp only [Matrix.of_apply, le_refl, dif_pos]
    exact hx _ rfl
  · intro τ i j hij
    exact dif_neg (not_le.2 hij)
  · intro T _ _ ψ g a hg1 hg2
    obtain ⟨k, ⟨hk1, hk2⟩, hk3⟩ := hu T ψ (fun o => o.elim (a : T) fun z => g z.1 z.2.1.1 z.2.1.2) (by
      rintro (_ | ⟨τ, ⟨i, j⟩, h⟩) hD
      · exact a.isUnit
      · obtain rfl : i = j := hD
        exact hg1 τ i)
    refine ⟨k, ⟨hk1, fun τ => ?_, hk2 none⟩, ?_⟩
    · ext i j
      simp only [Matrix.map_apply, Matrix.of_apply]
      by_cases h : j ≤ i
      · rw [dif_pos h]
        exact hk2 _
      · rw [dif_neg h, map_zero, hg2 τ i j (not_le.1 h)]
    · rintro k' ⟨h1, h2, h3⟩
      refine hk3 k' ⟨h1, ?_⟩
      rintro (_ | ⟨τ, ⟨i, j⟩, h⟩)
      · exact h3
      · have := congrFun (congrFun (h2 τ) i) j
        simp only [Matrix.map_apply, Matrix.of_apply, dif_pos h] at this
        exact this

end GlobalTheory
