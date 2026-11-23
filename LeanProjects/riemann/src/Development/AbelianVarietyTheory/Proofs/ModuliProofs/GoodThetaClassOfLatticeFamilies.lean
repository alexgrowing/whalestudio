import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UnimodularSymplecticCoordinatesAndLatticeRank
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectOfPolarisedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicThetaConstantsPolarisedLatticesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLatticeAutOfIsomorphicThetaObjectsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesShapeComplexStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ShapeOfUniformisedThetaObjectStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem countable_addEquiv_of_free_finite (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] :
    Countable (La ≃+ La) := by
  let bas := Module.Free.chooseBasis ℤ La
  haveI : Countable La := bas.equivFun.injective.countable
  have hinj : Function.Injective (fun (gm : La ≃+ La) (i : Module.Free.ChooseBasisIndex ℤ La) => gm (bas i)) := by
    intro gm gm' h
    have h2 : gm.toAddMonoidHom.toIntLinearMap = gm'.toAddMonoidHom.toIntLinearMap :=
      bas.ext (fun i => congrFun h i)
    ext x
    exact LinearMap.congr_fun h2 x
  exact hinj.countable

theorem goodClass_of_lattice_families : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d r : ℕ) (La : Fin r → Type) [∀ i, AddCommGroup (La i)] (EF : ∀ i, LinearMap.BilinForm ℤ (La i)) (lam : ∀ i, Fin (2 * g) → La i) (ac : ∀ i, J → La i → La i) (B : Fin r → Set (Fin d → ℂ)) (Q : ∀ i, (Fin d → ℂ) → (La i →+ (Fin g → ℂ))) (Hm : Fin r → (Fin d → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ t t', C t → TMap t' t (𝟙 _) → C t') → (∀ t, C t → t.Prim w w') → (∀ i, Function.Bijective (EF i) ∧ IsOpen (B i) ∧ IsPreconnected (B i) ∧ (∀ x, DifferentiableOn ℂ (fun bb => Q i bb x) (B i)) ∧ (∀ x, ac i w x + ac i w' x = x) ∧ (∀ x y, EF i (ac i w x) y = EF i x (ac i w' y)) ∧ (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF i (lam i i₁) (lam i i₂) : ℂ) / ((N' ^ 2 : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) ∧ (∀ j₁ i₁, ∃ y, ac i j₁ (lam i i₁) = ∑ i', Mat j₁ i' i₁ • lam i i' + (N' ^ 2) • y) ∧ (∀ bb ∈ B i, (Function.Injective (Q i bb) ∧ DiscreteTopology ((Q i bb)).range ∧ Submodule.span ℝ (Set.range (Q i bb)) = ⊤ ∧ ((Hm i bb)).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (Hm i bb) z z).re) ∧ ∀ x y, (hermForm (Hm i bb) ((Q i bb) x) ((Q i bb) y)).im = EF i x y) ∧ ∀ j₁, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q i bb x) = Q i bb (ac i j₁ x)) ∧ ∀ y, y ≠ 0 → (hermForm (Hm i bb) (F y) (F y)).re < κ * (hermForm (Hm i bb) y y).re) ∧ (∀ bb ∈ B i, ∀ z' ∈ B i, (∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, Q i z' x = h (Q i bb x)) → bb = z') ∧ ∀ bb ∈ B i, ∀ t : TObj g (N' ^ 2) J b (spMap em), (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH (Hm i bb) χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ ((Q i bb)).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = (Q i bb) x → χ' l = (-1) ^ EF i x (ac i w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((N' ^ 2 : ℕ) : ℂ)⁻¹ • (Q i bb) (lam i i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F ((Q i bb) x) = (Q i bb) (ac i j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.Prim w w' → C t) → (∀ t, C t → ∃ i, ∃ bb ∈ B i, (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH (Hm i bb) χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ ((Q i bb)).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = (Q i bb) x → χ' l = (-1) ^ EF i x (ac i w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((N' ^ 2 : ℕ) : ℂ)⁻¹ • (Q i bb) (lam i i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F ((Q i bb) x) = (Q i bb) (ac i j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀)) → GoodClass em C Mat κ w w' d := by
  intro h1 h2 h3 h4 g J _ Mat κ n w w' hn hodd
  obtain ⟨j₀, hqt⟩ := GlobalTheory.T.thetaPoint_determines_shape_complex h1 h2 g J Mat κ n hn hodd
  refine ⟨max j₀ 1, ?_⟩
  intro j hj N' hN' o _ b em C d r La _ EF lam ac B Q Hm hiso hprim hfam hcov
  subst hN'
  have hj0 : j ≥ j₀ := le_trans (le_max_left _ _) hj
  have hj1 : j ≠ 0 := by have := le_trans (le_max_right _ _) hj; omega
  have hth := fun i => GlobalTheory.T.exists_holomorphic_thetaConstants_polarisedLattices h1 h2 h3 h4 o g (n ^ j) J b em w w' (La i) (EF i) (lam i) (ac i) d (B i) (Q i) (Hm i)
    hodd.pow (hfam i).1 (hfam i).2.1 (hfam i).2.2.2.1
    (fun bb hbb => ⟨((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).1,
      (((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).2 w).imp fun F hF => hF.1⟩)
    (hfam i).2.2.2.2.1 (hfam i).2.2.2.2.2.1
  choose θ hθd hθ using hth
  have hsh := fun i bb (hbb : bb ∈ B i) t ht => GlobalTheory.T.shape_of_uniformised_theta_object h1 h2 h3 h4 o g ((n ^ j) ^ 2) J b em w w' t (La i) (EF i)
    (lam i) (ac i) (Q i bb) (Hm i bb) Mat κ ht (hfam i).2.2.2.2.2.2.2.1 ((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).2
  have hbuild := fun i bb (hbb : bb ∈ B i) => GlobalTheory.T.exists_thetaObject_of_polarisedLattice h1 h2 h3 h4 o g ((n ^ j) ^ 2) J b em w w' (La i) (EF i)
    (lam i) (ac i) (Q i bb) (Hm i bb) (hfam i).1 ((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).1
    (fun j₁ => (((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).2 j₁).imp fun F hF => hF.1)
    (hfam i).2.2.2.2.1 (hfam i).2.2.2.2.2.1 (hfam i).2.2.2.2.2.2.1
  refine ⟨hiso, fun t ht => ⟨?_, hprim t ht⟩, r, B, θ, fun i => ⟨(hfam i).2.1, (hfam i).2.2.1, hθd i, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · obtain ⟨i, bb, hbb, hu⟩ := hcov t ht
    exact hsh i bb hbb t hu
  · obtain ⟨t, htp, hu⟩ := hbuild i z hz
    exact ⟨t, (hfam i).2.2.2.2.2.2.2.2.2.2 z hz t hu htp, hθ i z hz t hu⟩
  · obtain ⟨hfree, hfin, -⟩ := unimodular_symplectic_coordinates_and_lattice_rank.2 (La i) (EF i) g (Q i z) (Hm i z)
      ((hfam i).2.2.2.2.2.2.2.2.1 z hz).1
    haveI := countable_addEquiv_of_free_finite (La i)
    have hc : (⋃ gm : La i ≃+ La i, {z' ∈ B i | ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
        ∀ x, h (Q i z' x) = Q i z (gm x)}).Countable := by
      refine Set.countable_iUnion fun gm => Set.Subsingleton.countable ?_
      rintro z₁ ⟨hz₁, k₁, hk₁⟩ z₂ ⟨hz₂, k₂, hk₂⟩
      refine (hfam i).2.2.2.2.2.2.2.2.2.1 z₁ hz₁ z₂ hz₂ ⟨k₁.trans k₂.symm, fun x => ?_⟩
      rw [LinearEquiv.trans_apply, hk₁, ← hk₂, LinearEquiv.symm_apply_apply]
    refine hc.mono ?_
    rintro z' ⟨hz', c, hcz⟩
    obtain ⟨t, -, hu⟩ := hbuild i z hz
    obtain ⟨t', -, hu'⟩ := hbuild i z' hz'
    have ht' := hθ i z' hz' t' hu'
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨a, ha⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh h1 h2 o g (n ^ j) J b _ _ t' n ℂ (𝟙 _) (θ i z') ⊥ hn.two_le
        (dvd_pow_self n hj1) ht' Ideal.isPrime_bot 0
      apply ha
      rw [hcz]
      simp
    rw [hcz] at ht'
    have hm := hqt j hj0 o b em t t' (θ i z) c hc0 (hsh i z hz t hu) (hsh i z' hz' t' hu') (hθ i z hz t hu) ht'
    obtain ⟨gm, h, hgm⟩ := GlobalTheory.T.exists_lattice_aut_of_isomorphic_theta_objects o g ((n ^ j) ^ 2) J b em w w' t t' (La i) (EF i) (lam i) (ac i) (Q i z) (Q i z')
      (Hm i z) (Hm i z') ((hfam i).2.2.2.2.2.2.2.2.1 z hz).1.1 ((hfam i).2.2.2.2.2.2.2.2.1 z' hz').1.1 hu hu' hm
    exact Set.mem_iUnion.2 ⟨gm, hz', h, hgm⟩
  · intro t ht
    obtain ⟨i, bb, hbb, hu⟩ := hcov t ht
    exact ⟨i, bb, hbb, hθ i bb hbb t hu⟩

end GlobalTheory
