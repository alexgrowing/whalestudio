import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThEqClassicalThetaFunctionValuesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UnimodularSymplecticCoordinatesAndLatticeRank
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.NegOneZpowFormApplySemicharacter
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem exists_holomorphic_thetaConstants_of_family : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (w w' : J) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (d : ℕ) (B : Set (Fin d → ℂ)) (Q : (Fin d → ℂ) → (La →+ (Fin g → ℂ))) (Hm : (Fin d → ℂ) → Matrix (Fin g) (Fin g) ℂ), Odd N' → Function.Bijective EF → IsOpen B → (∀ x, DifferentiableOn ℂ (fun bb => Q bb x) B) → (∀ bb ∈ B, (Function.Injective (Q bb) ∧ DiscreteTopology ((Q bb)).range ∧ Submodule.span ℝ (Set.range (Q bb)) = ⊤ ∧ ((Hm bb)).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (Hm bb) z z).re) ∧ ∀ x y, (hermForm (Hm bb) ((Q bb) x) ((Q bb) y)).im = EF x y) ∧ ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q bb x) = Q bb (ac w x)) → (∀ x, ac w x + ac w' x = x) → (∀ x y, EF (ac w x) y = EF x (ac w' y)) → ∃ θ : (Fin d → ℂ) → Ix g (N' ^ 2) → ℂ, (∀ a, DifferentiableOn ℂ (fun z => θ z a) B) ∧ ∀ bb ∈ B, ∀ t : TObj g (N' ^ 2) J b (spMap em), (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH (Hm bb) χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ ((Q bb)).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = (Q bb) x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((N' ^ 2 : ℕ) : ℂ)⁻¹ • (Q bb) (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F ((Q bb) x) = (Q bb) (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.HasTh (𝟙 _) (θ bb) := by
  intro hL hL2 _ hU o _ g N' J b em w w' La _ EF lam ac d B Q Hm hN hE hB hQ hpol hsum hadj
  rcases B.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · exact ⟨0, fun _ => differentiableOn_empty, fun _ h => absurd h (Set.notMem_empty _)⟩
  obtain ⟨hp₀, F₀, hF₀⟩ := hpol b₀ hb₀
  obtain ⟨hfree, hfin, -, halt⟩ :=
    unimodular_symplectic_coordinates_and_lattice_rank.2 La EF g (Q b₀) (Hm b₀) hp₀
  have hadd : ∀ x y, ac w (x + y) = ac w x + ac w y := fun x y => hp₀.1 (by
    rw [map_add, ← hF₀, ← hF₀, ← hF₀, map_add, map_add])
  let W : La →ₗ[ℤ] La := (AddMonoidHom.mk' (ac w) hadd).toIntLinearMap
  have hW : ∀ x, W x = ac w x := fun _ => rfl
  have hW' : ∀ x, (LinearMap.id - W : La →ₗ[ℤ] La) x = ac w' x := fun x => by
    rw [LinearMap.sub_apply, LinearMap.id_apply, hW, sub_eq_iff_eq_add', hsum]
  have hsemi := neg_one_zpow_form_apply_semicharacter La EF W (LinearMap.id - W) halt
    (add_sub_cancel _ _) (fun x y => by rw [hW, hW', hadj])
  simp only [hW] at hsemi
  obtain ⟨θ, hθ, hhol⟩ := HolTheta.exists_theta_holomorphic La EF
    (fun x => (-1 : ℂ) ^ EF x (ac w x)) g d N' B Q Hm hN.pos hE
    (fun x => by
      rcases Int.even_or_odd (EF x (ac w x)) with h | h
      · exact Or.inl h.neg_one_zpow
      · exact Or.inr h.neg_one_zpow)
    hsemi hB hQ (fun bb hb => (hpol bb hb).1)
  let x : Ix g (N' ^ 2) → La := fun a => ∑ i, ((a i).val : ℤ) • lam i
  refine ⟨fun z a => (-1 : ℂ) ^ EF (x a) (ac w (x a)) *
      (Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm (Hm z) (Q z (x a)) (Q z (x a))) *
        θ z ((N' : ℂ)⁻¹ • Q z (x a))), fun a => (hhol (x a)).const_mul _, ?_⟩
  rintro bb hb t ⟨u, χ', hAH, hΛ, hχ, hpt, -⟩
  obtain ⟨hne, hdiff, hfe⟩ := hθ bb hb
  let lam' : Fin (2 * g) → u.Λ := fun i => ⟨Q bb (lam i), (hΛ _).2 ⟨_, rfl⟩⟩
  have hth : u.IsThetaFn (Hm bb) χ' 1 (θ bb) := by
    refine ⟨hdiff, fun l z => ?_⟩
    obtain ⟨y, hy⟩ := (hΛ l).1 l.2
    rw [pow_one, hχ y l hy.symm, ← hy, hfe]
  have key := T.hasTh_eq_classicalThetaFunction_values hL hL2 hU o g N' J b em t u (Hm bb) χ' (θ bb) lam' hN hAH hth hne
    (fun i => by rw [hpt i, Nat.cast_pow])
  have hx : ∀ a : Ix g (N' ^ 2),
      ∑ i, ((a i).val : ℂ) • (lam' i : Fin g → ℂ) = Q bb (x a) := fun a => by
    simp only [x, lam', map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [natCast_zsmul, Nat.cast_smul_eq_nsmul]
  have hx' : ∀ a : Ix g (N' ^ 2),
      χ' (∑ i, ((a i).val : ℤ) • lam' i) = (-1) ^ EF (x a) (ac w (x a)) := fun a => by
    refine hχ _ _ ?_
    simp only [x, lam', map_sum, map_zsmul, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
  simp only [hx, hx'] at key
  convert key using 2 with a
  exact (_root_.mul_assoc _ _ _).symm

end GlobalTheory
