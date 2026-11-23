import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasisStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocalFactorFree

private theorem aux {R S M I : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite R M] [Module.Free R M]
    [Finite I] (e : S) (he : IsIdempotentElem e) [IsDomain (S ⧸ Ideal.span {1 - e})]
    [IsPrincipalIdealRing (S ⧸ Ideal.span {1 - e})]
    (b : Module.Basis I R (LinearMap.range (LinearMap.mulLeft R e))) :
    ∃ (h : ℕ) (y : Fin h → M), LinearIndependent R (fun q : I × Fin h => (b q.1 : S) • y q.2) ∧
      ∀ m : M, m ∈ Submodule.span R (Set.range fun q : I × Fin h => (b q.1 : S) • y q.2) ↔ (1 - e) • m = 0 := by
  classical
  let f : LinearMap.range (LinearMap.mulLeft R e) →ₗ[R] (S ⧸ Ideal.span {1 - e}) :=
    (Ideal.Quotient.mkₐ R (Ideal.span {1 - e})).toLinearMap ∘ₗ (Submodule.subtype _)
  have hf : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨_, s, rfl⟩ hs
      have h1 : e * s ∈ Ideal.span {1 - e} := Ideal.Quotient.eq_zero_iff_mem.1 hs
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h1
      apply Subtype.ext
      change e * s = 0
      have h2 : e * (e * s) = e * s := by rw [← _root_.mul_assoc, he.eq]
      rw [← h2, ← ht]
      linear_combination t * he.mul_one_sub_self
    · intro a
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
      refine ⟨⟨e * s, s, rfl⟩, ?_⟩
      change Ideal.Quotient.mk _ (e * s) = Ideal.Quotient.mk _ s
      rw [Ideal.Quotient.eq]
      exact Ideal.mem_span_singleton'.2 ⟨-s, by ring⟩
  let bA : Module.Basis I R (S ⧸ Ideal.span {1 - e}) := b.map (LinearEquiv.ofBijective f hf)
  haveI : Module.Finite R (S ⧸ Ideal.span {1 - e}) := Module.Finite.of_basis bA
  haveI : Module.Free R (S ⧸ Ideal.span {1 - e}) := Module.Free.of_basis bA
  let N : Submodule S M := Submodule.torsionBy S M (1 - e)
  haveI : Module.Finite R N := Module.Finite.of_injective (N.subtype.restrictScalars R) Subtype.val_injective
  letI : Module (S ⧸ Ideal.span {1 - e}) N := inferInstanceAs (Module (S ⧸ Submodule.span S {1 - e}) (Submodule.torsionBy S M (1 - e)))
  have hsm : ∀ (s : S) (n : N), (Ideal.Quotient.mk (Ideal.span {1 - e}) s) • n = s • n := fun _ _ => rfl
  haveI : IsScalarTower R (S ⧸ Ideal.span {1 - e}) N := ⟨fun r a n => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : r • Ideal.Quotient.mk (Ideal.span {1 - e}) s = Ideal.Quotient.mk (Ideal.span {1 - e}) (r • s) := rfl
    rw [this, hsm, hsm, smul_assoc]⟩
  haveI : Module.Finite (S ⧸ Ideal.span {1 - e}) N := Module.Finite.of_restrictScalars_finite R _ _
  haveI : Module.IsTorsionFree (S ⧸ Ideal.span {1 - e}) N := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a n han
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    obtain ⟨r, hr, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) a).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ha)
    have h1 : r • n = 0 := by
      rw [← algebraMap_smul (S ⧸ Ideal.span {1 - e}) r n, hc, mul_comm, mul_smul, han, smul_zero]
    have h2 : r • (n : M) = 0 := congrArg Subtype.val h1
    exact Subtype.ext ((smul_eq_zero.1 h2).resolve_left hr)
  let y := Module.finBasis (S ⧸ Ideal.span {1 - e}) N
  let B := bA.smulTower y
  have hB : (fun q : I × Fin _ => (b q.1 : S) • (y q.2 : M)) = (N.subtype.restrictScalars R) ∘ B := by
    funext q
    simp only [B, Function.comp, Module.Basis.smulTower_apply]
    rfl
  refine ⟨_, fun j => (y j : M), ?_, fun m => ?_⟩
  · rw [hB]
    exact B.linearIndependent.map' _ (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  · rw [hB, Set.range_comp, ← Submodule.map_span, B.span_eq, Submodule.map_top]
    constructor
    · rintro ⟨n, rfl⟩
      exact n.2
    · intro hm
      exact ⟨⟨m, hm⟩, rfl⟩

private theorem aux2 {R S I κ : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing S] [Algebra R S]
    [Fintype κ] [DecidableEq κ]
    [Finite I] (e : S) (he : IsIdempotentElem e) [IsDomain (S ⧸ Ideal.span {1 - e})]
    [IsPrincipalIdealRing (S ⧸ Ideal.span {1 - e})]
    (b : Module.Basis I R (LinearMap.range (LinearMap.mulLeft R e))) (ρ : S →ₐ[R] Matrix κ κ R) :
    ∃ (h : ℕ) (y : Fin h → κ → R), LinearIndependent R (fun q : I × Fin h => ρ (b q.1 : S) *ᵥ y q.2) ∧
      Submodule.span R (Set.range fun q : I × Fin h => ρ (b q.1 : S) *ᵥ y q.2) =
        LinearMap.range (Matrix.mulVecLin (ρ e)) := by
  letI : Module S (κ → R) := Module.compHom (κ → R) (ρ : S →+* Matrix κ κ R)
  have hsm : ∀ (s : S) (v : κ → R), s • v = ρ s *ᵥ v := fun _ _ => rfl
  haveI : IsScalarTower R S (κ → R) := ⟨fun r s v => by
    rw [hsm, hsm, map_smul, Matrix.smul_mulVec]⟩
  obtain ⟨h, y, h1, h2⟩ := aux (M := κ → R) e he b
  refine ⟨h, y, h1, ?_⟩
  ext m
  refine (h2 m).trans ⟨fun hm => ⟨m, ?_⟩, ?_⟩
  · change e • m = m
    rw [sub_smul, one_smul, sub_eq_zero] at hm
    exact hm.symm
  · rintro ⟨v, rfl⟩
    change (1 - e) • e • v = 0
    rw [← mul_smul, he.one_sub_mul_self, zero_smul]

theorem exists_free_generators : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]), ∃ (h : ℕ) (y : Fin h → κ → ℤ_[p]), LinearIndependent ℤ_[p] (fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) ∧ Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) := by
  intro p _ OE _ _ _ _ _ w b κ _ _ ρ
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.padic_unit_quotient_principal_basis p OE w
  exact aux2 w.e w.idem b ρ

end GlobalTheory.LocalFactorFree
