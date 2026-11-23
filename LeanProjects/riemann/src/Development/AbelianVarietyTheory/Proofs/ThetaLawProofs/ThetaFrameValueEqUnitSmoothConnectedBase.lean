import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamilyStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasAlgebraicChartsOfIsStandardSmooth
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedAndDenseComplHypersurface
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMvPolynomialOfPolyBoundOffHypersurface
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedUnramifiedCoverOfIrreducible
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsPrimitiveElementDiscriminantMultiple
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsConnectedPrincipalOpen
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.PrincipalOpenDenseComplexPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedBasicOpenComplexPointsOfDense
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.RootConst

open GlobalTheory.AffinePoints

theorem preconnectedSpace_algHom (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S]
    [Algebra.FiniteType ℂ S] : PreconnectedSpace (S →ₐ[ℂ] ℂ) := by
  have hc := isConnected_basicOpen_complexPoints_of_dense
    (exists_isConnected_principalOpen noetherNormalization_primitive
      (isConnected_unramified_cover_of_irreducible isConnected_and_dense_compl_hypersurface
        exists_mvPolynomial_of_poly_bound_off_hypersurface))
    (principalOpen_dense_complexPoints noetherNormalization_primitive
      isConnected_and_dense_compl_hypersurface) S 1 one_ne_zero
  refine ⟨(isEmbedding_coe (R := ℂ) (A := S) (C := ℂ)).isInducing.isPreconnected_image.1 ?_⟩
  convert hc.isPreconnected using 1
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨_, rfl, by simp⟩
  · rintro ⟨φ, rfl, -⟩
    exact ⟨φ, trivial, rfl⟩

theorem exists_chart (S : Type) [CommRing S] [Algebra ℂ S] [Algebra.Smooth ℂ S] (p : S →ₐ[ℂ] ℂ) :
    ∃ (d : ℕ) (e : OpenPartialHomeomorph (S →ₐ[ℂ] ℂ) (Fin d → ℂ)),
      IsAlgebraicChart e ∧ p ∈ e.source := by
  have := RingHom.ker_isPrime p
  obtain ⟨s, hs, J, K, _, _, ⟨Q⟩⟩ :=
    Algebra.IsSmoothAt.exists_notMem_isStandardSmooth ℂ (RingHom.ker p)
  have H : Algebra.IsStandardSmoothOfRelativeDimension Q.dimension ℂ (Localization.Away s) :=
    Q.isStandardSmoothOfRelativeDimension rfl
  exact ⟨Q.dimension, exists_isAlgebraicChart_of_away s (Localization.Away s) p hs⟩

theorem continuous_of_holomorphic_families (S : Type) [CommRing S] [Algebra ℂ S]
    [Algebra.Smooth ℂ S] (t : (S →ₐ[ℂ] ℂ) → ℂ)
    (h : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (S →ₐ[ℂ] ℂ)), IsOpen B →
      (∀ a : S, DifferentiableOn ℂ (fun p => s p a) B) → ContinuousOn (fun p => t (s p)) B) :
    Continuous t := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨d, e, he, hp⟩ := exists_chart S p
  have h1 := h d e.target e.symm e.open_target fun a => (he.analyticOnNhd a).differentiableOn
  have h2 : ContinuousOn t e.source :=
    (h1.comp e.continuousOn e.mapsTo).congr fun q hq => by
      simp only [Function.comp_apply, e.left_inv hq]
  exact h2.continuousAt (e.open_source.mem_nhds hp)

theorem eq_of_pow_eq_one {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {u : X → ℂ}
    (hu : Continuous u) {N : ℕ} (hN : 1 ≤ N) (h : ∀ x, u x ^ N = 1) (x y : X) : u x = u y := by
  have hfin : {z : ℂ | z ^ N = 1}.Finite := by
    refine (Polynomial.nthRootsFinset N (1 : ℂ)).finite_toSet.subset fun z hz => ?_
    exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset hN 1).2 hz)
  exact isPreconnected_univ.constant_of_mapsTo hfin.isDiscrete hu.continuousOn
    (fun z _ => h z) trivial trivial

theorem value_eq_unit_of_pow_eq : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → ∀ (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.Smooth ℂ S] (y : KeyIn S) (N : ℕ) (r : Sˣ) (t : (S →ₐ[ℂ] ℂ) → ℂ) (s₀ : S →ₐ[ℂ] ℂ), 1 ≤ N → (∀ s, ∃ x : KeyIn ℂ, KeyPB x y s.toRingHom ∧ (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t s = M.det ^ 4 / c ^ 8)) → (∀ s, t s ^ N = s r ^ N) → t s₀ = s₀ r → ∀ s, t s = s r := by
  intro hL hT hI S _ _ _ _ y N r t s₀ hN hx hpow h0 s
  have := preconnectedSpace_algHom S
  have ht : Continuous t := continuous_of_holomorphic_families S t fun m B σ hB hσ =>
    GlobalTheory.T.continuousOn_thetaFrameValue_holomorphicFamily hL hT hI S y m B σ (fun p => t (σ p)) hB hσ fun p _ => hx (σ p)
  have hr : ∀ q : S →ₐ[ℂ] ℂ, q r ≠ 0 := fun q => (r.isUnit.map q).ne_zero
  have hu : Continuous fun q : S →ₐ[ℂ] ℂ => t q / q r := ht.div (continuous_eval _) hr
  have h1 := eq_of_pow_eq_one hu hN
    (fun q => by rw [div_pow, hpow, div_self (pow_ne_zero N (hr q))]) s s₀
  rw [h0, div_self (hr s₀)] at h1
  exact (div_eq_one_iff_eq (hr s)).1 h1

end GlobalTheory.RootConst
