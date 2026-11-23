import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralCombinationOfMemHaO
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem totalDegree_le_and_exists_combination_of_mem_FFV :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (a : ((E →+* ℂ) × ℕ → ℕ)) (n : ℕ), ∀ P₀ ∈ FFV (Dw := Dw) T a n, P₀.totalDegree ≤ DF Dw a ∧ ∃ (k : ℕ) (cf : Fin k → T.V) (Pi : Fin k → MvPolynomial (LtN Dw n) c.F), (∀ i, Pi i ∈ harmA c a n) ∧ P₀ = ∑ i, algebraMap T.V T.Fr (cf i) • MvPolynomial.map io (Pi i) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io a n P₀ hP
  haveI : CharZero T.Fr := charZero_of_injective_algebraMap (IsFractionRing.injective T.V T.Fr)
  haveI : CharZero c.F := io.charZero
  refine ⟨?_, ?_⟩
  · refine Finset.sup_le fun m hm => le_of_eq ?_
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP.1.2.2 m hm σ i
  · obtain ⟨s, cf, Q, hcf, hQ, hs⟩ := GlobalTheory.exists_integral_combination_of_mem_HaO (E →+* ℂ) Dw.mult n ℤ ℚ T.Fr
      (Rat.castHom T.Fr) (algebraMap T.V T.Fr).range (fun x => ⟨(x : T.V), by simp⟩)
      ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) P₀ hP
    choose cf' hcf' using hcf
    refine ⟨s, cf', fun i => MvPolynomial.map (Rat.castHom c.F) (Q i), fun i => ?_, ?_⟩
    · obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hQ i
      refine ⟨⟨PullbackSections.harmK_map _ h1, PullbackSections.rowInv_map _ h2, PullbackSections.rowDeg_map _ h3⟩, fun m => ?_⟩
      rw [MvPolynomial.coeff_map]
      obtain ⟨z, hz⟩ := h4 m
      rw [← hz]
      have : (Rat.castHom c.F) (algebraMap ℤ ℚ z) = (z : c.F) := by simp
      rw [this]
      exact intCast_mem _ z
    · rw [hs]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MvPolynomial.map_map, hcf' i, MvPolynomial.smul_eq_C_mul,
        Subsingleton.elim (io.comp (Rat.castHom c.F)) (Rat.castHom T.Fr)]

end GlobalTheory
