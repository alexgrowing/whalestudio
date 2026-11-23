import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ScalCompSpecMap

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExpandsFracLinear

open GlobalTheory.ExpandsLinear

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k n : ℕ) (c : Fin n → FractionRing R) (s : Fin n → U.SecK k) (E : Fin n → Fam D.toPre (FractionRing R) k) (s₀ : U.SecK k), (∀ l, U.Expands k (s l) (E l)) → (∀ jj, s₀.f jj = ∑ l, resTop _ (scal (pullback.snd G.hom (jK R)) (c l)) * (s l).f jj) → U.Expands k s₀ (∑ l, c l • E l) := by
  intro R _ _ I D A G _ _ U k n c s E s₀ hE hs
  simp only [UnifPre.Expands] at hE ⊢
  choose r hr σ f h1 h2 h3 using hE
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) (Finset.univ : Finset (Fin n))
    (fun l => c l / algebraMap R (FractionRing R) (r l))
  choose a ha using fun l => hb l (Finset.mem_univ l)
  have hc : ∀ l, algebraMap R (FractionRing R) (a l) * algebraMap R (FractionRing R) (r l) =
      algebraMap R (FractionRing R) (b : R) * c l := by
    intro l
    have hrl : algebraMap R (FractionRing R) (r l) ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
      exact fun h => hr l (IsFractionRing.injective R (FractionRing R) h)
    rw [ha l, Algebra.smul_def]
    field_simp
  refine ⟨b, nonZeroDivisors.ne_zero b.2, secComb (fun l => scal G.hom (a l)) σ,
    fun α => secComb (fun l => scal D.toPre.P.A.hom (a l)) (fun l => f l α), ?_, ?_, ?_⟩
  · exact secScal_comb (algebraMap R (FractionRing R)) U.LG.L _ _ _ _ (pullback.fst G.hom (jK R))
      (pullback.snd G.hom (jK R)) _ G.hom rfl pullback.condition s σ r a b c hc h1 s₀ hs
  · intro α
    refine secScal_comb (algebraMap R (FractionRing R)) D.toPre.P.L _ _ _ _ (D.toPre.prB (FractionRing R)).left
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left _ D.toPre.P.A.hom ?_ ?_ (fun l => (E l).s α)
      (fun l => f l α) r a b c hc (fun l => h2 l α) _ ?_
    · have hh := (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm
      unfold DegPre.BF TF at *
      rw [hh]
      congr 1
      show jFK (FractionRing R) ≫ jK R = _
      unfold jFK jK
      rw [← Spec.map_comp]
      rfl
    · exact Over.w (D.toPre.prB (FractionRing R))
    · intro j
      rw [fam_sum_f]
      simp only [smul_f]
      rfl
  · intro e
    exact expandsAt_linear R I D A G U k e n a σ f _ _ (fun l => h3 l e) (fun j => rfl) (fun α j => rfl)

end GlobalTheory.ExpandsFracLinear
