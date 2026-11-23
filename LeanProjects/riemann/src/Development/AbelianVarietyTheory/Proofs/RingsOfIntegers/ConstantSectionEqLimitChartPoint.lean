import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupPointsOfIntegralChartSpec
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

namespace GlobalTheory.TransUnit

theorem ptOf_const_left : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (G : Over (Sp V)) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (X : limO V d 1 ⟶ G), IsLimit x X → ∀ (α : Fin d → V) (hα : Small α) (aV : Sp V ⟶ G.left), (∀ m : ℕ, ∃ ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] V ⧸ maximalIdeal V ^ (m + 1), (∀ p, ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (α p.2)) ∧ spMap (Ideal.Quotient.mk (maximalIdeal V ^ (m + 1))) ≫ aV = spMap (ψ : Jet V (Fin 1 × Fin d) m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ (x m).left) → ∀ n : ℕ, (ptOf X (Sm.const B α hα : Sm B n)).left = spMap (algebraMap V (PS V n d)) ≫ aV := by
  intro V _ _ _ _ _ d O _ _ B G x X hX α hα aV ha n
  let χ : PS V 1 d →ₐ[V] V :=
    GlobalTheory.mvEvalAdic V (maximalIdeal V) (fun p : Fin 1 × Fin d => α p.2) (fun p => hα p.2)
  have hχ : ∀ p, χ (MvPowerSeries.X p) = α p.2 := fun p => GlobalTheory.mvEvalAdic_X _ _ _ p
  have h1 : evA ![(Sm.const B α hα : Sm B n)] = (Algebra.ofId V (PS V n d)).comp χ := by
    refine AlgHom.ext fun f => (evA_apply _ f).trans ?_
    refine evC_eq_algHom _ (fun p : Fin 1 × Fin d => ((![(Sm.const B α hα : Sm B n)] : Fin 1 → Sm B n) p.1).2 p.2)
      _ (fun p => ?_) f
    obtain ⟨i, j⟩ := p
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [AlgHom.comp_apply, hχ]
    rfl
  have h2 : spMap (χ : PS V 1 d →+* V) ≫ X.left = aV := by
    refine GlobalTheory.hom_ext_of_isHausdorff (maximalIdeal V) fun m => ?_
    obtain ⟨ψ, hψ, e⟩ := ha m
    have hj : ∀ p : Fin 1 × Fin d, jetA (V := V) (Fin 1 × Fin d) m (MvPowerSeries.X p) =
        Ideal.Quotient.mk _ (MvPolynomial.X p) := fun p => by
      first
      | exact (mk_psTrunc m _ (MvPowerSeries.constantCoeff_X p)).trans (Chart.pj_X m p)
      | exact FBIdSy.mk_psTrunc_X m p
      | exact (mk_psTrunc m _ (MvPowerSeries.constantCoeff_X p)).symm.trans (Chart.pj_X m p)
    have k : ψ.comp (jetA (Fin 1 × Fin d) m) = (Ideal.Quotient.mkₐ V (maximalIdeal V ^ (m + 1))).comp χ := by
      have hv : ∀ p, (ψ.comp (jetA (Fin 1 × Fin d) m)) (MvPowerSeries.X p) = Ideal.Quotient.mk _ (α p.2) :=
        fun p => by rw [AlgHom.comp_apply, hj, hψ]
      have hv' : ∀ p, ((Ideal.Quotient.mkₐ V (maximalIdeal V ^ (m + 1))).comp χ) (MvPowerSeries.X p) =
          Ideal.Quotient.mk _ (α p.2) := fun p => by rw [AlgHom.comp_apply, hχ]; rfl
      refine AlgHom.ext fun f => ?_
      have := GlobalTheory.algHom_sub_mem_pow _ _
        (J := (maximalIdeal V).map (Ideal.Quotient.mk (maximalIdeal V ^ (m + 1))))
        (fun p => hv p ▸ Ideal.mem_map_of_mem _ (hα p.2)) (fun p => hv' p ▸ Ideal.mem_map_of_mem _ (hα p.2))
        (n := m + 1) (fun p => by rw [hv, hv', sub_self]; exact zero_mem _) f
      rw [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_bot, sub_eq_zero] at this
      exact this
    have k2 := GlobalTheory.PlaceFormPt.spMap_homAt (jetA (Fin 1 × Fin d) m) ψ X.left
    rw [k] at k2
    have k3 : (x m).left = (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetA (Fin 1 × Fin d) m)).left ≫ X.left :=
      (congrArg (fun q => q.left) (hX m)).symm
    refine Eq.trans ?_ (k2.symm.trans ((congrArg (_ ≫ ·) k3.symm).trans e.symm))
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ X.left) (Spec.map_comp _ _).symm)
  rw [← h2, ptOf, h1]
  exact (congrArg (· ≫ X.left) (Spec.map_comp (CommRingCat.ofHom (χ : PS V 1 d →+* V))
    (CommRingCat.ofHom (algebraMap V (PS V n d))))).trans (Category.assoc _ _ _)

end GlobalTheory.TransUnit
