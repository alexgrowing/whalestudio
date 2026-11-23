import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulCoeEqZero
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqTan
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv GlobalTheory.ExpUniqCh0

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetOneTan

theorem jetOne_tan_span : ∀ {S : Type} [CommRing S] {ρ : Type} [Fintype ρ] [DecidableEq ρ],
    (∀ r : ρ, (jetTrunc : Jet S ρ (0 + 1) →ₐ[S] Jet S ρ 0) (Ideal.Quotient.mk _ (MvPolynomial.X r)) = 0) ∧
    ∀ p : Jet S ρ (0 + 1), (jetTrunc : Jet S ρ (0 + 1) →ₐ[S] Jet S ρ 0) p = 0 →
      (∀ r, ((jetTan r : Jet S ρ (0 + 1) →ₐ[S] DualNumber S) p).fst = 0) ∧
      p = ∑ r, ((jetTan r : Jet S ρ (0 + 1) →ₐ[S] DualNumber S) p).snd •
        (Ideal.Quotient.mk _ (MvPolynomial.X r) : Jet S ρ (0 + 1)) := by
  intro S _ ρ _ _
  refine ⟨fun r => ?_, fun p hp => ?_⟩
  · show Ideal.Quotient.mk _ (MvPolynomial.X r) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact Ideal.subset_span ⟨r, rfl⟩
  have hI : p ∈ Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.Ij S ρ (0 + 1) := by
    have := Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.mem_pow_of_trunc_eq_zero p hp
    rwa [pow_one] at this
  have hfst : ∀ r, ((Formalism.L2.Pj.jetTan r : Formalism.L2.Pj.Jet S ρ (0 + 1) →ₐ[S] DualNumber S) p).fst = 0 := by
    intro r
    obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun (R := Formalism.L2.Pj.Jet S ρ (0 + 1))).1 hI
    rw [← hc, map_sum, TrivSqZeroExt.fst_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_mul, Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan.jetTan_alt, TrivSqZeroExt.fst_mul]
    split_ifs
    · rw [DualNumber.fst_eps, mul_zero]
    · rw [TrivSqZeroExt.fst_zero, mul_zero]
  refine ⟨hfst, ?_⟩
  rw [← sub_eq_zero]
  refine Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan.eq_zero_of_tan _ ?_ fun l => ?_
  · refine Ideal.sub_mem _ hI (Ideal.sum_mem _ fun r _ => ?_)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨r, rfl⟩)
  · rw [map_sub, map_sum]
    have e : ∀ r ∈ (Finset.univ : Finset ρ),
        (Formalism.L2.Pj.jetTan l : Formalism.L2.Pj.Jet S ρ (0 + 1) →ₐ[S] DualNumber S)
          (((Formalism.L2.Pj.jetTan r : Formalism.L2.Pj.Jet S ρ (0 + 1) →ₐ[S] DualNumber S) p).snd •
            (Ideal.Quotient.mk _ (MvPolynomial.X r) : Formalism.L2.Pj.Jet S ρ (0 + 1))) =
        if l = r then ((Formalism.L2.Pj.jetTan r : Formalism.L2.Pj.Jet S ρ (0 + 1) →ₐ[S] DualNumber S) p).snd •
          (DualNumber.eps : DualNumber S) else 0 := by
      intro r _
      rw [map_smul]
      have := Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan.jetTan_alt (R := S) l r
      erw [this]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · exact smul_zero _
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq, if_pos (Finset.mem_univ l)]
    ext
    · rw [TrivSqZeroExt.fst_sub, hfst, TrivSqZeroExt.fst_smul, DualNumber.fst_eps, smul_zero, sub_zero,
        TrivSqZeroExt.fst_zero]
    · rw [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_smul, DualNumber.snd_eps, smul_eq_mul, _root_.mul_one, sub_self,
        TrivSqZeroExt.snd_zero]

end GlobalTheory.JetOneTan
