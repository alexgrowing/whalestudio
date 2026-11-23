import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionSumMulMiddleCoordinate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSeriesSchwartzBruhatContinuousSchrodinger

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMixSum

variable {D : D7}

theorem finite_rat_mem {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) :
    {γ : Matrix (Fin m) (Fin n) D.host.E | rat γ ∈ K}.Finite := by
  obtain ⟨hg, hlc, hsc, ht2, hdisc, -⟩ := lattice_Mx D m n
  have hcl : IsClosed (ratMx D m n : Set (Mx D m n)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratMx D m n → Mx D m n) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (rat_injective (D := D) (m := m) (n := n)).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨rat γ, γ, rfl⟩, hγ, rfl⟩

theorem mixS_poinX : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → ∀ x, d.mixS T ψ v.μ v.𝓕 (poinX ψ d T β) x 0 = β x := by
  intro D ψ hψ S S₀ T ρ d v β hβ x
  have h := v.covol
  have hψc : Continuous ψ := hψ.1.1
  have hn : ∀ t, ‖ψ t‖ = 1 := hψ.1.2.1
  have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  obtain ⟨i1, i2, i3, -⟩ := lattice_Mx D T.rank ρ
  haveI : BorelSpace (Mx D T.rank ρ) := ⟨rfl⟩
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
  haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (Matrix (Fin T.rank) (Fin ρ) D.host.E) := inferInstanceAs (Countable (_ → _ → D.host.E))
  haveI : ContinuousSub (Mx D T.rank ρ) := @IsTopologicalAddGroup.to_continuousSub _ _ _ i1
  have hone : v.μ.real v.𝓕 = 1 := by rw [Measure.real, h.2.2, ENNReal.toReal_one]

  have hfin : {ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E | β (x + rat ξ) ≠ 0}.Finite := by
    refine (finite_rat_mem _ (hβ.supp.isCompact.image (continuous_sub_right x))).subset fun ξ hξ => ?_
    exact ⟨x + rat ξ, subset_tsupport β hξ, add_sub_cancel_left x (rat ξ)⟩

  have key : ∀ a, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T 0) (poinX ψ d T β))) 0 =
      ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * β (x + rat ξ) := by
    intro a
    rw [d.integrandS_eq, poinX_coords, ← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, symplOH_Y_X, ← d.symplOH_extX_extY T x a,
      ← d.symplOH_extX_extY T (x + 2 • rat ξ) a, map_add (d.extX T), two_nsmul, map_add (d.extX T), GlobalTheory.OrientedHeis.symplOH_add_left,
      GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.Core.Rk.ThetaOf.symplO_eq_add, neg_add_cancel_left]
  have hF := hasSum_integral_of_summable_integral_norm (μ := v.μ.restrict v.𝓕)
    (F := fun (ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E) a =>
      ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * β (x + rat ξ)) (fun ξ => ?_) ?_
  · rw [HypDec.mixS]
    simp only [key]
    refine hF.unique ?_
    have h0 : ∫ a in v.𝓕, ψ (symplO S T (d.extX T (rat 0)) (d.extY T a)) * β (x + rat 0) ∂v.μ = β x := by
      simp only [rat_zero, map_zero, GlobalTheory.Core.Rk.ThetaOf.symplO_eq_add, symplOH_zero_left, add_zero,
        AddChar.map_zero_eq_one, one_mul, setIntegral_const, hone, one_smul]
    rw [← h0]
    refine hasSum_single (f := fun ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E =>
      ∫ a in v.𝓕, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * β (x + rat ξ) ∂v.μ) 0 fun ξ hξ => ?_
    rw [integral_mul_const, GlobalTheory.Core.Rk.ThetaOf.integral_pair hψ d T h hξ, zero_mul]
  · refine Integrable.mul_const (Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun a => (hn _).le)) _
    exact (hψc.comp (GlobalTheory.Core.Rk.ThetaOf.continuous_symplO continuous_const hY)).measurable.aestronglyMeasurable
  · simp only [norm_mul, hn, one_mul, setIntegral_const, hone, one_smul]
    refine summable_of_finite_support (hfin.subset fun ξ hξ => ?_)
    exact fun h0 => (Function.mem_support.1 hξ) (by simp only [h0, norm_zero])

end GlobalTheory.BumpMixSum

end
