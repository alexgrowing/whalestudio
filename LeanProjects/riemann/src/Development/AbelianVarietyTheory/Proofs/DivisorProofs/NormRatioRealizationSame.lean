import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesUnitOfReadInjScaleRootConjRootCoordRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleRootOfPrintStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormRatioRealizationSameDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordOfIndep
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf

set_option autoImplicit false

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct

namespace GlobalTheory.BigOn.Exp

theorem seriesUnit : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → AtTw fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f f', rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      rdAt p w j hρ' ν' f' = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ u : FractionRing ((Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)), (∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1) ∧ f' = u • f := by
  intro h1 h2 h3 h4
  have hI := readInj
  have hS := GlobalTheory.T.scaleRoot_of_cuspRapidDecay_of_reciprocity_of_rayClassField h1 h2 h3 h4
  have hC := GlobalTheory.T.norm_ratio_realization_same_dual h1 h2 h3 h4
  have hR := coordRange
  unfold ReadInj at hI
  unfold ScaleRoot at hS
  unfold CoordRange at hR
  unfold AtTw AtPts at hI hS hC hR ⊢
  refine Closed.imp (Closed.and (Closed.and (Closed.and hI hS) hC) hR) ?_
  intro eps Fm CH _ h
  obtain ⟨x0, hx0⟩ := EvPt.and (EvPt.and (EvPt.and h.1.1.1 h.1.1.2) h.1.2) h.2
  refine ⟨x0, ?_⟩
  intro x hx hle i p hp hm w hw j ρ ρ' hρ hρ' ν ν' hpin hlev hpin' hSB hN hN' hR0 hR0' s h P hd hP f f' hf hf'
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hx0 x hx hle i p hp
  have hν : ν ≠ 0 := hN.1
  have hν' : ν' ≠ 0 := hN'.1
  have inj' := a1 hm w hw j ρ' hρ' ν hν
  have inj := a1 hm w hw j ρ hρ ν hν
  by_cases hf0 : f = 0
  · subst hf0
    have h0 : rdAt p w j hρ' ν' f' = rdAt p w j hρ' ν' 0 := by
      rw [hf', ← hf, map_zero, map_zero]
    have := a1 hm w hw j ρ' hρ' ν' hν' h0
    exact ⟨1, ⟨1, one_ne_zero, one_pow 1⟩, by rw [this, smul_zero]⟩
  · have hθ : ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P ≠ 0 := by
      intro h0
      apply hf0
      apply inj
      rw [hf, h0, map_zero]
    obtain ⟨n, hn, hnn⟩ := a2 hm w hw j ρ ρ' hρ hρ' ν ν' hpin hpin' hSB hN hN' hR0 hR0' s h P hd hP hθ
    obtain ⟨c, ⟨m, hm0, hcm⟩, hc⟩ := a3 hm w hw j ρ ρ' hρ hρ' ν ν' hpin hlev hpin' hSB hN hN' hR0 hR0' s h P hd hP f hf
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hm0] at hcm
      exact zero_ne_one hcm
    have hap := fun ν₁ g =>
      realRd_apply p.nexp p.v₀ hρ' ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ν₁ g
    have key : rdAt p w j hρ' ν f' = (ν' * ν⁻¹ * c⁻¹) • rdAt p w j hρ' ν f := by
      rw [hc, ← hf', smul_smul]
      have e1 := hap ν f'
      have e2 := hap ν' f'
      simp only [rdAt]
      rw [e1, e2, smul_smul]
      congr 1
      field_simp
    obtain ⟨u, hu⟩ := a4 hm w hw j ρ' hρ' ν _ hν f f' hf0 key
    refine ⟨u, ⟨n * m, mul_ne_zero hn hm0, ?_⟩, ?_⟩
    · apply (ρ'.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w)).injective
      rw [map_pow, map_one, hu, mul_pow, mul_pow, pow_mul ν', hnn, ← pow_mul, inv_pow, inv_pow,
        mul_inv_cancel₀ (pow_ne_zero _ hν), mul_comm n m, pow_mul c, hcm]
      simp
    · apply inj'
      rw [key, map_smulₛₗ, hu]

end GlobalTheory.BigOn.Exp
