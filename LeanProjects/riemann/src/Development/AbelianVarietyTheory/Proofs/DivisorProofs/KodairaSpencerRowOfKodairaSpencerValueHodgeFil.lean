import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSRowsFil

theorem isKSRow_of_isKSValue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (θ : Matrix (Fin n) (Fin n) K) (s : K), (∀ σ k, IsTangent (ub σ k)) → (∀ a b, (e.symm a).1 ≠ conjEmb (e.symm b).1 → θ a b = 0) → (∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w, IsLieComb (fun a => s * ∑ b, θ a b * ψ f (hb (e.symm b))) (fun a => ub (e.symm a).1 (e.symm a).2) w → GlobalTheory.DeRham.IsKSValue h f w) → ∀ (τ : E →+* ℂ) (a₀ : Fin (Dw.mult (conjEmb τ))), (∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w) → ∃ w, IsLieComb (fun b => s * θ (e ⟨τ, b⟩) (e ⟨conjEmb τ, a₀⟩)) (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w := by
  intro E _ _ _ H Dw K _ A _ A' _ i h hA ψ ub hb n e θ s htan hθ hKS τ a₀ hrow
  obtain ⟨w₀, f, hfF, hf, -⟩ := hrow
  haveI : IsCommMonObj A := hA.comm
  have hcc : ∀ σ : E →+* ℂ, conjEmb (conjEmb σ) = σ := fun σ ↦ RingHom.ext fun x ↦ Complex.conj_conj _
  have hc : ∀ a, s * ∑ b, θ a b * ψ f (hb (e.symm b)) = s * θ a (e ⟨conjEmb τ, a₀⟩) := by
    intro a
    congr 1
    rw [Finset.sum_eq_single (e ⟨conjEmb τ, a₀⟩)]
    · rw [hf, Equiv.symm_apply_apply, if_pos rfl, mul_one]
    · intro b _ hb'
      rw [hf, if_neg, mul_zero]
      intro hq
      exact hb' (by rw [← hq, Equiv.apply_symm_apply])
    · intro hn; exact absurd (Finset.mem_univ _) hn
  refine ⟨GlobalTheory.SqZero.tanExp (ub τ) (fun b ↦ s * θ (e ⟨τ, b⟩) (e ⟨conjEmb τ, a₀⟩)),
    (GlobalTheory.LieComb.isLieComb_iff_tanExp _ _).2 rfl, f, hfF, hf, hKS f hfF _ ?_⟩
  rw [GlobalTheory.LieComb.isLieComb_iff_tanExp]
  symm
  simp only [GlobalTheory.SqZero.tanExp, GlobalTheory.SqZero.lieExp, hc]
  rw [Fintype.prod_equiv e.symm _ (fun p : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) ↦
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo K (TrivSqZeroExt.inr (s * θ (e p) (e ⟨conjEmb τ, a₀⟩)) : DualNumber K)
        (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ ub p.1 p.2) (fun a ↦ by simp only [Equiv.apply_symm_apply]),
    Fintype.prod_sigma, Finset.prod_eq_single τ]
  · intro σ _ hσ
    refine Finset.prod_eq_one fun k _ ↦ GlobalTheory.SqZero.epsTo_zero_comp ((ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).2 (htan σ k)) _ ?_ _
    rw [hθ _ _ (by simpa [hcc] using hσ), mul_zero, TrivSqZeroExt.inr_zero]
  · intro hn; exact absurd (Finset.mem_univ _) hn

end GlobalTheory.KSRowsFil
