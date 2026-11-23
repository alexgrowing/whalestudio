import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentOverBaseRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFramedLiftsEquivMovedGroupCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardFramedLiftsLevelCoverConstStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevModel

theorem cover_degree_const : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E), (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0 ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ (π k₂) (δ k₂)) → ∃ N : ℕ, 0 < N ∧ ∀ k, ∑ᶠ k₂ : {k₂ // π k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ = N := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ pr δ hπ
  classical
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  letI : Field (CAt σ₂) := inferInstanceAs (Field ℂ)
  letI : IsAlgClosed (CAt σ₂) := inferInstanceAs (IsAlgClosed ℂ)
  have hC := GlobalTheory.T.complexFramedLifts_equiv_movedGroupCosets D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ pr δ hπ
  have hK := GlobalTheory.T.card_framed_lifts_levelCover_const D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂
  have hfin : ∀ k (k₂ : {k₂ // pr k₂ = k}), Finite (↥((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ⧸ (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).subgroupOf ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ) := by
    intro k k₂
    have h := (hπ k₂.1).2.2.2.1
    rw [k₂.2] at h
    exact Subgroup.index_ne_zero_iff_finite.1 h
  have hS : ∀ k (x' : ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).dom), (∑ᶠ k₂ : {k₂ // pr k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ) = Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k x')} ∧ Finite {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k x')} := by
    intro k x'
    obtain ⟨e⟩ := hC k x'
    haveI := hfin k
    refine ⟨?_, Finite.of_equiv _ e.symm⟩
    rw [Nat.card_congr e, Nat.card_sigma, finsum_eq_sum_of_fintype]
    rfl
  have hne : ∀ y : FrPt Xo c (CAt σ₂), Nonempty {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} := by
    intro y
    obtain ⟨-, -, -, -, -, -, hlift, -, -⟩ := hd
    obtain ⟨y₂, hy₂⟩ := hlift (CAt σ₂) (fun _ => rfl) y
    exact ⟨⟨y₂, hy₂⟩⟩
  by_cases hc : Nonempty (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp
  · obtain ⟨k₀⟩ := hc
    obtain ⟨x₀, hx₀⟩ := GlobalTheory.UnifFamily.dom_nonempty ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k₀)
    refine ⟨Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k₀ ⟨x₀, hx₀⟩)}, ?_, fun k => ?_⟩
    · haveI := (hS k₀ ⟨x₀, hx₀⟩).2
      haveI := hne ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k₀ ⟨x₀, hx₀⟩)
      exact Nat.card_pos
    · obtain ⟨x, hx⟩ := GlobalTheory.UnifFamily.dom_nonempty ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k)
      rw [(hS k ⟨x, hx⟩).1]
      exact hK _ _
  · refine ⟨1, one_pos, fun k => (hc ⟨k⟩).elim⟩

end GlobalTheory.LevModel
