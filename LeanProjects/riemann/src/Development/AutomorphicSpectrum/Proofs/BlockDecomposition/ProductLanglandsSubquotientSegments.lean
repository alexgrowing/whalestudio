import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCuspProdIrr
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

noncomputable section

namespace GlobalTheory.CompanionTheory.LProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLSeg_append {p q : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (Δ₁ : Fin p → Segment k)
    (Δ₂ : Fin q → Segment k) (h₁ : ∀ i, IsLSeg (Δ₁ i) (x i).rep) (h₂ : ∀ i, IsLSeg (Δ₂ i) (y i).rep)
    (i : Fin (p + q)) : IsLSeg (Fin.append Δ₁ Δ₂ i) (Fin.append x y i).rep := by
  induction i using Fin.addCases with
  | left i => rw [Fin.append_left, Fin.append_left]; exact h₁ i
  | right i => rw [Fin.append_right, Fin.append_right]; exact h₂ i

theorem map_append {p q : ℕ} (Δ₁ : Fin p → Segment k) (Δ₂ : Fin q → Segment k) :
    Finset.univ.val.map (Fin.append Δ₁ Δ₂) = Finset.univ.val.map Δ₁ + Finset.univ.val.map Δ₂ := by
  rw [Fin.univ_val_map, Fin.univ_val_map, Fin.univ_val_map, List.ofFn_fin_append]
  rfl

theorem prod₂_isSubquotient_append {r t p q : ℕ} {U W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) U) (ρ : Representation ℂ (GL (Fin t) k) W)
    (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hd : ∑ i, (Fin.append x y i).1 = r + t) (h₁ : IsSubquotient σ (prodIrr x hx))
    (h₂ : IsSubquotient ρ (prodIrr y hy)) : IsSubquotient (prod₂ σ ρ) (prodIrr (Fin.append x y) hd) := by
  obtain ⟨F⟩ := GlobalTheory.T.product_irreducible_append_equiv k p q r t x y hx hy hd
  exact GlobalTheory.CompanionTheory.Ysupp.isSubquotient_of_prod₂_equiv (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)
    h₁ h₂ (Representation.Equiv.refl _) F

end GlobalTheory.CompanionTheory.LProd

theorem GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (a b : IrrGL k), IsL 𝔪 a.rep → IsL 𝔫 b.rep → ∃ (h : ℕ) (z : Fin h → IrrGL k) (Δ : Fin h → Segment k) (hd : ∑ i, (z i).1 = a.1 + b.1), (∀ i, IsLSeg (Δ i) (z i).rep) ∧ Finset.univ.val.map Δ = 𝔪 + 𝔫 ∧ IsSubquotient (prod₂ a.rep b.rep) (prodIrr z hd) := by
  intro k _ _ _ _ _ 𝔪 𝔫 a b ha hb
  obtain ⟨p, x, hx, ⟨Δ₁, hO₁, hL₁⟩, hc₁⟩ := ha
  obtain ⟨q, y, hy, ⟨Δ₂, hO₂, hL₂⟩, hc₂⟩ := hb
  have hd : ∑ i, (Fin.append x y i).1 = a.1 + b.1 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, hx, hy]
  refine ⟨p + q, Fin.append x y, Fin.append Δ₁ Δ₂, hd, GlobalTheory.CompanionTheory.LProd.isLSeg_append x y Δ₁ Δ₂ hL₁ hL₂, ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.LProd.map_append, hO₁.1, hO₂.1]
  · exact GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_append _ _ x y hx hy hd hc₁.isSubquotient hc₂.isSubquotient

end
