import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGL.SumProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ}

theorem sum_fst_of_lFactors {𝔪 : Multiset (Segment k)} {h : ℕ} {x : Fin h → IrrGL k} (hx : LFactors 𝔪 x) :
    ∑ a, (x a).1 = (𝔪.map Segment.deg).sum := by
  obtain ⟨Δ, ⟨rfl, -⟩, hΔ⟩ := hx
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact Finset.sum_congr rfl fun a _ => (hΔ a).deg_eq.symm

theorem deg_of_isL {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) :
    (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, hd, hx, -⟩ := h
  exact (sum_fst_of_lFactors hx).symm.trans hd

theorem exists_isLSeg_of_isL {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π)
    {Δ : Segment k} (hΔ : Δ ∈ 𝔪) : ∃ y : IrrGL k, IsLSeg Δ y.rep := by
  obtain ⟨_, x, -, ⟨D, ⟨rfl, -⟩, hD⟩, -⟩ := h
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hΔ
  exact ⟨x a, hD a⟩

theorem exists_isL [CharZero k] (hS : StandardCosocleGL) {𝔪 : Multiset (Segment k)}
    (h : ∀ Δ ∈ 𝔪, ∃ y : IrrGL k, IsLSeg Δ y.rep) (hN : (𝔪.map Segment.deg).sum = N) :
    ∃ π : IrrRep (GL (Fin N) k), IsL 𝔪 π.ρ := by
  obtain ⟨D, hD⟩ := exists_isOrderedForm 𝔪
  have hm : ∀ i, D i ∈ 𝔪 := fun i => hD.1 ▸ Multiset.mem_map_of_mem D (Finset.mem_univ i)
  choose x hx using fun i => h _ (hm i)
  have hF : LFactors 𝔪 x := ⟨D, hD, hx⟩
  have hd : ∑ a, (x a).1 = N := (sum_fst_of_lFactors hF).trans hN
  obtain ⟨π, hπ⟩ := hS k 𝔪 _ _ x hd hF
  exact ⟨π, _, x, hd, hF, hπ⟩

theorem isL_add_of_equiv_prod₂ : LanglandsMultisegments → StandardCosocleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (r t : ℕ) (σ : IrrRep (GL (Fin r) k)) (τ : IrrRep (GL (Fin t) k)) (π : IrrRep (GL (Fin (r + t)) k)) (𝔪 𝔫 : Multiset (Segment k)), IsL 𝔪 σ.ρ → IsL 𝔫 τ.ρ → Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) → IsL (𝔪 + 𝔫) π.ρ := by
  rintro hM hS k _ _ _ _ _ r t σ τ π 𝔪 𝔫 h1 h2 ⟨e⟩
  obtain ⟨y, hy⟩ := exists_isL (N := r + t) hS (𝔪 := 𝔪 + 𝔫)
    (fun Δ hΔ => (Multiset.mem_add.1 hΔ).elim (exists_isLSeg_of_isL h1) (exists_isLSeg_of_isL h2))
    (by rw [Multiset.map_add, Multiset.sum_add, deg_of_isL h1, deg_of_isL h2])
  have hd : ∑ a, (![IrrGL.of σ.ρ σ.smooth σ.irr, IrrGL.of τ.ρ τ.smooth τ.irr] a).1 = r + t := Fin.sum_univ_two _
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr σ.ρ σ.smooth σ.irr τ.ρ τ.smooth τ.irr hd
  have ψ := IrrGL.equivOf y.ρ y.smooth y.irr
  have a1 : IsL 𝔪 (IrrGL.of σ.ρ σ.smooth σ.irr).rep := h1.of_equiv (IrrGL.equivOf _ _ _)
  have a2 : IsL 𝔫 (IrrGL.of τ.ρ τ.smooth τ.irr).rep := h2.of_equiv (IrrGL.equivOf _ _ _)
  have a3 : IsL (𝔪 + 𝔫) (IrrGL.of y.ρ y.smooth y.irr).rep := hy.of_equiv ψ
  have hs := (hM k).2 𝔪 𝔫 ![IrrGL.of σ.ρ σ.smooth σ.irr, IrrGL.of τ.ρ τ.smooth τ.irr]
    (IrrGL.of y.ρ y.smooth y.irr) hd a1 a2 a3
  have E := (e.trans φ).symm
  obtain ⟨θ⟩ := IsSubquotient.nonempty_equiv
    (hs.trans (.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)) (IrrRep.irr _) π.irr
  exact a3.of_equiv θ.symm

end GlobalTheory.LocGL.SumProd
