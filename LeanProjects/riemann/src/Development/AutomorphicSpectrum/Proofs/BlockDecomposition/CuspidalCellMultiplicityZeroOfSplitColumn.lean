import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedProductDropZeroFactorsStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

noncomputable section

namespace GlobalTheory.CompanionTheory.FineProd.CellMulti

set_option synthInstance.maxHeartbeats 400000

theorem jhMult_cell_eq_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h r : ℕ} (x : Fin h → IrrGL k) (y : Fin r → IrrGL k), (∀ j, (y j).IsCusp) → ∀ (b : Fin h → Fin r → ℕ) (hrow : ∀ i, ∑ j, b i j = (x i).1) (hcol : ∀ j, ∑ i, b i j = (y j).1) (j : Fin r) (i i' : Fin h), i ≠ i' → b i j ≠ 0 → b i' j ≠ 0 → jhMult (piTensor fun j => (y j).rep) (cellFunctor (c := fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i)) (fun j => stdBlocks (fun i => b i j) (hcol j)) (piTensor fun i => (x i).rep)) = 0 := by
  intro k _ _ _ _ hA h r x y hy b hrow hcol j i i' hii hi hi'
  classical
  by_contra h0
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (y j).2.rep
  have hτs : IsSmooth (piTensor fun j => (y j).rep) := isSmooth_piTensor fun j => (y j).2.rep.smooth
  obtain ⟨s, -, hS⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_of_cell (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).2 _ _
    (fun i => (x i).2.rep.smooth) (fun i => hasFiniteLength_of_isIrreducible (x i).2.rep.irr) hτ hτs h0
  have h1 := GlobalTheory.LocGL.SupportUnique.isSubquotient_factor (fun j => multiProd (stdBlocks (fun i => b i j) (hcol j)) fun i => (s i j).ρ) j
    (y j).2.rep.irr
    ((GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (y j).rep) (fun j => (y j).2.rep.irr) j).trans
      (GlobalTheory.LocGL.SupportUnique.isSubquotient_comp hS _))
  let Y : Fin h → IrrGL k := fun i => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr
  have hYb : ∀ c, (Y c).1 = b c j := fun _ => rfl
  let ψ := prodIrrEquiv (hcol j) (fun i => (s i j).ρ) (fun i => (s i j).smooth) fun i => (s i j).irr
  have h2 := h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective)
  let S : Finset (Fin h) := Finset.univ.filter fun c => b c j ≠ 0
  let o : Fin S.card ↪o Fin h := S.orderEmbOfFin rfl
  have hcard : 2 ≤ S.card := Finset.one_lt_card.2 ⟨i, by simp [S, hi], i', by simp [S, hi'], hii⟩
  have ho : ∀ a, o a ∈ S := fun a => Finset.orderEmbOfFin_mem _ _ _
  have hrange : ∀ c, (Y c).1 ≠ 0 → c ∈ Set.range o := fun c hc => by
    rw [Finset.range_orderEmbOfFin]
    simpa [S, hYb] using hc
  have hsum : ∑ a, (Y (o a)).1 = (y j).1 := by
    have e1 : ∑ a, (Y (o a)).1 = ∑ c : S, b c j :=
      Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _ fun a => rfl
    rw [e1, Finset.sum_coe_sort S (fun c => b c j), ← hcol j]
    exact Finset.sum_subset (Finset.subset_univ _) fun c _ hc => by simpa [S] using hc
  obtain ⟨E⟩ := GlobalTheory.T.induced_product_drop_zero_factors Y (hcol j) o o.strictMono hrange hsum
  have h3 := h2.trans (.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)
  refine jhMult_ne_zero_iff.2 h3
    (GlobalTheory.T.cuspidal_multiplicity_product_zero hA (y j) (fun a => Y (o a)) hsum (hy j) hcard fun a => Nat.pos_of_ne_zero ?_)
  have := ho a
  simpa [S, hYb] using this

end GlobalTheory.CompanionTheory.FineProd.CellMulti
