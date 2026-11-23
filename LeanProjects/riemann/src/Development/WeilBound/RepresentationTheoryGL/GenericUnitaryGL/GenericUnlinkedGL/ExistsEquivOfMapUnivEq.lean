import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSupportRealisedByProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankProductLeOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankExtensionBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanLocalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSwapProductGenericStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.RgGu

theorem exists_equiv_of_map_univ_eq {α : Type*} {h h' : ℕ} (x : Fin h → α) (y : Fin h' → α)
    (H : Finset.univ.val.map x = Finset.univ.val.map y) : ∃ e : Fin h ≃ Fin h', ∀ a, y (e a) = x a := by
  classical
  have hc : ∀ v, Fintype.card {a // x a = v} = Fintype.card {b // y b = v} := fun v => by
    have := congrArg (Multiset.count v) H
    simp only [Multiset.count_map] at this
    simp only [Fintype.card_subtype, Finset.card_def, Finset.filter_val, eq_comm (b := v)]
    exact this
  exact ⟨Equiv.ofFiberEquiv fun v => Fintype.equivOfCardEq (hc v), fun a => Equiv.ofFiberEquiv_map _ a⟩

theorem genericUnique_of_perm {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (hW : GlobalTheory.BZSeg.WhitRankIrr k)
    (hC : GlobalTheory.BZSeg.CuspGeneric k)
    (hP : GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL k), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (τ : Equiv.Perm (Fin h)) (hd' : ∑ a, (x (τ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (τ a)) hd')) :
    GenericUnique k := by
  intro N s V W _ _ _ _ π σ hπ hσ gπ gσ
  obtain ⟨ψ, hψc, hψ1, gπψ⟩ := gπ
  have gσψ : IsGenericFor ψ σ := (isGeneric_iff_isGenericFor hψc hψ1 σ).1 gσ
  obtain ⟨h, x, hd, hxs, hxc, hπx⟩ := GlobalTheory.T.cuspidal_support_realised_by_product k π s hπ
  obtain ⟨h', y, hd', hys, hyc, hσy⟩ := GlobalTheory.T.cuspidal_support_realised_by_product k σ s hσ
  obtain ⟨e, he⟩ := exists_equiv_of_map_univ_eq x y (hxs.trans hys.symm)
  have hh : h = h' := by simpa using Fintype.card_congr e
  subst hh
  have hfun : (fun a => y (e a)) = x := funext he
  subst hfun
  have hσx : IsSubquotient σ (prodIrr (fun a => y (e a)) hd) :=
    hP hA (GlobalTheory.T.gelfand_kazhdan_local hA) hH hW hC ψ hψc hψ1 y hyc hd' e hd σ hσ.isSmooth hσ.isIrreducible gσψ hσy
  exact GlobalTheory.T.whittaker_rank_extension_bound k ψ hψc N (prodIrr (fun a => y (e a)) hd) π σ (isSmooth_prodIrr _ hd)
    (GlobalTheory.T.whittaker_rank_product_le_one k hH hW ψ hψc hψ1 h N _ hd) hπ.isIrreducible hσ.isIrreducible hπx hσx gπψ gσψ

theorem perm_abs {α : Type 1} {h : ℕ} (P : (Fin h → α) → Prop)
    (hP : ∀ (y : Fin h → α) (j : ℕ) (hj : j + 1 < h), P y → P fun a => y (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a))
    (x : Fin h → α) (hx : P x) (τ : Equiv.Perm (Fin h)) : P fun a => x (τ a) := by
  rcases h with _ | n
  · obtain rfl : τ = 1 := Subsingleton.elim _ _
    exact hx
  have hτ : τ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  induction hτ using Submonoid.closure_induction_right with
  | one => exact hx
  | mul_right t ht s hs' ih =>
    obtain ⟨i, rfl⟩ := hs'
    exact hP (fun a => x (t a)) i.1 (by omega) ih

theorem perm_of_swap : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL k), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (τ : Equiv.Perm (Fin h)) (hd' : ∑ a, (x (τ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (τ a)) hd') := by
  intro k _ _ _ _ hA hG hH hW hC ψ hc h1 h N x hx hd τ hd' W _ _ σ hs hi hg hσ
  let P : (Fin h → IrrGL k) → Prop := fun y =>
    (∀ a, (y a).IsCusp) ∧ ∃ e : ∑ a, (y a).1 = N, IsSubquotient σ (prodIrr y e)
  have step : ∀ (y : Fin h → IrrGL k) (j : ℕ) (hj : j + 1 < h), P y →
      P fun a => y (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a) := by
    rintro y j hj ⟨c, e, H⟩
    have e' : ∑ a, (y (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N :=
      (Equiv.sum_comp (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩) fun a => (y a).1).trans e
    exact ⟨fun a => c _, e', @GlobalTheory.T.cuspidal_swap_product_generic k _ _ _ _ hA hG hH hW hC ψ hc h1 h N y c e j hj e' W _ _ σ hs hi hg H⟩
  obtain ⟨-, e, H⟩ := perm_abs P step x ⟨hx, hd, hσ⟩ τ
  exact H

theorem genericUnique_of {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (hW : GlobalTheory.BZSeg.WhitRankIrr k)
    (hC : GlobalTheory.BZSeg.CuspGeneric k) : GenericUnique k :=
  genericUnique_of_perm hA hH hW hC (@perm_of_swap k _ _ _ _)

end GlobalTheory.RgGu

end
