import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroBasicTwistOfSpecialForm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientUnramPrinSeriesOfHasSupport

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spPiSub

theorem exists_equiv_of_map_eq {ι κ α : Type*} [Fintype ι] [Fintype κ] (f : ι → α) (g : κ → α)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) : ∃ e : ι ≃ κ, ∀ i, g (e i) = f i := by
  have hc : ∀ c, Fintype.card {i // f i = c} = Fintype.card {j // g j = c} := by
    intro c
    have h1 := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at h1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card, Finset.filter_val, eq_comm] using h1
  exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hc c), fun i => Equiv.ofFiberEquiv_map _ i⟩

theorem map_univ_eq_sum {ι α : Type*} [Fintype ι] (φ : ι → α) :
    Finset.univ.val.map φ = ∑ i, ({φ i} : Multiset α) := by
  rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton (Multiset.map φ Finset.univ.val),
    Multiset.map_map]
  rfl

theorem sum_map_univ {s n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {α : Type*}
    (F : ∀ a, Fin (d a) → α) :
    ∑ a, Finset.univ.val.map (F a) = Finset.univ.val.map fun i => F (e.symm i).1 (e.symm i).2 := by
  calc ∑ a, Finset.univ.val.map (F a) = ∑ a, ∑ j, ({F a j} : Multiset α) := by
        simp only [map_univ_eq_sum]
    _ = ∑ p : Σ a, Fin (d a), ({F p.1 p.2} : Multiset α) := (Fintype.sum_sigma (fun p : Σ a, Fin (d a) => ({F p.1 p.2} : Multiset α))).symm
    _ = ∑ i, ({F (e.symm i).1 (e.symm i).2} : Multiset α) :=
        (Equiv.sum_comp e.symm (fun p : Σ a, Fin (d a) => ({F p.1 p.2} : Multiset α))).symm
    _ = _ := (map_univ_eq_sum _).symm

end UpperTheory.TNZ.Grp.P_spPiSub

namespace UpperTheory.TNZ.Grp

open P_spPiSub

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_spPiSub {n : ℕ} (G : Grp k n) : G.SpecialRepresentationSubProp := by
  intro hOrd hL Y _ _ τ _ _ ν hν hc hI
  let χ : Fin G.s → kˣ →* ℂˣ := fun a => absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))
  have hχ : ∀ a, IsSmoothChar (χ a) := fun a => isSmoothChar_absPow _
  have hsupp : ∀ a, HasSupport (G.twD τ a)
      (Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) := by
    intro a
    have h1 := (hasSupport_of_isCuspSupport (hc a)).tw (χ a) (hχ a)
    rw [Multiset.map_map] at h1
    convert h1 using 2
    · rfl
    · rename_i j _
      exact (IrrGL.tw_ofChar (ν a j) (χ a) (hν a j) (hχ a)).symm
  have hcOf : ∀ i, IsSmoothChar (G.cOf ν i) := fun i => (hν _ _).mul (isSmoothChar_absPow _)
  have hS := SupportRing.hasSupport_multiProd hL.loc.zel G.hd (G.twD τ) (fun a => (hsupp a).isSmooth)
    (fun a => (hsupp a).isIrreducible) hsupp hI
  have hsum : (∑ a, Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) =
      Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i) :=
    sum_map_univ G.e (fun a j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a)))
  obtain ⟨h, x, hx, -, -, e', he⟩ := hS
  rw [hsum] at hx
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq x (fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i)) hx
  obtain rfl : x = fun b => IrrGL.ofChar (G.cOf ν (σ b)) (hcOf _) := funext fun b => (hσ b).symm
  have hn : h = n := by simpa using Fintype.card_congr σ
  subst hn
  let φ := multiProdEquiv e' fun b =>
    (equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ b)) (hcOf _))).symm
  have hsq : IsSubquotient (multiProd G.e (G.twD τ)) (prinSeries fun b => G.cOf ν (σ b)) :=
    (he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)).trans
      (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e' _)
  exact hOrd hL _ _ (isSmooth_parInd _ _) hI _ hcOf σ hsq

end UpperTheory.TNZ.Grp
