import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.CongrProd
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PNueq
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PReorder
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.PComb
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenUnitCCOf
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenericUnitary.IsGenericOfEquiv
import Development.WeilBound.CoreStatements.AutomorphicKernels.RamifiedExponentBounds.LocalExpBoundHolds

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Fin

open PositivityTheory.Gud.Pf

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def readOff (Γ : Segment k) : Option (IrrGL k × ℝ) :=
  open Classical in
  if hex : ∃ p : IrrGL k × ℝ, ∃ Δ : Segment k, PositivityTheory.UdReth2.IsCentred Δ ∧ IsLSeg Δ p.1.rep ∧ Γ = Δ.nu (p.2 : ℂ)
  then some (Classical.choose hex) else none

theorem readOff_nu {Δ : Segment k} {δ : IrrGL k} (hc : PositivityTheory.UdReth2.IsCentred Δ) (hL : IsLSeg Δ δ.rep) (t : ℝ) :
    readOff (Δ.nu (t : ℂ)) = some (δ, t) := by
  have hex : ∃ p : IrrGL k × ℝ, ∃ Δ' : Segment k, PositivityTheory.UdReth2.IsCentred Δ' ∧ IsLSeg Δ' p.1.rep ∧
      Δ.nu (t : ℂ) = Δ'.nu (p.2 : ℂ) := ⟨(δ, t), Δ, hc, hL, rfl⟩
  unfold readOff
  rw [dif_pos hex]
  obtain ⟨Δ', hc', hL', he⟩ := Classical.choose_spec hex
  obtain ⟨h1, rfl⟩ := eq_of_nu_eq hc hc' he
  have h2 := eq_of_isLSeg' hL hL'
  congr 1
  exact Prod.ext h2.symm h1.symm

theorem tail_step {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V} {h : ℕ}
    (X : Fin h → IrrGL k) (hd : ∑ j, (X j).1 = N) (φ : π.Equiv (prodIrr X hd)) (F : List (IrrGL k))
    (hF : List.Perm F (List.ofFn X))
    (hR : ∀ (σ : Equiv.Perm (Fin h)) (hd' : ∑ j, (X (σ j)).1 = N),
      Nonempty ((prodIrr X hd).Equiv (prodIrr (fun j => X (σ j)) hd'))) :
    ∃ (h' : ℕ) (x : Fin h' → IrrGL k) (hd : ∑ a, (x a).1 = N), List.ofFn x = F ∧ Nonempty (π.Equiv (prodIrr x hd)) := by
  obtain ⟨y, hy, σ, rfl⟩ := perm_ofFn X F hF
  have hd' : ∑ j, (X (σ j)).1 = N := by
    rw [Equiv.sum_comp σ (fun j => (X j).1)]
    exact hd
  exact ⟨h, fun j => X (σ j), hd', hy, ⟨φ.trans (hR σ hd').some⟩⟩

end Local

theorem genericUnitaryDualGL_holds : GlobalTheory.Published.GenericUnitaryDualGL := by
  intro k _ _ _ _ _ N V _ _ π hsm hirr hU hgen
  obtain ⟨h, δ, Δ, s, hL, hCC, hs, hd, ⟨φ⟩⟩ :=
    PositivityTheory.RgUd.Exp.genUnitCCOf (fun k => PositivityTheory.RgUd.expBound k) GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds
      k N V π hsm hirr hU hgen
  have hcent : ∀ j, PositivityTheory.UdReth2.IsCentred (Δ j) := fun j => isCentred_of_unitCC (hL j) (hCC j)
  have hirrP := GlobalTheory.Parabolic.isIrreducible_of_equiv φ hirr
  have hUP := GlobalTheory.GenericUnitary.isUnitarisable_of_equiv φ hU
  have hsym := segs_symm δ Δ s hL hCC hs hd hirrP hUP
  have e1 : ∀ j, readOff ((Δ j).nu ((s j : ℝ) : ℂ)) = some (δ j, s j) :=
    fun j => readOff_nu (hcent j) (hL j) (s j)
  have e2 : ∀ j, readOff ((Δ j).nu ((-s j : ℝ) : ℂ)) = some (δ j, -s j) :=
    fun j => readOff_nu (hcent j) (hL j) (-s j)
  have hm := congrArg (Multiset.map readOff) hsym
  simp only [Multiset.map_map, Function.comp_def, e1, e2] at hm
  have hm2 : Multiset.map (fun j => (δ j, -s j)) Finset.univ.val =
      Multiset.map (fun j => (δ j, s j)) Finset.univ.val := by
    refine (Multiset.map_injective (Option.some_injective _) ?_).symm
    simpa [Multiset.map_map, Function.comp_def] using hm
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at hm2
  set l := List.ofFn (fun j => (δ j, s j)) with hl
  have hperm : (l.map (fun p : IrrGL k × ℝ => (p.1, -p.2))).Perm l := by
    rw [hl, List.map_ofFn]
    exact hm2
  obtain ⟨a, b, hb, hab⟩ := comb l hperm
  have memL : ∀ p ∈ l, ∃ j, (δ j, s j) = p := by
    intro p hp
    rw [hl, List.mem_ofFn] at hp
    obtain ⟨j, hj⟩ := hp
    exact ⟨j, hj⟩
  have hUL : ∀ j, GlobalTheory.GenericUnitary.IsUnitaryLSeg (δ j) :=
    fun j => ⟨⟨Δ j, hL j⟩, unitarisable_of_unitCC (hL j) (hCC j)⟩
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : (x, (0 : ℝ)) ∈ l := hab.subset (List.mem_append_left _ (List.mem_map_of_mem hx))
    obtain ⟨j, hj⟩ := memL _ hx'
    have : δ j = x := congrArg Prod.fst hj
    rw [← this]
    exact hUL j
  · intro p hp
    obtain ⟨j, hj⟩ := memL p (hb p hp).2
    subst hj
    exact ⟨hUL j, (hb _ hp).1, (abs_lt.mp (hs j)).2⟩
  · have hfac : GlobalTheory.GenericUnitary.factors a b =
        (a.map (fun x => (x, (0 : ℝ))) ++ b.flatMap (fun p : IrrGL k × ℝ => [p, (p.1, -p.2)])).map
          (fun p : IrrGL k × ℝ => p.1.nu (p.2 : ℂ)) := by
      simp [GlobalTheory.GenericUnitary.factors, List.map_flatMap, Function.comp_def, IrrGL.nu_zero]
    have hF : (GlobalTheory.GenericUnitary.factors a b).Perm (List.ofFn (fun j => (δ j).nu ((s j : ℝ) : ℂ))) := by
      rw [hfac]
      have := hab.map (fun p : IrrGL k × ℝ => p.1.nu (p.2 : ℂ))
      rw [hl, List.map_ofFn] at this
      exact this
    exact tail_step (fun j => (δ j).nu ((s j : ℝ) : ℂ)) hd φ _ hF
      (fun σ hd' => reorder δ Δ s hL hcent hs σ hd hd')

end PositivityTheory.Gud.Fin

end
