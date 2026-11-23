import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsJacQuot
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FAssocL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeft
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem ind₂_equiv_pair (y z : IrrGL k) {N : ℕ} (h : y.1 + z.1 = N) (hd : ∑ a, (![y, z] a).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor y.rep z.rep)).Equiv (prodIrr ![y, z] hd)) := by
  subst h
  exact nonempty_prod₂_equiv_prodIrr_pair y z hd

private theorem emb_unit (x : IrrGL k) : ∃ y : IrrGL k, y.1 = 0 ∧ Emb x y x := by
  let o : IrrRep (GL (Fin 0) k) := IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one
  let y : IrrGL k := IrrGL.of o.ρ o.smooth o.irr
  have φ : o.ρ.Equiv y.rep := IrrGL.equivOf o.ρ o.smooth o.irr
  have κ : y.2.rep.V ≃ₗ[ℂ] ℂ := φ.toLinearEquiv.symm
  have h : 0 + x.1 = x.1 := Nat.zero_add _
  have hd : ∑ a, (![y, x] a).1 = x.1 := (Fin.sum_univ_two _).trans h
  obtain ⟨a⟩ := GlobalTheory.ProdReorder.ind₂_line_left h y.rep κ x.rep x.2.rep.smooth
  obtain ⟨b⟩ := ind₂_equiv_pair y x h hd
  exact ⟨y, rfl, hd, (a.symm.trans b).toIntertwiningMap, (a.symm.trans b).toLinearEquiv.injective⟩

private theorem emb_deg {x y z : IrrGL k} (h : Emb x y z) : y.1 + z.1 = x.1 := by
  obtain ⟨hd, -⟩ := h
  exact (Fin.sum_univ_two _).symm.trans hd

private theorem suppIn_occ {v y ρ : IrrGL k} {P : Set (IrrGL k)} (h : Occ v y ρ) (hy : SuppIn y P)
    (hρ : ρ.IsCusp) (hP : ρ ∈ P) : SuppIn v P := by
  obtain ⟨hd, hne⟩ := h
  obtain ⟨A, hA, hAP⟩ := hy
  have hS := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := ![y, ρ]) (hd := hd) (t := ![A, {ρ}])
    (fun a => by
      fin_cases a
      · exact hA
      · exact hasSupport_self hρ) v.2.rep.irr (jhMult_ne_zero_iff.1 hne)
  refine ⟨_, hS, fun w hw => ?_⟩
  rw [Fin.sum_univ_two] at hw
  rcases Multiset.mem_add.1 hw with h | h
  · exact hAP w h
  · have : w = ρ := Multiset.mem_singleton.1 h
    exact this ▸ hP

end

theorem UpperTheory.Lit.Full.decompL :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k) (P : Set (IrrGL k)), ∃ y z, Emb x y z ∧ SuppIn y P ∧ FirstIn z Pᶜ := by
  intro hG hBZ k _ _ _ _ x P
  have key : ∀ (n : ℕ) (y z : IrrGL k), z.1 = n → Emb x y z → SuppIn y P →
      ∃ y z, Emb x y z ∧ SuppIn y P ∧ FirstIn z Pᶜ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y z hz hE hS
      by_cases hF : FirstIn z Pᶜ
      · exact ⟨y, z, hE, hS, hF⟩
      unfold FirstIn at hF
      push Not at hF
      obtain ⟨q, hq, hc, hj, hP⟩ := hF
      have hP' : q 0 ∈ P := by simpa using hP
      obtain ⟨w, hw⟩ := UpperTheory.Lit.Full.embL hG hBZ k z q hq hc hj
      obtain ⟨v, hv, hvw⟩ := UpperTheory.Lit.Full.assocL hG hBZ k x y z (q 0) w hE hw
      have h1 := emb_deg hw
      have h2 := hc.1
      exact ih w.1 (by omega) v w rfl hvw (suppIn_occ hv hS hc hP')
  obtain ⟨y, hy, hE⟩ := emb_unit x
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG y
  refine key _ y x rfl hE ⟨s, hs, ?_⟩
  rw [GlobalTheory.LocGL.SupportUnique.eq_zero_of_hasSupport hy hs]
  simp
