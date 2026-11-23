import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleOfJhMultEqOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsClassificationCuspidalSupport
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDistinctCuspidalPairEmbedding
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleOfClsGLEqSingle
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TotallyDisjointProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegments
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TDZ

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.JHMult
open GlobalTheory.CompanionTheory.Hypotheses₂.TD

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem commute_pair (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness)
    (hZ : ZelevinskyPolynomialRing) (g : Fin 2 → IrrGL k) (h0 : (g 0).IsCusp) (h1 : (g 1).IsCusp)
    (hU : ∀ j : ℤ, |j| ≤ 1 → g 0 ≠ (g 1).nu (j : ℂ)) {n : Type} [Fintype n] [DecidableEq n]
    (f : (Σ i, Fin (g i).1) ≃ n) (f' : (Σ i, Fin (g (Equiv.swap 0 1 i)).1) ≃ n) :
    Nonempty ((multiProd f fun i => (g i).rep).Equiv (multiProd f' fun i => (g (Equiv.swap 0 1 i)).rep)) := by
  let σ : ∀ i, Irr k (g i).1 := fun i => Irr.ofIrrRep (g i).2.rep
  have hc : ∀ i, (g i).IsCusp := fun i => by
    fin_cases i
    · exact h0
    · exact h1
  have i1 : (multiProd f fun i => (σ i).π).IsIrreducible :=
    isIrreducible_multiProd_of_prod₂ (fun i => (g i).1) σ
      (GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.isIrreducible_prod₂_of_polynomialRing hG hBZ hZ k (g 0) (g 1) h0 h1 hU) f
  have g0 : g (Equiv.swap 0 1 0) = g 1 := by simp
  have g1 : g (Equiv.swap 0 1 1) = g 0 := by simp
  have i2 : (multiProd f' fun i => (σ (Equiv.swap 0 1 i)).π).IsIrreducible :=
    isIrreducible_multiProd_of_prod₂ (fun i => (g (Equiv.swap 0 1 i)).1) (fun i => σ (Equiv.swap 0 1 i))
      (GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.isIrreducible_prod₂_of_polynomialRing hG hBZ hZ k _ _ (hc _) (hc _) (by
        rw [g0, g1]
        exact unlinked_symm hU)) f'
  refine GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap.swap_equiv_of_irreducible hG hBZ k n (fun i => (g i).1) σ
    (fun i => ⟨(hc i).1, (hc i).2⟩) ?_ f f' i1 i2
  show IrrGL.of (g 0).rep (g 0).2.rep.smooth (g 0).2.rep.irr ≠ IrrGL.of (g 1).rep (g 1).2.rep.smooth (g 1).2.rep.irr
  rw [IrrGL.of_rep, IrrGL.of_rep]
  have := hU 0 (by simp)
  simpa using this

theorem occurs (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness)
    (hZ : ZelevinskyPolynomialRing) {d : Fin 2 → ℕ}
    (p : ∀ i, Irr k (d i)) {A : Fin 2 → Multiset (IrrGL k)} (hA : ∀ i, HasSupport (p i).π (A i))
    (hAB : ∀ x ∈ A 0, x ∉ A 1) (hU : ∀ x ∈ A 0, ∀ y ∈ A 1, ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ))
    (e : (Σ i, Fin (d i)) ≃ Fin (d 0 + d 1)) (Q : Irr k (d 0 + d 1))
    (hQ : IsSubquotient Q.π (multiProd e fun i => (p i).π)) :
    IsSubquotient (piTensor fun i => (p i).π) (jac e Q.π) := by
  classical
  obtain ⟨s, u, e₃, hc, φ, hφ⟩ := GlobalTheory.CompanionTheory.CuspEmbed.main hBZ hG k _ Q
  have hS₁ : HasSupport Q.π (Finset.univ.val.map u) :=
    ⟨s, u, rfl, Q.irr, fun a => ⟨(hc a).1, (u a).2.rep.irr, (hc a).2⟩, e₃, .of_injective φ hφ⟩
  have hd : ∑ i, d i = d 0 + d 1 := Fin.sum_univ_two d
  have hS₂ : HasSupport Q.π (A 0 + A 1) := by
    obtain ⟨φ'⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks d hd) _).1
      (piTensor fun i => (p i).π)
    let ψ := φ'.trans (prodIrrEquiv hd (fun i => (p i).π) (fun i => (p i).smooth) fun i => (p i).irr)
    have h := hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (p i).π (p i).smooth (p i).irr)
      (fun i => (hA i).of_equiv (IrrGL.equivOf _ _ _)) Q.irr
      (hQ.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
    rwa [Fin.sum_univ_two] at h
  have hm : Finset.univ.val.map u = A 0 + A 1 := hasSupport_unique hG hBZ hS₁ hS₂
  let S : Finset (Fin s) := Finset.univ.filter fun a => u a ∈ A 1
  let σ : ∀ a, Irr k (u a).1 := fun a => Irr.ofIrrRep (u a).2.rep
  have mem : ∀ a, u a ∈ A 0 ∨ u a ∈ A 1 := fun a =>
    Multiset.mem_add.1 (hm ▸ Multiset.mem_map_of_mem u (Finset.mem_univ a))
  have mem1 : ∀ a, a ∈ S → u a ∈ A 1 := fun a ha => (Finset.mem_filter.1 ha).2
  have mem0 : ∀ a, a ∉ S → u a ∈ A 0 := fun a ha =>
    (mem a).resolve_right fun h => ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have mS : S.val.map u = A 1 := by
    have h : S.val.map u = (Finset.univ.val.map u).filter (· ∈ A 1) := by
      rw [Multiset.filter_map]
      rfl
    rw [h, hm, Multiset.filter_add, Multiset.filter_eq_nil.2 (fun x hx => hAB x hx),
      Multiset.filter_eq_self.2 (fun x hx => hx), zero_add]
  have mC : Sᶜ.val.map u = A 0 := by
    have h : Sᶜ.val.map u = (Finset.univ.val.map u).filter (· ∉ A 1) := by
      rw [Multiset.filter_map, Finset.compl_filter]
      rfl
    rw [h, hm, Multiset.filter_add, Multiset.filter_eq_self.2 (fun x hx => hAB x hx),
      Multiset.filter_eq_nil.2 (fun x hx h => h hx), add_zero]
  have deg : ∀ (T : Finset (Fin s)) (C : Multiset (IrrGL k)), T.val.map u = C →
      ∑ a : Fin T.card, (u (T.orderEmbOfFin rfl a)).1 = (C.map Sigma.fst).sum := by
    intro T C h
    rw [← h, ← map_orderEmb T u, Multiset.map_map]
    rfl
  have c₁ : Fintype.card (Σ a : Fin Sᶜ.card, Fin (u (Sᶜ.orderEmbOfFin rfl a)).1) = Fintype.card (Fin (d 0)) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [deg _ _ mC, (hA 0).sum_fst, Fintype.card_fin]
  have c₂ : Fintype.card (Σ a : Fin S.card, Fin (u (S.orderEmbOfFin rfl a)).1) = Fintype.card (Fin (d 1)) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [deg _ _ mS, (hA 1).sum_fst, Fintype.card_fin]
  let e₁ := Fintype.equivOfCardEq c₁
  let e₂ := Fintype.equivOfCardEq c₂
  obtain ⟨Φ⟩ := GlobalTheory.T.parabolicProduct_equiv_product_of_partition k s (fun a => (u a).1) σ S (d 0) (d 1) e₃ e₁ e₂
    (fun a b ha hb n _ _ f f' => commute_pair hG hBZ hZ (fun i => u (![a, b] i)) (hc a) (hc b)
      (hU _ (mem0 a ha) _ (mem1 b hb)) f f')
  have hsupp : ∀ (T : Finset (Fin s)) (C : Multiset (IrrGL k)), T.val.map u = C → ∀ (n : ℕ)
      (f : (Σ a : Fin T.card, Fin (u (T.orderEmbOfFin rfl a)).1) ≃ Fin n)
      (y : IrrRep (GL (Fin n) k)), IsSubquotient y.ρ (multiProd f fun a => (σ (T.orderEmbOfFin rfl a)).π) →
      HasSupport y.ρ C := by
    intro T C hT n f y hy
    refine ⟨T.card, fun a => u (T.orderEmbOfFin rfl a), ?_, y.irr,
      fun a => ⟨(hc _).1, (u _).2.rep.irr, (hc _).2⟩, f, hy⟩
    rw [map_orderEmb, hT]
  exact occurs_of_prod₂ hG hBZ p hA hAB e Q hQ
    ⟨_, multiProd e₁ fun a => (σ (Sᶜ.orderEmbOfFin rfl a)).π, isSmooth_parInd _ _⟩
    ⟨_, multiProd e₂ fun a => (σ (S.orderEmbOfFin rfl a)).π, isSmooth_parInd _ _⟩
    (hsupp _ _ mC _ e₁) (hsupp _ _ mS _ e₂) (Φ.toIntertwiningMap.comp φ) (Φ.toLinearEquiv.injective.comp hφ)

theorem isIrreducible_prod₂ (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness)
    (hZ : ZelevinskyPolynomialRing) {r t : ℕ} (π₁ : Irr k r) (π₂ : Irr k t)
    {A₀ A₁ : Multiset (IrrGL k)} (H₁ : HasSupport π₁.π A₀) (H₂ : HasSupport π₂.π A₁)
    (hU : ∀ x ∈ A₀, ∀ y ∈ A₁, ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ)) :
    (prod₂ π₁.π π₂.π).IsIrreducible := by
  have hAB : ∀ x ∈ A₀, x ∉ A₁ := fun x hx hx' => hU x hx x hx' 0 (by simp) (by simp)
  let dd : Fin 2 → ℕ := ![r, t]
  let p : ∀ i, Irr k (dd i) := fun i =>
    Fin.cases (motive := fun i => Irr k (dd i)) π₁
      (fun j => Fin.cases (motive := fun j : Fin 1 => Irr k (dd j.succ)) π₂ (fun l => l.elim0) j) i
  let A : Fin 2 → Multiset (IrrGL k) := ![A₀, A₁]
  have hA : ∀ i, HasSupport (p i).π (A i) := by
    intro i
    fin_cases i
    · exact H₁
    · exact H₂
  have hd : ∑ i, dd i = dd 0 + dd 1 := Fin.sum_univ_two dd
  have hirr := isIrreducible_of_occurs hG hBZ p hA hAB (stdBlocks dd hd)
    (fun Q hQ => occurs hG hBZ hZ p hA hAB hU (stdBlocks dd hd) Q hQ)
  obtain ⟨E⟩ := GlobalTheory.LocGL.nonempty_prod₂_equiv_multiProd hd fun i => (p i).π
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E.symm hirr

end GlobalTheory.CompanionTheory.Hypotheses₂.TDZ

theorem GlobalTheory.CompanionTheory.Hypotheses₂.totallyDisjointProductIrreducible_of_polynomialRing :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
      GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.TotallyDisjointProductIrreducible := by
  intro hG hBZ hZ k _ _ _ _ r t s s' π₁ π₂ d d' σ σ' h₁ h₂ hdis
  refine GlobalTheory.CompanionTheory.Hypotheses₂.TDZ.isIrreducible_prod₂ hG hBZ hZ π₁ π₂ (GlobalTheory.LocGL.hasSupport_of_isCuspSupport h₁)
    (GlobalTheory.LocGL.hasSupport_of_isCuspSupport h₂) ?_
  intro x hx y hy j hj heq
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
  obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨hpq, hn⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_equiv_of_eq_nu (σ a) (σ' b) j heq
  exact hdis a b hpq j hj hn

theorem GlobalTheory.CompanionTheory.Hypotheses₂.totallyDisjointProductIrreducible_of_parts :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.SegmentRepresentation →
      GlobalTheory.Published.GrothendieckRingPolynomial → GlobalTheory.Published.TotallyDisjointProductIrreducible :=
  fun hG hS hP => GlobalTheory.CompanionTheory.Hypotheses₂.totallyDisjointProductIrreducible_of_polynomialRing hG
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
    (GlobalTheory.zelevinskyPolynomialRing_of_parts GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness hS hP)

end
