import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyDisjointProductIrreducibleOfPolynomialRin
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsClassificationCuspidalSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import BuildAid.D5

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem UpperTheory.Lit.Mix.front_support_decomposition (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (m + n)) k) V) (A₀ A₁ : Multiset (IrrGL k)) (hA : HasSupport π (A₀ + A₁))
    (hm₀ : (A₀.map Sigma.fst).sum = m) (hU : ∀ x ∈ A₀, ∀ y ∈ A₁, ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ))
    (s : ℕ) (u : Fin s → IrrGL k) (e₃ : (Σ a, Fin (u a).1) ≃ Fin (m + n)) (hc : ∀ a, (u a).IsCusp)
    (φ : π.IntertwiningMap (multiProd e₃ fun a => (u a).rep)) (hφ : Function.Injective φ) :
    ∃ (h h' : ℕ) (u : Fin h → IrrGL k) (w : Fin h' → IrrGL k) (hu : ∑ a, (u a).1 = m) (hw : ∑ a, (w a).1 = n),
      Finset.univ.val.map u = A₀ ∧
        ∃ f : π.IntertwiningMap (prod₂ (prodIrr u hu) (prodIrr w hw)), Function.Injective f := by
  classical
  have hAB : ∀ x ∈ A₀, x ∉ A₁ := fun x hx hx' => hU x hx x hx' 0 (by simp) (by simp)
  have hn₁ : (A₁.map Sigma.fst).sum = n := by
    have h := hA.sum_fst
    rw [Multiset.map_add, Multiset.sum_add, hm₀, Fintype.card_fin] at h
    omega
  have hS₁ : HasSupport π (Finset.univ.val.map u) :=
    ⟨s, u, rfl, hA.isIrreducible, fun a => ⟨(hc a).1, (u a).2.rep.irr, (hc a).2⟩, e₃, .of_injective φ hφ⟩
  have hm : Finset.univ.val.map u = A₀ + A₁ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ hS₁ hA
  let S : Finset (Fin s) := Finset.univ.filter fun a => u a ∈ A₁
  let σ : ∀ a, GlobalTheory.SplitRead.Irr k (u a).1 := fun a => GlobalTheory.SplitRead.Irr.ofIrrRep (u a).2.rep
  have mem : ∀ a, u a ∈ A₀ ∨ u a ∈ A₁ := fun a =>
    Multiset.mem_add.1 (hm ▸ Multiset.mem_map_of_mem u (Finset.mem_univ a))
  have mem1 : ∀ a, a ∈ S → u a ∈ A₁ := fun a ha => (Finset.mem_filter.1 ha).2
  have mem0 : ∀ a, a ∉ S → u a ∈ A₀ := fun a ha =>
    (mem a).resolve_right fun h => ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have mS : S.val.map u = A₁ := by
    have h : S.val.map u = (Finset.univ.val.map u).filter (· ∈ A₁) := by
      rw [Multiset.filter_map]
      rfl
    rw [h, hm, Multiset.filter_add, Multiset.filter_eq_nil.2 (fun x hx => hAB x hx),
      Multiset.filter_eq_self.2 (fun x hx => hx), zero_add]
  have mC : Sᶜ.val.map u = A₀ := by
    have h : Sᶜ.val.map u = (Finset.univ.val.map u).filter (· ∉ A₁) := by
      rw [Multiset.filter_map, Finset.compl_filter]
      rfl
    rw [h, hm, Multiset.filter_add, Multiset.filter_eq_self.2 (fun x hx => hAB x hx),
      Multiset.filter_eq_nil.2 (fun x hx h => h hx), add_zero]
  have deg : ∀ (T : Finset (Fin s)) (C : Multiset (IrrGL k)), T.val.map u = C →
      ∑ a : Fin T.card, (u (T.orderEmbOfFin rfl a)).1 = (C.map Sigma.fst).sum := by
    intro T C h
    rw [← h, ← GlobalTheory.CompanionTheory.Hypotheses₂.TD.map_orderEmb T u, Multiset.map_map]
    rfl
  have c₁ : ∑ a : Fin Sᶜ.card, (u (Sᶜ.orderEmbOfFin rfl a)).1 = m := (deg _ _ mC).trans hm₀
  have c₂ : ∑ a : Fin S.card, (u (S.orderEmbOfFin rfl a)).1 = n := (deg _ _ mS).trans hn₁
  have hΦ := GlobalTheory.T.parabolicProduct_equiv_product_of_partition k s (fun a => (u a).1) σ S m n e₃
    (stdBlocks (fun a => (u (Sᶜ.orderEmbOfFin rfl a)).1) c₁) (stdBlocks (fun a => (u (S.orderEmbOfFin rfl a)).1) c₂)
    (fun a b ha hb n _ _ f f' => GlobalTheory.CompanionTheory.Hypotheses₂.TDZ.commute_pair hG hBZ hZ (fun i => u (![a, b] i)) (hc a) (hc b)
      (hU _ (mem0 a ha) _ (mem1 b hb)) f f')
  exact hΦ.elim fun Φ => ⟨_, _, fun a => u (Sᶜ.orderEmbOfFin rfl a), fun a => u (S.orderEmbOfFin rfl a), c₁, c₂,
    (GlobalTheory.CompanionTheory.Hypotheses₂.TD.map_orderEmb _ u).trans mC, Φ.toIntertwiningMap.comp φ, Φ.toLinearEquiv.injective.comp hφ⟩

theorem UpperTheory.Lit.Mix.front :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin (m + n)) k) V) (A₀ A₁ : Multiset (IrrGL k)), HasSupport σ (A₀ + A₁) → (A₀.map Sigma.fst).sum = m → (∀ x ∈ A₀, ∀ y ∈ A₁, ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ)) → ∃ (h h' : ℕ) (u : Fin h → IrrGL k) (w : Fin h' → IrrGL k) (hu : ∑ a, (u a).1 = m) (hw : ∑ a, (w a).1 = n), Finset.univ.val.map u = A₀ ∧ ∃ f : σ.IntertwiningMap (prod₂ (prodIrr u hu) (prodIrr w hw)), Function.Injective f := by
  intro hG hBZ hZ k _ _ _ _ m n V _ _ π A₀ A₁ hA hm₀ hU
  exact (GlobalTheory.CompanionTheory.CuspEmbed.main hBZ hG k _ (GlobalTheory.SplitRead.Irr.mk V π hA.isSmooth hA.isIrreducible)).elim fun s H =>
    H.elim fun u H => H.elim fun e H => H.2.elim fun φ hφ =>
      UpperTheory.Lit.Mix.front_support_decomposition hG hBZ hZ k m n V π A₀ A₁ hA hm₀ hU s u e H.1 φ hφ
