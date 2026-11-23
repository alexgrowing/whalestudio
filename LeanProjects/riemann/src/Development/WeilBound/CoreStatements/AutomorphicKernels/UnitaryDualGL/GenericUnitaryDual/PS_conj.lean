import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
import BuildAid.D4

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Symm.Pf

open PositivityTheory.RgGu.NR (ConjEquiv)

section Gen

variable {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U]
  [Module ℂ U]

theorem conjEquiv_trans_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    (h : ConjEquiv π σ) (e : σ.Equiv τ) : ConjEquiv π τ := by
  obtain ⟨φ, hφ, hc⟩ := h
  refine ⟨(e.toLinearEquiv.toLinearMap).comp φ, e.toLinearEquiv.bijective.comp hφ, fun g v => ?_⟩
  have := Representation.IntertwiningMap.isIntertwining σ τ e.toIntertwiningMap g (φ v)
  simp only [LinearMap.comp_apply, hc]
  exact this

theorem equiv_trans_conjEquiv {ρ : Representation ℂ G U} {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv π) (h : ConjEquiv π σ) : ConjEquiv ρ σ := by
  obtain ⟨φ, hφ, hc⟩ := h
  refine ⟨φ.comp (e.toLinearEquiv.toLinearMap), hφ.comp e.toLinearEquiv.bijective, fun g v => ?_⟩
  have := Representation.IntertwiningMap.isIntertwining ρ π e.toIntertwiningMap g v
  simp only [LinearMap.comp_apply]
  rw [← hc]
  exact congrArg φ this

theorem nonempty_equiv_of_conj {π : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    (h₁ : ConjEquiv π σ) (h₂ : ConjEquiv π τ) : Nonempty (σ.Equiv τ) := by
  obtain ⟨φ, hφ, hc⟩ := h₁
  obtain ⟨ψ, hψ, hc'⟩ := h₂
  let inv := PositivityTheory.RgGu.NR.ConjProd.semiInv φ hφ
  have h1 : ∀ w, φ (inv w) = w := PositivityTheory.RgGu.NR.ConjProd.semiInv_apply φ hφ
  have h2 : ∀ v, inv (φ v) = v := PositivityTheory.RgGu.NR.ConjProd.semiInv_apply' φ hφ
  have hinv : ∀ g w, inv (σ g w) = π g (inv w) := fun g w => hφ.1 (by rw [hc, h1, h1])
  let L : W →ₗ[ℂ] U :=
    { toFun := fun w => ψ (inv w)
      map_add' := fun a b => by simp only [map_add]
      map_smul' := fun c a => by
        simp only [map_smulₛₗ, RingHom.id_apply]
        simp }
  have hL : ∀ w, L w = ψ (inv w) := fun _ => rfl
  have hbij : Function.Bijective L := by
    refine ⟨fun a b hab => ?_, fun u => ?_⟩
    · rw [hL, hL] at hab
      have := hψ.1 hab
      rw [← h1 a, ← h1 b, this]
    · obtain ⟨v, rfl⟩ := hψ.2 u
      exact ⟨φ v, by rw [hL, h2]⟩
  let f : σ.IntertwiningMap τ :=
    { toLinearMap := L
      isIntertwining' := fun g => by
        ext w
        show ψ (inv (σ g w)) = τ g (ψ (inv w))
        rw [hinv, hc'] }
  exact ⟨equivOfBijective f hbij⟩

end Gen

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nonempty_equiv_prodIrr_of_eq {h N : ℕ} {z y : Fin h → IrrGL k} (e : z = y) (hz : ∑ a, (z a).1 = N)
    (hy : ∑ a, (y a).1 = N) : Nonempty ((prodIrr z hz).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem detChar_one (n : ℕ) : detChar (Fin n) (1 : kˣ →* ℂˣ) = 1 := MonoidHom.one_comp _

def C1 (x y : IrrGL k) : Prop :=
  ∃ (n : ℕ) (c c' : IrrCl (GL (Fin n) k)), x = ⟨n, c⟩ ∧ y = ⟨n, c'⟩ ∧ ConjEquiv c.rep.ρ c'.rep.ρ

theorem contra_equiv_of_conj {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GL (Fin N) k) V) (Q : Representation ℂ (GL (Fin N) k) W) (hs : IsSmooth P) (hi : P.IsIrreducible)
    (hu : IsUnitarisable P) (h : ConjEquiv P Q) : Nonempty ((contra P).Equiv Q) := by
  have h0 : ConjEquiv P (contra P) := by
    have := PositivityTheory.RgGu.NR.conjDual k N _ P hs hi hu 0
    simpa only [Complex.ofReal_zero, absPow_zero, detChar_one, twist_one] using this
  exact nonempty_equiv_of_conj h0 h

open GlobalTheory.ProdFlatten

def CjB {n : ℕ} (A C : BR k n) : Prop := ConjEquiv A.ρ C.ρ

def ctr {n : ℕ} (A : BR k n) : BR k n := ⟨_, contra A.ρ⟩

def IU {n : ℕ} (A : BR k n) : Prop := A.ρ.IsIrreducible ∧ IsUnitarisable A.ρ

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem iso_ctr {n : ℕ} {A C : BR k n} (hs : Sm A) (h : IU A) (hc : CjB A C) : Iso (ctr A) C :=
  contra_equiv_of_conj A.ρ C.ρ hs h.1 h.2 hc

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem cj_mp {h N : ℕ} (n : Fin h → ℕ) (hd : ∑ j, n j = N) (A C : ∀ a, BR k (n a)) (hc : ∀ a, CjB (A a) (C a)) :
    CjB (mp n hd A) (mp n hd C) :=
  PositivityTheory.RgGu.NR.conjProd k h N n hd _ _ (fun a => (A a).ρ) (fun a => (C a).ρ) hc

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem cj_one {n : ℕ} (c c' : IrrCl (GL (Fin n) k)) (h : ConjEquiv c.rep.ρ c'.rep.ρ) : CjB (one ⟨n, c⟩) (one ⟨n, c'⟩) := h

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem iu_pr {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ j, (x j).1 = N) (hi : (prodIrr x hd).IsIrreducible)
    (hu : IsUnitarisable (prodIrr x hd)) : IU (pr x hd) := ⟨hi, hu⟩

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem of_iso_ctr {h N : ℕ} (x y : Fin h → IrrGL k) (hd : ∑ j, (x j).1 = N) (hd' : ∑ j, (y j).1 = N)
    (H : Iso (ctr (pr x hd)) (pr y hd')) : Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr y hd')) := H

attribute [irreducible] CjB ctr IU

unseal GlobalTheory.ProdFlatten.pr in
theorem cj_pr {h N : ℕ} (n : Fin h → ℕ) (c c' : ∀ a, IrrCl (GL (Fin (n a)) k)) (hd : ∑ j, n j = N)
    (hc : ∀ a, ConjEquiv (c a).rep.ρ (c' a).rep.ρ) : CjB (pr (fun a => ⟨n a, c a⟩) hd) (pr (fun a => ⟨n a, c' a⟩) hd) :=
  cj_mp n hd (fun a => one ⟨n a, c a⟩) (fun a => one ⟨n a, c' a⟩) fun a => cj_one (c a) (c' a) (hc a)

theorem conjugate_product_of_pairs {h N : ℕ} (x y : Fin h → IrrGL k) (H : ∀ a, C1 (x a) (y a)) (hd : ∑ j, (x j).1 = N) :
    ∃ hd' : ∑ j, (y j).1 = N, CjB (pr x hd) (pr y hd') := by
  choose n c c' e e' hc using H
  obtain rfl : x = fun a => ⟨n a, c a⟩ := funext e
  obtain rfl : y = fun a => ⟨n a, c' a⟩ := funext e'
  exact ⟨hd, cj_pr n c c' hd hc⟩

theorem contragredient_product_of_pairs {h N : ℕ} (x y : Fin h → IrrGL k) (H : ∀ a, C1 (x a) (y a)) (hd : ∑ j, (x j).1 = N)
    (hi : (prodIrr x hd).IsIrreducible) (hu : IsUnitarisable (prodIrr x hd)) :
    ∃ hd' : ∑ j, (y j).1 = N, Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr y hd')) :=
  (conjugate_product_of_pairs x y H hd).imp fun hd' hc => of_iso_ctr x y hd hd' (iso_ctr (sm_pr x hd) (iu_pr x hd hi hu) hc)

theorem contragredient_pair_twist (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (δ : IrrGL k) (hu : IsUnitarisable δ.rep) (s : ℝ) :
    C1 (δ.nu s) ((Zc.dualCl δ).nu s) := by
  have hs : IsSmooth (twist (contra δ.rep) (detChar (Fin δ.1) (absPow k (s : ℂ)))) :=
    isSmooth_twist (isSmooth_contra _) (isSmoothChar_absPow _).detChar
  have hi : (twist (contra δ.rep) (detChar (Fin δ.1) (absPow k (s : ℂ)))).IsIrreducible :=
    isIrreducible_twist (GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA _ δ.2.rep.smooth δ.2.rep.irr) _
  refine ⟨δ.1, (δ.nu s).2, (IrrGL.of _ hs hi).2, rfl, ?_, ?_⟩
  · show _ = IrrGL.of _ hs hi
    rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA, IrrGL.nu, IrrGL.tw_of]
  · exact conjEquiv_trans_equiv (equiv_trans_conjEquiv (IrrGL.twEquiv δ (absPow k (s : ℂ)) (isSmoothChar_absPow _)).symm
      (PositivityTheory.RgGu.NR.conjDual k δ.1 _ δ.rep δ.2.rep.smooth δ.2.rep.irr hu s)) (IrrGL.equivOf _ hs hi)

theorem conj_side (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (δ : Fin h → IrrGL k) (s : Fin h → ℝ)
    (hδu : ∀ j, IsUnitarisable (δ j).rep) (hd : ∑ j, ((δ j).nu (s j)).1 = N)
    (hi : (prodIrr (fun j => (δ j).nu (s j)) hd).IsIrreducible)
    (hu : IsUnitarisable (prodIrr (fun j => (δ j).nu (s j)) hd)) :
    ∃ hd' : ∑ j, ((Zc.dualCl (δ j)).nu (s j)).1 = N,
      Nonempty ((contra (prodIrr (fun j => (δ j).nu (s j)) hd)).Equiv
        (prodIrr (fun j => (Zc.dualCl (δ j)).nu (s j)) hd')) :=
  contragredient_product_of_pairs (fun j => (δ j).nu (s j)) (fun j => (Zc.dualCl (δ j)).nu (s j)) (fun j => contragredient_pair_twist hA (δ j) (hδu j) (s j)) hd hi hu

end Local

end PositivityTheory.Gud.Symm.Pf

end
