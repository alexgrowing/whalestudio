import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv

noncomputable section

open ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace UpperTheory.TNZ.ProductIrreducible₂

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem exists_det_eq (u : kˣ) : ∃ g : GL (Fin 1) k, GeneralLinearGroup.det g = u := by
  refine ⟨⟨Matrix.diagonal fun _ => (u : k), Matrix.diagonal fun _ => ((u⁻¹ : kˣ) : k), ?_, ?_⟩, ?_⟩
  · simp [Matrix.diagonal_mul_diagonal]
  · simp [Matrix.diagonal_mul_diagonal]
  · ext
    simp [Matrix.GeneralLinearGroup.val_det_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem char_eq_of_equiv {μ μ' χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ (GL (Fin 1) k) W} (ψ : (detRep (Fin 1) μ').Equiv τ)
    (φ : (detRep (Fin 1) μ).Equiv (twist τ (detChar (Fin 1) χ))) (g : GL (Fin 1) k) :
    (μ (GeneralLinearGroup.det g) : ℂ) =
      (χ (GeneralLinearGroup.det g) : ℂ) * (μ' (GeneralLinearGroup.det g) : ℂ) := by
  have hτ : ∀ w : W, τ g w = (μ' (GeneralLinearGroup.det g) : ℂ) • w := by
    intro w
    obtain ⟨x, rfl⟩ := ψ.toLinearEquiv.surjective w
    have key : ψ.toLinearEquiv (detRep (Fin 1) μ' g x) = τ g (ψ.toLinearEquiv x) :=
      LinearMap.congr_fun (ψ.toIntertwiningMap.isIntertwining' g) x
    rw [← key]
    simp only [detRep, ofChar_apply, detChar_apply]
    rw [← smul_eq_mul, map_smul]
  have key : φ.toLinearEquiv (detRep (Fin 1) μ g 1) = twist τ (detChar (Fin 1) χ) g (φ.toLinearEquiv 1) :=
    LinearMap.congr_fun (φ.toIntertwiningMap.isIntertwining' g) 1
  simp only [detRep, ofChar_apply, detChar_apply, twist_apply, hτ, mul_one, smul_smul] at key
  have hne : φ.toLinearEquiv 1 ≠ 0 := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]
    exact one_ne_zero
  have h1 : φ.toLinearEquiv ((μ (GeneralLinearGroup.det g) : ℂ)) =
      (μ (GeneralLinearGroup.det g) : ℂ) • φ.toLinearEquiv 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [h1] at key
  exact smul_left_injective ℂ hne key

theorem eq_on_units (y : IrrGL k) (h : 1 = y.1) (μ μ' : kˣ →* ℂˣ) (hμ : IsSmoothChar μ)
    (hs' : IsSmooth (detRep (Fin 1) μ')) (hi' : (detRep (Fin 1) μ').IsIrreducible)
    (hy : IrrGL.of (detRep (Fin 1) μ') hs' hi' = y) (j : ℤ)
    (hφ : Nonempty ((h ▸ GlobalTheory.SplitRead.Irr.ofDet 1 μ hμ : GlobalTheory.SplitRead.Irr k y.1).π.Equiv
      (twist (GlobalTheory.SplitRead.Irr.ofIrrRep y.2.rep).π (detChar (Fin y.1) (absPow k (j : ℂ))))))
    (u : kˣ) (hu : valuation k (u : k) = 1) : μ u = μ' u := by
  subst hy
  obtain ⟨φ⟩ := hφ
  obtain ⟨g, hg⟩ := exists_det_eq u
  have := char_eq_of_equiv (IrrGL.equivOf (detRep (Fin 1) μ') hs' hi') φ g
  rw [hg] at this
  have habs : (absPow k (j : ℂ) u : ℂ) = 1 := by
    rw [val_absPow, nabs_eq_one (k := k) hu]
    simp
  rw [habs, one_mul] at this
  exact Units.ext this

theorem product_irreducible_of_distinct_twists (hL : GlobalTheory.Mem.LiteralAutomorphy.LitLoc) :
    ∀ (s N : ℕ) (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)]
      [∀ b, Module ℂ (X b)] (σ : ∀ b, Representation ℂ (GL (Fin (d b)) k) (X b)),
      (∀ b, IsSmooth (σ b)) → (∀ b, (σ b).IsIrreducible) → ∀ η : Fin s → kˣ →* ℂˣ,
      (∀ b c, b ≠ c → ∃ u : kˣ, valuation k (u : k) = 1 ∧ η b u ≠ η c u) →
      ∀ μ : ∀ b, Fin (d b) → kˣ →* ℂˣ,
      (∀ b j, IsSmoothChar (μ b j) ∧ ∀ u : kˣ, valuation k (u : k) = 1 → μ b j u = η b u) →
      (∀ b, IsCuspSupport (σ b) (fun _ => 1) (fun j => detRep (Fin 1) (μ b j))) →
        (multiProd (stdBlocks d hd) σ).IsIrreducible := by
  intro s
  induction s with
  | zero =>
    intros
    exact GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd_zero _ _
  | succ s ih =>
    intro N d hd X _ _ σ hs hi η hη μ hμ hcs
    have e : N = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ _)
    subst e
    obtain ⟨E⟩ := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ d hd σ
    have hτi : (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ).IsIrreducible :=
      ih _ (fun i => d i.succ) rfl (fun i => X i.succ) (fun i => σ i.succ) (fun i => hs _) (fun i => hi _)
        (fun i => η i.succ) (fun b c hbc => hη _ _ fun h => hbc (Fin.succ_injective _ h))
        (fun i => μ i.succ) (fun i => hμ _) (fun i => hcs _)
    have hτs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ) :=
      isSmooth_parInd _ _
    obtain ⟨h', x, hx, hxc⟩ := GlobalTheory.LocGL.SupportRing.hasSupport_multiProd hL.zel (d := fun i : Fin s => d i.succ) rfl
      (fun i => σ i.succ) (fun i => hs _) (fun i => hi _) (fun i => hasSupport_of_isCuspSupport (hcs i.succ)) hτi
    have hP := hL.disj k (d 0) (∑ i : Fin s, d i.succ) (d 0) h'
      { V := X 0, π := σ 0, smooth := hs 0, irr := hi 0 }
      { V := _, π := multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ, smooth := hτs,
        irr := hτi }
      (fun _ => 1) (fun b => (x b).1) (fun a => GlobalTheory.SplitRead.Irr.ofDet 1 (μ 0 a) (hμ 0 a).1)
      (fun b => GlobalTheory.SplitRead.Irr.ofIrrRep (x b).2.rep) (hcs 0) hxc ?_
    · exact GlobalTheory.Parabolic.isIrreducible_of_equiv E hP
    · intro a b hab j _ hφ
      have hxb : x b ∈ ∑ i : Fin s, Finset.univ.val.map fun a =>
          IrrGL.of (detRep (Fin 1) (μ i.succ a)) ((hcs i.succ).2.1 a).2.2.1 ((hcs i.succ).2.1 a).2.1 := by
        rw [← hx]
        exact Multiset.mem_map_of_mem x (Finset.mem_univ_val b)
      obtain ⟨c, -, hc⟩ := Multiset.mem_sum.1 hxb
      obtain ⟨j', -, hj'⟩ := Multiset.mem_map.1 hc
      obtain ⟨u, hu, hne⟩ := hη 0 c.succ (Fin.succ_ne_zero c).symm
      apply hne
      rw [← (hμ 0 a).2 u hu, ← (hμ c.succ j').2 u hu]
      exact eq_on_units (x b) hab (μ 0 a) (μ c.succ j') (hμ 0 a).1 _ _ hj' j hφ u hu

end UpperTheory.TNZ.ProductIrreducible₂

namespace UpperTheory.TNZ

theorem step_prodIrr : ProductIrreducibleProp := by
  unfold ProductIrreducibleProp
  intro hC hL k _ _ _ _ s N d hd X _ _ σ hs hi η hη hdv hne
  have H := fun b => hC hL k (d b) (X b) (σ b) (hs b) (hi b) (η b) (hη b) (hdv b)
  choose μ hμ hcs using H
  exact ProductIrreducible₂.product_irreducible_of_distinct_twists hL s N d hd X σ hs hi η hne μ hμ hcs

end UpperTheory.TNZ
