import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.GenericUnitary

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N : ℕ}

def IsUnitaryLSeg (δ : IrrGL k) : Prop := (∃ Δ : Segment k, IsLSeg Δ δ.rep) ∧ IsUnitarisable δ.rep

def factors (δ : List (IrrGL k)) (τ : List (IrrGL k × ℝ)) : List (IrrGL k) :=
  δ ++ τ.flatMap fun p => [p.1.nu (p.2 : ℝ), p.1.nu ((-p.2 : ℝ) : ℂ)]

def IsComplementaryProduct (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ (δ : List (IrrGL k)) (τ : List (IrrGL k × ℝ)), (∀ x ∈ δ, IsUnitaryLSeg x) ∧
    (∀ p ∈ τ, IsUnitaryLSeg p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) ∧
    ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), List.ofFn x = factors δ τ ∧
      Nonempty (π.Equiv (prodIrr x hd))

end GlobalTheory.GenericUnitary

namespace GlobalTheory.Published

def GenericUnitaryDualGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π → IsGeneric π → GenericUnitary.IsComplementaryProduct π

end GlobalTheory.Published

namespace GlobalTheory.GenericUnitary

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N : ℕ}

theorem exists_of_mem_factors {δ : List (IrrGL k)} {τ : List (IrrGL k × ℝ)} (hδ : ∀ x ∈ δ, IsUnitaryLSeg x)
    (hτ : ∀ p ∈ τ, IsUnitaryLSeg p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) {y : IrrGL k} (hy : y ∈ factors δ τ) :
    ∃ (x : IrrGL k) (s : ℝ), IsUnitaryLSeg x ∧ |s| < 1 / 2 ∧ y = x.nu s := by
  rcases List.mem_append.1 hy with hy | hy
  · exact ⟨y, 0, hδ y hy, by norm_num, by simp⟩
  · obtain ⟨p, hp, hy⟩ := List.mem_flatMap.1 hy
    obtain ⟨h1, h2, h3⟩ := hτ p hp
    rcases List.mem_pair.1 hy with rfl | rfl
    · exact ⟨p.1, p.2, h1, by rwa [abs_of_pos h2], rfl⟩
    · exact ⟨p.1, -p.2, h1, by rwa [abs_neg, abs_of_pos h2], rfl⟩

theorem IsComplementaryProduct.exists_prod {π : Representation ℂ (GL (Fin N) k) V} (H : IsComplementaryProduct π) :
    ∃ (h : ℕ) (δ : Fin h → IrrGL k) (Δ : Fin h → Segment k) (s : Fin h → ℝ),
      (∀ j, IsLSeg (Δ j) (δ j).rep) ∧ (∀ j, IsUnitarisable (δ j).rep) ∧ (∀ j, |s j| < 1 / 2) ∧
      ∃ hd : ∑ j, ((δ j).nu (s j)).1 = N, Nonempty (π.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) := by
  obtain ⟨δ, τ, hδ, hτ, h, x, hd, hx, φ⟩ := H
  choose y s hy hs e using fun j => exists_of_mem_factors hδ hτ (y := x j) (hx ▸ List.mem_ofFn.2 ⟨j, rfl⟩)
  choose Δ hΔ using fun j => (hy j).1
  obtain rfl : x = fun j => (y j).nu (s j) := funext e
  exact ⟨h, y, Δ, s, hΔ, fun j => (hy j).2, hs, hd, φ⟩

theorem isUnitarisable_of_equiv {G : Type} [Group G] {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : π.Equiv σ) (h : IsUnitarisable π) : IsUnitarisable σ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B ∘ₗ φ.symm.toLinearEquiv.toLinearMap).compl₂ φ.symm.toLinearEquiv.toLinearMap, fun v w => h1 _ _,
    fun v hv => h2 _ (φ.symm.toLinearEquiv.map_ne_zero_iff.2 hv), fun g v w => ?_⟩
  have e : ∀ v, φ.symm.toLinearEquiv (σ g v) = π g (φ.symm.toLinearEquiv v) := fun v =>
    φ.symm.toIntertwiningMap.isIntertwining _ _ g v
  show B (φ.symm.toLinearEquiv (σ g v)) (φ.symm.toLinearEquiv (σ g w)) = _
  rw [e, e, h3]
  rfl

theorem isUnitaryLSeg_of_isCusp {ρ : IrrGL k} (hρ : ρ.IsCusp) (hu : IsUnitarisable ρ.rep) : IsUnitaryLSeg ρ :=
  ⟨⟨_, (single_spec hρ).2.1⟩, hu⟩

theorem IsUnitaryLSeg.isComplementaryProduct {δ : IrrGL k} (h : IsUnitaryLSeg δ) : IsComplementaryProduct δ.rep :=
  ⟨[δ], [], by simpa using h, by simp, 1, fun _ => δ, by simp, rfl, nonempty_equiv_prodIrr_one δ _⟩

theorem IsComplementaryProduct.of_equiv {π : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W}
    (H : IsComplementaryProduct π) (φ : π.Equiv σ) : IsComplementaryProduct σ := by
  obtain ⟨δ, τ, hδ, hτ, h, x, hd, hx, ⟨ψ⟩⟩ := H
  exact ⟨δ, τ, hδ, hτ, h, x, hd, hx, ⟨φ.symm.trans ψ⟩⟩

theorem isComplementaryProduct_of_isCuspidal {π : Representation ℂ (GL (Fin N) k) V} (hN : 0 < N)
    (hi : π.IsIrreducible) (hc : IsCuspidal π) (hu : IsUnitarisable π) : IsComplementaryProduct π :=
  (isUnitaryLSeg_of_isCusp (IrrGL.isCusp_of.2 ⟨hN, hc⟩)
    (isUnitarisable_of_equiv (IrrGL.equivOf π hc.1 hi) hu)).isComplementaryProduct.of_equiv
    (IrrGL.equivOf π hc.1 hi).symm

theorem unitaryChar_spec {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    IsSmooth (detRep (Fin 1) χ) ∧ (detRep (Fin 1) χ).IsIrreducible ∧ IsUnitarisable (detRep (Fin 1) χ) ∧
      IsGeneric (detRep (Fin 1) χ) ∧ IsComplementaryProduct (detRep (Fin 1) χ) :=
  have h : IsUnitarisable (detRep (Fin 1) χ) := (isUnitarisable_ofChar_iff _).2 fun _ => hu _
  ⟨(isCuspidal_detRep_one hs).1, isIrreducible_ofChar _, h, isGeneric_detRep_one χ,
    isComplementaryProduct_of_isCuspidal one_pos (isIrreducible_ofChar _) (isCuspidal_detRep_one hs) h⟩

end GlobalTheory.GenericUnitary

namespace GlobalTheory.Published

theorem GenericUnitaryDualGL.exists_prod (H : GenericUnitaryDualGL) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (hs : IsSmooth π) (hi : π.IsIrreducible) (hu : IsUnitarisable π)
    (hg : IsGeneric π) :
    ∃ (h : ℕ) (δ : Fin h → IrrGL k) (Δ : Fin h → Segment k) (s : Fin h → ℝ),
      (∀ j, IsLSeg (Δ j) (δ j).rep) ∧ (∀ j, IsUnitarisable (δ j).rep) ∧ (∀ j, |s j| < 1 / 2) ∧
      ∃ hd : ∑ j, ((δ j).nu (s j)).1 = N, Nonempty (π.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) :=
  (H k N V π hs hi hu hg).exists_prod

end GlobalTheory.Published
