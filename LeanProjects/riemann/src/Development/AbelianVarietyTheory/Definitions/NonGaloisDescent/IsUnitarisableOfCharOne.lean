import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsSquareIntegrableOfTrivial

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N t : ℕ}

namespace IrrGL

def IsEssSqInt (x : IrrGL k) : Prop :=
  ∃ (δ : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), UnitaryDual.IsSquareIntegrable δ ∧ x = δ.tw χ hχ

theorem IsEssSqInt.tw {x : IrrGL k} (h : x.IsEssSqInt) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : (x.tw χ hχ).IsEssSqInt := by
  obtain ⟨δ, ψ, hψ, hδ, rfl⟩ := h
  exact ⟨δ, ψ * χ, hψ.mul hχ, hδ, tw_tw _ _ _ _ _⟩

theorem IsEssSqInt.nu {x : IrrGL k} (h : x.IsEssSqInt) (s : ℂ) : (x.nu s).IsEssSqInt := h.tw _ _

end IrrGL

def IsBoxSum (x : Fin t → IrrGL k) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ (Δ : Fin t → Segment k) (σ : Equiv.Perm (Fin t)) (hd : ∑ a, (x (σ a)).1 = N),
    (∀ i, IsLSeg (Δ i) (x i).rep) ∧ (∀ i j, i < j → ¬ (Δ (σ i)).Precedes (Δ (σ j))) ∧
      IsCosocle π (prodIrr (fun a => x (σ a)) hd)

def IsGenSpeh (π₀ : IrrGL k) (t : ℕ) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  π₀.IsCusp ∧ IsUnitarisable π₀.rep ∧ 0 < t ∧ IsBoxSum (spehFactor π₀ t) π

section BoxSum

variable {x : Fin t → IrrGL k} {π : Representation ℂ (GL (Fin N) k) V}

theorem IsBoxSum.of_equiv (h : IsBoxSum x π) {σ' : Representation ℂ (GL (Fin N) k) W} (φ : π.Equiv σ') :
    IsBoxSum x σ' := by
  obtain ⟨Δ, σ, hd, hL, hP, hc⟩ := h
  exact ⟨Δ, σ, hd, hL, hP, hc.of_equiv φ (.refl _)⟩

theorem IsBoxSum.sum_fst (h : IsBoxSum x π) : ∑ a, (x a).1 = N := by
  obtain ⟨-, σ, hd, -⟩ := h
  rw [← hd]
  exact (Equiv.sum_comp σ (fun a => (x a).1)).symm

theorem isBoxSum_single {y : IrrGL k} {Δ : Segment k} (hΔ : IsLSeg Δ y.rep) :
    IsBoxSum (fun _ : Fin 1 => y) y.rep := by
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_one y (by simp)
  exact ⟨fun _ => Δ, Equiv.refl _, by simp, fun _ => hΔ, fun i j hij => absurd (Subsingleton.elim i j) hij.ne,
    (isCosocle_self y.2.rep.irr).of_equiv (.refl _) φ⟩

end BoxSum

section GenSpeh

theorem IsGenSpeh.of_equiv {π₀ : IrrGL k} {π : Representation ℂ (GL (Fin N) k) V} (h : IsGenSpeh π₀ t π)
    {σ : Representation ℂ (GL (Fin N) k) W} (φ : π.Equiv σ) : IsGenSpeh π₀ t σ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.of_equiv φ⟩

theorem IsGenSpeh.mul_eq {π₀ : IrrGL k} {π : Representation ℂ (GL (Fin N) k) V} (h : IsGenSpeh π₀ t π) :
    t * π₀.1 = N := by
  rw [← h.2.2.2.sum_fst]
  simp [spehFactor]

example : ¬ IsGenSpeh (IrrGL.ofChar (1 : kˣ →* ℂˣ) isSmoothChar_one) 1 (detRep (Fin 2) (1 : kˣ →* ℂˣ)) := fun h => by
  have := h.mul_eq
  simp [IrrGL.ofChar] at this

example (π₀ : IrrGL k) (π : Representation ℂ (GL (Fin 0) k) V) : ¬ IsGenSpeh π₀ 0 π := fun h => h.2.2.1.false

example : IsBoxSum (fun _ : Fin 1 => IrrGL.ofChar (1 : kˣ →* ℂˣ) isSmoothChar_one)
    (IrrGL.ofChar (1 : kˣ →* ℂˣ) isSmoothChar_one).rep :=
  isBoxSum_single (single_spec (IrrGL.isCusp_ofChar _ _)).2.1

end GenSpeh

end GlobalTheory.LocGL
