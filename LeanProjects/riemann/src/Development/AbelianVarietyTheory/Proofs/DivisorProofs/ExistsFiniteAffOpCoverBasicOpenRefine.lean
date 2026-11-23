import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsTop
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent

namespace GlobalTheory

theorem exists_finite_affOp_cover_basicOpen_refine :
    ∀ (X : Scheme.{0}) [IsIntegral X] [CompactSpace X], ∃ (ι : Type) (_ : Finite ι) (W : ι → AffOp X), ∀ U : AffOp X, ∃ (m : ℕ) (a : Fin m → Γ(X, U.1)) (V : Fin m → AffOp X), Ideal.span (Set.range a) = ⊤ ∧ ∀ k, (V k).1 = X.basicOpen (a k) ∧ ∃ i, (V k).1 ≤ (W i).1 := by
  intro X _ _
  have hB := X.isBasis_affineOpens
  have hx : ∀ x : X, ∃ U' : X.Opens, IsAffineOpen U' ∧ x ∈ U' := by
    intro x
    obtain ⟨U', hU', hxU', -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp hB) (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨U', hU', hxU'⟩
  choose W₀ hW₀a hW₀x using hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (W₀ x : Set X))
    (fun x => (W₀ x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hW₀x x⟩)
  refine ⟨t, inferInstance, fun x => ⟨W₀ x.1, hW₀a x.1, ⟨⟨x.1, hW₀x x.1⟩⟩⟩, ?_⟩
  intro U
  have hcov : ∀ x : X, ∃ i : t, x ∈ W₀ i.1 := by
    intro x
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨⟨i, hi⟩, hxi⟩
  choose ix hix using hcov
  have hf : ∀ x : U.1, ∃ f : Γ(X, U.1), X.basicOpen f ≤ U.1 ⊓ W₀ (ix x.1).1 ∧ (x : X) ∈ X.basicOpen f := by
    intro x
    exact U.2.1.exists_basicOpen_le (V := U.1 ⊓ W₀ (ix x.1).1) ⟨x.1, ⟨x.2, hix x.1⟩⟩ x.2
  choose f hfle hfx using hf
  obtain ⟨s, hs⟩ := U.2.1.isCompact.elim_finite_subcover (fun x : U.1 => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).isOpen) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hfx ⟨x, hx⟩⟩)
  let e := s.equivFin
  refine ⟨s.card, fun k => f (e.symm k).1, fun k => ⟨X.basicOpen (f (e.symm k).1), U.2.1.basicOpen _, ⟨⟨(e.symm k).1.1, hfx _⟩⟩⟩, ?_, fun k => ⟨rfl, ⟨ix (e.symm k).1.1, le_trans (hfle _) inf_le_right⟩⟩⟩
  rw [← U.2.1.iSup_basicOpen_eq_self_iff]
  apply le_antisymm
  · exact iSup_le fun g => X.basicOpen_le g.1
  · intro x hxU
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hxU)
    have : (x : X) ∈ ((⨆ g : Set.range (fun k => f (e.symm k).1), X.basicOpen (g : Γ(X, U.1)) : X.Opens) : Set X) := by
      rw [TopologicalSpace.Opens.coe_iSup]
      refine Set.mem_iUnion.mpr ⟨⟨f y, ⟨e ⟨y, hy⟩, by simp⟩⟩, hxy⟩
    exact this

end GlobalTheory
