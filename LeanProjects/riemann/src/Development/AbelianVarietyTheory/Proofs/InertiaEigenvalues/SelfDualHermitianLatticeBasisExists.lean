import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitNorm

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.SelfDualLattice

section Forms

variable {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
  {h : V → V → K.E}

def formL (hadd : ∀ x y z, h (x + y) z = h x z + h y z) (hsmul : ∀ (c : K.E) x z, h (c • x) z = c * h x z)
    (z : V) : V →ₗ[K.E] K.E where
  toFun x := h x z
  map_add' x y := hadd x y z
  map_smul' c x := hsmul c x z

end Forms

end GlobalTheory.SelfDualLattice

namespace GlobalTheory.SelfDualLattice

variable {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
  {h : V → V → K.E}

end GlobalTheory.SelfDualLattice

namespace GlobalTheory.SelfDualLattice

theorem exists_orthonormal_family (K : UQ)
    (hN : ∀ u : K.Oˣ, K.c (algebraMap K.O K.E u) = algebraMap K.O K.E u →
      ∃ z : K.Oˣ, algebraMap K.O K.E u = algebraMap K.O K.E z * K.c (algebraMap K.O K.E z))
    (hT : ∃ z : K.O, algebraMap K.O K.E z + K.c (algebraMap K.O K.E z) = 1) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
      [Module.Finite K.E V] (h : V → V → K.E), Module.finrank K.E V = n →
      (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) →
      (∀ x y, h y x = K.c (h x y)) → ∀ L : Submodule K.O V, L.FG →
      Submodule.span K.E (L : Set V) = ⊤ →
      (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
      ∃ m, ∃ v : Fin m → V, (∀ i j, h (v i) (v j) = if i = j then 1 else 0) ∧
        Submodule.span K.O (Set.range v) = L := by
  first
  | exact @_root_.GlobalTheory.UnitPairNorm.main
  | exact _root_.GlobalTheory.UnitPairNorm.main
  | (apply _root_.GlobalTheory.UnitPairNorm.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitPairNorm.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitPairNorm.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitPairNorm.main ..)

end GlobalTheory.SelfDualLattice

namespace GlobalTheory.SelfDualLattice

theorem exists_orthonormal_basis : ∀ (K : UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [Module.Finite K.E V] (h : V → V → K.E),
    (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) →
    (∀ x y, h y x = K.c (h x y)) → ∀ L : Submodule K.O V, L.FG →
    Submodule.span K.E (L : Set V) = ⊤ →
    (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V, Submodule.span K.O (Set.range b) = L ∧
      ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  intro K V _ _ _ _ _ h hadd hsmul hsym L hfg hspan hdual
  obtain ⟨hN, hT, -, -⟩ := GlobalTheory.T.unramifiedQuadratic_norms_trace_uniformizer_facts K
  obtain ⟨m, v, hvo, hvs⟩ := exists_orthonormal_family K hN hT _ V h rfl hadd hsmul hsym L hfg hspan hdual
  have hli : LinearIndependent K.E v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (formL hadd hsmul (v i)) hg
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    change ∑ j, g j * h (v j) (v i) = 0 at this
    simpa [hvo] using this
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range v) := by
    rw [← hspan, ← hvs, Submodule.span_span_of_tower]
  set b0 := Module.Basis.mk hli hsp with hb0
  have hm : m = Module.finrank K.E V := by
    rw [Module.finrank_eq_card_basis b0, Fintype.card_fin]
  refine ⟨b0.reindex (finCongr hm), ?_, ?_⟩
  · rw [Module.Basis.range_reindex, hb0, Module.Basis.coe_mk, hvs]
  · intro i j
    simp only [Module.Basis.reindex_apply, hb0, Module.Basis.coe_mk, hvo]
    simp

end GlobalTheory.SelfDualLattice
