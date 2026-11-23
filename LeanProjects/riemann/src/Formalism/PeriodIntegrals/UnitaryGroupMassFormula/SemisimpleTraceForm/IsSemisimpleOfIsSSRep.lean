import Mathlib
import Formalism.PeriodIntegrals.SSAscent
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceNilStep

namespace PI.SSAscent.UnitaryGroupMassFormula

open PI.SSAscent
open Matrix

section Bridge

variable {k : Type} [Field k] {a : ℕ}

def stabAlg (W : Submodule k (Fin a → k)) : Subalgebra k (Matrix (Fin a) (Fin a) k) where
  carrier := {x | ∀ v ∈ W, x *ᵥ v ∈ W}
  mul_mem' := by
    intro x y hx hy v hv
    rw [← Matrix.mulVec_mulVec]
    exact hx _ (hy v hv)
  add_mem' := by
    intro x y hx hy v hv
    rw [Matrix.add_mulVec]
    exact W.add_mem (hx v hv) (hy v hv)
  algebraMap_mem' := by
    intro c v hv
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem c hv

private theorem mem_stabAlg_iff (W : Submodule k (Fin a → k))
    (x : Matrix (Fin a) (Fin a) k) : x ∈ stabAlg W ↔ ∀ v ∈ W, x *ᵥ v ∈ W :=
  Iff.rfl

theorem imAlg_le_stabAlg {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k))
    (h : IsInv ρ W) : imAlg ρ ≤ stabAlg W := by
  unfold imAlg
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨g, rfl⟩
  exact (mem_stabAlg_iff W _).mpr (fun v hv => h g v hv)

instance towerSub (A : Subalgebra k (Matrix (Fin a) (Fin a) k)) :
    IsScalarTower k A (Fin a → k) where
  smul_assoc c x v := by
    change ((c • x : A) : Matrix (Fin a) (Fin a) k) *ᵥ v = c • ((x : Matrix (Fin a) (Fin a) k) *ᵥ v)
    rw [Subalgebra.coe_smul, Matrix.smul_mulVec]

theorem smul_sub_def (A : Subalgebra k (Matrix (Fin a) (Fin a) k)) (x : A) (v : Fin a → k) :
    x • v = (x : Matrix (Fin a) (Fin a) k) *ᵥ v := rfl

def liftSub (A : Subalgebra k (Matrix (Fin a) (Fin a) k)) (W : Submodule k (Fin a → k))
    (h : A ≤ stabAlg W) : Submodule A (Fin a → k) where
  carrier := W
  add_mem' := W.add_mem
  zero_mem' := W.zero_mem
  smul_mem' x v hv := by
    rw [smul_sub_def]
    exact h x.2 v hv

theorem restrict_liftSub (A : Subalgebra k (Matrix (Fin a) (Fin a) k)) (W : Submodule k (Fin a → k))
    (h : A ≤ stabAlg W) : (liftSub A W h).restrictScalars k = W := by
  ext v
  exact Iff.rfl

theorem isInv_restrict {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k)
    (N : Submodule (imAlg ρ) (Fin a → k)) : IsInv ρ (N.restrictScalars k) := by
  intro g v hv
  have hg : (ρ g : Matrix (Fin a) (Fin a) k) ∈ imAlg ρ :=
    Algebra.subset_adjoin ⟨g, rfl⟩
  have hmem : (⟨_, hg⟩ : imAlg ρ) • v ∈ N := N.smul_mem _ hv
  rw [smul_sub_def] at hmem
  exact hmem

private theorem mem_liftSub_iff (A : Subalgebra k (Matrix (Fin a) (Fin a) k))
    (W : Submodule k (Fin a → k)) (h : A ≤ stabAlg W) (v : Fin a → k) :
    v ∈ liftSub A W h ↔ v ∈ W :=
  Iff.rfl

private theorem exists_isCompl_of_isSSRep {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k)
    (hρ : PI.SSAscent.IsSSRep ρ) (N : Submodule (imAlg ρ) (Fin a → k)) :
    ∃ N', IsCompl N N' := by
  obtain ⟨W', hW', hc⟩ := hρ (N.restrictScalars k) (isInv_restrict ρ N)
  have hle : imAlg ρ ≤ stabAlg W' := imAlg_le_stabAlg ρ W' hW'
  refine ⟨liftSub (imAlg ρ) W' hle, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxN hxW'
    exact (Submodule.disjoint_def.mp hc.disjoint) x hxN
      ((mem_liftSub_iff _ W' hle x).mp hxW')
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hx : x ∈ N.restrictScalars k ⊔ W' := by
      rw [codisjoint_iff.mp hc.codisjoint]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
    exact Submodule.mem_sup.mpr ⟨y, hy, z, (mem_liftSub_iff _ W' hle z).mpr hz, hyz⟩

theorem isSemisimple_of_isSSRep {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k) (hρ : IsSSRep ρ) :
    IsSemisimpleModule (imAlg ρ) (Fin a → k) := by
  have key : ∀ N : Submodule (imAlg ρ) (Fin a → k), ∃ N', IsCompl N N' :=
    exists_isCompl_of_isSSRep ρ hρ
  haveI : ComplementedLattice (Submodule (imAlg ρ) (Fin a → k)) := ⟨key⟩
  exact ⟨⟩

theorem isSSRep_of_isSemisimple {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k)
    (h : IsSemisimpleModule (imAlg ρ) (Fin a → k)) : IsSSRep ρ := by
  intro W hW
  have hle : imAlg ρ ≤ stabAlg W := imAlg_le_stabAlg ρ W hW
  obtain ⟨N', hc⟩ := exists_isCompl (liftSub (imAlg ρ) W hle)
  refine ⟨N'.restrictScalars k, isInv_restrict ρ N', ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxW hxN'
    exact (Submodule.disjoint_def.mp hc.disjoint) x
      ((mem_liftSub_iff _ W hle x).mpr hxW) hxN'
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hx : x ∈ liftSub (imAlg ρ) W hle ⊔ N' := by
      rw [codisjoint_iff.mp hc.codisjoint]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
    exact Submodule.mem_sup.mpr ⟨y, (mem_liftSub_iff _ W hle y).mp hy, z, hz, hyz⟩

end Bridge

end PI.SSAscent.UnitaryGroupMassFormula
