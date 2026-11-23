import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Formalism.SharpRestriction.LevelLetterCocycles.HerrClassFieldOfNorms

noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation TensorProduct

section Gen

variable (S : Sit)

def oneT (T : LocLat S.G S.Qp S.LL S.O) : ↥T.L.T →ₗ[S.O] TW S.RW T :=
  TensorProduct.mk S.O S.RW ↥T.L.T 1

def OneInj : Prop := ∀ T : LocLat S.G S.Qp S.LL S.O, Function.Injective (oneT S T)

def GenFix : Prop :=
  ∀ (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T),
    (∀ g, S.W.resΓ g = S.W.gamK → T.actT g t = t) →
    (∀ g, S.W.resΓ g ∈ S.W.DelF → T.actT g t = t) →
    (∀ g, S.W.resΓ g = 1 → T.actT g t = t) → ∀ g, T.actT g t = t

variable {S}

theorem oneT_apply (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T) : oneT S T t = (1 : S.RW) ⊗ₜ[S.O] t := rfl

theorem TWact_one {R : Type} [CommRing R] [Algebra S.O R] (f : R →ₐ[S.O] R) (T : LocLat S.G S.Qp S.LL S.O)
    (g : S.G) (t : ↥T.L.T) : TWact f T g ((1 : R) ⊗ₜ[S.O] t) = (1 : R) ⊗ₜ[S.O] T.actT g t := by
  simp only [TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]

theorem TWmap_one {R : Type} [CommRing R] [Algebra S.O R] (f : R →ₐ[S.O] R) (T : LocLat S.G S.Qp S.LL S.O)
    (t : ↥T.L.T) : TWmap f T ((1 : R) ⊗ₜ[S.O] t) = (1 : R) ⊗ₜ[S.O] t := by
  simp only [TWmap, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, LinearMap.id_apply]

theorem mem_H0Lat {T : LocLat S.G S.Qp S.LL S.O} (t : ↥T.L.T) : t ∈ invariantLattice T ↔ ∀ g, T.actT g t = t := by
  simp only [invariantLattice, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  first
  | rfl
  | exact Iff.rfl
  | (constructor <;> intro h g <;> exact h g)

theorem mem_fixDD {T : LocLat S.G S.Qp S.LL S.O} (x : S.W.DD T) : x ∈ fixDD S.W T ↔
    S.W.φD T x = x ∧ S.W.γD T S.W.gamK x = x ∧ ∀ δ ∈ S.W.DelF, S.W.γD T δ x = x := by
  simp only [fixDD, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, and_assoc]

private theorem nonempty_invariantLattice_equiv_fixDD (E : S.Comparison₂)
    (hin : ∀ (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T), (∀ g, T.actT g t = t) →
      (1 : S.RW) ⊗ₜ[S.O] t ∈ Set.range (E.jD T))
    (hfix : ∀ (T : LocLat S.G S.Qp S.LL S.O) (b : TW S.RW T), TWmap S.φR T b = b →
      ∃ t : ↥T.L.T, b = (1 : S.RW) ⊗ₜ[S.O] t)
    (hi : OneInj S) (hg : GenFix S) (T : LocLat S.G S.Qp S.LL S.O) :
    Nonempty (↥(invariantLattice T) ≃ₗ[S.O] ↥(fixDD S.W T)) := by

  have key : (invariantLattice T).map (oneT S T) = (fixDD S.W T).map (E.jD T) := by
    ext b
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [mem_H0Lat] at ht
      obtain ⟨d, hd⟩ := hin T t ht
      refine ⟨d, ?_, ?_⟩
      · rw [mem_fixDD]
        refine ⟨?_, ?_, ?_⟩
        · apply E.jD_inj T
          rw [E.jD_φ, hd, TWmap_one]
        · obtain ⟨g, hgg⟩ := S.W.resΓ_onto S.W.gamK
          apply E.jD_inj T
          rw [← hgg, E.jD_act, hd, TWact_one, ht g]
        · intro δ _
          obtain ⟨g, hgg⟩ := S.W.resΓ_onto δ
          apply E.jD_inj T
          rw [← hgg, E.jD_act, hd, TWact_one, ht g]
      · rw [oneT_apply, hd]
    · rintro ⟨d, hd, rfl⟩
      rw [mem_fixDD] at hd
      obtain ⟨hφ, hγ, hδ⟩ := hd
      obtain ⟨t, ht⟩ := hfix T (E.jD T d) (by rw [← E.jD_φ, hφ])
      have hact : ∀ g : S.G, S.W.γD T (S.W.resΓ g) d = d → T.actT g t = t := by
        intro g hgd
        apply hi T
        rw [oneT_apply, oneT_apply, ← TWact_one (S.gR g), ← ht, ← E.jD_act, hgd]
      refine ⟨t, ?_, ?_⟩
      · rw [mem_H0Lat]
        apply hg T t
        · intro g hgK
          exact hact g (by rw [hgK, hγ])
        · intro g hgD
          exact hact g (hδ _ hgD)
        · intro g h1
          exact hact g (by rw [h1, S.W.γD_one])
      · rw [oneT_apply, ht]
  exact ⟨(Submodule.equivMapOfInjective (oneT S T) (hi T) (invariantLattice T)).trans
    ((LinearEquiv.ofEq _ _ key).trans
      (Submodule.equivMapOfInjective (E.jD T) (E.jD_inj T) (fixDD S.W T)).symm)⟩

end Gen

theorem invariants_iso_of_generators (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (hi : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
      OneInj (sit D.loc HW l (D.locA l) K 1 LL hA.2.2))
    (hg : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
      GenFix (sit D.loc HW l (D.locA l) K 1 LL hA.2.2)) :
    H0InvariantsTheorem D HW F := by
  intro hF l hl K LL hA T
  obtain ⟨hW, hD⟩ := hF l K 1 LL hA.2.2
  refine nonempty_invariantLattice_equiv_fixDD (S := sit D.loc HW l (D.locA l) K 1 LL hA.2.2) ((F l).E K 1 LL hA.2.2).tie
    (fun T t ht => ?_) (fun T b hb => (hW T).2.1 b hb) (hi l K LL hA) (hg l K LL hA) T

  refine Set.mem_range.mpr (LinearMap.mem_range.mp ((hD T).2 _ ?_ ?_))
  · intro g _
    rw [TWact_one, ht g]
  · rw [TWmap_one, sub_self]
    exact Submodule.zero_mem _

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
