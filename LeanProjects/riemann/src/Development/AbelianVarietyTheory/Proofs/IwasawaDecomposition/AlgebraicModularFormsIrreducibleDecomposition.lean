import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeSpacesOrthogonalOfClassSumInnerStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutReps

variable {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

theorem comap_ne_bot_iff {f : M →ₗ[ℂ] N} (hf : Function.Injective f) (A : Submodule ℂ N) :
    A.comap f ≠ ⊥ ↔ A ⊓ LinearMap.range f ≠ ⊥ := by
  rw [inf_comm, ← Submodule.map_comap_eq, not_iff_not]
  constructor
  · intro h; rw [h, Submodule.map_bot]
  · intro h
    exact Submodule.map_injective_of_injective hf (by rw [h, Submodule.map_bot])

theorem iSupIndep_comap {ι : Type} {f : M →ₗ[ℂ] N} (hf : Function.Injective f) {A : ι → Submodule ℂ N}
    (hA : iSupIndep A) : iSupIndep (fun i => (A i).comap f) := by
  intro i
  rw [disjoint_iff]
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hx
  have h3 : f x ∈ ⨆ j, ⨆ (_ : j ≠ i), A j := by
    have hle : (⨆ j, ⨆ (_ : j ≠ i), (A j).comap f) ≤ (⨆ j, ⨆ (_ : j ≠ i), A j).comap f := by
      apply iSup_le; intro j; apply iSup_le; intro hj
      exact Submodule.comap_mono (le_iSup₂_of_le j hj le_rfl)
    exact hle h2
  have h4 : f x ∈ A i ⊓ ⨆ j, ⨆ (_ : j ≠ i), A j := Submodule.mem_inf.mpr ⟨h1, h3⟩
  rw [disjoint_iff.mp (hA i)] at h4
  have : f x = 0 := (Submodule.mem_bot ℂ).mp h4
  exact (Submodule.mem_bot ℂ).mpr (hf (this.trans (map_zero f).symm))

theorem iSup_comap_eq_top {ι : Type} {f : M →ₗ[ℂ] N} (hf : Function.Injective f) {A : ι → Submodule ℂ N}
    (hA : ⨆ i, A i ⊓ LinearMap.range f = LinearMap.range f) : ⨆ i, (A i).comap f = ⊤ := by
  apply Submodule.map_injective_of_injective hf
  rw [Submodule.map_iSup, Submodule.map_top]
  simp_rw [Submodule.map_comap_eq]
  simpa only [inf_comm] using hA

end GlobalTheory.AutReps

theorem GlobalTheory.AutReps.mtReal_decomp : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j), ∃ (ι : Type) (_ : Finite ι) (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), (∀ P, NG.IsIrrRep Mr.wt.ρ (F P)) ∧ (∀ P P', NG.IsoRep (F P) (F P') → P = P') ∧ (∀ S', NG.IsIrrRep Mr.wt.ρ S' → (NG.isoTyp Mr.wt.ρ S').comap Mr.real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') ∧ (∀ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real ≠ ⊥) ∧ iSupIndep (fun P => (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real) ∧ ⨆ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real = ⊤ := by
  intro D μ j Mr
  obtain ⟨_, ι, hι, S, hirr, hinj, hsurj, hne, hind, hsup⟩ :=
    GlobalTheory.T.typeSpaces_orthogonal_of_classSum_inner D.host.E D.R.nV Mr.wt Mr.J Mr.χ Mr.J_open
  have hR := Mr.real_range
  refine ⟨ι, hι, S, hirr, hinj, ?_, ?_, ?_, ?_⟩
  · intro S' h1 h2
    apply hsurj S' h1
    rw [← hR]; exact (GlobalTheory.AutReps.comap_ne_bot_iff Mr.real_inj _).mp h2
  · intro P
    rw [GlobalTheory.AutReps.comap_ne_bot_iff Mr.real_inj, hR]; exact hne P
  · exact GlobalTheory.AutReps.iSupIndep_comap Mr.real_inj hind
  · apply GlobalTheory.AutReps.iSup_comap_eq_top Mr.real_inj
    rw [hR]; exact hsup
