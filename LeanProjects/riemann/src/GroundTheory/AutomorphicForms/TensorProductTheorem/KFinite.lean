import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.CompactRep
import GroundTheory.AutomorphicForms.TensorProductTheorem.MatrixCoeff

noncomputable section

namespace GroundTheory.Automorphic

namespace CompactRep

open Module Set

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {X : Type*} [AddCommGroup X] [Module ℂ X]

structure IsKFinite (σ : Representation ℂ K X) : Prop where
  locallyFinite : ∀ v, FiniteDimensional ℂ (Submodule.span ℂ (range fun k => σ k v))
  continuous : Representation.HasContinuousCoeff σ

variable {σ : Representation ℂ K X}

theorem hasContinuousCoeff_subrep (hσ : Representation.HasContinuousCoeff σ)
    (P : Subrepresentation σ) : Representation.HasContinuousCoeff P.toRepresentation := by
  intro φ w
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ
  have : ∀ k, φ (P.toRepresentation k w) = ψ (σ k w) := fun k => by
    rw [← hψ]
    rfl
  simp only [this]
  exact hσ ψ w

theorem exists_subrep_compl (h : IsKFinite σ) (v : X) {Y : Subrepresentation σ}
    (hY : Y ≤ RestrictedTensor.orbitSpan σ v) :
    ∃ C : Subrepresentation σ, C ≤ RestrictedTensor.orbitSpan σ v ∧ Y ⊓ C = ⊥ ∧
      Y ⊔ C = RestrictedTensor.orbitSpan σ v := by
  set F := RestrictedTensor.orbitSpan σ v
  have hFd : FiniteDimensional ℂ F.toSubmodule := h.locallyFinite v
  have hFc := hasContinuousCoeff_subrep h.continuous F
  set U : Submodule ℂ F.toSubmodule := Y.toSubmodule.comap F.toSubmodule.subtype
  obtain ⟨C', hC', hC's⟩ := exists_isCompl_stable hFc U fun k u hu =>
    Y.apply_mem_toSubmodule k hu
  refine ⟨⟨C'.map F.toSubmodule.subtype, ?_⟩, ?_, ?_, ?_⟩
  · rintro k _ ⟨c, hc, rfl⟩
    exact ⟨_, hC's k c hc, rfl⟩
  · rintro _ ⟨c, -, rfl⟩
    exact c.2
  · apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_inf]
    change _ = (⊥ : Submodule ℂ X)
    rw [eq_bot_iff]
    rintro _ ⟨hxY, ⟨c, hc, rfl⟩⟩
    have hcU : c ∈ U := hxY
    have : c ∈ U ⊓ C' := ⟨hcU, hc⟩
    rw [disjoint_iff.1 hC'.1, Submodule.mem_bot] at this
    rw [this]
    exact Submodule.zero_mem _
  · apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_sup]
    refine le_antisymm (sup_le hY ?_) fun x hx => ?_
    · rintro _ ⟨c, -, rfl⟩
      exact c.2
    · have hxtop : (⟨x, hx⟩ : F.toSubmodule) ∈ U ⊔ C' := by
        rw [codisjoint_iff.1 hC'.2]; trivial
      obtain ⟨u, hu, c, hc, huc⟩ := Submodule.mem_sup.1 hxtop
      rw [Submodule.mem_sup]
      refine ⟨u, hu, c, ⟨c, hc, rfl⟩, ?_⟩
      have := congrArg Subtype.val huc
      simpa using this

variable (σ) in

abbrev Alg := MonoidAlgebra ℂ K

theorem isSemisimpleModule_asModule (h : IsKFinite σ) :
    IsSemisimpleModule (MonoidAlgebra ℂ K) σ.asModule := by
  set e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)
  rw [isSemisimpleModule_iff]
  refine complementedLattice_of_complementedLattice_Iic (s := univ)
    (f := fun v : X => e (RestrictedTensor.orbitSpan σ v)) (fun v _ => ?_) ?_
  · refine ⟨fun ⟨N, hN⟩ => ?_⟩
    have hY : e.symm N ≤ RestrictedTensor.orbitSpan σ v := by
      have := e.symm.monotone hN
      simpa using this
    obtain ⟨C, hCle, hinf, hsup⟩ := exists_subrep_compl h v hY
    refine ⟨⟨e C, e.monotone hCle⟩, ⟨disjoint_iff.2 ?_, codisjoint_iff.2 ?_⟩⟩
    · apply Subtype.ext
      show N ⊓ e C = ⊥
      have := congrArg e hinf
      rwa [e.map_inf, e.apply_symm_apply, e.map_bot] at this
    · apply Subtype.ext
      show N ⊔ e C = e (RestrictedTensor.orbitSpan σ v)
      have := congrArg e hsup
      rwa [e.map_sup, e.apply_symm_apply] at this
  · refine eq_top_iff.2 fun x _ => ?_
    refine Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem (mem_univ x) ?_)
    exact RestrictedTensor.mem_orbitSpan_self σ x

section Isotypic

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]

theorem isFullyInvariant_sSup {s : Set (Submodule R M)} (h : ∀ m ∈ s, m.IsFullyInvariant) :
    (sSup s).IsFullyInvariant := fun f =>
  sSup_le fun m hm => (h m hm f).trans (Submodule.comap_mono (le_sSup hm))

theorem isCompl_isotypicComponent {c : Submodule R M} (hc : c ∈ isotypicComponents R M) :
    IsCompl c (sSup (isotypicComponents R M \ {c})) := by
  refine ⟨sSupIndep_isotypicComponents R M hc, codisjoint_iff.2 ?_⟩
  rw [eq_top_iff, ← sSup_isotypicComponents (R := R) (M := M)]
  refine sSup_le fun m hm => ?_
  by_cases hmc : m = c
  · exact hmc ▸ le_sup_left
  · exact le_sup_of_le_right (le_sSup ⟨hm, hmc⟩)

def isoProj {c : Submodule R M} (hc : c ∈ isotypicComponents R M) : Module.End R M :=
  c.subtype ∘ₗ Submodule.projectionOnto c _ (isCompl_isotypicComponent hc)

theorem isoProj_apply_of_mem {c : Submodule R M} (hc : c ∈ isotypicComponents R M) {x : M}
    (hx : x ∈ c) : isoProj hc x = x := by
  simp [isoProj, Submodule.projectionOnto_apply_of_mem_left _ hx]

theorem isoProj_mem_isotypicComponent {c : Submodule R M} (hc : c ∈ isotypicComponents R M)
    (x : M) : isoProj hc x ∈ c :=
  Subtype.prop _

theorem isoProj_apply_of_mem_compl {c : Submodule R M} (hc : c ∈ isotypicComponents R M) {x : M}
    (hx : x ∈ sSup (isotypicComponents R M \ {c})) : isoProj hc x = 0 := by
  simp [isoProj, (Submodule.projectionOnto_apply_eq_zero_iff _).2 hx]

theorem isoProj_comm {c : Submodule R M} (hc : c ∈ isotypicComponents R M) (f : Module.End R M)
    (x : M) : isoProj hc (f x) = f (isoProj hc x) := by
  have hcompl := isCompl_isotypicComponent hc
  have hfc : c.IsFullyInvariant := Submodule.IsFullyInvariant.of_mem_isotypicComponents hc
  have hfr : (sSup (isotypicComponents R M \ {c})).IsFullyInvariant :=
    isFullyInvariant_sSup fun m hm => Submodule.IsFullyInvariant.of_mem_isotypicComponents hm.1
  have hx : x ∈ c ⊔ sSup (isotypicComponents R M \ {c}) := by
    rw [codisjoint_iff.1 hcompl.2]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add f, map_add (isoProj hc), map_add (isoProj hc), isoProj_apply_of_mem hc (hfc f ha),
    isoProj_apply_of_mem_compl hc (hfr f hb), isoProj_apply_of_mem hc ha,
    isoProj_apply_of_mem_compl hc hb, add_zero, add_zero]

theorem isoProj_mem {c : Submodule R M} (hc : c ∈ isotypicComponents R M) (Y : Submodule R M)
    {y : M} (hy : y ∈ Y) : isoProj hc y ∈ Y := by
  obtain ⟨Y', hY'⟩ := exists_isCompl Y
  set f : Module.End R M := Y.subtype ∘ₗ Submodule.projectionOnto Y Y' hY'
  have hfy : f y = y := by simp [f, Submodule.projectionOnto_apply_of_mem_left _ hy]
  rw [← hfy, isoProj_comm hc f]
  exact Subtype.prop _

end Isotypic

end CompactRep

end GroundTheory.Automorphic
