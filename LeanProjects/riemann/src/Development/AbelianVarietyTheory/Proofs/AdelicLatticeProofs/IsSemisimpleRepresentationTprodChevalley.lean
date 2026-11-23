import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodOfIsIrreducibleAlStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationOfISupRangeEquivariantStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

section
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} in

theorem _root_.GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom (σ : Subrepresentation ρ) (h : IsAtom σ) :
    σ.toRepresentation.IsIrreducible := by
  let F : Subrepresentation σ.toRepresentation → Subrepresentation ρ := fun τ =>
    ⟨τ.toSubmodule.map σ.toSubmodule.subtype, by
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨σ.toRepresentation g w, τ.apply_mem_toSubmodule g hw, rfl⟩⟩
  have hinj : Function.Injective (Submodule.map σ.toSubmodule.subtype) :=
    Submodule.map_injective_of_injective σ.toSubmodule.injective_subtype
  have hle : ∀ τ, F τ ≤ σ := by
    intro τ
    show τ.toSubmodule.map σ.toSubmodule.subtype ≤ σ.toSubmodule
    rw [Submodule.map_le_iff_le_comap]
    intro w _
    exact w.2
  have hF : ∀ τ, F τ = ⊥ ∨ F τ = σ := fun τ => h.le_iff.mp (hle τ)
  have hbot : ∀ τ, F τ = ⊥ → τ = ⊥ := by
    intro τ hτ
    apply Subrepresentation.ext
    apply hinj
    have := congrArg Subrepresentation.toSubmodule hτ
    change _ = Submodule.map _ ⊥
    rw [Submodule.map_bot]
    exact this
  have htop : ∀ τ, F τ = σ → τ = ⊤ := by
    intro τ hτ
    apply Subrepresentation.ext
    apply hinj
    have := congrArg Subrepresentation.toSubmodule hτ
    simp only [F] at this
    rw [this]
    exact (Submodule.map_subtype_top σ.toSubmodule).symm
  have hne : (⊥ : Subrepresentation σ.toRepresentation) ≠ ⊤ := by
    intro he
    apply h.1
    have h1 : F ⊤ = σ := by
      apply Subrepresentation.ext
      exact Submodule.map_subtype_top σ.toSubmodule
    have h2 : F ⊥ = ⊥ := by
      apply Subrepresentation.ext
      exact Submodule.map_bot _
    rw [← h1, ← he, h2]
  haveI : Nontrivial (Subrepresentation σ.toRepresentation) := ⟨⟨⊥, ⊤, hne⟩⟩
  exact ⟨fun τ => (hF τ).imp (hbot τ) (htop τ)⟩

theorem iSup_atoms_eq_top [FiniteDimensional ℂ V] (h : ρ.IsSemisimpleRepresentation) :
    (⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule) = ⊤ := by
  let S : Subrepresentation ρ :=
    ⟨⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule, by
      intro g v hv
      have : (⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule) ≤
          (⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule).comap (ρ g) :=
        iSup_le fun σ w hw =>
          Submodule.mem_iSup_of_mem σ (σ.1.apply_mem_toSubmodule g hw)
      exact this hv⟩
  haveI : WellFoundedLT (Subrepresentation ρ) :=
    StrictMono.wellFoundedLT (f := Subrepresentation.toSubmodule) (fun _ _ hab => hab)
  haveI : IsAtomic (Subrepresentation ρ) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  obtain ⟨T, hT⟩ := exists_isCompl S
  rcases eq_bot_or_exists_atom_le T with h0 | ⟨a, ha, haT⟩
  · subst h0
    have : S = ⊤ := by simpa using hT.sup_eq_top
    exact congrArg Subrepresentation.toSubmodule this
  · exfalso
    have haS : a ≤ S := fun w hw =>
      Submodule.mem_iSup_of_mem (⟨a, ha⟩ : {σ : Subrepresentation ρ // IsAtom σ}) hw
    exact ha.1 (hT.disjoint haS haT |> le_bot_iff.mp)

end

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private theorem iSup_atoms_toSubmodule_eq_whole_of_semisimple {G : Type} [Group G] {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hρ : ρ.IsSemisimpleRepresentation) :
    ⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule = ⊤ := by
  haveI : ComplementedLattice (Subrepresentation ρ) := hρ
  haveI : WellFoundedLT (Subrepresentation ρ) :=
    StrictMono.wellFoundedLT (f := Subrepresentation.toSubmodule) fun a b hab =>
      lt_of_le_of_ne hab.le fun he => hab.ne (Subrepresentation.toSubmodule_injective he)
  haveI : IsAtomic (Subrepresentation ρ) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  set A := ⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule with hA
  let α : Subrepresentation ρ := ⟨A, by
    intro g v hv
    refine Submodule.iSup_induction _ (motive := fun v => ρ g v ∈ A) hv ?_ ?_ ?_
    · intro σ w hw
      exact (le_iSup (fun σ : {σ : Subrepresentation ρ // IsAtom σ} => σ.1.toSubmodule) σ)
        (σ.1.apply_mem_toSubmodule g hw)
    · simp
    · intro x y hx hy
      simpa using A.add_mem hx hy⟩
  obtain ⟨β, hβ⟩ := exists_isCompl α
  have hβbot : β = ⊥ := by
    rcases eq_bot_or_exists_atom_le β with h | ⟨τ, hτ, hτβ⟩
    · exact h
    · exfalso
      have hτα : τ ≤ α := fun v hv =>
        (le_iSup (fun σ : {σ : Subrepresentation ρ // IsAtom σ} => σ.1.toSubmodule) ⟨τ, hτ⟩) hv
      exact hτ.1 (le_bot_iff.mp (hβ.1 hτα hτβ))
  have hαtop : α = ⊤ := by
    have := hβ.2.eq_top
    rwa [hβbot, sup_bot_eq] at this
  exact congrArg Subrepresentation.toSubmodule hαtop

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

theorem _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W], ρ.IsSemisimpleRepresentation → ρ'.IsSemisimpleRepresentation → (ρ.tprod ρ').IsSemisimpleRepresentation := by
  intro G _ V _ _ ρ W _ _ ρ' _ _ hρ hρ'
  let J := {σ : Subrepresentation ρ // IsAtom σ} × {τ : Subrepresentation ρ' // IsAtom τ}
  let p : (j : J) → j.1.1.toSubmodule ⊗[ℂ] j.2.1.toSubmodule →ₗ[ℂ] V ⊗[ℂ] W := fun j =>
    TensorProduct.map j.1.1.toSubmodule.subtype j.2.1.toSubmodule.subtype
  refine _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range G (V ⊗[ℂ] W) (ρ.tprod ρ') J
    (fun j => j.1.1.toSubmodule ⊗[ℂ] j.2.1.toSubmodule)
    (fun j => j.1.1.toRepresentation.tprod j.2.1.toRepresentation) p ?_ ?_ ?_
  · intro j
    exact _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod_of_isIrreducible G _ _ _ _
      (_root_.GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom j.1.1 j.1.2)
      (_root_.GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom j.2.1 j.2.2)
  · intro j g v
    simp only [p]
    rw [Representation.tprod_apply, Representation.tprod_apply, ← LinearMap.comp_apply,
      ← LinearMap.comp_apply, ← TensorProduct.map_comp, ← TensorProduct.map_comp]
    rfl
  · rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
    rintro _ ⟨v, w, rfl⟩
    have hv : v ∈ ⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule := by
      rw [iSup_atoms_toSubmodule_eq_whole_of_semisimple ρ hρ]; trivial
    have hw : w ∈ ⨆ τ : {τ : Subrepresentation ρ' // IsAtom τ}, τ.1.toSubmodule := by
      rw [iSup_atoms_toSubmodule_eq_whole_of_semisimple ρ' hρ']; trivial
    refine Submodule.iSup_induction _ (motive := fun v => ∀ w,
      w ∈ ⨆ τ : {τ : Subrepresentation ρ' // IsAtom τ}, τ.1.toSubmodule →
        v ⊗ₜ[ℂ] w ∈ ⨆ j, LinearMap.range (p j)) hv ?_ ?_ ?_ w hw
    · intro σ x hx w hw
      refine Submodule.iSup_induction _
        (motive := fun w => x ⊗ₜ[ℂ] w ∈ ⨆ j, LinearMap.range (p j)) hw ?_ ?_ ?_
      · intro τ y hy
        exact (le_iSup (fun j => LinearMap.range (p j)) (σ, τ))
          ⟨(⟨x, hx⟩ : σ.1.toSubmodule) ⊗ₜ[ℂ] (⟨y, hy⟩ : τ.1.toSubmodule), rfl⟩
      · simp
      · intro a b ha hb
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ ha hb
    · intro w _
      simp
    · intro a b ha hb w hw
      rw [TensorProduct.add_tmul]
      exact Submodule.add_mem _ (ha w hw) (hb w hw)

end GlobalTheory.ClassFin
