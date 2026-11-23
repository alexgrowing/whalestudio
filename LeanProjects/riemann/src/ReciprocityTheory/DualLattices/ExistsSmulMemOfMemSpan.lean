import ReciprocityTheory.DualLattices.TensorSpan
import Lemmata.MiscLemmasL.Imports

noncomputable section

namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

open Module

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem exists_smul_mem_of_mem_span [IsDomain R] [IsFractionRing R C]
    {V : Type} [AddCommGroup V] [Module C V] [Module R V] [IsScalarTower R C V]
    (S : Submodule R V) {x : V} (hx : x ∈ Submodule.span C (S : Set V)) :
    ∃ r : R, r ≠ 0 ∧ r • x ∈ S := by
  exact Bl.SecondBlockLemmaM.goal1 (C := C) S hx

theorem free_of_finite_torsionFree [IsDomain R] [ValuationRing R] (P : Type) [AddCommGroup P]
    [Module R P] [Module.Finite R P] (h : ∀ (r : R) (x : P), r ≠ 0 → r • x = 0 → x = 0) :
    Module.Free R P := by
  have : Module.Flat R P := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
    exact h a x (nonZeroDivisors.ne_zero a.2) ha
  exact Module.free_of_flat_of_isLocalRing

theorem algebraMap_ne_zero [IsFractionRing R C] {r : R} (hr : r ≠ 0) : algebraMap R C r ≠ 0 := by
  intro h0
  exact hr ((IsFractionRing.injective R C) (by simpa using h0))

theorem isLat_of_fg [IsDomain R] [ValuationRing R] [IsFractionRing R C]
    {X : Type} [Fintype X] [DecidableEq X] (M : Submodule R (X → C)) (hfg : M.FG)
    (hsp : Submodule.span C (M : Set (X → C)) = ⊤) : IsLat R M := by
  have : Module.Finite R M := Module.Finite.iff_fg.2 hfg
  have : Module.Free R M := free_of_finite_torsionFree M (by
    rintro r ⟨x, hx⟩ hr h
    have h' : (r • x : X → C) = 0 := by simpa using congrArg Subtype.val h
    rw [← algebraMap_smul C r x] at h'
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left (algebraMap_ne_zero hr)))
  let b := Module.Free.chooseBasis R M
  let v : Module.Free.ChooseBasisIndex R M → X → C := fun i => (b i : X → C)
  have hR : LinearIndependent R v := b.linearIndependent.map' M.subtype (Submodule.ker_subtype _)
  have hC : LinearIndependent C v := (LinearIndependent.iff_fractionRing R C).1 hR
  have hspR : Submodule.span R (Set.range v) = M := by
    have : Set.range v = M.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspC : Submodule.span C (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower R, hspR, hsp]
  let bC := Basis.mk hC (by rw [hspC])
  have hcard : Fintype.card X = Fintype.card (Module.Free.ChooseBasisIndex R M) := by
    rw [← Module.finrank_fintype_fun_eq_card (R := C), Module.finrank_eq_card_basis bC]
  let e : X ≃ Module.Free.ChooseBasisIndex R M := Fintype.equivOfCardEq hcard
  refine ⟨fun x j => v (e j) x, ?_, ?_⟩
  · have hli : LinearIndependent C (fun j x => v (e j) x) := hC.comp e e.injective
    have hu := (Matrix.linearIndependent_cols_iff_isUnit (A := (fun x j => v (e j) x : Matrix X X C))).1
      (by convert hli using 1; rfl)
    exact (Matrix.isUnit_iff_isUnit_det _).1 hu
  · have : Set.range (fun j x => v (e j) x) = Set.range v := by
      ext f; constructor
      · rintro ⟨j, rfl⟩; exact ⟨e j, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨e.symm i, by simp⟩
    rw [this, hspR]

theorem fg_of_isLat {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)}
    (h : IsLat R M) : M.FG := by
  obtain ⟨B, -, rfl⟩ := h
  exact Submodule.fg_span (Set.finite_range _)

theorem span_top_of_isLat {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)}
    (h : IsLat R M) : Submodule.span C (M : Set (X → C)) = ⊤ := by
  obtain ⟨B, hB, rfl⟩ := h
  rw [Submodule.span_span_of_tower]
  have hli : LinearIndependent C (fun j x => B x j) := by
    have := (Matrix.linearIndependent_cols_iff_isUnit (A := B)).2 ((Matrix.isUnit_iff_isUnit_det B).2 hB)
    convert this using 1; rfl
  exact hli.span_eq_top_of_card_eq_finrank' (by simp)

theorem exists_proj [IsDomain R] [ValuationRing R] [IsFractionRing R C]
    {X : Type} [Fintype X] (A : Submodule R (X → C)) (hfg : A.FG)
    (hsp : Submodule.span C (A : Set (X → C)) = ⊤) (W : Submodule C (X → C)) :
    ∃ E : (X → C) →ₗ[C] (X → C), (∀ f ∈ A, E f ∈ A ∧ E f ∈ W) ∧ ∀ f ∈ W, E f = f := by
  classical
  let P : Submodule R A := (W.restrictScalars R).comap A.subtype
  have : Module.Finite R A := Module.Finite.iff_fg.2 hfg
  have : Module.Free R (A ⧸ P) := free_of_finite_torsionFree _ (by
    intro r x hr hx
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective P x
    rw [← map_smul, ← LinearMap.mem_ker, Submodule.ker_mkQ] at hx
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    have hx' : ((r • a : A) : X → C) ∈ W := hx
    show (a : X → C) ∈ W
    have : (a : X → C) = (algebraMap R C r)⁻¹ • ((r • a : A) : X → C) := by
      rw [Submodule.coe_smul, ← algebraMap_smul C r (a : X → C), smul_smul,
        inv_mul_cancel₀ (algebraMap_ne_zero hr), one_smul]
    rw [this]; exact W.smul_mem _ hx')
  obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ LinearMap.id
    (Submodule.mkQ_surjective P)
  have hs' : ∀ y, P.mkQ (s y) = y := fun y => LinearMap.congr_fun hs y
  let S : Submodule R (X → C) := LinearMap.range (A.subtype ∘ₗ s)
  let W' : Submodule C (X → C) := Submodule.span C (S : Set (X → C))
  have hdec : ∀ a : A, ((a - s (P.mkQ a) : A) : X → C) ∈ W := by
    intro a
    have h2 : P.mkQ (a - s (P.mkQ a)) = 0 := by rw [map_sub, hs', sub_self]
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at h2
    exact h2
  have hSW' : ∀ a : A, ((s (P.mkQ a) : A) : X → C) ∈ W' :=
    fun a => Submodule.subset_span ⟨P.mkQ a, rfl⟩
  have hcompl : IsCompl W W' := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxW hxW'
      obtain ⟨r, hr, hrx⟩ := exists_smul_mem_of_mem_span S hxW'
      obtain ⟨y, hy⟩ := hrx
      have hyW : ((s y : A) : X → C) ∈ W := by
        have : ((s y : A) : X → C) = r • x := hy
        rw [this, ← algebraMap_smul C r x]; exact W.smul_mem _ hxW
      have hy0 : y = 0 := by
        rw [← hs' y, ← LinearMap.mem_ker, Submodule.ker_mkQ]; exact hyW
      have : r • x = 0 := by rw [← hy]; simp [hy0]
      rw [← algebraMap_smul C r x] at this
      exact (smul_eq_zero.1 this).resolve_left (algebraMap_ne_zero hr)
    · rw [codisjoint_iff, eq_top_iff, ← hsp, Submodule.span_le]
      intro f hf
      have : f = ((⟨f, hf⟩ - s (P.mkQ ⟨f, hf⟩) : A) : X → C) + ((s (P.mkQ ⟨f, hf⟩) : A) : X → C) := by
        simp
      rw [this]
      exact Submodule.add_mem_sup (hdec _) (hSW' _)
  have hc : IsCompl (LinearMap.range W.subtype) W' := by rw [Submodule.range_subtype]; exact hcompl
  let E : (X → C) →ₗ[C] (X → C) :=
    W.subtype ∘ₗ LinearMap.linearProjOfIsCompl W' W.subtype W.injective_subtype hc
  have hEW : ∀ f ∈ W, E f = f := by
    intro f hf
    have : E (W.subtype ⟨f, hf⟩) = W.subtype ⟨f, hf⟩ := by
      simp only [E, LinearMap.comp_apply, LinearMap.linearProjOfIsCompl_apply_left]
    simpa using this
  have hEW' : ∀ f ∈ W', E f = 0 := by
    intro f hf
    simp only [E, LinearMap.comp_apply,
      LinearMap.linearProjOfIsCompl_apply_right' W' W.subtype W.injective_subtype hc f hf, map_zero]
  refine ⟨E, ?_, hEW⟩
  intro f hf
  have hsplit : f = ((⟨f, hf⟩ - s (P.mkQ ⟨f, hf⟩) : A) : X → C) + ((s (P.mkQ ⟨f, hf⟩) : A) : X → C) := by
    simp
  have : E f = ((⟨f, hf⟩ - s (P.mkQ ⟨f, hf⟩) : A) : X → C) := by
    conv_lhs => rw [hsplit]
    rw [map_add, hEW _ (hdec _), hEW' _ (hSW' _), add_zero]
  rw [this]
  exact ⟨Subtype.prop _, hdec _⟩

end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
