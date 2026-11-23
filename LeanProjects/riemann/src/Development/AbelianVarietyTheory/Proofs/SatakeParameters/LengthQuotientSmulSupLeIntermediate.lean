import Mathlib
open Pointwise

namespace GlobalTheory

theorem length_quotient_tower_of_le {R : Type} [CommRing R] {X : Type} [AddCommGroup X] [Module R X]
    (Y W : Submodule R X) (hYW : Y ≤ W) :
    Module.length R (X ⧸ Y) =
      Module.length R (W ⧸ Y.comap W.subtype) + Module.length R (X ⧸ W) := by
  have hf : Function.Injective ((Y.comap W.subtype).mapQ Y W.subtype le_rfl) := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
    simp
  refine Module.length_eq_add_of_exact ((Y.comap W.subtype).mapQ Y W.subtype le_rfl)
    (Submodule.factor hYW) hf (Submodule.factor_surjective hYW) ?_
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    constructor
    · intro h
      have hx : x ∈ W := by
        simpa [Submodule.Quotient.mk_eq_zero] using h
      exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩
    · rintro ⟨w, hw⟩
      rw [← hw]
      induction w using Submodule.Quotient.induction_on with
      | H z => simp [Submodule.Quotient.mk_eq_zero]

theorem length_quotient_smul_sup_le : ∀ (O A : Type) [CommRing O] [AddCommGroup A] [Module O A]
    (Z B B' : Submodule O A) (a : O), B ≤ B' →
    Module.length O (↥Z ⧸ (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype) ≤
      Module.length O ((↥Z ⧸ B'.comap Z.subtype) ⧸ LinearMap.range (a • (LinearMap.id :
        (↥Z ⧸ B'.comap Z.subtype) →ₗ[O] (↥Z ⧸ B'.comap Z.subtype)))) +
      Module.length O (↥(Z ⊓ B') ⧸ B.comap (Z ⊓ B').subtype) := by
  intro O A _ _ _ Z B B' a hBB'
  set N : Submodule O Z := (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype with hN
  set C : Submodule O Z := B'.comap Z.subtype with hC
  set K : Submodule O Z := N ⊔ C with hK
  rw [length_quotient_tower_of_le N K le_sup_left, add_comm]
  refine add_le_add ?_ ?_
  ·
    let f : (↥Z ⧸ C) →ₗ[O] (↥Z ⧸ K) := Submodule.factor (le_sup_right : C ≤ K)
    have hf : LinearMap.range (a • (LinearMap.id : (↥Z ⧸ C) →ₗ[O] (↥Z ⧸ C))) ≤ LinearMap.ker f := by
      rintro y ⟨q, rfl⟩
      induction q using Submodule.Quotient.induction_on with
      | H z =>
        rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
        change a • (Submodule.Quotient.mk z : ↥Z ⧸ K) = 0
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        refine Submodule.mem_sup_left ?_
        show ((a • z : Z) : A) ∈ Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B
        exact Submodule.mem_sup_left ⟨z, z.2, by simp⟩
    refine Module.length_le_of_surjective (Submodule.liftQ _ f hf) ?_
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H z =>
      exact ⟨Submodule.Quotient.mk (Submodule.Quotient.mk z), rfl⟩
  ·
    let ι : ↥(Z ⊓ B') →ₗ[O] K :=
      LinearMap.codRestrict K (LinearMap.codRestrict Z (Z ⊓ B').subtype (fun x => x.2.1))
        (fun x => Submodule.mem_sup_right (show _ ∈ C from x.2.2))
    let φ : ↥(Z ⊓ B') →ₗ[O] (↥K ⧸ N.comap K.subtype) := (N.comap K.subtype).mkQ ∘ₗ ι
    have hφ : B.comap (Z ⊓ B').subtype ≤ LinearMap.ker φ := by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      show ((x : A)) ∈ Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B
      exact Submodule.mem_sup_right hx
    refine Module.length_le_of_surjective (Submodule.liftQ _ φ hφ) ?_
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H k =>
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp k.2
      refine ⟨Submodule.Quotient.mk ⟨(z : A), z.2, hz⟩, ?_⟩
      rw [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq]
      have : ((ι ⟨(z : A), z.2, hz⟩ - k : K) : Z) = -y := by
        ext
        simp only [ι, ← hyz, Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_add]
        change (z : A) - ((y : A) + (z : A)) = -(y : A)
        abel
      show ((ι ⟨(z : A), z.2, hz⟩ - k : K) : Z) ∈ N
      rw [this]
      exact N.neg_mem hy

end GlobalTheory
