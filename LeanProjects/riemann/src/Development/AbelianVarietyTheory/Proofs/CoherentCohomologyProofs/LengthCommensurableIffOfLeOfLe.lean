import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective

namespace GlobalTheory

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

section Chain

theorem relLength_eq_add_of_le {A B C : Submodule R V} (hCB : C ≤ B) (hBA : B ≤ A) :
    relLength A C = relLength A B + relLength B C := by
  have hle : C.submoduleOf A ≤ B.submoduleOf A := Submodule.comap_mono hCB
  have hex := Module.length_eq_add_of_exact (LinearMap.ker (Submodule.factor hle)).subtype
    (Submodule.factor hle) (Submodule.injective_subtype _) (Submodule.factor_surjective hle)
    (LinearMap.exact_subtype_ker_map _)
  have hker : LinearMap.ker (Submodule.factor hle) =
      (B.submoduleOf A).map (C.submoduleOf A).mkQ := by
    rw [Submodule.factor, Submodule.ker_mapQ, Submodule.comap_id]
  rw [hker, ← relLength_eq_length_map_mkQ, relLength_submoduleOf hBA] at hex
  rw [add_comm]
  exact hex

theorem relLength_inf_eq_add (A B C : Submodule R V) :
    relLength A (B ⊓ C) = relLength A B + relLength (A ⊓ B) C := by
  have h := relLength_eq_add_of_le (A := A) (B := A ⊓ B) (C := A ⊓ B ⊓ C) inf_le_left inf_le_left
  rwa [relLength_inf_right, relLength_inf_right, inf_assoc, relLength_inf_right] at h

theorem relLength_sup_eq_add (A B C : Submodule R V) :
    relLength (A ⊔ B) C = relLength A (B ⊔ C) + relLength B C := by
  have h := relLength_eq_add_of_le (A := A ⊔ (B ⊔ C)) (B := B ⊔ C) (C := C) le_sup_right
    le_sup_right
  rwa [relLength_sup_left, relLength_sup_left, ← sup_assoc, relLength_sup_left] at h

theorem relLength_eq_add_sup_of_le {A B : Submodule R V} (hBA : B ≤ A) (C : Submodule R V) :
    relLength A C = relLength A (B ⊔ C) + relLength B C := by
  rw [← relLength_sup_eq_add, sup_eq_left.mpr hBA]

theorem relLength_eq_add_inf_of_le (A : Submodule R V) {B C : Submodule R V} (hCB : C ≤ B) :
    relLength A C = relLength A B + relLength (A ⊓ B) C := by
  rw [← relLength_inf_eq_add, inf_eq_right.mpr hCB]

theorem relLength_le_add (A B C : Submodule R V) :
    relLength A C ≤ relLength A B + relLength B C :=
  calc relLength A C ≤ relLength A (B ⊓ C) := relLength_anti_right A inf_le_right
    _ = relLength A B + relLength (A ⊓ B) C := relLength_inf_eq_add A B C
    _ ≤ relLength A B + relLength B C := by
      gcongr
      exact inf_le_right

theorem relLength_inf_le_add (A B C : Submodule R V) :
    relLength A (B ⊓ C) ≤ relLength A B + relLength A C := by
  rw [relLength_inf_eq_add]
  gcongr
  exact inf_le_left

theorem relLength_sup_le_add (A B C : Submodule R V) :
    relLength (A ⊔ B) C ≤ relLength A C + relLength B C := by
  rw [relLength_sup_eq_add]
  gcongr
  exact le_sup_right

theorem relLength_ne_top_trans {A B C : Submodule R V} (hAB : relLength A B ≠ ⊤)
    (hBC : relLength B C ≠ ⊤) : relLength A C ≠ ⊤ :=
  ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hAB, hBC⟩) (relLength_le_add A B C)

theorem relLength_inf_ne_top_iff {A B C : Submodule R V} :
    relLength A (B ⊓ C) ≠ ⊤ ↔ relLength A B ≠ ⊤ ∧ relLength A C ≠ ⊤ :=
  ⟨fun h => ⟨ne_top_of_le_ne_top h (relLength_anti_right A inf_le_left),
      ne_top_of_le_ne_top h (relLength_anti_right A inf_le_right)⟩,
    fun h => ne_top_of_le_ne_top (WithTop.add_ne_top.mpr h) (relLength_inf_le_add A B C)⟩

theorem relLength_sup_ne_top_iff {A B C : Submodule R V} :
    relLength (A ⊔ B) C ≠ ⊤ ↔ relLength A C ≠ ⊤ ∧ relLength B C ≠ ⊤ :=
  ⟨fun h => ⟨ne_top_of_le_ne_top h (relLength_mono_left le_sup_left C),
      ne_top_of_le_ne_top h (relLength_mono_left le_sup_right C)⟩,
    fun h => ne_top_of_le_ne_top (WithTop.add_ne_top.mpr h) (relLength_sup_le_add A B C)⟩

end Chain

section Commensurable

variable {A A' B B' C : Submodule R V}

@[trans] theorem LengthCommensurable.trans (hAB : LengthCommensurable A B)
    (hBC : LengthCommensurable B C) : LengthCommensurable A C :=
  ⟨relLength_ne_top_trans hAB.1 hBC.1, relLength_ne_top_trans hBC.2 hAB.2⟩

theorem lengthCommensurable_equivalence :
    Equivalence (LengthCommensurable : Submodule R V → Submodule R V → Prop) :=
  ⟨LengthCommensurable.refl, LengthCommensurable.symm, LengthCommensurable.trans⟩

instance : Trans (LengthCommensurable : Submodule R V → Submodule R V → Prop)
    LengthCommensurable LengthCommensurable :=
  ⟨LengthCommensurable.trans⟩

theorem lengthCommensurable_iff_of_le_of_le (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable A C ↔ LengthCommensurable A B ∧ LengthCommensurable B C := by
  rw [lengthCommensurable_iff_of_ge hCB, lengthCommensurable_iff_of_ge hBA,
    lengthCommensurable_iff_of_ge (hCB.trans hBA), relLength_eq_add_of_le hCB hBA]
  exact WithTop.add_ne_top

namespace LengthCommensurable

theorem of_between_left (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable A B :=
  ((lengthCommensurable_iff_of_le_of_le hCB hBA).mp h).1

theorem of_between_right (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable B C :=
  ((lengthCommensurable_iff_of_le_of_le hCB hBA).mp h).2

theorem inf_right (hAB : LengthCommensurable A B) (hAC : LengthCommensurable A C) :
    LengthCommensurable A (B ⊓ C) :=
  ⟨relLength_inf_ne_top_iff.mpr ⟨hAB.1, hAC.1⟩,
    ne_top_of_le_ne_top hAB.2 (relLength_mono_left inf_le_left A)⟩

theorem sup_right (hAB : LengthCommensurable A B) (hAC : LengthCommensurable A C) :
    LengthCommensurable A (B ⊔ C) :=
  ⟨ne_top_of_le_ne_top hAB.1 (relLength_anti_right A le_sup_left),
    relLength_sup_ne_top_iff.mpr ⟨hAB.2, hAC.2⟩⟩

theorem inf_left (hAC : LengthCommensurable A C) (hBC : LengthCommensurable B C) :
    LengthCommensurable (A ⊓ B) C :=
  (hAC.symm.inf_right hBC.symm).symm

theorem sup_left (hAC : LengthCommensurable A C) (hBC : LengthCommensurable B C) :
    LengthCommensurable (A ⊔ B) C :=
  (hAC.symm.sup_right hBC.symm).symm

theorem sup_inf (h : LengthCommensurable A B) : LengthCommensurable (A ⊔ B) (A ⊓ B) :=
  ((refl A).sup_left h.symm).inf_right (h.sup_left (refl B))

theorem inf (hA : LengthCommensurable A A') (hB : LengthCommensurable B B') :
    LengthCommensurable (A ⊓ B) (A' ⊓ B') :=
  ⟨relLength_inf_ne_top_iff.mpr
      ⟨ne_top_of_le_ne_top hA.1 (relLength_mono_left inf_le_left A'),
        ne_top_of_le_ne_top hB.1 (relLength_mono_left inf_le_right B')⟩,
    relLength_inf_ne_top_iff.mpr
      ⟨ne_top_of_le_ne_top hA.2 (relLength_mono_left inf_le_left A),
        ne_top_of_le_ne_top hB.2 (relLength_mono_left inf_le_right B)⟩⟩

theorem sup (hA : LengthCommensurable A A') (hB : LengthCommensurable B B') :
    LengthCommensurable (A ⊔ B) (A' ⊔ B') :=
  ⟨relLength_sup_ne_top_iff.mpr
      ⟨ne_top_of_le_ne_top hA.1 (relLength_anti_right A le_sup_left),
        ne_top_of_le_ne_top hB.1 (relLength_anti_right B le_sup_right)⟩,
    relLength_sup_ne_top_iff.mpr
      ⟨ne_top_of_le_ne_top hA.2 (relLength_anti_right A' le_sup_left),
        ne_top_of_le_ne_top hB.2 (relLength_anti_right B' le_sup_right)⟩⟩

theorem toNat_relLength_eq_add_of_le (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    (relLength A C).toNat = (relLength A B).toNat + (relLength B C).toNat := by
  rw [relLength_eq_add_of_le hCB hBA,
    ENat.toNat_add (h.of_between_left hCB hBA).1 (h.of_between_right hCB hBA).1]

theorem signedLength_eq_toNat_sub_of_le {D : Submodule R V} (h : LengthCommensurable A B)
    (hAD : LengthCommensurable A D) (hDA : D ≤ A) (hDB : D ≤ B) :
    signedLength A B = ((relLength A D).toNat : ℤ) - ((relLength B D).toNat : ℤ) := by
  have hBD : LengthCommensurable B D := h.symm.trans hAD
  have h₁ := hAD.toNat_relLength_eq_add_of_le (B := A ⊓ B) (le_inf hDA hDB) inf_le_left
  have h₂ := hBD.toNat_relLength_eq_add_of_le (B := A ⊓ B) (le_inf hDA hDB) inf_le_right
  rw [relLength_inf_right] at h₁
  rw [relLength_inf_right'] at h₂
  rw [h₁, h₂, signedLength]
  push_cast
  ring

theorem signedLength_eq_add (hAB : LengthCommensurable A B) (hBC : LengthCommensurable B C) :
    signedLength A C = signedLength A B + signedLength B C := by
  have hAC := hAB.trans hBC
  have hAD : LengthCommensurable A (A ⊓ B ⊓ C) := ((refl A).inf_right hAB).inf_right hAC
  have hA : A ⊓ B ⊓ C ≤ A := inf_le_left.trans inf_le_left
  have hB : A ⊓ B ⊓ C ≤ B := inf_le_left.trans inf_le_right
  have hC : A ⊓ B ⊓ C ≤ C := inf_le_right
  rw [hAB.signedLength_eq_toNat_sub_of_le hAD hA hB, hAC.signedLength_eq_toNat_sub_of_le hAD hA hC,
    hBC.signedLength_eq_toNat_sub_of_le (hAB.symm.trans hAD) hB hC]
  ring

theorem signedLength_add (hAB : LengthCommensurable A B) (hBC : LengthCommensurable B C) :
    signedLength A B + signedLength B C = signedLength A C :=
  (hAB.signedLength_eq_add hBC).symm

theorem signedLength_eq_sub_right (hAC : LengthCommensurable A C) (hBC : LengthCommensurable B C) :
    signedLength A B = signedLength A C - signedLength B C := by
  rw [hAC.signedLength_eq_add hBC.symm, hBC.signedLength_swap, sub_eq_add_neg]

theorem signedLength_eq_sub_left (hCA : LengthCommensurable C A) (hCB : LengthCommensurable C B) :
    signedLength A B = signedLength C B - signedLength C A := by
  rw [hCA.symm.signedLength_eq_add hCB, hCA.signedLength_swap, neg_add_eq_sub]

theorem signedLength_eq_toNat_sub_of_ge {D : Submodule R V} (h : LengthCommensurable A B)
    (hDA : LengthCommensurable D A) (hAD : A ≤ D) (hBD : B ≤ D) :
    signedLength A B = ((relLength D B).toNat : ℤ) - ((relLength D A).toNat : ℤ) := by
  rw [hDA.signedLength_eq_sub_left (hDA.trans h), hDA.signedLength_of_ge hAD,
    (hDA.trans h).signedLength_of_ge hBD]

end LengthCommensurable

theorem lengthCommensurable_finset_inf' {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → Submodule R V} (h : ∀ i ∈ s, LengthCommensurable A (f i)) :
    LengthCommensurable A (s.inf' hs f) :=
  Finset.inf'_induction hs f (p := LengthCommensurable A) (fun _ h₁ _ h₂ => h₁.inf_right h₂) h

theorem lengthCommensurable_finset_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → Submodule R V} (h : ∀ i ∈ s, LengthCommensurable A (f i)) :
    LengthCommensurable A (s.sup' hs f) :=
  Finset.sup'_induction hs f (p := LengthCommensurable A) (fun _ h₁ _ h₂ => h₁.sup_right h₂) h

end Commensurable

theorem relLength_chain :
    (∀ A B C : Submodule R V, C ≤ B → B ≤ A → relLength A C = relLength A B + relLength B C) ∧
    (∀ A B C : Submodule R V, relLength A C ≤ relLength A B + relLength B C) ∧
    Equivalence (LengthCommensurable : Submodule R V → Submodule R V → Prop) ∧
    (∀ A B C : Submodule R V, LengthCommensurable A B → LengthCommensurable A C →
      LengthCommensurable A (B ⊓ C) ∧ LengthCommensurable A (B ⊔ C)) ∧
    (∀ A A' B B' : Submodule R V, LengthCommensurable A A' → LengthCommensurable B B' →
      LengthCommensurable (A ⊓ B) (A' ⊓ B') ∧ LengthCommensurable (A ⊔ B) (A' ⊔ B')) ∧
    (∀ A B C : Submodule R V, LengthCommensurable A B → LengthCommensurable B C →
      signedLength A C = signedLength A B + signedLength B C) :=
  ⟨fun _ _ _ => relLength_eq_add_of_le, relLength_le_add, lengthCommensurable_equivalence,
    fun _ _ _ h₁ h₂ => ⟨h₁.inf_right h₂, h₁.sup_right h₂⟩,
    fun _ _ _ _ h₁ h₂ => ⟨h₁.inf h₂, h₁.sup h₂⟩,
    fun _ _ _ => LengthCommensurable.signedLength_eq_add⟩

end GlobalTheory
