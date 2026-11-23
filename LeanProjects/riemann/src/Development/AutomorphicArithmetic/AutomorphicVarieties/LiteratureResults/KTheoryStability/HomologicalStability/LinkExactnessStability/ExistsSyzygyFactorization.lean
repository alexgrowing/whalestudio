import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.TruncFirstCycles

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → Function.Exact (d 1).hom (d 0).hom → ∃ (Z : Rep k G) (ι : Z ⟶ C 1) (h : ι ≫ d 0 = 0) (b : C 2 ⟶ Z), (ShortComplex.mk ι (d 0) h).ShortExact ∧ b ≫ ι = d 1 ∧ Function.Surjective b.hom ∧ d 2 ≫ b = 0 ∧ (Function.Exact (d 2).hom (d 1).hom → Function.Exact (d 2).hom b.hom) := by
  intro k G _ _ C d hdd hsurj hex
  have hz0 : ∀ x : C 2, (d 0).hom ((d 1).hom x) = 0 := by
    intro x
    have h := congrArg (fun f => (Rep.Hom.hom f) x) (hdd 0)
    simpa [Rep.hom_comp] using h
  have hz1 : ∀ x : C 3, (d 1).hom ((d 2).hom x) = 0 := by
    intro x
    have h := congrArg (fun f => (Rep.Hom.hom f) x) (hdd 1)
    simpa [Rep.hom_comp] using h
  let K := (d 0).hom.ker
  let ι : Rep.of K.toRepresentation ⟶ C 1 :=
    Rep.ofHom (σ := (C 1).ρ) ⟨K.toSubmodule.subtype, fun g => by ext; rfl⟩
  let bl : C 2 →ₗ[k] K.toSubmodule :=
    (d 1).hom.toLinearMap.codRestrict K.toSubmodule (fun x => hz0 x)
  let b : C 2 ⟶ Rep.of K.toRepresentation :=
    Rep.ofHom (ρ := (C 2).ρ) ⟨bl, fun g => by
      ext x
      exact Rep.hom_comm_apply (d 1) g x⟩
  have hιd : ι ≫ d 0 = 0 := by
    apply Rep.hom_ext
    ext x
    exact x.2
  refine ⟨Rep.of K.toRepresentation, ι, hιd, b, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      { exact := (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _ <|
          (ShortComplex.moduleCat_exact_iff _).2 fun x hx => ⟨⟨x, hx⟩, rfl⟩
        mono_f := (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
        epi_g := (Rep.epi_iff_surjective _).2 hsurj }
  · apply Rep.hom_ext
    ext x
    rfl
  · intro z
    obtain ⟨y, hy⟩ := (hex z.1).1 z.2
    exact ⟨y, Subtype.ext hy⟩
  · apply Rep.hom_ext
    ext x
    exact hz1 x
  · intro h2 y
    rw [← h2 y]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end GlobalTheory.HomStab.TruncFirstCycles

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.exists_syzygy_factorization : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → Function.Exact (d 1).hom (d 0).hom → ∃ (Z : Rep k G) (ι : Z ⟶ C 1) (h : ι ≫ d 0 = 0) (b : C 2 ⟶ Z), (ShortComplex.mk ι (d 0) h).ShortExact ∧ b ≫ ι = d 1 ∧ Function.Surjective b.hom ∧ d 2 ≫ b = 0 ∧ (Function.Exact (d 2).hom (d 1).hom → Function.Exact (d 2).hom b.hom) := by
  first
  | exact @GlobalTheory.HomStab.TruncFirstCycles.main
end
