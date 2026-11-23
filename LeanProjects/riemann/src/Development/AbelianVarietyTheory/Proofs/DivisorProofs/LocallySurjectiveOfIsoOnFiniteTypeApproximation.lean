import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsAddCommGrpIffElementsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitFiniteTypeIntRingsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.LocSurjFT

theorem etFF_id (A : CommRingCat.{0}) : EtFF (𝟙 A) := by
  refine ⟨?_, ?_⟩
  · change (algebraMap A A).Etale
    exact RingHom.etale_algebraMap.2 inferInstance
  · change (algebraMap A A).FaithfullyFlat
    exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance

theorem locSurj_of_iso_on_finiteType : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocSurj EtFF ε := by
  intro N M ε F0 ι hF0 hι hneg hpos _hN hiso n A z hz
  rcases lt_trichotomy n 0 with hn | rfl | hn
  ·
    haveI := AddCommGrpCat.subsingleton_of_isZero (hneg n hn A)
    refine ⟨A, 𝟙 A, etFF_id A, 0, 0, by simp, Subsingleton.elim _ _⟩
  ·
    obtain ⟨x, rfl⟩ := ((hι A).2 z).1 hz
    obtain ⟨J, _, _, D, κ, ⟨hc⟩, hft⟩ := GlobalTheory.T.exists_filteredColimit_finiteType_int_rings A
    obtain ⟨j, x0, hx0⟩ := ((GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} F0).1 hF0 J D (Cocone.mk A κ) hc).1 x
    haveI := hiso (D.obj j) (hft j)
    set z0 : (M.obj (D.obj j)).X 0 := ι.app (D.obj j) x0 with hz0
    set c0 : (N.obj (D.obj j)).X 0 := (inv (ε.app (D.obj j))).f 0 z0 with hc0
    have hεc0 : (ε.app (D.obj j)).f 0 c0 = z0 := by
      have := congrArg (fun h => (h.f 0).hom z0) (IsIso.inv_hom_id (ε.app (D.obj j)))
      simpa [hc0] using this
    have hdz0 : (M.obj (D.obj j)).d 0 (0 + 1) z0 = 0 := ((hι (D.obj j)).2 z0).2 ⟨x0, rfl⟩
    have hdc0 : (N.obj (D.obj j)).d 0 (0 + 1) c0 = 0 := by
      have := congrArg (fun h => h.hom z0) ((inv (ε.app (D.obj j))).comm 0 (0 + 1))
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at this
      rw [hc0, this, hdz0, map_zero]
    have h2 : (M.map (κ.app j)).f 0 z0 = ι.app A x := by
      have := ConcreteCategory.congr_hom (ι.naturality (κ.app j)) x0
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
      rw [hz0, ← hx0]
      exact this.symm
    clear_value c0 z0
    refine ⟨A, 𝟙 A, etFF_id A, (N.map (κ.app j)).f 0 c0, 0, ?_, ?_⟩
    · have := ConcreteCategory.congr_hom ((N.map (κ.app j)).comm 0 (0 + 1)) c0
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hdc0, map_zero] at this
      exact this
    · have h1 := ConcreteCategory.congr_hom (congrArg (fun h => h.f 0) (ε.naturality (κ.app j))) c0
      simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at h1
      have h1' : (ε.app A).f 0 ((N.map (κ.app j)).f 0 c0) = (M.map (κ.app j)).f 0 ((ε.app (D.obj j)).f 0 c0) := h1
      rw [h1', hεc0, h2]
      simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, map_zero, add_zero]
      rfl
  ·
    obtain ⟨B, g, hg, y, hy⟩ := hpos n hn A z hz
    refine ⟨B, g, hg, 0, -y, by simp, ?_⟩
    rw [map_neg, hy]
    simp

end GlobalTheory.EtC.LocSurjFT
