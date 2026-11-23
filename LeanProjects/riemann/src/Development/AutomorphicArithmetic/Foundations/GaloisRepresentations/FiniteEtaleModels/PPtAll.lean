import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLevelStructureAtGeometricPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private theorem lev_pow {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (l : D.La → (T ⟶ o.A)) : IsEtLevOver o (𝔞 ^ r) 1 l ↔ IsEtLevOver o 𝔞 r l := by
  unfold IsEtLevOver wSub
  simp only [pow_one]

private theorem lev_top {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {T : Over S} :
    IsEtLevOver o (⊤ : Ideal (𝓞 D.F)) 1 (fun _ : D.La => (1 : T ⟶ o.A)) := by
  have hw : ∀ y : D.La, y ∈ wSub D (⊤ : Ideal (𝓞 D.F)) 1 := by
    intro y
    refine Submodule.subset_span ⟨1, by simp, y, ?_⟩
    simp
  refine ⟨fun _ _ => (_root_.mul_one _).symm, fun c _ => ?_, fun _ _ => rfl, fun k _ _ x => ⟨fun y _ => hw y, fun g hg => ⟨0, ?_⟩⟩⟩
  · haveI := o.act.hom c
    exact (MonObj.one_comp _).symm
  · have h1 := hg 1 (by simp)
    rw [map_one, o.act.one, Category.comp_id] at h1
    rw [h1]
    exact MonObj.comp_one _

theorem UpperTheory.Gal.FiniteEtaleModels.ptAll_holds :
    IdealInd → CrtMul → PtAll := by
  intro hI hC p _ D R _ b N 𝔞 r hc he S s o k _ _ x
  have key : ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o (𝔞 ^ r) 1 l := by
    refine hI (𝓞 D.F) (IsEtPlace b)
      (fun 𝔠 => ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o 𝔠 1 l) ?_ ?_ ?_ (𝔞 ^ r)
      (pow_ne_zero _ he.1) ?_
    · exact ⟨_, lev_top o⟩
    · intro w e _ hw
      obtain ⟨l, hl⟩ := GlobalTheory.T.exists_etaleLevelStructure_at_geometricPoint p D R b N w e hc hw S s o k x
      exact ⟨l, (lev_pow o w e l).2 hl⟩
    · rintro 𝔟 𝔠 hbc ⟨l₁, h₁⟩ ⟨l₂, h₂⟩
      exact ⟨_, hC p D R b N S s o 𝔟 𝔠 hbc _ l₁ l₂ h₁ h₂⟩
    · intro w hw hle
      exact he.2 w hw (hw.isPrime.le_of_pow_le hle)
  obtain ⟨l, hl⟩ := key
  exact ⟨l, (lev_pow o 𝔞 r l).1 hl⟩
