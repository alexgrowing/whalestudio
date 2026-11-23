import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculusStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecLocalRingHomExtOfInjectiveLocalHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftLocalPointAlongAffineFlatSurjectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem GlobalTheory.SiegLev.SQuot.eq_of_siegPB : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [CommRing o'] (ζ : o) (ζ' : o') (F : SFam h N ζ') (j : o →+* o') (Q : SQuot F n ζ j) (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ Q.X) (s' : Sp R ⟶ Sp o) (c : SiegPre h n ζ s'), x ≫ Q.s = y ≫ Q.s → SiegPB c Q.univ x → SiegPB c Q.univ y → x = y := by
  intro h n N o o' _ _ ζ ζ' F j Q R _ _ x y s' c hxy hx hy
  haveI := Q.fin; haveI := Q.etale; haveI := Q.onto
  obtain ⟨R1, _, _, φ1, hl1, hφ1, x1, hx1⟩ := GlobalTheory.T.exists_lift_localPoint_along_affine_flat_surjection R Q.X F.X Q.π x
  obtain ⟨R2, _, _, φ2, hl2, hφ2, y2, hy2⟩ := GlobalTheory.T.exists_lift_localPoint_along_affine_flat_surjection R1 Q.X F.X Q.π (spMap φ1 ≫ y)
  set g : Sp R2 ⟶ Sp R := spMap φ2 ≫ spMap φ1 with hg
  set x2 : Sp R2 ⟶ F.X := spMap φ2 ≫ x1 with hx2d
  have hx2 : x2 ≫ Q.π = g ≫ x := by simp only [x2, g, Category.assoc, hx1]
  have hy2' : y2 ≫ Q.π = g ≫ y := by simp only [g, Category.assoc, hy2]
  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨c2, hc2⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n o o ζ ζ (RingHom.id o) (Sp R) (Sp R2) s' (g ≫ s') g rfl (by rw [hid, Category.comp_id])).1 c
  have key : ∀ z : Sp R ⟶ Q.X, ∀ z2 : Sp R2 ⟶ F.X, z2 ≫ Q.π = g ≫ z → SiegPB c Q.univ z → SRel c2 F.univ 1 (N / n) z2 := by
    intro z z2 hz hcz
    have A := (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n n o o o ζ ζ ζ Q.X (Sp R) (Sp R2) Q.s s' (g ≫ s') Q.univ c c2 z g 1 1 1 ((sRel_one_one_iff _ _ _).2 hcz)).1
    have B : SRel c2 Q.univ 1 1 (g ≫ z) := A.1 ((sRel_one_one_iff _ _ _).2 hc2)
    have C := (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n N n o o' o ζ ζ' ζ Q.X F.X (Sp R2) Q.s F.s (g ≫ s') Q.univ F.univ c2 Q.π z2 1 (N / n) 1 Q.low).1
    rw [hz] at C
    exact C.2 B
  have e := Q.fibre R2 x2 y2 (g ≫ s') c2 (by
      rw [← Q.base, ← Category.assoc, ← Category.assoc y2, hx2, hy2', Category.assoc, Category.assoc, hxy]; simp only [g, Category.assoc])
    (key x x2 hx2 hx) (key y y2 hy2' hy)
  rw [hx2, hy2'] at e
  have hcomp : spMap (φ2.comp φ1) = g := by
    simp only [g, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  exact GlobalTheory.T.spec_localRing_hom_ext_of_injective_localHom R R2 (φ2.comp φ1) inferInstance (hφ2.comp hφ1) Q.X x y (by rw [hcomp]; exact e)
