import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValSectionUnit
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.E8Ring
open GlobalTheory.Mum.UnitValuedLeadingSection

noncomputable section

namespace GlobalTheory.Mum.UnitValuedLeadingSection

open Formalism.L2.Pj GlobalTheory.PsiCoordLocal

theorem gs_jK_toOpen_top {R : Type} [CommRing R] [IsDomain R] (z : (TK R).left) (r : R) :
    gs (jK R) z ⊤ (DegPre.toOpen (R := R) ⊤ r) = thK R z (algebraMap R (FractionRing R) r) := by
  have hz : jK R z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
  rw [gs_eq _ z ⊤ hz]
  have e := congrArg (fun f => f.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have t : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    simp [DegPre.toOpen]
  rw [t]
  simp only [thK, RingHom.comp_apply]
  rw [e]
  rfl

theorem psiIn_iff_val : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), TopGood D.P z J → ∀ (χ : D.X) (I : Ideal R), D.PsiIn χ I ↔ ∃ r ∈ I, ((val (D.psi χ) (𝟙 _) z J : ((TK R).left.presheaf.stalk z)ˣ) : (TK R).left.presheaf.stalk z) = thK R z (algebraMap R (FractionRing R) r) := by
  intro R _ _ _ D z J hJ χ I
  let j : PUnit → D.P.L.ι := fun _ => J (𝟙 _ ≫ D.xK χ)
  have hxK : 𝟙 _ ≫ D.xK χ = jK R ≫ (D.c χ).left := by
    rw [Category.id_comp]
    show (toUnit (TK R) ≫ D.c χ).left = _
    rw [Over.comp_left]
    congr 1 <;> simp
  have hj : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) := by
    have := hJ.2 (D.c χ).left (Over.w (D.c χ))
    show ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (J (𝟙 _ ≫ D.xK χ))
    rw [hxK, this]
  have h := generic_le D χ j hj
  have key : ∀ r : R, ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) =
      ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val ↔
      ((val (D.psi χ) (𝟙 _) z J : ((TK R).left.presheaf.stalk z)ˣ) : (TK R).left.presheaf.stalk z) =
        thK R z (algebraMap R (FractionRing R) r) := by
    intro r
    have hz : z ∈ jK R ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
    have g1 : gs (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z _ (((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r)) =
        thK R z (algebraMap R (FractionRing R) r) := by
      rw [gs_pull (𝟙 _) (jK R) z ⊤ trivial, Category.id_comp]
      exact gs_jK_toOpen_top z r
    have g2 : gs (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z _ (((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val) =
        ((val (D.psi χ) (𝟙 _) z J : ((TK R).left.presheaf.stalk z)ˣ) : (TK R).left.presheaf.stalk z) := by
      refine (gs_res _ z h hz _).trans ((gs_unit _ _ _ (h hz) _).trans ?_)
      rfl
    constructor
    · intro e
      rw [← g1, ← g2, e]
    · intro e
      refine fn_ext fun y _ => ?_
      obtain rfl : y = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) y z
      rw [g1, g2, e]
  constructor
  · intro hI
    obtain ⟨s, hs, es⟩ := hI j ⊤ (isAffineOpen_top _) hj h
    obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ toOpen_top_bijective.2).1 hs
    exact ⟨r, hr, (key r).1 es⟩
  · rintro ⟨r, hr, e⟩
    exact (GlobalTheory.PeriodFormEdge.psiIn_iff ⟨j, hj, h, (key r).2 e⟩ I).2 hr

end GlobalTheory.Mum.UnitValuedLeadingSection
