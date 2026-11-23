import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPowDeg

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory

namespace PsiScalIn

open PsiInPull PsiInPow

variable {R : Type} [CommRing R] [IsDomain R]

def sig (z : Spec (CommRingCat.of (FractionRing R))) :
    FractionRing R →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z :=
  ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom

theorem gs_scal_id (z : Spec (CommRingCat.of (FractionRing R))) (c : FractionRing R) :
    gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing R)))) c) = sig z c := by
  rw [gs_eq _ z ⊤ trivial]; rfl

theorem gs_toOpen (z : Spec (CommRingCat.of (FractionRing R))) (V : (Spec (CommRingCat.of R)).Opens)
    (hz : jK R z ∈ V) (r : R) : gs (jK R) z V (DegPre.toOpen V r) = sig z (algebraMap R _ r) := by
  have nat := congrArg (fun g => g.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  refine (gs_res (jK R) z (le_top : V ≤ ⊤) hz _).trans ((gs_eq (jK R) z ⊤ trivial _).trans ?_)
  simp only [sig, RingHom.comp_apply]
  rw [nat]
  rfl

theorem key (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) (h : PsiScal D ga a) (χ : D.X) (q : D.P.L.ι)
    (V : (Spec (CommRingCat.of R)).Opens) (hle : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q)
    (z : Spec (CommRingCat.of (FractionRing R))) (hz : jK R z ∈ V) :
    ∃ u : Γ(Spec (CommRingCat.of R), V)ˣ,
      (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q)) ((D.psi χ).s (fun _ => q))).val =
        sig z (a χ).val * gs (jK R) z V u.val := by
  have hle' : V ≤ LB.wchart D.P.L (fun _ : PUnit => (D.c χ).left) (fun _ => q) := fun y hy =>
    mem_wchart _ _ _ _ (hle hy)
  obtain ⟨J, hJ, e⟩ := exists_good D.P.L D.P.isLB (Z := (TK R).left) z (K := PUnit) (fun _ => D.xK χ) (fun _ => q)
    (fun _ _ _ => rfl) (fun _ => hle hz)
  have e0 : J (D.xK χ) = q := e PUnit.unit
  have v := (h χ).2 (TK R) (𝟙 _) z J hJ
  have v1 := val_of (D.psi χ) (𝟙 _) z J (fun _ => q) (fun _ => (congrArg J (Category.id_comp _)).trans e0)
  have v2 := val_of (ga χ) (toUnit (TK R)).left z J (fun _ => q) (fun _ => e0)
  refine ⟨res hle' ((ga χ).s (fun _ => q)), (congrArg Units.val v1).symm.trans (v.trans ?_)⟩
  refine congrArg₂ (· * ·) (gs_scal_id z _) ?_
  refine (congrArg Units.val v2).trans ?_
  exact ((gs_unit _ _ _ hz _).trans (congrArg Units.val (gm_res _ _ hle' hz _))).symm

theorem main_local [IsLocalRing R] (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) (h : PsiScal D ga a) (χ : D.X) (J : Ideal R) :
    D.PsiIn χ J ↔ ∃ r ∈ J, algebraMap R (FractionRing R) r = (a χ).val := by
  constructor
  · intro H
    obtain ⟨q, hq⟩ := exists_chart D.P.isLB ((D.c χ).left (IsLocalRing.closedPoint R))
    have hle : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q := fun y _ =>
      (IsLocalRing.specializes_closedPoint y).mem_open ((D.c χ).left ⁻¹ᵁ D.P.L.U q).isOpen hq
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
    obtain ⟨r, hr, e⟩ := gs_of_psiIn D χ J H q ⊤ (isAffineOpen_top _) hle z trivial
    obtain ⟨u, hu⟩ := key D ga a h χ q ⊤ hle z trivial
    have hs : Function.Surjective (DegPre.toOpen (R := R) ⊤) := by
      intro b
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b, ?_⟩
      simp [DegPre.toOpen]
    obtain ⟨s, hsJ, es⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 (Ideal.mul_mem_right (u⁻¹).val _ hr)
    refine ⟨s, hsJ, (sig z).injective ?_⟩
    have hz : jK R z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
    rw [← gs_toOpen z ⊤ hz, es, gs_mul _ _ _ hz, e.trans hu, _root_.mul_assoc,
      ← gs_mul _ _ _ hz, Units.mul_inv, gs_eq _ _ _ hz, map_one, map_one, _root_.mul_one]
  · rintro ⟨r, hr, e⟩
    refine psiIn_of_gs D χ J fun q V _ hle z hz => ?_
    obtain ⟨u, hu⟩ := key D ga a h χ q V hle z hz
    refine ⟨DegPre.toOpen V r * u.val, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr), ?_⟩
    rw [gs_mul _ _ _ hz, gs_toOpen z V hz, e]
    exact hu.symm

end PsiScalIn

theorem psiIn_iff_scalar_mem : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → ∀ (χ : D.X) (J : Ideal V), J ≠ ⊥ → (D.PsiIn χ J ↔ ∃ r ∈ J, algebraMap V (FractionRing V) r = (a χ).val) :=
  fun _ _ _ _ D ga a h χ J _ => PsiScalIn.main_local D ga a h χ J

end GlobalTheory
