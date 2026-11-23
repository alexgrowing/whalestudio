import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInIffScalarMem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.JKAppTopInjective

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRing

theorem scalar_mem_of_psiIn : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → ∀ (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), PsiScal D ga a → ∀ (x : D'.X) (J' : Ideal V), D'.PsiIn x J' → ∀ p q : R, algebraMap R (FractionRing R) q * (a (xe x)).val = algebraMap R (FractionRing R) p → ∃ m ∈ J', φ p = φ q * m := by
  intro R V _ _ _ _ _ φ D D' β v xe _ hv hc gam hgam hψ ga a hS x J' hJ' p q hpq
  obtain ⟨ga', a', hS'⟩ := exists_psiScal V D'
  obtain ⟨m₀, hm₀, em₀⟩ := (PsiScalIn.main_local D' ga' a' hS' x J').1 hJ'
  obtain ⟨t, ht, Ht⟩ := CubTransport.exists_pmaps ((isGen_iff v).1 hv) D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => (D'.c x).left) (φ := fun _ => (D.c (xe x)).left) (ε := fun _ => -1) (spMap φ) (fun _ => hc x)
    (ga (xe x)) (hS (xe x)).1
  obtain ⟨c, hcu⟩ := exists_unit_val_eq_mul D'.P.isLB (hS' x).1 ht
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (FractionRing V))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing V)))
  choose I hI using fun χ : (TK V).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  choose I' hI' using fun χ : (TK V).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ z)
  have gI : Good D.P.L (Z := (TK V).left) z I := hI
  have gI' : Good D'.P.L (Z := (TK V).left) z I' := hI'
  have hx : D'.xK x ≫ β = gam ≫ D.xK (xe x) := by
    change (jK V ≫ (D'.c x).left) ≫ β = gam ≫ jK R ≫ (D.c (xe x)).left
    rw [Category.assoc, hc x, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ (D.c (xe x)).left) hgam.symm
  have e₁ := CubTransport.val_pmaps (fun _ => hx) (hψ x) (𝟙 _) gI gI'
  have e₂ := CubTransport.val_pmaps (fun _ => hc x) Ht (jK V) gI gI'
  have e₃ := (hS (xe x)).2 (Over.mk (gam ≫ jK R)) (Over.homMk gam rfl) z I gI
  have e₄ := (hS' x).2 (TK V) (𝟙 _) z I' gI'
  have e₅ := hcu _ (jK V) z I' gI'
  rw [Category.id_comp, Fintype.prod_unique, Category.id_comp] at e₁
  rw [Fintype.prod_unique, ← hgam] at e₂
  obtain ⟨Ω, f₁, f₂⟩ : ∃ Ω : ((Spec (CommRingCat.of (FractionRing V))).presheaf.stalk z)ˣ,
      val (Z := Spec (CommRingCat.of (FractionRing V))) (D.psi (xe x)) gam z I = Ω * val (Z := Spec (CommRingCat.of (FractionRing V))) (D'.psi x) (𝟙 _) z I' ∧
        val (Z := Spec (CommRingCat.of (FractionRing V))) (ga (xe x)) (gam ≫ jK R) z I = Ω * val (Z := Spec (CommRingCat.of (FractionRing V))) t (jK V) z I' := ⟨_, e₁, e₂⟩
  have f₃ : (val (Z := Spec (CommRingCat.of (FractionRing V))) (D.psi (xe x)) gam z I).val =
      gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (a (xe x)).val) * (val (Z := Spec (CommRingCat.of (FractionRing V))) (ga (xe x)) (gam ≫ jK R) z I).val := e₃
  have f₄ : (val (Z := Spec (CommRingCat.of (FractionRing V))) (D'.psi x) (𝟙 _) z I').val =
      PsiScalIn.sig z (a' x).val * (val (Z := Spec (CommRingCat.of (FractionRing V))) (ga' x) (jK V) z I').val :=
    e₄.trans (congrArg₂ (· * ·) (PsiScalIn.gs_scal_id z _) rfl)
  let u : V := (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom c.val
  have hu : gs (jK V) z ⊤ c.val = PsiScalIn.sig z (algebraMap V _ u) := by
    refine Eq.trans (congrArg (gs (jK V) z ⊤) ?_) (PsiScalIn.gs_toOpen z ⊤ trivial u)
    simp [u, DegPre.toOpen]
  have key : gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (a (xe x)).val) = PsiScalIn.sig z (algebraMap V _ (m₀ * u)) := by
    rw [f₁, f₂, Units.val_mul, Units.val_mul, f₄, mul_left_comm (gs _ _ _ _), Units.mul_right_inj] at f₃
    have f₅ := f₃.symm.trans (congrArg (PsiScalIn.sig z (a' x).val * ·) (e₅.trans (congrArg (· * _) hu)))
    rw [← _root_.mul_assoc, Units.mul_left_inj] at f₅
    rw [map_mul, map_mul, em₀]
    exact f₅
  have hs : ∀ r : R, gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (algebraMap R (FractionRing R) r)) =
      PsiScalIn.sig z (algebraMap V _ (φ r)) := fun r => by
    have k : ∀ {A : Type} [CommRing A] (w : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of A)) (s : A),
        gs (𝟙 _) z ⊤ (scal w s) = cst w z s := fun w s =>
      (gs_pull (𝟙 _) w z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
    refine (congrArg _ (PsiInt.scal_jK gam r).symm).trans ((k _ r).trans ?_)
    refine (congrArg (fun w => cst w z r) hgam).trans ((cst_comp (jK V) φ z r).trans ?_)
    refine Eq.trans ?_ (PsiScalIn.gs_toOpen z ⊤ trivial (φ r))
    exact (gs_res (jK V) z (U := ⊤) (V := ⊤) le_top trivial _).symm
  refine ⟨m₀ * u, J'.mul_mem_right u hm₀, IsFractionRing.injective V (FractionRing V) ((PsiScalIn.sig z).injective ?_)⟩
  rw [map_mul (algebraMap V _) (φ q), map_mul (PsiScalIn.sig z), ← hs, ← hs, ← key, ← hpq, ← gs_mul _ z ⊤ trivial]
  unfold scal
  rw [map_mul, map_mul]

end GlobalTheory.PsiRing
