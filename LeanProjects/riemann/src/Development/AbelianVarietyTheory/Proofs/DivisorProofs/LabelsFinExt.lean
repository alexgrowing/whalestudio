import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrExtensionQkPointsRational
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LabExt

open GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem qkExt_refl {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C]
    [Algebra (FractionRing R) C] {k : ℕ} (p : QkPt D C k) : QkExt (RingHom.id C) p p := by
  have e : spMap (RingHom.id C) = 𝟙 _ := Spec.map_id _
  refine ⟨rfl, by rw [e, Category.id_comp], fun χ => ?_⟩
  rw [e]
  exact corr_of_val D.P.isLB fun y J hJ =>
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val (p.g.s χ) r y J) (Category.id_comp _))).symm

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (f : B →+* C) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [spMap, spMap, ← Spec.map_comp]; rfl

section Lab

variable {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] {ρ : R →+* R₁}
  {D : DegPre R} {D₁ : DegPre R₁} [Algebra (FractionRing R) (Kb R₁)]

def pre (hρ : IsPullDeg ρ D D₁) (hG : GlobalFnsSt) (hF : Compat ρ (Kb R₁)) (hB : D.TauBimult) (hB₁ : D₁.TauBimult)
    {k : ℕ} (P : QkPt D₁ (Kb R₁) k) : QkPt D (Kb R₁) k :=
  Classical.choose (pullQk_surjective hρ hG hF hB hB₁ P)

theorem symm_comp (τ : Kb R ≃ₐ[FractionRing R] Kb R₁) :
    (τ.symm : Kb R₁ →+* Kb R).comp (algebraMap (FractionRing R) (Kb R₁)) = algebraMap (FractionRing R) (Kb R) :=
  RingHom.ext fun x => τ.symm.commutes x

theorem tau_comp (τ : Kb R ≃ₐ[FractionRing R] Kb R₁) :
    (τ : Kb R →+* Kb R₁).comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R₁) :=
  RingHom.ext fun x => τ.commutes x

def down (hB : D.TauBimult) (τ : Kb R ≃ₐ[FractionRing R] Kb R₁) {k : ℕ} (q : QkPt D (Kb R₁) k) : QkPt D (Kb R) k :=
  qkExt hB (τ.symm : Kb R₁ →+* Kb R) (symm_comp τ) q

variable {A : PolAV (Sp (FractionRing R))} {A₁ : PolAV (Sp (FractionRing R₁))}

theorem lift_w (τ : Kb R ≃ₐ[FractionRing R] Kb R₁) (gb : FractionRing R →+* FractionRing R₁)
    (hgbK : (algebraMap (FractionRing R₁) (Kb R₁)).comp gb = algebraMap (FractionRing R) (Kb R₁))
    (x : TFK (R := R) (Kb R) ⟶ A.A) :
    (spMap (τ : Kb R →+* Kb R₁) ≫ x.left) ≫ A.A.hom = jFK (R := R₁) (Kb R₁) ≫ spMap gb := by
  rw [Category.assoc, Over.w x]
  change spMap (τ : Kb R →+* Kb R₁) ≫ spMap (algebraMap (FractionRing R) (Kb R)) =
    spMap (algebraMap (FractionRing R₁) (Kb R₁)) ≫ spMap gb
  rw [spMap_comp', spMap_comp', tau_comp, hgbK]

def liftPt (τ : Kb R ≃ₐ[FractionRing R] Kb R₁) {b : A₁.A.left ⟶ A.A.left} {gb : FractionRing R →+* FractionRing R₁}
    (hpb : IsPullback b A₁.A.hom A.A.hom (spMap gb))
    (hgbK : (algebraMap (FractionRing R₁) (Kb R₁)).comp gb = algebraMap (FractionRing R) (Kb R₁))
    (x : TFK (R := R) (Kb R) ⟶ A.A) : TFK (R := R₁) (Kb R₁) ⟶ A₁.A :=
  Over.homMk (hpb.lift _ _ (lift_w τ gb hgbK x)) (hpb.lift_snd _ _ _)

end Lab

end GlobalTheory.LabExt
