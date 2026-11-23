import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.PoincareDeRhamDualityOfCube
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.DualRT

open CrystallinePoints.Pd GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

variable {R : Type} [CommRing R] {X : Scheme.{0}}

@[reducible] def ptOf {s : X ⟶ Sp R} (T : TT s) : Pt s := ⟨T.obj.B, pt T, pt_w T⟩

theorem pt_comp {s : X ⟶ Sp R} {T T' : TT s} (a : T ⟶ T') :
    spMap (a.hom.φ : T.obj.B →+* T'.obj.B) ≫ pt T = pt T' := by
  have key : (a.hom.φ : T.obj.B →+* T'.obj.B).comp ((πe T).symm : T.obj.B₀ →+* T.obj.B)
      = ((πe T').symm : T'.obj.B₀ →+* T'.obj.B).comp a.hom.φ₀ := by
    ext x
    obtain ⟨b, rfl⟩ := (πe T).surjective x
    apply (πe T').injective
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply,
      RingEquiv.apply_symm_apply, AlgHom.coe_toRingHom]
    simp only [πe, RingEquiv.ofBijective_apply]
    exact (a.hom.comm b).symm
  unfold pt
  rw [← a.hom.pt]
  simp only [spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [key]

def ofPC (s : X ⟶ Sp R) : CoefMap (RingHom.id R) (FP s) ((IsTriv s).ι ⋙ O (dp0 R) s) where
  G := { obj := ptOf
         map := fun a ↦ ⟨a.hom.φ, pt_comp a⟩
         map_id := fun _ ↦ hom_ext fun _ ↦ rfl
         map_comp := fun _ _ ↦ hom_ext fun _ ↦ rfl }
  α T := RingHom.id T.obj.B
  naturality _ _ := rfl
  smul _ _ _ := rfl

def toPO (s : X ⟶ Sp R) : CoefMap (RingHom.id R) ((IsTriv s).ι ⋙ O (dp0 R) s) (FP s) :=
  ptCoef (F := FP s) (fun P ↦ P.x) (fun P ↦ P.w) fun _ _ a ↦ a.pt

theorem toPO_toH1O (s : X ⟶ Sp R) (c : FirstDeRham s) : (toPO s).pull1 (toH1O s c) = toP s c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rfl

private theorem spMap_id_comp_spMap_symm_comp {A : Type} [CommRing A] [Algebra R A] {Y : Scheme} (e : A ≃+* A)
    (he : ∀ z, e z = z) (y : Sp A ⟶ Y) :
    spMap ((AlgHom.id R A : A →ₐ[R] A) : A →+* A) ≫ spMap (e.symm : A →+* A) ≫ y = y := by
  have h1 : (e.symm : A →+* A) = RingHom.id A := by
    ext z
    apply e.injective
    show e (e.symm z) = e z
    rw [RingEquiv.apply_symm_apply, he]
  have h2 : ((AlgHom.id R A : A →ₐ[R] A) : A →+* A) = RingHom.id A := rfl
  rw [h1, h2]
  simp [spMap]

theorem toPO_ofPC (s : X ⟶ Sp R) (c : H1OnPoints s) : (toPO s).pull1 ((ofPC s).pull1 c) = c := by
  rw [← CoefMap.pullCohomologyOne_comp]
  let θ : ((ofPC s).comp (toPO s)).G ⟶ (CoefMap.id (FP s)).G :=
    { app := fun P => ⟨AlgHom.id R P.B, spMap_id_comp_spMap_symm_comp _ (fun _ => rfl) P.x⟩
      naturality := fun _ _ _ => CrystallinePoints.Pd.hom_ext fun _ => rfl }
  exact (CoefMap.pullCohomologyOne_eq_of_natTrans _ (CoefMap.id (FP s)) θ (fun _ _ => rfl) c).trans (CoefMap.pullCohomologyOne_id c)

private theorem cmpO_toH1O_eq_toHO1_cmp1 (s : X ⟶ Sp R) (c : FirstDeRham s) :
    GlobalTheory.CechDR.cmpO s (toH1O s c) = toHO1 s (cmp1 s c) := by
  obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ c
  rfl

theorem toPicard_surjective (s : X ⟶ Sp R) (h₁ : Function.Surjective (cmp1 s)) (h₂ : Function.Surjective (toHO1 s)) :
    Function.Surjective (toP s) := by
  intro t
  obtain ⟨c, hc⟩ := (h₂.comp h₁) (GlobalTheory.CechDR.cmpO s ((ofPC s).pull1 t))
  refine ⟨c, ?_⟩
  have e : toH1O s c = (ofPC s).pull1 t :=
    GlobalTheory.CechDR.cmpO_injective R X s (by rw [cmpO_toH1O_eq_toHO1_cmp1]; exact hc)
  rw [← toPO_toH1O, e, toPO_ofPC]

theorem surjAll_of_hodge (hC : CrystallineSmoothLift) (hH : AbelianHodgeDeRham) : SurjAll := by
  intro R _ A _ g hAb hsm
  haveI := hAb
  haveI : IsProper A.hom := IsAbelianScheme.proper
  have hs : A.hom ≫ 𝟙 (Sp R) = A.hom := Category.comp_id _
  refine toPicard_surjective _ ?_ ?_
  · rw [hs]
    exact (hC.bijective_cechDeRhamComparison_degreeOne A.hom IsAbelianScheme.smooth inferInstance inferInstance).2
  · rw [hs]
    exact (hH R A g hAb hsm).2.2.2.2.1.2.2

end PositivityTheory.DualRT
