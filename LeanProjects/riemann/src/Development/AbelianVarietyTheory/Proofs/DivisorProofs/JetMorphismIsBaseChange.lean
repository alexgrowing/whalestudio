import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct

section Aug

variable {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}

theorem JetRing.π_comp_algebraMap (J : JetRing R I n) : J.π.comp (algebraMap R J.B) = RingHom.id R := by
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, J.π_eq, Algebra.algebraMap_eq_smul_one,
    ← J.one, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul]
  simp

theorem JetRing.π_surjective (J : JetRing R I n) : Function.Surjective J.π := fun r =>
  ⟨algebraMap R J.B r, by simpa using RingHom.congr_fun J.π_comp_algebraMap r⟩

end Aug

theorem grpMor_isBC (P : AbelianDeRham) {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))) :
    m.IsBC := by
  obtain ⟨-, -, PB, PR, -⟩ := P
  obtain ⟨C, _, φ, hφ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback X.A (spMap (algebraMap R J.B))
  have eid : spMap J.π ≫ spMap (algebraMap R J.B) = 𝟙 _ := by
    rw [spMap_comp_spMap, J.π_comp_algebraMap]
    exact Spec.map_id _
  have w : 𝟙 X.A.left ≫ X.A.hom = (X.A.hom ≫ spMap J.π) ≫ spMap (algebraMap R J.B) := by
    rw [Category.assoc, eid, Category.comp_id, Category.id_comp]
  have e1 : hφ.1.lift _ _ w ≫ φ = 𝟙 _ := hφ.1.lift_fst _ _ _
  have e2 : hφ.1.lift _ _ w ≫ C.hom = X.A.hom ≫ spMap J.π := hφ.1.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl X.A).hom := inferInstanceAs (IsMonHom (𝟙 X.A))
  have hic : IsGrpPullback X.A C (spMap J.π) (hφ.1.lift _ _ w) :=
    hφ.cancel ((isGrpPullback_of_iso (Iso.refl X.A)).congr eid.symm e1.symm) e2
  have hC := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback X.ab hφ
  have gC := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 X.dim
  obtain ⟨bc, -⟩ := PB R X.A _ X.ab X.dim J.B C φ hφ
  have rg := PR _ C _ hC gC _ J.κ J.nil R J.π J.π_surjective rfl X.A _ hic
  have e : ∀ z, liftSemi m.pull z = (liftMor J.κ hic).pull (liftSemi (bcMor hφ).pull z) := fun z => by
    induction z with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r c =>
      rw [liftSemi_tmul, liftSemi_tmul, map_smul,
        ← GrpMor.pull_pull (bcMor hφ) (liftMor J.κ hic) m (fun _ => rfl) (by simpa using e1) c]
  have : ⇑(liftSemi m.pull) = (liftMor J.κ hic).pull ∘ liftSemi (bcMor hφ).pull := funext e
  unfold GrpMor.IsBC
  rw [this]
  exact rg.comp bc

end GlobalTheory.LatJet
