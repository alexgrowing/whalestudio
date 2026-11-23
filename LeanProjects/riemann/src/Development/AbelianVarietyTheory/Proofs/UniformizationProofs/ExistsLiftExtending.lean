import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAffineWeightUnits
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianPartLift

section General
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_torus_lift [Module.Free ℤ X] {Z' Z : Over S} (ρ : Z' ⟶ Z)
    (h : ∀ a : Γ(Z'.left, ⊤)ˣ, ∃ r : Γ(Z.left, ⊤)ˣ, ρ.left.appTop.hom r.val = a.val)
    (t : Z' ⟶ splitTorus S X) : ∃ t' : Z ⟶ splitTorus S X, ρ ≫ t' = t := by
  let e := Module.Free.chooseBasis ℤ X
  choose r hr using h
  let l : X →ₗ[ℤ] Additive Γ(Z.left, ⊤)ˣ := e.constr ℤ fun k => Additive.ofMul (r (chV t (e k)))
  let m : X →ₗ[ℤ] Additive Γ(Z'.left, ⊤)ˣ :=
    (MonoidHom.toAdditiveRight (splitTorusPointsEquiv S X Z' t)).toIntLinearMap
  let n : Additive Γ(Z.left, ⊤)ˣ →ₗ[ℤ] Additive Γ(Z'.left, ⊤)ˣ :=
    (MonoidHom.toAdditive (Units.map ρ.left.appTop.hom.toMonoidHom)).toIntLinearMap
  have hl : n ∘ₗ l = m := e.ext fun k => by
    rw [LinearMap.comp_apply, Module.Basis.constr_basis]
    exact congrArg Additive.ofMul (Units.ext (hr _))
  let t' := (splitTorusPointsEquiv S X Z).symm (AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom)
  have ht' : ∀ χ, chV t' χ = Additive.toMul (l χ) := fun χ => by
    rw [chV, MulEquiv.apply_symm_apply]; rfl
  refine ⟨t', (splitTorusPointsEquiv S X Z').injective (MonoidHom.ext fun χ => Units.ext ?_)⟩
  have e₁ : (chV (ρ ≫ t') (Multiplicative.toAdd χ)).val = ρ.left.appTop.hom (chV t' (Multiplicative.toAdd χ)).val := by
    rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]
  refine e₁.trans ?_
  rw [ht']
  exact congrArg (fun a => (Additive.toMul a).val) (LinearMap.congr_fun hl (Multiplicative.toAdd χ))

theorem units_lift {A A' : Type} [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A'] (f : A →+* A')
    (hf : Function.Surjective f) (a : Γ(Spec (CommRingCat.of A'), ⊤)ˣ) :
    ∃ r : Γ(Spec (CommRingCat.of A), ⊤)ˣ, (Spec.map (CommRingCat.ofHom f)).appTop.hom r.val = a.val := by
  have : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨c, hc⟩ := hf ((Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom a.val)
  have hu : IsUnit c := IsUnit.of_map f c (hc ▸ a.isUnit.map _)
  refine ⟨(hu.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).unit, ?_⟩
  rw [IsUnit.unit_spec]
  have e := congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  rw [← e, hc]
  exact congrArg (fun q => q.hom a.val) (Scheme.ΓSpecIso (CommRingCat.of A')).hom_inv_id

theorem exists_lift_extending [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    {A A' : Type} [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A'] (f : A →+* A')
    (hf : Function.Surjective f) (b : Spec (CommRingCat.of A) ⟶ Q.B.left) (y : Spec (CommRingCat.of A') ⟶ G.left)
    (hy : y ≫ Q.q.left = Spec.map (CommRingCat.ofHom f) ≫ b) :
    ∃ g : Spec (CommRingCat.of A) ⟶ G.left, g ≫ Q.q.left = b ∧ Spec.map (CommRingCat.ofHom f) ≫ g = y := by
  have := Q.q_hom
  have := Q.i_hom
  let b' : Over.mk (b ≫ Q.B.hom) ⟶ Q.B := Over.homMk b rfl
  let y' : Over.mk (y ≫ G.hom) ⟶ G := Over.homMk y rfl
  let ρ : Over.mk (y ≫ G.hom) ⟶ Over.mk (b ≫ Q.B.hom) := Over.homMk (Spec.map (CommRingCat.ofHom f)) (by
    change Spec.map (CommRingCat.ofHom f) ≫ b ≫ Q.B.hom = y ≫ G.hom
    rw [← Category.assoc, ← hy, Category.assoc, Over.w])
  have hy' : y' ≫ Q.q = ρ ≫ b' := Over.OverMorphism.ext hy
  obtain ⟨g, hg⟩ := Q.exists_lift b'
  have h₁ : (y' * (ρ ≫ g)⁻¹) ≫ Q.q = toUnit _ ≫ η[Q.B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hg, hy', mul_inv_cancel, Hom.one_def]
  obtain ⟨t, ht⟩ := exists_torus_lift ρ (units_lift f hf) (Q.isKernel.lift _ _ h₁)
  have h₃ : (t ≫ Q.i) ≫ Q.q = 1 := by
    rw [Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (t ≫ toUnit _) (toUnit _)]
  have a₁ : ((t ≫ Q.i) * g) ≫ Q.q = b' := by rw [MonObj.mul_comp, h₃, _root_.one_mul, hg]
  have a₂ : ρ ≫ ((t ≫ Q.i) * g) = y' := by
    rw [MonObj.comp_mul, ← Category.assoc, ht, IsPullback.lift_fst, inv_mul_cancel_right]
  exact ⟨((t ≫ Q.i) * g).left, congrArg (fun q => q.left) a₁, congrArg (fun q => q.left) a₂⟩

end General

open GlobalTheory.FormalPoint

theorem main : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B, ∃ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ b
  let I := IsLocalRing.maximalIdeal V
  let φ := algebraMap V W
  let J := I.map φ
  have hJ : J ≠ ⊤ := ne_top_of_isHausdorff J
  have hloc := isLocalRing_quotient_pow hJ
  have hbw : b.left ≫ a.B.hom = Spec.map (CommRingCat.ofHom φ) := Over.w b
  have pb : ∀ e, IsPullback (a.b e) (t.l e).Q.B.hom a.B.hom (thick V I e) := fun e => (a.b_pb e).1.1
  have w : ∀ e, (adicLevelι J (e + 1) ≫ b.left) ≫ a.B.hom = levelMap I φ e ≫ thick V I e := fun e =>
    (Category.assoc _ _ _).trans ((congrArg _ hbw).trans (levelMap_thick I φ e).symm)
  let c : ∀ e, Spec (CommRingCat.of (W ⧸ J ^ (e + 1))) ⟶ (t.l e).Q.B.left := fun e => (pb e).lift _ _ (w e)
  have c₁ : ∀ e, c e ≫ a.b e = adicLevelι J (e + 1) ≫ b.left := fun e => (pb e).lift_fst _ _ _
  have c₂ : ∀ e, c e ≫ (t.l e).Q.B.hom = levelMap I φ e := fun e => (pb e).lift_snd _ _ _
  have mth : ∀ e, Mono (thick V I e) := fun e => have := isClosedImmersion_red (I ^ (e + 1)); inferInstance
  have mono : ∀ e, Mono (a.b e) := fun e =>
    (MorphismProperty.monomorphisms _).of_isPullback (pb e).flip (mth e)
  have cc : ∀ e, c e ≫ t.β e = adicLevelMap J (Nat.le_succ (e + 1)) ≫ c (e + 1) := fun e => by
    have := mono (e + 1)
    rw [← cancel_mono (a.b (e + 1)), Category.assoc, Category.assoc, a.b_β, c₁, c₁, adicLevelMap_ι_assoc]
  let P := fun e => {x : Spec (CommRingCat.of (W ⧸ J ^ (e + 1))) ⟶ (thickObj V I e G).left //
    x ≫ (t.l e).Q.q.left = c e}
  have base : Nonempty (P 0) := by
    obtain ⟨g, hg⟩ := (t.l 0).Q.exists_lift (Over.homMk (c 0) rfl : Over.mk (c 0 ≫ (t.l 0).Q.B.hom) ⟶ (t.l 0).Q.B)
    exact ⟨⟨g.left, congrArg (fun q => q.left) hg⟩⟩
  have step : ∀ e (x : P e), ∃ x' : P (e + 1),
      adicLevelMap J (Nat.le_succ (e + 1)) ≫ x'.1 = x.1 ≫ thickMap V I e G := fun e x => by
    obtain ⟨g, h₁, h₂⟩ := exists_lift_extending (t.l (e + 1)).Q (Ideal.Quotient.factorPow J (Nat.le_succ (e + 1)))
      (Ideal.Quotient.factor_surjective _) (c (e + 1)) (x.1 ≫ thickMap V I e G)
      (by rw [Category.assoc, ← t.β_q, ← Category.assoc, x.2, cc])
    exact ⟨⟨g, h₁⟩, h₂⟩
  choose nx hnx using step
  let x : ∀ e, P e := fun e => Nat.rec base.some nx e
  have hx : ∀ e, adicLevelMap J (Nat.le_succ (e + 1)) ≫ (x (e + 1)).1 = (x e).1 ≫ thickMap V I e G :=
    fun e => hnx e (x e)
  have tm : ∀ e, thickMap V I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left := fun e =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have fam : IsAdicFamily J fun e => (x e).1 ≫ (fstG I e G).left := fun e => by
    rw [← Category.assoc, hx, Category.assoc, tm]
  have fw : ∀ e, (fstG I e G).left ≫ G.hom = (thickObj V I e G).hom ≫ thick V I e := fun e => pullback.condition
  obtain ⟨g, ⟨g₁, g₂⟩, -⟩ := existsUnique_over_of_isAdicFamily (Spec.map (CommRingCat.ofHom φ)) G.hom fam fun e => by
    rw [Category.assoc, fw, ← Over.w (t.l e).Q.q, Category.assoc, ← Category.assoc, (x e).2, ← Category.assoc, c₂]
    exact levelMap_thick I φ e
  refine ⟨Over.homMk g g₁, fun e Z r xe h => ?_⟩
  replace h : xe ≫ (fstG I e G).left = r ≫ g := h
  obtain ⟨l, rfl⟩ := exists_factor_level I φ r (xe ≫ (thickObj V I e G).hom) (by
    rw [Category.assoc, ← fw, ← Category.assoc, h, Category.assoc, g₁])
  have : Mono (fstG I e G).left := have := mth e; (inferInstance : Mono (pullback.fst G.hom (thick V I e)))
  have hxe : xe = l ≫ (x e).1 := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc, Category.assoc, g₂]
  rw [hxe, Category.assoc, Category.assoc, ← c₁, ← Category.assoc (x e).1, (x e).2]

end GlobalTheory.AbelianPartLift
