import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionSectionsUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionMapUniformisationGenericStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorSecLocal

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem pow_comp_of_isMonHom {S : Scheme.{0}} {G G' Z : Over S} [MonObj G] [MonObj G'] (φ : G ⟶ G')
    [IsMonHom φ] (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem toric_torsion_section_overLocal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (k : ℕ)
    (s : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t.G)),
    (∀ (A : Type) [CommRing A] (a : R →+* A) τ h, s A a τ h ^ k = 1) →
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (a' : R →+* A') (f : A →+* A') τ h τ' h',
      a' = f.comp a → (∀ χ, (τ' χ : A') = f (τ χ : A)) → (s A' a' τ' h').left = spMap f ≫ (s A a τ h).left) →
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (a' : R →+* A')
      (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ) →
    ∀ (X' : Type) [AddCommGroup X'] (ρ : P.D.toPre.X →+ X')
      (V : Type) [CommRing V] [IsLocalRing V] (ψ : R →+* V) (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
      (j : splitTorus (Sp V) X' ⟶ tV.G) [IsMonHom j]
      (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
      (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ))),
      m₀'.φ = m₀.φ ≫ mV.φ →
      GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    ∀ (U : Type) [CommRing U] [IsLocalRing U] (u : V →+* U), IsLocalHom u → IsUnit (k : U) →
    ∀ (τU : Multiplicative X' →* Uˣ) (τ : Multiplicative P.D.toPre.X →* Uˣ) (h : τ ^ k = 1),
      τU ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τU (Multiplicative.ofAdd (ρ χ))) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) X'),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τU (Multiplicative.ofAdd χ))) →
      (s U (u.comp ψ) τ h).left = (z ≫ j).left ≫ mV.φ := by
  intro E _ _ _ H R _ _ _ t P k s hs1 hs2 hs3 X' _ ρ V _ _ ψ tV mV j _ t₀ m₀ h₀ m₀' hφ hpull
    U _ _ u hu hk τU τ h hτU hττ z hz
  have hg : spMap (u.comp ψ) = (Over.mk (spMap u)).hom ≫ spMap ψ := spMap_comp_ringHom ψ u
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv mV.cart (Over.mk (spMap u)) (spMap (u.comp ψ)) hg

  have hzk : z ^ k = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp V) X' (Over.mk (spMap u))).injective
    rw [map_pow, map_one]
    refine MonoidHom.ext fun m => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    have e1 := hz (Multiplicative.toAdd m)
    simp only [GlobalTheory.UU.chV, ofAdd_toAdd] at e1
    rw [e1]
    have e2 : τU m ^ k = 1 := by rw [← MonoidHom.pow_apply, hτU, MonoidHom.one_apply]
    simp only [unitOn, ← map_pow, e2, map_one]
  have hx : s U (u.comp ψ) τ h = e (z ≫ j) := by
    refine GlobalTheory.T.smoothCommGroupScheme_eq_of_pow_eq_of_closedPoint (Sp R) t.G t.semi.smooth U (spMap (u.comp ψ)) k hk _ _ ?_
      (ResidueField U) (residue U) inferInstance ?_
    · rw [hs1, ← map_pow, ← pow_comp_of_isMonHom, hzk, MonObj.one_comp, map_one]
    · let cU := residue U
      let τ₀ : Multiplicative P.D.toPre.X →* (ResidueField U)ˣ :=
        (Units.map (cU : U →* ResidueField U)).comp τ
      have h' : τ₀ ^ k = 1 := by
        refine MonoidHom.ext fun m => ?_
        rw [MonoidHom.pow_apply, MonoidHom.one_apply]
        show Units.map _ (τ m) ^ k = 1
        rw [← map_pow, ← MonoidHom.pow_apply, h, MonoidHom.one_apply, map_one]
      have n1 := hs2 U (ResidueField U) (u.comp ψ) (cU.comp (u.comp ψ)) cU τ h τ₀ h' rfl (fun χ => rfl)
      let w₁ : Multiplicative X' →* Γ(Sp (ResidueField U), ⊤)ˣ :=
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField U))).inv.hom.toMonoidHom).comp
          ((Units.map (cU : U →* ResidueField U)).comp τU)
      let z₁ : Over.mk (spMap (ResidueField.map u)) ⟶ splitTorus (Sp (ResidueField V)) X' :=
        (GlobalTheory.splitTorusPointsEquiv _ X' _).symm w₁
      have hz₁ : ∀ χ, GlobalTheory.UU.chV z₁ χ = w₁ (Multiplicative.ofAdd χ) := fun χ => by
        simp only [GlobalTheory.UU.chV, z₁, MulEquiv.apply_symm_apply]
      let z₀ := z₁ ≫ GlobalTheory.SplitTorus.torusMap _ ρ
      have hz₀ : ∀ χ, GlobalTheory.UU.chV z₀ χ = unitOn (τ₀ (Multiplicative.ofAdd χ)) := fun χ => by
        apply Units.ext
        rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
          GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
          ← GlobalTheory.UU.chV_val, hz₁]
        show _ = (unitOn ((Units.map (cU : U →* ResidueField U)) (τ (Multiplicative.ofAdd χ)))).val
        rw [hττ]; rfl
      have hres : cU.comp u = (ResidueField.map u).comp (residue V) := by
        ext r; simp [cU, ResidueField.map_residue]
      have hcomp : cU.comp (u.comp ψ) = (ResidueField.map u).comp ((residue V).comp ψ) := by
        rw [← RingHom.comp_assoc, hres, RingHom.comp_assoc]
      have n2 := hs3 (ResidueField V) (ResidueField U) ((residue V).comp ψ) h₀ (cU.comp (u.comp ψ))
        (ResidueField.map u) t₀ m₀' τ₀ h' z₀ hcomp hz₀
      have hzz : z₁.left ≫ GlobalTheory.SplitTorus.bcMap (spMap (residue V)) X' = spMap cU ≫ z.left := by
        refine GlobalTheory.UU.splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
        · rw [Category.assoc, GlobalTheory.SplitTorus.bcMap_hom, ← Category.assoc, Over.w z₁, Category.assoc,
            Over.w z]
          show spMap (ResidueField.map u) ≫ spMap (residue V) = spMap cU ≫ spMap u
          rw [← spMap_comp_ringHom, ← spMap_comp_ringHom, hres]
        · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, GlobalTheory.UU.bcMap_charUnit,
            Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ← GlobalTheory.UU.chV_val,
            ← GlobalTheory.UU.chV_val, hz₁, hz]
          show (Scheme.ΓSpecIso _).inv.hom (cU (τU _).val) =
            (Spec.map (CommRingCat.ofHom cU)).appTop.hom ((Scheme.ΓSpecIso _).inv.hom (τU _).val)
          rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
      rw [he, ← n1, n2, hφ]
      have hz₀t : z₀ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' = z₁ ≫ GlobalTheory.TorusPart.pullTorus m₀.cart j := by
        rw [hpull, Category.assoc]
      rw [hz₀t, Over.comp_left, Category.assoc, ← Category.assoc (GlobalTheory.TorusPart.pullTorus m₀.cart j).left,
        GlobalTheory.TorusPart.pullTorus_left]
      have k3 := congrArg (· ≫ j.left ≫ mV.φ) hzz
      simp only [Category.assoc, Over.comp_left] at k3 ⊢
      exact k3
  rw [hx, he]

end GlobalTheory.TorSecLocal
