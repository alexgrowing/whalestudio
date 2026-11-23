import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAVStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRingStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.PairingScheme

theorem exists_unitOn {K : Type} [CommRing K] (c : Γ(Sp K, ⊤)ˣ) : ∃ z : Kˣ, unitOn z = c := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c, ?_⟩
  ext
  simp [unitOn]

theorem comp_pow_eq_one {S : Scheme.{0}} {T X A : Over S} [GrpObj X] [GrpObj A] (f : X ⟶ A) [IsMonHom f]
    {x : T ⟶ X} {k : ℕ} (hx : x ^ k = 1) : (x ≫ f) ^ k = 1 := by
  rw [← MonObj.pow_comp, hx, MonObj.one_comp]

theorem pull_pow_eq_one {S : Scheme.{0}} {T T' X : Over S} [GrpObj X] (t : T' ⟶ T)
    {x : T ⟶ X} {k : ℕ} (hx : x ^ k = 1) : (t ≫ x) ^ k = 1 := by
  rw [← MonObj.comp_pow, hx, MonObj.comp_one]

theorem weilIs_iff_of_lamEq : Out.Laws → ∀ (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] (X Y A B : Out.PolAV (Sp R)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → LamEq A.L f₁ f₂ B.L g₁ g₂ → ∀ (T : Over (Sp R)) (k : ℕ) (x : T ⟶ X.A) (y : T ⟶ Y.A) (c : Γ(T.left, ⊤)ˣ), 0 < k → x ^ k = 1 → y ^ k = 1 → (Out.WeilIs A.A A.L k (x ≫ f₁) (y ≫ f₂) c ↔ Out.WeilIs B.A B.L k (x ≫ g₁) (y ≫ g₂) c) := by
  intro hL R _ _ _ X Y A B f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ hlam T k x y c hk hx hy
  have hN : IsLocallyNoetherian (Sp R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
  obtain ⟨T₀, x₀, y₀, hx₀, hy₀, huniv, hsep⟩ := GlobalTheory.T.exists_universal_torsion_pair_polAV hL R X Y k hk
  obtain ⟨a, ha, -⟩ := (hL.weil (Sp R) A k T₀).1 _ _ (comp_pow_eq_one f₁ hx₀) (comp_pow_eq_one f₂ hy₀)
  obtain ⟨b, hb, -⟩ := (hL.weil (Sp R) B k T₀).1 _ _ (comp_pow_eq_one g₁ hx₀) (comp_pow_eq_one g₂ hy₀)
  have hab : a = b := by
    apply Units.ext
    refine hsep _ _ fun k' _ _ _ β t => ?_
    have hw := (GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring hL R X Y A B f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ k' β).1 hlam
    have ha' := CommPairing.weilIs_pull hL.globalFns A.isAb A.isLB t ha
    have hb' := CommPairing.weilIs_pull hL.globalFns B.isAb B.isLB t hb
    obtain ⟨z, hz⟩ := exists_unitOn (K := k') (Units.map t.left.appTop.hom.toMonoidHom a)
    have hx' := pull_pow_eq_one t hx₀
    have hy' := pull_pow_eq_one t hy₀
    rw [← Category.assoc, ← Category.assoc] at ha' hb'
    have h₁ := (hw k (t ≫ x₀) (t ≫ y₀) z hk hx' hy').1 (by rw [hz]; exact ha')
    rw [hz] at h₁
    have h₂ := ((hL.weil (Sp R) B k _).1 _ _ (comp_pow_eq_one g₁ hx') (comp_pow_eq_one g₂ hy')).unique h₁ hb'
    exact congrArg Units.val h₂
  subst hab
  obtain ⟨t, rfl, rfl⟩ := huniv T x y hx hy
  have ha' := CommPairing.weilIs_pull hL.globalFns A.isAb A.isLB t ha
  have hb' := CommPairing.weilIs_pull hL.globalFns B.isAb B.isLB t hb
  rw [← Category.assoc, ← Category.assoc] at ha' hb'
  constructor
  · intro H
    rw [((hL.weil (Sp R) A k _).1 _ _ (comp_pow_eq_one f₁ hx) (comp_pow_eq_one f₂ hy)).unique H ha']
    exact hb'
  · intro H
    rw [((hL.weil (Sp R) B k _).1 _ _ (comp_pow_eq_one g₁ hx) (comp_pow_eq_one g₂ hy)).unique H hb']
    exact ha'

end GlobalTheory.PairingScheme
