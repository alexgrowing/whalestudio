import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSectionAdditiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapSnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtPull

theorem secVal_congr {B : Type} [CommRing B] {Z : Scheme.{0}} {x x' : Spec (CommRingCat.of B) ⟶ Z} (e : x = x')
    (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ x' ⁻¹ᵁ W) (s : Γ(Z, W)) : secVal x W h s = secVal x' W h' s := by
  subst e
  rfl

theorem epsMul_snd {C : Type} [CommRing C] (c : C) (a : DualNumber C) :
    (GlobalTheory.CompanionTheory.Ar.epsMul c a).snd = c * a.snd := by
  simp [GlobalTheory.CompanionTheory.Ar.epsMul]

theorem one_left_eps {S : Scheme.{0}} (G : Over S) [GrpObj G] {C : Type} [CommRing C] (y : Sp C ⟶ S) :
    (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left = spMap (algebraMap C (DualNumber C)) ≫ (1 : Over.mk y ⟶ G).left := by
  rw [Hom.one_def, Hom.one_def]
  simp

theorem pt_zero {S : Scheme.{0}} {G : Over S} [GrpObj G] {C : Type} [CommRing C] {y : Sp C ⟶ S} {L : Type}
    [AddCommGroup L] [Module C L] (M : LieModel G y L) : M.pt 0 = 1 := by
  have := M.add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem one_snd {S : Scheme.{0}} (G : Over S) [GrpObj G] {C : Type} [CommRing C] (y : Sp C ⟶ S) (W : G.left.Opens)
    (h0 : ⊤ ≤ (1 : Over.mk y ⟶ G).left ⁻¹ᵁ W) (h1 : ⊤ ≤ (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left ⁻¹ᵁ W) (s : Γ(G.left, W)) :
    (secVal (B := DualNumber C) (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left W h1 s).snd = 0 := by
  have e := one_left_eps G y
  have h2 : ⊤ ≤ (spMap (algebraMap C (DualNumber C)) ≫ (1 : Over.mk y ⟶ G).left) ⁻¹ᵁ W := e ▸ h1
  rw [secVal_congr e W h1 h2 s, secring C (DualNumber C) _ G.left _ W h0 h2 s]
  exact TrivSqZeroExt.snd_inl _ _

theorem exists_linear_snd : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (C : Type) [CommRing C] (y : Sp C ⟶ S) (L : Type) [AddCommGroup L] [Module C L] (M : LieModel G y L) (W : G.left.Opens) (h : ∀ l, ⊤ ≤ (M.pt l).left ⁻¹ᵁ W) (s : Γ(G.left, W)), ∃ D : L →ₗ[C] C, ∀ l, D l = (secVal (B := DualNumber C) (M.pt l).left W (h l) s).snd := by
  intro S G _ C _ y L _ _ M W h s
  have p0 := pt_zero M
  have h1 : ⊤ ≤ (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left ⁻¹ᵁ W := p0 ▸ h 0
  have h0 : ⊤ ≤ (1 : Over.mk y ⟶ G).left ⁻¹ᵁ W := by
    intro z _
    have t : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ (M.pt 0).left = (1 : Over.mk y ⟶ G).left := M.tan 0
    show (1 : Over.mk y ⟶ G).left z ∈ W
    rw [← t]
    exact h 0 (show spMap (TrivSqZeroExt.fstHom C C C).toRingHom z ∈ (⊤ : Scheme.Opens _) from trivial)
  refine ⟨{ toFun := fun l => (secVal (B := DualNumber C) (M.pt l).left W (h l) s).snd, map_add' := ?_, map_smul' := ?_ },
    fun l => rfl⟩
  · intro l l'
    have e : (M.pt (l + l')).left = (M.pt l * M.pt l').left := by rw [M.add]
    have hvw : ⊤ ≤ (M.pt l * M.pt l').left ⁻¹ᵁ W := e ▸ h (l + l')
    have key := GlobalTheory.T.tangent_section_additive S G C y (M.pt l) (M.pt l') (M.tan l) (M.tan l') W (h l) (h l') hvw h1 s
    have key' := congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom.hom t) key
    simp only [map_add] at key'
    have key'' : secVal (B := DualNumber C) (M.pt l * M.pt l').left W hvw s +
        secVal (B := DualNumber C) (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left W h1 s =
        secVal (B := DualNumber C) (M.pt l).left W (h l) s + secVal (B := DualNumber C) (M.pt l').left W (h l') s := key'
    have key3 := congrArg TrivSqZeroExt.snd key''
    rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_add, one_snd G y W h0 h1 s, add_zero] at key3
    show (secVal (B := DualNumber C) (M.pt (l + l')).left W (h (l + l')) s).snd = _
    rw [secVal_congr e W (h (l + l')) hvw s]
    exact key3
  · intro c l
    have e := M.smul c l
    have h2 : ⊤ ≤ (spMap (GlobalTheory.CompanionTheory.Ar.epsMul c) ≫ (M.pt l).left) ⁻¹ᵁ W := e ▸ h (c • l)
    show (secVal (B := DualNumber C) (M.pt (c • l)).left W (h (c • l)) s).snd = c • _
    rw [secVal_congr e W (h (c • l)) h2 s, secring _ _ _ G.left _ W (h l) h2 s, epsMul_snd]
    rfl

end GlobalTheory.CompanionTheory.Ar.HtPull
