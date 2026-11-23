import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasisStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianMetricDifferentialEqOfPairingRelationStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.LenOne

theorem re_form_smul_le {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] (h : HermFam K V)
    (s : K →+* ℂ) (t : K) {x : V} (hx : x ≠ 0) : (h.form s x (t • x)).re ≤ ‖s t‖ * (h.form s x x).re := by
  have hp := (h.posDef s 1 ![x] (by simpa [linearIndependent_unique_iff] using hx)).diag_pos (i := 0)
  have hp' : 0 < h.form s x x := by simpa using hp
  obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hp'
  rw [h.smul_right, Complex.mul_re, ← h2, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_right (Complex.re_le_norm _) h1.le

theorem diff_single_eq {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} (F : GenFib P)
    (F' : GenFib P') {f : P.A ⟶ P'.A} {f₀ : F.P₀.A ⟶ F'.P₀.A} (e : f₀.left ≫ F'.φ = F.φ ≫ f.left)
    {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    (hM : ∀ c w, IsLieComb c F.v w → IsLieComb (M c) F'.v (w ≫ f₀)) (i : Fin F.P₀.g) {U : Fin F'.P₀.g → K}
    {w : epsR K ⟶ F'.P₀.A} (hU : IsLieComb U F'.v w) (hw : w.left ≫ F'.φ = (F.v i).left ≫ F.φ ≫ f.left) :
    M (Pi.single i 1) = U := by
  have := F.P₀.isAb.comm
  have := F'.P₀.isAb.comm
  obtain rfl : w = F.v i ≫ f₀ := Over.OverMorphism.ext (F'.fib.2.1.1.hom_ext
    (by rw [hw, Over.comp_left, Category.assoc, e]) ((Over.w _).trans (Over.w _).symm))
  exact (F'.basis.2 _ ((LieComb.lieComb_algebra K _ _ F'.v F'.basis.1).2.1 U _ hU)).unique
    (hM _ _ ((LieComb.lieComb_algebra K _ _ F.v F.basis.1).2.2.2.1 i)) hU

theorem form_image_le : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P P' : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A), F.IsHerm h → F'.IsHerm h' → IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → ∀ (i : Fin F.P₀.g) (t : K) (w : epsR K ⟶ F.P₀.A) (U : Fin F'.P₀.g → K) (w' : epsR K ⟶ F'.P₀.A), IsLieComb (Pi.single i t) F.v w → (F.v i).left ≫ F.φ ≫ g.left = w.left ≫ F.φ → IsLieComb U F'.v w' → w'.left ≫ F'.φ = (F.v i).left ≫ F.φ ≫ f.left → ∀ s : K →+* ℂ, (h'.form s U U).re ≤ ‖s t‖ * (h.form s (Pi.single i 1) (Pi.single i 1)).re := by
  intro hT hL K _ _ P P' F F' h h' f g hh hh' hf hg hlam i t w U w' hw ew hU ew' s
  obtain ⟨⟨M, hM, -⟩, f₀, -, ef, hf₀⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f hf
  obtain ⟨⟨N, hN, -⟩, g₀, -, eg, hg₀⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F g hg
  have h1 := diff_single_eq F F' ef (hf₀ M hM) i hU ew'
  have h2 := diff_single_eq F F eg (hg₀ N hN) i hw ew.symm
  have h3 := GlobalTheory.T.hermitianMetric_differential_eq_of_pairing_relation hT hL K P F P' F' h h' f g M N hh hh' hf hg hlam hM hN s (Pi.single i 1) (Pi.single i 1)
  have h4 : (Pi.single i t : Fin F.P₀.g → K) = t • (Pi.single i 1 : Fin F.P₀.g → K) := by
    rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [h1, h2, h4] at h3
  rw [h3]
  exact re_form_smul_le h s t (by simp)

end GlobalTheory.LamF.LenOne
