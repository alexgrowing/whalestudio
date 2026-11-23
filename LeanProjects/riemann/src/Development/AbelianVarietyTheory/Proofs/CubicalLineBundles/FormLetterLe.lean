import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.GramStdBasisPosDefAndHq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TopLieVectorNormSqEqGramDetStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianLengthImageEigenBasisVectorLeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamEqOfWeilIsAllPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.VecLineNormSqEqForm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem form_letter_le (hU : ThetaUnifAV) (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E]
    [StarRing (𝓞 E)] {K : Type} [Field K] [NumberField K] {S : Set (E →+* ℂ)}
    (A B : Out.PolAV (Sp (𝓞 K))) (oa : A.OAct (𝓞 E)) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left)
    (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)) (hx : IsFibreOf A x (gmap K) φ)
    (hT : IsLieType A oa x φ τ lab) (F' : GenFib B) (h' : HermFam K (Fin F'.P₀.g → K)) (H' : F'.IsHerm h')
    (f : A.A ⟶ B.A) (hf : IsMonHom f) (a : 𝓞 E)
    (hW : ∀ (Tb : Over (Sp (𝓞 K))) (k : ℕ) (x y : Tb ⟶ A.A) (c : Γ(Tb.left, ⊤)ˣ), 0 < k →
      pnsmulPt k x = toUnit Tb ≫ η[A.A] → pnsmulPt k y = toUnit Tb ≫ η[A.A] →
      (Out.WeilIs B.A B.L k (x ≫ f) (y ≫ f) c ↔ Out.WeilIs A.A A.L k (x ≫ oa.act a) y c))
    (La : ℝ) (hb : ∀ τ : E →+* ℂ, ‖τ (a : E)‖ ≤ La ^ 2) (i : Fin x.P.g) (ℓ : MLine K) (hℓ : IsVecLine A x φ i ℓ)
    (U : Fin F'.P₀.g → K) (w' : epsR K ⟶ F'.P₀.A) (hw : IsLieComb U F'.v w')
    (e : w'.left ≫ F'.φ = (x.v i).left ≫ φ ≫ f.left) (s : K →+* ℂ) :
    (h'.form s U U).re ≤ (La * ℓ.n s) ^ 2 := by
  have hp : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ :=
    (isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) A x φ).1 hx
  obtain ⟨h, H⟩ := (GlobalTheory.CM.LieMetric.exists_unique_isHerm hU hL K A (GenFib.mk x.P φ hp x.v x.basis)).1
  have hg : IsMonHom (oa.act a) := oa.hom a
  obtain ⟨w, hw1, hw2⟩ := hT a i
  have h1 := GlobalTheory.T.hermitianLength_image_eigenBasisVector_le hU hL K A B (GenFib.mk x.P φ hp x.v x.basis) F' h h' f (oa.act a) H H' hf hg
    (lamEq_of_weilIs_all_points hL K A B f (oa.act a) hf hg hW) i _ w U w' hw1 hw2 hw e s
  have h2 := GlobalTheory.CM.LieMetric.vecLine_norm_sq_eq_form hU hL K A x φ hp h H i ℓ hℓ s
  refine h1.trans ?_
  rw [mul_pow]
  refine le_trans (le_of_eq (congrArg _ h2.symm)) ?_
  exact mul_le_mul_of_nonneg_right (hb (s.comp (lab (τ i)))) (sq_nonneg _)

theorem lamLen : ThetaUnifAV → Out.Laws → LamLenSt := by
  intro hU hL E _ _ _ _ H l c _ nΨ n' f o La hG L hLg σ
  obtain ⟨-, -, -, hB, hΨ, hA', -, -, -, tΨ, t', -, -, hI, hP, hb, vΨ, v', -, hgood, -, harch, -⟩ := hG
  have hp : IsPolFibre (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB.P o.φB :=
    (isFibreOf_iff_isPolFibre (𝓞 o.K₁) o.K₁ (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB o.φB).1 hB
  obtain ⟨h, Hh⟩ := (GlobalTheory.CM.LieMetric.exists_unique_isHerm hU hL o.K₁ o.B
    (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis)).1
  obtain ⟨g1, g2⟩ := gram_stdBasis_posDef_and_hq o.K₁ o.xB.P.g h σ
  refine ⟨_, g1, ?_, fun k => ?_⟩
  · have := GlobalTheory.T.topLieVector_norm_sq_eq_gramDet hU hL o.K₁ o.B o.xB o.φB hp h Hh o.Tl o.LamL σ (harch σ)
    exact ((congrArg Real.sqrt this).symm.trans (Real.sqrt_sq (hgood.2 σ).le)).symm
  · rw [g2]
    obtain ⟨w, hw1, hw2⟩ := hLg.2.2.1 k
    have h4 := hLg.2.2.2 k
    unfold LamLetters.IsLetter at hw1
    cases hs : L.src k with
    | inl q =>
      rw [hs] at hw1 h4
      simp only at hw1 h4
      rw [h4]
      exact form_letter_le hU hL o.AΨ o.B o.oaΨ o.xΨ o.φΨg (S := psiSet H) o.τΨ _ hΨ tΨ
        (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis) h Hh (o.φΨ q.1) (hI.1 _) (o.hΨ q.1) (hP.2.2.1 q.1) La
        (hb.1 q.1) q.2 _ (vΨ q.2) _ w hw2 hw1 σ
    | inr q =>
      rw [hs] at hw1 h4
      simp only at hw1 h4
      rw [h4]
      exact form_letter_le hU hL o.A' o.B o.oa' o.x' o.φ'g (S := (psiSet H)ᶜ) o.τ' _ hA' t'
        (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis) h Hh (o.φ' q.1) (hI.2.1 _) (o.h' q.1) (hP.2.2.2 q.1) La
        (hb.2 q.1) q.2 _ (v' q.2) _ w hw2 hw1 σ

end GlobalTheory.LamF
