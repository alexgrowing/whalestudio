import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairingStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplexStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCubeLBPairingIsoBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingEqOfIsomorphicCubePairingsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.NormHom

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A C : Over S} {A' C' : Over S'}
  [GrpObj A] [GrpObj C] [GrpObj A'] [GrpObj C'] {φ : A'.left ⟶ A.left} {ψ : C'.left ⟶ C.left}

theorem push_inj (h : IsGrpPullback A' A f φ) {T : Over S'} {x y : T ⟶ A'}
    (e : pushHom h T x = pushHom h T y) : x = y :=
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem push_comp (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) {p : A ⟶ C} {p' : A' ⟶ C'}
    (e : p'.left ≫ ψ = φ ≫ p.left) {T : Over S'} (x : T ⟶ A') :
    pushHom h' T (x ≫ p') = pushHom h T x ≫ p :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, e, Category.assoc])

theorem exists_monHom_lift (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) (p : A ⟶ C) [IsMonHom p] :
    ∃ p' : A' ⟶ C', IsMonHom p' ∧ p'.left ≫ ψ = φ ≫ p.left := by
  obtain ⟨p', e⟩ : ∃ p' : A' ⟶ C', p'.left ≫ ψ = φ ≫ p.left :=
    ⟨Over.homMk (h'.1.lift (φ ≫ p.left) A'.hom (by rw [Category.assoc, Over.w, h.1.w])) (h'.1.lift_snd _ _ _),
      h'.1.lift_fst _ _ _⟩
  refine ⟨p', ?_, e⟩
  have h1 : (1 : 𝟙_ (Over S') ⟶ A') ≫ p' = 1 := by
    apply push_inj h'
    rw [push_comp h h' e, map_one, map_one, MonObj.one_comp]
  have h2 : (fst A' A' * snd A' A') ≫ p' = (fst A' A' ≫ p') * (snd A' A' ≫ p') := by
    apply push_inj h'
    rw [push_comp h h' e, map_mul, map_mul, MonObj.mul_comp, push_comp h h' e, push_comp h h' e]
  constructor
  · simpa [Hom.one_def] using h1
  · rw [Hom.mul_def, Hom.mul_def] at h2
    have e1 : lift (fst A' A' ≫ p') (snd A' A' ≫ p') = p' ⊗ₘ p' := by ext <;> simp
    simpa [e1] using h2
end

theorem isVecOver_comp {R R' : Type} [CommRing R] [CommRing R'] {s : R →+* R'} {A C : Over (Sp R)}
    {A' C' : Over (Sp R')} {φ : A'.left ⟶ A.left} {ψ : C'.left ⟶ C.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'}
    (hv : IsVecOver s φ v v') {p : A ⟶ C} {p' : A' ⟶ C'} (e : p'.left ≫ ψ = φ ≫ p.left) :
    IsVecOver s ψ (v ≫ p) (v' ≫ p') := by
  unfold IsVecOver at hv ⊢
  rw [Over.comp_left, Over.comp_left, Category.assoc, e, ← Category.assoc, hv, Category.assoc]

theorem lieNormSq_comp : ThetaUnifAV → Out.Laws → ∀ (R : Type) [CommRing R] (P P' : Out.PolAV (Sp R)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (v : epsR R ⟶ P.A) (a : R) (s : R →+* ℂ) (r r' : ℝ), IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → IsTangent v → IsLieComb ![a] ![v] (v ≫ g) → IsLieNormSq P v s r → IsLieNormSq P' (v ≫ f) s r' → r' = (s a).re * r := by
  rintro hU hL R _ P P' f g v a s r r' hf hg hlam hv hc ⟨Q, φ, v₁, u, Hm, χ, w, hφ, hv₁, hA, hw, rfl⟩
    ⟨Q', φ', v₁', u', Hm', χ', w', hφ', hv₁', hA', hw', rfl⟩
  obtain ⟨f₁, hf₁, ef⟩ := exists_monHom_lift hφ.2.1 hφ'.2.1 f
  obtain ⟨g₁, hg₁, eg⟩ := exists_monHom_lift hφ.2.1 hφ.2.1 g
  obtain ⟨-, -, -, -, t₁, t₂, -⟩ := GlobalTheory.T.appellHumbert_unif_tangent_weilPairing hU Q Q.g u Hm χ hA
  obtain ⟨-, -, -, -, t₁', t₂', -⟩ := GlobalTheory.T.appellHumbert_unif_tangent_weilPairing hU Q' Q'.g u' Hm' χ' hA'
  obtain ⟨F, hF, -, hFd, -⟩ :=
    GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' t₁' t₂' f₁ hf₁
  obtain ⟨G, hG, -, hGd, -⟩ :=
    GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb Q.L Q.L Q.g Q.g u u t₁ t₂ g₁ hg₁
  have ht : IsTangent v₁ := hv₁.isTangent hφ.2.1 hv
  have hlam₁ : LamEq Q'.L f₁ f₁ Q.L g₁ (𝟙 Q.A) :=
    GlobalTheory.T.isCubeLBPairingIso_baseChange _ _ (spMap s) P.A P.A P'.A P.A Q.A Q.A Q'.A Q.A φ φ φ' φ hφ.2.1.1.w hφ.2.1.1.w hφ'.2.1 hφ.2.1
      P'.L P.L Q'.L Q.L P'.isLB P.isLB Q'.isLB Q.isLB hφ'.2.2 hφ.2.2 f f g (𝟙 _) f₁ f₁ g₁ (𝟙 _) ef ef eg
      (by simp) hlam
  have hweil := GlobalTheory.T.weil_pairing_eq_of_isomorphic_cube_pairings hL ℂ Q Q Q' Q f₁ f₁ g₁ (𝟙 _) hf₁ hf₁ hg₁ inferInstance hlam₁
  have hherm := (GlobalTheory.T.weilEq_iff_hermForm_eq_complex hU hL Q Q Q' Q u u u' u Hm' Hm χ' χ hA' hA f₁ f₁ g₁ (𝟙 _) F F G LinearMap.id
    hF hF hG (fun z => by simp)).1 hweil w w
  have e₁ : v₁' = v₁ ≫ f₁ :=
    (existsUnique_isVecOver hφ'.2.1.1 (v ≫ f)).unique hv₁' (isVecOver_comp hv₁ ef)
  subst e₁
  have e₂ : w' = F w := (t₁' _ (hFd w v₁ ht hw).1).unique hw' (hFd w v₁ ht hw).2
  have hc₁ := (GlobalTheory.lieComb_baseChange R ℂ s P.A Q.A φ hφ.2.1 1 ![v] (v ≫ g) ![a] ![v₁] (v₁ ≫ g₁)
    (fun j => by fin_cases j; exact hv₁) hc).1 (isVecOver_comp hv₁ eg)
  have hd := GlobalTheory.UnifDifferential.isDiff_of_isLieComb Q.A Q.L Q.g 1 u ![w] ![v₁] _ _
    (fun j => by fin_cases j; exact ht) (fun j => by fin_cases j; exact hw) hc₁
  have e₃ : G w = s a • w := by
    have := (t₁ _ (hGd w v₁ ht hw).1).unique (hGd w v₁ ht hw).2 hd
    simpa using this
  have him : (hermForm Hm w w).im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    have hH : ∀ i j, (starRingEnd ℂ) (Hm i j) = Hm j i := fun i j => hA.1.apply j i
    simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply,
      RCLike.star_def, Complex.conj_conj, hH]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e₂, hherm, e₃, LinearMap.id_apply]
  have e₄ : hermForm Hm (s a • w) w = s a * hermForm Hm w w := by
    rw [hermForm, hermForm, smul_dotProduct, smul_eq_mul]
  rw [e₄, Complex.mul_re, him]
  ring

end GlobalTheory.NormHom
end
