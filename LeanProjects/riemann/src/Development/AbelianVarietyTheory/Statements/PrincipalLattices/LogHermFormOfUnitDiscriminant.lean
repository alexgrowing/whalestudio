import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped UpperHalfPlane

namespace GlobalTheory

section Defs

variable {R R' : Type} [CommRing R] [CommRing R']

def IsPolFibre (f : R →+* R') (P : Out.PolAV (Sp R)) (P' : Out.PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left) : Prop :=
  P'.g = P.g ∧ IsGrpPullback P'.A P.A (spMap f) φ ∧ LBIso (P.L.pull φ) P'.L

def IsVecOver (f : R →+* R') {A : Over (Sp R)} {A' : Over (Sp R')} (φ : A'.left ⟶ A.left) (v : epsR R ⟶ A)
    (v' : epsR R' ⟶ A') : Prop :=
  v'.left ≫ φ = spMap (Chart.dualMapR f) ≫ v.left

def IsLieNormSq (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (s : R →+* ℂ) (r : ℝ) : Prop :=
  ∃ (P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u : HolUnif P'.A P'.L P'.g)
    (Hm : Matrix (Fin P'.g) (Fin P'.g) ℂ) (χ : u.Λ → ℂ) (w : Fin P'.g → ℂ),
    IsPolFibre s P P' φ ∧ IsVecOver s φ v v' ∧ u.IsAH Hm χ ∧ u.IsDiff w v' ∧ r = Real.pi * (hermForm Hm w w).re

end Defs

def CMCurve : Prop :=
  ∀ d : ℕ, 7 ≤ d → Squarefree d → d % 4 = 3 →
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → (∃ r : K, r ^ 2 = -(d : K)) →
  ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (w : M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A),
    (w : ℂ) = (1 + Complex.I * √d) / 2 ∧ P.g = 1 ∧ IsLieBasis ![v] ∧
    (∃ (P₀ : Out.PolAV (Sp M)) (φ : P₀.A.left ⟶ P.A.left) (v₀ : epsR M ⟶ P₀.A) (W : P₀.A ⟶ P₀.A),
      IsPolFibre (algebraMap (𝓞 M) M) P P₀ φ ∧ IsVecOver (algebraMap (𝓞 M) M) φ v v₀ ∧ IsLieBasis ![v₀] ∧
      IsMonHom W ∧ (W ≫ W) * (𝟙 P₀.A) ^ ((1 + d) / 4) = W ∧ IsLieComb ![w] ![v₀] (v₀ ≫ W)) ∧
    (∀ (P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left),
      IsPolFibre ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) P P' φ → ∀ u : HolUnif P'.A P'.L P'.g,
      ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ u.Λ ↔ ∃ m n : ℤ, z = fun _ => c * (m + n * (w : ℂ))) ∧
    (∀ s : M →+* ℂ, ∃ r : ℝ, 0 < r ∧ ∀ r', IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) r' ↔ r' = r) ∧
    ∀ n : (M →+* ℂ) → ℝ, (∀ s, IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) (n s)) →
    ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) →
      (∑ s, Real.log (n s)) / Module.finrank ℚ M =
        (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K

section Inhabitants

variable {R R' : Type} [CommRing R] [CommRing R']

theorem spMap_comp_spMap {R'' : Type} [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

theorem IsVecOver.isTangent {f : R →+* R'} {A : Over (Sp R)} {A' : Over (Sp R')} [GrpObj A] [GrpObj A']
    {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A (spMap f) φ) {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'}
    (h : IsVecOver f φ v v') (hv : IsTangent v) : IsTangent v' := by
  refine hφ.1.hom_ext ?_ ?_
  · have e := PolBaseChange.eSec_comm hφ
    unfold eSec at e
    rw [Category.assoc, h, e, ← hv, ← Category.assoc, ← Category.assoc]
    congr 1
    refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
    congr 1
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [Category.assoc, Over.w v', Over.w η[A']]
    refine (spMap_comp_spMap _ _).trans ?_
    refine Eq.trans ?_ (Spec.map_id (CommRingCat.of R'))
    congr 1

theorem existsUnique_isVecOver {f : R →+* R'} {A : Over (Sp R)} {A' : Over (Sp R')} {φ : A'.left ⟶ A.left}
    (hφ : IsPullback φ A'.hom A.hom (spMap f)) (v : epsR R ⟶ A) : ∃! v' : epsR R' ⟶ A', IsVecOver f φ v v' := by
  have w : (spMap (Chart.dualMapR f) ≫ v.left) ≫ A.hom = (epsR R').hom ≫ spMap f := by
    rw [Category.assoc, Over.w v]
    refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
    congr 1
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨Over.homMk (hφ.lift _ _ w) (hφ.lift_snd _ _ w), hφ.lift_fst _ _ w, fun v' h => ?_⟩
  exact Over.OverMorphism.ext (hφ.hom_ext (h.trans (hφ.lift_fst _ _ w).symm)
    ((Over.w v').trans (hφ.lift_snd _ _ w).symm))

theorem exists_isPolFibre (hB : Out.PolBaseChangeSt) (f : R →+* R') (P : Out.PolAV (Sp R)) :
    ∃ P' φ, IsPolFibre f P P' φ := by
  obtain ⟨P', φ, hφ, hg, hm, t⟩ := hB _ _ (spMap f) P
  refine ⟨P', φ, hg, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, t⟩
  have ex : x₀ = Out.toBase hφ.w x := Over.OverMorphism.ext hx
  have ey : y₀ = Out.toBase hφ.w y := Over.OverMorphism.ext hy
  rw [ex, ey, ← hm]
  rfl

theorem exists_isLieNormSq (hU : ThetaUnifAV) (hB : Out.PolBaseChangeSt) (P : Out.PolAV (Sp R))
    {v : epsR R ⟶ P.A} (hv : IsTangent v) (s : R →+* ℂ) : ∃ r, IsLieNormSq P v s r := by
  obtain ⟨P', φ, h⟩ := exists_isPolFibre hB s P
  obtain ⟨v', hv', -⟩ := existsUnique_isVecOver h.2.1.1 v
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u, Hm, χ, -, hA, -, hd, -⟩ := hU P' rig hrig
  obtain ⟨w, hw, -⟩ := hd v' (hv'.isTangent h.2.1 hv)
  exact ⟨_, P', φ, v', u, Hm, χ, w, h, hv', hA, hw, rfl⟩

theorem exists_quadraticField_sq_eq_neg {d : ℕ} (hd : 0 < d) : ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K),
    Module.finrank ℚ K = 2 ∧ ∃ r : K, r ^ 2 = -(d : K) := by
  let r : ℂ := √d * Complex.I
  have hr : r ^ 2 = -d := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  have hm : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ) : Polynomial ℚ).Monic := by monicity!
  have he : Polynomial.aeval r (Polynomial.X ^ 2 + Polynomial.C (d : ℚ) : Polynomial ℚ) = 0 := by
    simp [hr]
  have hi : IsIntegral ℚ r := ⟨_, hm, he⟩
  have hfin := IntermediateField.adjoin.finiteDimensional hi
  have hK : NumberField (IntermediateField.adjoin ℚ {r}) := ⟨⟩
  refine ⟨_, hK, ?_, IntermediateField.AdjoinSimple.gen ℚ r, Subtype.ext (by simp [hr])⟩
  rw [IntermediateField.adjoin.finrank hi]
  refine le_antisymm ((Polynomial.natDegree_le_natDegree (minpoly.min ℚ r hm he)).trans
    (by compute_degree)) ((minpoly.two_le_natDegree_iff hi).2 ?_)
  rintro ⟨q, hq⟩
  have := congrArg Complex.im hq
  simp [r, eq_comm (a := (0 : ℝ)), hd.ne'] at this

theorem cmCurve_hypotheses :
    (7 ≤ 7 ∧ Squarefree 7 ∧ 7 % 4 = 3) ∧ (7 ≤ 23 ∧ Squarefree 23 ∧ 23 % 4 = 3) ∧
    ∀ d : ℕ, 7 ≤ d → Squarefree d → d % 4 = 3 → ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Module.finrank ℚ K = 2 ∧ (∃ r : K, r ^ 2 = -(d : K)) ∧ discr K = -d ∧ Nonempty (K →+* ℂ) ∧
      ∀ σ : K →+* ℂ, ∃ τ : ClassGroup (𝓞 K) → ℍ, ∀ C, IsIdealClassPoint σ C (τ C) := by
  refine ⟨⟨le_rfl, (by norm_num : Nat.Prime 7).squarefree, rfl⟩,
    ⟨by norm_num, (by norm_num : Nat.Prime 23).squarefree, rfl⟩, fun d h7 hs h4 => ?_⟩
  obtain ⟨K, _, h2, r, hr⟩ := exists_quadraticField_sq_eq_neg (d := d) (by omega)
  have hD := discr_eq_neg_of_sq_eq h2 hs h4 hr
  refine ⟨K, inferInstance, inferInstance, h2, ⟨r, hr⟩, hD, ⟨algebraMap K ℂ⟩, fun σ => ?_⟩
  choose τ hτ using exists_isIdealClassPoint h2 hD σ
  exact ⟨τ, hτ⟩

end Inhabitants

section Sign

end Sign

end GlobalTheory
