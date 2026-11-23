import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDeRhamPeriodMapEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveLatticeMultiplierStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorMinpolyEigenvalueCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImagePolynomialEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCorrespondencePolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalPolynomialLinearFactorSplitStatement
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CMEigen

theorem exists_algebraic_eigenvectors : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (U : Unif φ L 0 X) (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ) (hp : X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p),
    IsCMType φ →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧ a i ≠ 0) →
    (∀ b : E, (∀ x ∈ L, b * x ∈ L) → ∃ α : X.A ⟶ X.A, IsMonHom α ∧
      ∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
    (∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
      ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left) →
    ∃ (y₀ : I → HdR X₀.A) (yv : I → HdR X.A) (w : I → ℂ), ∀ i,
      y₀ i ≠ 0 ∧ (GlobalTheory.Published.AbelianDeRham.bcMor hp.grp).Corr (y₀ i) (yv i) ∧ U.IsCMVec i (yv i) (w i) ∧ w i ≠ 0 ∧
        IsAlgebraic ℚ (w i / a i) := by
  intro hPC hD _hDC E _ _ _ I _ φ L 𝔠 X₀ X p U v₀ v a hp _hφ hva hex hdesc
  obtain ⟨P, hspan, hP⟩ := GlobalTheory.T.cm_de_rham_period_map_equivariant hPC E I φ L 𝔠 X U
  obtain ⟨b, hbL, hbprim⟩ := GlobalTheory.T.exists_primitive_lattice_multiplier E I φ L 𝔠 X U
  obtain ⟨α, hαm, hα⟩ := hex b hbL
  haveI := hαm
  obtain ⟨α₀, hα₀m, hα₀⟩ := hdesc b α hα
  haveI := hα₀m
  obtain ⟨hf, heig⟩ := GlobalTheory.T.generator_minpoly_eigenvalue_compat E (HdR X.A) P hspan b (push (dp0 ℂ) (𝟙 _) α) (hP b α hα) hbprim
  have hE₀ : LieExact X₀.A := (hD.2.1 Qb X₀.A _ X₀.ab X₀.dim).1
  have hE : LieExact X.A := (hD.2.1 ℂ X.A _ X.ab X.dim).1
  obtain ⟨hBC, hF⟩ := hD.2.2.1 Qb X₀.A _ X₀.ab X₀.dim ℂ X.A p hp.grp
  let D : (Fin (Module.finrank ℚ (FR E)) → ℂ) →L[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    ContinuousLinearMap.pi fun j ↦ φ (U.e j) b • ContinuousLinearMap.proj j
  have hDz : ∀ z, D z = fun j ↦ φ (U.e j) b * z j := fun z ↦ by
    funext j; simp [D]
  have hD' : ∀ z, U.u.ex (D z) = U.u.ex z ≫ α := fun z ↦ by rw [hDz]; exact hα z
  have key : ∀ i, ∃ (y₀ : HdR X₀.A) (yv : HdR X.A), y₀ ≠ 0 ∧
      (GlobalTheory.Published.AbelianDeRham.bcMor hp.grp).Corr y₀ yv ∧ U.IsCMVec i yv (a i) := by
    intro i
    obtain ⟨hLC, hdiff, ha⟩ := hva i
    obtain ⟨Q, c, hQ, hQ1⟩ := GlobalTheory.T.minimal_polynomial_linear_factor_split E b (φ i)
    obtain ⟨h₀, hh₀⟩ := hE₀.2 (v₀ i).hom (v₀ i).isTangent
    obtain ⟨h, hh⟩ := hBC.exists h₀
    have hlie : IsLieImage h (v i).hom := IsLieImage.baseChange (hφ := hp.grp) hF hE hh hLC hh₀
    have hcorr := GlobalTheory.T.de_rham_correspondence_polynomial Qb ℂ (algebraMap Qb ℂ) X₀.A X.A _ p (GlobalTheory.Published.AbelianDeRham.bcMor hp.grp) α₀ α hα₀.symm h₀ h hh Q
    have hDw : D (Pi.single (U.e.symm i) (a i)) = φ i b • Pi.single (U.e.symm i) (a i) := by
      rw [hDz]
      funext j
      by_cases hj : j = U.e.symm i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    obtain ⟨v', hv'1, hv'2⟩ := GlobalTheory.T.lie_image_polynomial_endomorphism X.A (X.diag U.c) _ U.u α D hD' h (v i).hom _ (φ i b) hlie hdiff hDw
      (Q.map (algebraMap Qb ℂ))
    rw [hQ1, one_smul] at hv'2
    have hTy : push (dp0 ℂ) (𝟙 _) α (Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α) (Q.map (algebraMap Qb ℂ)) h) =
        φ i b • Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α) (Q.map (algebraMap Qb ℂ)) h := by
      have e1 := congrArg (Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α)) hQ
      rw [map_mul, map_mul, hf, mul_zero, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at e1
      have e2 := LinearMap.congr_fun e1 h
      rw [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.zero_apply, sub_eq_zero] at e2
      simpa [Algebra.algebraMap_eq_smul_one] using e2
    refine ⟨_, _, ?_, hcorr, fun a' α' _ hα' ↦ heig (φ i) a' _ (hP a' α' hα') _ hTy, v', hv'1, hv'2⟩
    intro h0
    rw [h0] at hcorr
    have hz : (GlobalTheory.Published.AbelianDeRham.bcMor hp.grp).Corr 0 0 := fun c ↦ by simp
    have hy0 := hBC.unique hcorr hz
    rw [hy0] at hv'1
    have hv1 : v' = 1 := (hE.1 0).unique hv'1 (isLieImage_one_iff.2 (zero_mem _))
    rw [hv1] at hv'2
    have := GlobalTheory.ArchMetricCompare.eq_zero_of_isDiff U.u hv'2
    exact ha (by simpa using congrFun this (U.e.symm i))
  choose y₀ yv hy using key
  exact ⟨y₀, yv, a, fun i ↦ ⟨(hy i).1, (hy i).2.1, (hy i).2.2, (hva i).2.2,
    by rw [div_self (hva i).2.2]; exact isAlgebraic_one⟩⟩

end GlobalTheory.CMEigen
