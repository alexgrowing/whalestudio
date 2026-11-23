import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoSymmetricBirigidifiedComplStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreExponentialKernelFullLatticeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELObjectOfPrimitivePeriodMapUniformised
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqExpRiemannFormAppellHumbertFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEqOfImDotProductMulVecStarEqOnSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealEqOfExpNegTwoPiIDivEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoOfSameAppellHumbertFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationOfExponentialLattStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem GlobalTheory.biIso_of_weil : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P P' : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → P'.IsLB → (∃ t : (P'.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A A) (fst A A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P'.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → LBIso P P' := by
  intro A _ _ g hA hs P P' hP hP1 hP2 hPs hP' hP'1 hP'2 hP's e La _ Q EF he hQ hker hW hW'
  obtain ⟨Λ, hd, hf, hk⟩ := GlobalTheory.T.complexFibreExponential_kernel_full_lattice (Sp ℂ) A g hA hs (𝟙 _) e he
  obtain ⟨L₀, u₀, hu₀⟩ := GlobalTheory.T.exists_holomorphic_uniformisation_of_exponential_lattice A g e Λ he hd hf hk
  obtain ⟨M, hM, hPM⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hs P hP hP1 hP2 hPs
  obtain ⟨M', hM', hPM'⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hs P' hP' hP'1 hP'2 hP's
  obtain ⟨u, Hm, χ, hue, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M hM
  obtain ⟨u', Hm', χ', hue', hF'⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M' hM'
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hL' : (abelian₂ A M').IsLB := LB.isLB_linComb hM' _ _

  have key : ∀ (M : LB A.left) (P : LB (G2 A).left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ)
      (χ : u.Λ → ℂ), M.IsLB → P.IsLB → u.ex = e → GlobalTheory.TorusRM.IsFactorAH u Hm χ →
      LBIso P (cubeLB A ![fst A A, snd A A] M) →
      (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
        Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) →
      ∀ a b : La, ((Q a) ⬝ᵥ ((2 : ℂ) • Hm).mulVec (star (Q b))).im = (EF a b : ℝ) := by
    intro M P u Hm χ hM hP hue hF hPM hW a b
    have hLM : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
    obtain ⟨ud, χd, hude, hFd⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag g A hA M u Hm χ hM hF
    have mem : ∀ x : La, Q x ∈ ud.Λ := fun x => (ud.ker _).1 (by rw [hude, hue]; exact (hker _).2 ⟨x, rfl⟩)
    refine GlobalTheory.T.eq_of_forall_cexp_neg_two_pi_I_mul_div_eq _ _ fun k hk => ?_
    have h1 := hW k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have h2 := GlobalTheory.T.weilPairing_eq_exp_riemannForm_appellHumbert_frame A hA _ (pull_isLB hLM _) g ud _ χd hFd k (Q a) (Q b)
      (Units.mk0 _ (Complex.exp_ne_zero _)) hk (mem a) (mem b) rfl
    rw [hude, hue] at h2
    have hiso : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left)
        (((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).pull (𝟙 A : A ⟶ A).left) := by
      refine LBIso.trans (pull_isLB hP _) (pull_isLB hLM _) (pull_isLB (pull_isLB hLM _) _)
        (GlobalTheory.RigidBundleGlue.LBIso.pull hPM _) ?_
      exact GlobalTheory.ThetaAffineGlue.lbIso_pull_id (pull_isLB hLM _)
    have h3 := GlobalTheory.PeriodObject.weilIs_of_lbIso GlobalTheory.globalFns_holds hA (pull_isLB hP _)
      (pull_isLB hLM _) hiso h2
    have := GlobalTheory.weilIs_unique_fieldPoint (Sp ℂ) A _ (pull_isLB hP _) ℂ (𝟙 _) k _ _ _ _ h1 h3
    have := congrArg Units.val this
    simpa using this.symm
  have hH : Hm = Hm' := by
    have e2 := GlobalTheory.T.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span' g ((2 : ℂ) • Hm) ((2 : ℂ) • Hm') (Set.range Q) ?_ ?_
    · have := congrArg (fun X => (1 / 2 : ℂ) • X) e2
      simpa [smul_smul] using this
    · have hR : Set.range Q = (Λ : Set (Fin g → ℂ)) := by
        ext z
        rw [SetLike.mem_coe, ← hk, hker]
        rfl
      rw [hR]; exact hf
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [key M P u Hm χ hM hP (hue.trans hu₀) hF hPM hW a b,
        key M' P' u' Hm' χ' hM' hP' (hue'.trans hu₀) hF' hPM' hW' a b]
  subst hH
  have hlam := GlobalTheory.T.mumfordBundleIso_of_same_appellHumbert_form g A hA hp M M' u u' Hm χ χ' hM hM' (hue'.trans hue.symm) hF hF'
  exact LBIso.trans hP hL hP' hPM (LBIso.trans hL hL' hP' hlam (LBIso.symm hPM'))
