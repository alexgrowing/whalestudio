import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodsLactSymplectic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussRMulFactor
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatchStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructureStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ZakLaws

theorem embR_neg {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (X : Data E r)
    (y : Matrix (Fin n) (Fin r) E) : embR X (-y) = -embR X y := by
  funext τ k a
  simp only [embR, Matrix.neg_apply, map_neg, Pi.neg_apply]

theorem EFR_neg_right {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (X : Data E r)
    (v v' : WR X n) : EFR X v (-v') = -EFR X v v' := by
  unfold EFR hermC
  simp only [Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib, Complex.neg_re]

variable {D : D7} {S T : HSp D}

theorem inf_incA (C : Ctx S T) (τ : D.what₂.Tau) (e : D.host.E) :
    C.θ τ (infPart D (incA D e)) = tauE D τ e := by
  have h := (C.inf τ).1 e
  simp only [infPart, Formalism.L2.Theta.incA] at h ⊢
  exact h

theorem realPt_actO (C : Ctx S T) {ga : GL (Fin T.rank) D.host.E} {γ : GA D T} (h : IsRatOf T ga γ)
    (w : WO S T) :
    C.realPt (actO S T 1 γ w) =
      fun σ k => ((ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map σ.1) *ᵥ C.realPt w σ k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hact⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  funext σ k a
  have he : ∀ z, (σ.1 : D.host.E →+* ℂ) z = conj (tauE D (C.m.e.symm σ) z) := by
    intro z
    have hz := C.m.e_emb (C.m.e.symm σ)
    rw [Equiv.apply_symm_apply] at hz
    rw [hz, ComplexEmbedding.conjugate_coe_eq]
  have hm : Formalism.L2.Theta.mt S 1⁻¹ = 1 := by
    simp [Formalism.L2.Theta.mt]
  have hg : Formalism.L2.Theta.mt T γ = (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map (incA D) := h
  have h1 : compAt C.θ (C.m.e.symm σ) (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) = 1 := by
    ext i j
    simp [compAt, Matrix.one_apply, apply_ite]
  simp only [Ctx.realPt]
  rw [(hact 1 γ w).2.2 (C.m.e.symm σ), hm, hg, h1, Matrix.mul_one]
  simp only [compAt, Matrix.map_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    inf_incA C, he, Ctx.realPt]

end GlobalTheory.Ker.ZakLaws

namespace GlobalTheory.Ker

theorem Ctx.th_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ x ∈ C.X.dom, ∀ φ : TF S.rank C.g, SW.IsSB φ → (∀ φ', SW.IsSB φ' → C.Th x (φ + φ') = C.Th x φ + C.Th x φ' ∧ (C.Th x φ = C.Th x φ' → φ = φ')) ∧ (∀ a : ℂ, C.Th x (a • φ) = a • C.Th x φ) ∧ (∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.rho (finW S T y) (C.Th x φ) = C.Th x (heisG C.X C.bas (-y) φ)) ∧ ∀ (ga : GL (Fin T.rank) D.host.E) (γ : GA D T), IsRatOf T ga γ → ∀ w, C.Th (lact ga x) (wG C.X C.bas C.idx ga φ) w = C.Th x φ (actO S T 1 γ⁻¹ w) := by
  intro D S T C x hx φ hφ
  obtain ⟨R, -, -, hadd, hR, -, -, hfin0, -, hact⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  have hth := GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C
  have hzak := GlobalTheory.T.adelicZakTheta_exists_unique D S T C
  have hlaws := thR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even
  have hZ : C.IsZak x φ (C.Th x φ) := (hzak x hx φ hφ).1
  have huniq : ∀ ψ, SW.IsSB ψ → ∀ f, C.IsZak x ψ f → f = C.Th x ψ := fun ψ hψ => (hzak x hx ψ hψ).2
  have hsub : ∀ w u, C.realPt (w - u) = C.realPt w - C.realPt u := by
    intro w u
    have hwu := hadd (w - u) u
    rw [sub_add_cancel] at hwu
    rw [hwu, add_sub_cancel_right]
  refine ⟨fun φ' hφ' => ⟨?_, ?_⟩, fun a => ?_, fun y => ?_, fun ga γ hγ w => ?_⟩
  · have hsb := (GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ φ φ' hφ hφ').1
    have hZ' := (hzak x hx φ' hφ').1
    refine (huniq _ hsb _ ⟨(hth.2.1 _ _ hZ.1 hZ'.1).1, fun w hw => ?_⟩).symm
    rw [Pi.add_apply, hZ.2 w hw, hZ'.2 w hw, ((hlaws x hx φ hφ).2.2.2.1 φ' hφ').2, Pi.add_apply]
  · intro heq
    have hZ' := (hzak x hx φ' hφ').1
    apply ((hlaws x hx φ hφ).2.2.2.1 φ' hφ').1
    funext v
    obtain ⟨hR1, hR2⟩ := hR v
    have e1 := hZ.2 (R v) hR1
    have e2 := hZ'.2 (R v) hR1
    rw [hR2] at e1 e2
    rw [← e1, ← e2, heq]
  · have hsb := (GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ φ φ hφ hφ).2.1 a
    refine (huniq _ hsb _ ⟨(hth.2.2 _ hZ.1).1 a, fun w hw => ?_⟩).symm
    rw [Pi.smul_apply, hZ.2 w hw, (hlaws x hx φ hφ).2.2.2.2 a, Pi.smul_apply]
  · have hsb := ((heisG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even).2.2.2 (-y) φ hφ).1
    refine huniq _ hsb _ ⟨(hth.2.2 _ hZ.1).2.1 _, fun w hw => ?_⟩
    obtain ⟨hrat, hfinW, hreal, -⟩ := (GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.2.2.2 y
    have hw' : IsRealPt (w - (ratW T S yᵀ - finW S T y)) := by
      unfold IsRealPt at hw hreal ⊢
      rw [Matrix.map_sub _ (map_sub (finPart D)), hw, hreal, sub_zero]
    rw [(hth.2.2 _ hZ.1).2.2.2.1 y w hw, hZ.2 _ hw', hsub, hsub, hrat, hfin0 _ hfinW, sub_zero,
      (hlaws x hx φ hφ).2.1 (-y), ZakLaws.embR_neg, ZakLaws.EFR_neg_right]
    simp only [Complex.ofReal_neg, mul_neg, neg_neg, sub_eq_add_neg]
  · have hq := (GlobalTheory.T.rational_unitary_group_structure D S T C).2.1
    have hinv : IsRatOf T ga⁻¹ γ⁻¹ := (hq γ γ ga ga hγ hγ).2.1
    have hun : IsUn C.X ga := (hq γ γ ga ga hγ hγ).2.2.2.1
    have hGQ : γ⁻¹ ∈ GQ T := (hq _ _ _ _ hinv hinv).2.2.1
    have hx' : lact ga x ∈ C.X.dom := IsUn.lact_mem hun hx
    have hsbw := (wG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even ga hun φ hφ).1
    have hZw : C.IsZak (lact ga x) (wG C.X C.bas C.idx ga φ) (fun w => C.Th x φ (actO S T 1 γ⁻¹ w)) := by
      refine ⟨(hth.2.2 _ hZ.1).2.2.2.2.1 1 (one_mem _) γ⁻¹ hGQ, fun w hw => ?_⟩
      dsimp only
      have hwr : IsRealPt (actO S T 1 γ⁻¹ w) := (hact 1 γ⁻¹ w).1 hw
      rw [hZ.2 _ hwr, ZakLaws.realPt_actO C hinv w,
        ← (hlaws x hx φ hφ).2.2.1 ga hun]
      congr 1
      funext τ k
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact (congrFun ((hzak (lact ga x) hx' _ hsbw).2 _ hZw) w).symm

end GlobalTheory.Ker
