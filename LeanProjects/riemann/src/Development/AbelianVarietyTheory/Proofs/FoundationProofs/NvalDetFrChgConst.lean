import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringComapEqNonunits
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralFramesModelInvertiblePushforward
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralLatticeStructureUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NatCastMemMaximalIdealOfOverLa
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames

namespace GlobalTheory.FlatLine.PlaceConst

theorem vV_map_eq {V K V' K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K']
    [Algebra V' K'] [IsFractionRing V' K'] (g : V →+* V') (χ : K →+* K')
    (h : χ.comp (algebraMap V K) = (algebraMap V' K').comp g) (e : ℕ)
    (he : ∀ ϖ : V, Irreducible ϖ → vV V' (algebraMap V' K' (g ϖ)) = e) (x : K) :
    vV V' (χ x) = e * vV V x := by
  by_cases hx : x = 0
  · simp [hx, vV]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hx
  have h' : ∀ a, χ (algebraMap V K a) = algebraMap V' K' (g a) := fun a => RingHom.congr_fun h a
  have h1 := he ϖ hϖ
  have h2 := GlobalTheory.PlaceCompletion.valV_algebraMap_of_irreducible (K' := K) hϖ
  have h3 := GlobalTheory.PlaceCompletion.valV_algebraMap_of_isUnit (K' := K) u.isUnit
  have h4 := GlobalTheory.PlaceCompletion.valV_algebraMap_of_isUnit (K' := K') (u.isUnit.map g)
  simp only [vV] at h1 ⊢
  rw [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, h', h', map_mul, map_mul, map_zpow₀, map_zpow₀, h2, h3, h4,
    one_mul, one_mul, WithZero.log_zpow, WithZero.log_zpow, WithZero.log_exp, ← h1]
  simp only [smul_eq_mul]
  ring

theorem nval_det_frChg_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ (y₀ : FrPt Xo c c.F) (τ : E →+* ℂ) (w : HeightOneSpectrum (𝓞 c.F)), ∃ b : ℝ, ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa w T.V io e → letI := io.toAlgebra; ∀ (y z : FrPt Xo c T.Fr) (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) T.Fr)) (a : T.Fr), Integral T io y → FrMap (Algebra.ofId c.F T.Fr) y₀ z → FrChg g a y z → nval T.V e (g τ).det = (b : EReal) := by
  intro E _ _ _ H Dw l Xo c hr hg y₀ τ w
  have hB := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hT := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨T₀, io₀, ho₀, -, hini⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion c.F w
  obtain ⟨O, _, β, Y, -, hY, hb⟩ :=
    modelAtSt_of_good GlobalTheory.partI_closed GlobalTheory.Moduli.moduli_scheme_exists E H Dw l Xo c hr hg w
  obtain ⟨b₀, hb₀⟩ := hb T₀ io₀ 1 ho₀
  letI := io₀.toAlgebra
  obtain ⟨z₀, hz₀⟩ :=
    GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c c.F T₀.Fr (Algebra.ofId c.F T₀.Fr) y₀
  obtain ⟨y₁, t, hbor⟩ := intFr_of_model (GlobalTheory.intFrames_of_laws hB hT E H Dw l Xo c) T₀ io₀ Y hY b₀ hb₀ z₀
  obtain ⟨g₁, a₁, hg₁, hc₁⟩ := (frChg_exists_unique E H Dw l Xo c T₀.Fr y₁.1 z₀).1 hbor.1.symm
  refine ⟨(vV T₀.V (g₁ τ).det : ℝ) / (1 : ℕ), ?_⟩
  intro T io e ho
  obtain ⟨φ, χ, -, hio, hχ, hϖ⟩ := hini T io e ho
  subst hio
  letI := (χ.comp io₀).toAlgebra
  intro y z g a hy hz hc
  let ψ : T₀.Fr →ₐ[c.F] T.Fr := { χ with commutes' := fun _ => rfl }
  obtain ⟨y₂, hy₂⟩ :=
    GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c T₀.Fr T.Fr ψ y₁.1
  have hi₂ : Integral T (χ.comp io₀) y₂ :=
    GlobalTheory.PlaceInt.Ext.integral_of_frMap T₀ T io₀ χ φ (fun s => (RingHom.congr_fun hχ s).symm) ψ y₁.1 y₂ rfl hy₂ y₁.2.2
  obtain ⟨z', hz'⟩ :=
    GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c T₀.Fr T.Fr ψ z₀
  have hzz : z' = z := by
    have h1 := Formalism.L2.Pj.frMap_trans (Xo := Xo) (c := c) _ _ _ _ ψ y₀ z₀ z' hz₀ hz'
    have h2 : ψ.comp (Algebra.ofId c.F T₀.Fr) = Algebra.ofId c.F T.Fr := Subsingleton.elim _ _
    rw [h2] at h1
    exact (frMap_unique_refl_iff E H Dw l Xo c c.F T.Fr _ y₀).1 _ _ h1 hz
  subst hzz
  have hc₂ := (ChgBC.frChg_baseChange E H Dw l Xo c T₀.Fr T.Fr ψ y₁.1 z₀ y₂ z' g₁ a₁ hc₁ hy₂).1 hz'
  have hx : y₂.x = y.x := hc₂.1.symm.trans hc.1
  have hA := allTest_of_secBaseChange hB E H Dw l Xo c T.Fr
  obtain ⟨A, hAu, hAc⟩ :=
    (intLatU_holds E H Dw l Xo c T (χ.comp io₀) ⟨y, hA y, hy⟩ ⟨y₂, hA y₂, hi₂⟩ hx).1 τ
  obtain ⟨g₃, a₃, -, hc₃⟩ := (frChg_exists_unique E H Dw l Xo c T.Fr y y₂).1 hx
  have h3 : g₃ τ = A.map (algebraMap T.V T.Fr) := by
    funext i
    exact (y.basis τ (y₂.u τ i) (hx ▸ y₂.tan τ i) (y₂.eig τ i)).unique (hc₃.2.1 τ i) (hAc i)
  have h4 := (frChg_refl_and_comp E H Dw l Xo c T.Fr y y₂ z').2 _ _ _ _ hc₃ hc₂
  have h5 := congrFun ((frChg_exists_unique E H Dw l Xo c T.Fr y z').2 _ _ _ _ hc h4).1 τ
  have h6 : (g τ).det = algebraMap T.V T.Fr A.det * χ (g₁ τ).det := by
    rw [h5, Matrix.det_mul, h3, RingHom.map_det, RingHom.map_det, mul_comm]
    rfl
  have hu := valV_algebraMap_unit T hAu
  have h7 := nval_bc χ ho.1 (vV_map_eq φ χ hχ e hϖ) 1 (g₁ τ).det
  rw [mul_one] at h7
  rw [h6, nval_mul_unit e (hAu.map _).ne_zero (by simp [vV, hu]), h7, nval_of_ne (hg₁ τ).ne_zero]

end GlobalTheory.FlatLine.PlaceConst
