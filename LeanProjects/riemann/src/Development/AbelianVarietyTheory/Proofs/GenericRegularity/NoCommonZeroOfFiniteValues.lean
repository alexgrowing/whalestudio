import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.LieFreePf
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReduced
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbedding

set_option synthInstance.maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_valuationSubring_hom_of_overLa {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) (T : CDVR) (io : K →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e) :
    ∃ b : (la.valuation K).valuationSubring →+* T.V,
      (algebraMap T.V T.Fr).comp b = io.comp (la.valuation K).valuationSubring.subtype := by
  have hmem : ∀ a : (la.valuation K).valuationSubring, io a ∈ (algebraMap T.V T.Fr).range := by
    intro a
    apply Formalism.L2.PjFree.mem_range_of_vV_nonneg
    rw [ho.2]
    refine mul_nonneg (by positivity) ?_
    by_cases ha : (a : K) = 0
    · simp [vLa, ha]
    · have hv : la.valuation K (a : K) ≤ 1 := a.2
      have hn : la.valuation K (a : K) ≠ 0 := (la.valuation K).ne_zero_iff.2 ha
      have := (WithZero.log_le_log hn one_ne_zero).2 hv
      simp only [WithZero.log_one] at this
      simp only [vLa]; omega
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  let eq : T.V ≃+* (algebraMap T.V T.Fr).range :=
    RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
      ⟨fun x y h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  refine ⟨eq.symm.toRingHom.comp
    ((io.comp (la.valuation K).valuationSubring.subtype).codRestrict _ hmem), ?_⟩
  ext a
  exact congrArg Subtype.val (eq.apply_symm_apply ⟨io a, hmem a⟩)

theorem noCommonZero_of_finite_values : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ la : HeightOneSpectrum (𝓞 c.F), ModelAt Xo c la → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → (∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, ∃ i, v (ws i) ≠ ⊤) → Formalism.L2.PjFree.NoCommonZero Xo c ws := by
  intro hST E _ _ _ H Dw l Xo c hL la hM a n m ws hws hv k _ _ _ y
  by_contra hcon
  push Not at hcon
  obtain ⟨p, φ, y', hy'⟩ := hL.test k y
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  have hker : ∀ i, evR Xo c (ws i) y' ∈ RingHom.ker φ.toRingHom := by
    intro i
    have := GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n (ws i) (hws i) p.R k φ y' y hy'
    rw [hcon i] at this
    exact this.symm
  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ (RingHom.ker_ne_top φ.toRingHom)
  let _ : Field (p.R ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite c.F (p.R ⧸ M) := finite_of_finite_type_of_isJacobsonRing c.F (p.R ⧸ M)
  have : NumberField (p.R ⧸ M) := NumberField.of_module_finite c.F (p.R ⧸ M)
  obtain ⟨T, κ, e, ho, hfin⟩ := GlobalTheory.locFld c.F (p.R ⧸ M) (algebraMap c.F (p.R ⧸ M)) la
  set io : c.F →+* T.Fr := κ.comp (algebraMap c.F (p.R ⧸ M)) with hio
  let _ : Algebra c.F T.Fr := io.toAlgebra
  let ψ : p.R →ₐ[c.F] T.Fr := { κ.comp (Ideal.Quotient.mk M) with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := hL.bc p.R T.Fr ψ y'
  have hz0 : ∀ i, evR Xo c (ws i) z = 0 := by
    intro i
    rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n (ws i) (hws i) p.R T.Fr ψ y' z hz]
    show κ (Ideal.Quotient.mk M _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (hle (hker i)), map_zero]
  obtain ⟨Y, hPI⟩ := hM
  obtain ⟨b, hb⟩ := exists_valuationSubring_hom_of_overLa la T io e ho
  have hIF : IntFramesSt Xo c :=
    intFrames Xo c Out.CubePf.cubePull (lieFree Xo c) (thetaFrame_of Xo c hST) (fun S _ _ y => hL.test S y)
  obtain ⟨w, t, hw⟩ := intFr_of_model hIF T io Y hPI b hb z
  obtain ⟨i, hi⟩ := hv _ ⟨PtV.mk la ho w hfin () trivial, rfl⟩
  apply hi
  show nval T.V e (evI w (ws i)) = ⊤
  have h0 : evI w (ws i) = 0 := by
    have := hL.wt a n (ws i) (hws i) T.Fr t z w.1 ⟨p, ψ, y', hz⟩ w.2.1 hw
    rw [hz0 i, mul_zero] at this
    exact this
  rw [h0, nval_zero]

end GlobalTheory.Reg
