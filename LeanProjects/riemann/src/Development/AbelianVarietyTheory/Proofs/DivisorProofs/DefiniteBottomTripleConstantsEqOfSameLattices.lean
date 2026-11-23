import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSmul
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.KerDiag
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCF
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseThetaKernelSeriesUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotSameRig

open GlobalTheory.Grid

variable {D : D7}

theorem heisO_smul {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (ζ : ℂ) (g : WO S T → ℂ) :
    heisO ψ S T w (ζ • g) = ζ • heisO ψ S T w g := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem thetaAt_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ}
    {f₀ Φ f f' : WO S T → ℂ} (ζ : ℂ) (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (h' : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c (ζ • f₀) Φ f') : f' = ζ • f := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c (ζ • f₀) (ζ • Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.trans Φ hΦ x hx, heisO_smul]
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.modul Φ hΦ y hy, heisO_smul]
      vac := by rw [LinearMap.smul_apply, hT.vac] }
  rw [h'.2 _ hT', hall Tm hT, LinearMap.smul_apply]

theorem isVacO_fixSig {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) :
    IsVacO ψ θ (Formalism.L2.Fam.ThC.fixSig S) (Formalism.L2.Fam.ThC.fixSig T) sS sT LS LT f :=
  ⟨h.1, h.2.inf, ⟨h.2.theta.quasi, h.2.theta.level, h.2.theta.cont, h.2.theta.smooth⟩, h.2.lat, h.2.fock, h.2.norm⟩

theorem setIntegral_eq_mul {V : HSp D} (ν₁ ν₂ : Measure (GA D V)) (fd₁ fd₂ : Set (GA D V)) (h₁ : ν₁.IsHaarMeasure)
    (h₂ : ν₂.IsHaarMeasure) (hfd₁ : IsFundamentalDomain (GQ V) fd₁ ν₁) (hfd₂ : IsFundamentalDomain (GQ V) fd₂ ν₂) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) →
      (IntegrableOn f fd₁ ν₁ ↔ IntegrableOn f fd₂ ν₂) ∧ ∫ g in fd₁, f g ∂ν₁ = c * ∫ g in fd₂, f g ∂ν₂ := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hc := Measure.isMulLeftInvariant_eq_smul ν₁ ν₂
  set c₀ : NNReal := Measure.haarScalarFactor ν₁ ν₂ with hc₀
  have hpos : 0 < c₀ := Measure.haarScalarFactor_pos_of_isHaarMeasure ν₁ ν₂
  have hc0 : (c₀ : ENNReal) ≠ 0 := by exact_mod_cast hpos.ne'
  have hctop : (c₀ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsm : (c₀ • ν₂ : Measure (GA D V)) = (c₀ : ENNReal) • ν₂ := rfl
  have hfd₂' : IsFundamentalDomain (GQ V) fd₂ ν₁ := hfd₂.mono (by rw [hc, hsm]; exact Measure.smul_absolutelyContinuous)
  refine ⟨(c₀ : ℂ), by exact_mod_cast hpos.ne', fun f hf => ?_⟩
  have hf' : ∀ (g : GQ V) (x : GA D V), f (g • x) = f x := fun g x => hf g g.2 x
  constructor
  · rw [hfd₁.integrableOn_iff hfd₂' hf', hc, hsm, IntegrableOn, Measure.restrict_smul, integrable_smul_measure hc0 hctop]
    rfl
  · rw [hfd₁.setIntegral_eq hfd₂' hf', hc, hsm, Measure.restrict_smul, integral_smul_measure]
    simp [Complex.real_smul]

set_option maxHeartbeats 1000000 in

theorem const_of_sameRig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    X.rA = Y.rA → X.rA' = Y.rA' → X.rW = Y.rW → ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → X.IsConst W.ψ W.θ c := by
  intro D T L sc G W i j A A' WW X Y hX hY hA hA' hW c hc

  have hvX := hX.is.isVac
  have hvY := hY.is.isVac
  rw [← hA, ← hW] at hvY
  have hvX' := hX.is.isVac'
  have hvY' := hY.is.isVac'
  rw [← hA', ← hW] at hvY'
  have hψ : IsStdChar D W.ψ (-1) := hvX.1
  have hθ : IsInfFam W.θ := hvX.2.inf
  have hcS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (hX.is.rigA.2.2 τ).1
  have hcT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hX.is.rigW.2.2 τ).1
  have hcS' : ∀ τ, IsCartanInv (gramAt D A' τ) (X.rA'.s τ) := fun τ => (hX.is.rigA'.2.2 τ).1
  obtain ⟨ζ, hζ1, hζ⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hψ hθ (Formalism.L2.Fam.ThC.fixSig (neg A))
    (Formalism.L2.Fam.ThC.fixSig WW) (fun τ => -X.rA.s τ) X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _)
    hcS hcT X.rA.Λ X.rW.Λ (GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1) hX.is.rigW.1 X.vac Y.vac (isVacO_fixSig hvX)
    (isVacO_fixSig hvY)
  obtain ⟨ζ', hζ1', hζ'⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hψ hθ (Formalism.L2.Fam.ThC.fixSig A')
    (Formalism.L2.Fam.ThC.fixSig WW) X.rA'.s X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _)
    hcS' hcT X.rA'.Λ X.rW.Λ hX.is.rigA'.1 hX.is.rigW.1 X.vac' Y.vac' (isVacO_fixSig hvX') (isVacO_fixSig hvY')
  have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hζ1; exact zero_ne_one hζ1
  have hζ0' : ζ' ≠ 0 := fun h => by rw [h, norm_zero] at hζ1'; exact zero_ne_one hζ1'

  have he : ∀ t, Y.e t = X.e t := fun t => GlobalTheory.BaseKernelUniq.idemSum_unique A (hY.is.idem t) (hX.is.idem t)
  have hid : ∀ t, Y.ideal (locPl G) t = X.ideal (locPl G) t := fun t => by
    unfold Tri.ideal
    exact Finset.prod_congr rfl fun w hw => by rw [(hY.is.expo t w hw).unique (hX.is.expo t w hw)]

  have hf : ∀ t, Y.f t = ζ • X.f t := fun t => by
    have h2 := hY.is.fst t
    rw [← hA, ← hW, he t, hid t, hζ] at h2
    exact thetaAt_smul (S := neg A) ζ (hX.is.fst t) h2
  have hf' : ∀ t, Y.f' t = ζ' • X.f' t := fun t => by
    have h2 := hY.is.snd t
    rw [← hA', ← hW, he t, hid t, hζ'] at h2
    exact thetaAt_smul ζ' (hX.is.snd t) h2

  have thX : ∀ t, IsThetaFunO W.ψ (neg A) WW (X.f t) := fun t =>
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hθ (hX.is.fst t) hvX.2.theta
  have thX' : ∀ t, IsThetaFunO W.ψ A' WW (X.f' t) := fun t =>
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hθ (hX.is.snd t) hvX'.2.theta

  have hk : ∀ t P h g, Y.ker W.ψ W.θ t P h g = ζ * X.ker W.ψ W.θ t P h g := by
    intro t P h g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) hψ hθ (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
      (thX t) P
    have hWX : IsWeilDatumO W.ψ (neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
    have hWY : IsWeilDatumO W.ψ (neg A) WW _ _ ((Y.ω t).toSgn true) := hY.is.weil t
    have hu := GlobalTheory.WeilUniq.weilDatum_unique D W.ψ hψ (neg A) WW _ _ _ _ hWY hWX ((ofSgn true A).symm g, h) _ hF
    unfold Tri.ker
    rw [← hA, ← hW, hf t, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul]
    show ((Y.ω t).toSgn true) ((ofSgn true A).symm g, h) (ζ • _) 0 =
      ζ * ((X.ω t).toSgn true) ((ofSgn true A).symm g, h) _ 0
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hu]
  have hk' : ∀ t P h g, Y.ker' W.ψ W.θ t P h g = ζ' * X.ker' W.ψ W.θ t P h g := by
    intro t P h g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := A') hψ hθ X.rA'.s X.rA'.B X.rW.s X.rW.B (thX' t) P
    have hWX : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
    have hWY : IsWeilDatumO W.ψ A' WW _ _ (Y.ω' t) := hY.is.weil' t
    have hu := GlobalTheory.WeilUniq.weilDatum_unique D W.ψ hψ A' WW _ _ _ _ hWY hWX (g, h) _ hF
    unfold Tri.ker'
    rw [← hA', ← hW, hf' t, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul]
    show (Y.ω' t) (g, h) (ζ' • _) 0 = ζ' * (X.ω' t) (g, h) _ 0
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hu]

  have inv : ∀ t P h, ∀ γ ∈ GQ A, ∀ g, X.ker W.ψ W.θ t P h (γ * g) = X.ker W.ψ W.θ t P h g := by
    intro t P h γ hγ g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) hψ hθ (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
      (thX t) P
    have hWX : IsWeilDatumO W.ψ (neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
    have e1 : (((ofSgn true A).symm (γ * g), h) : GA D (neg A) × GA D WW) =
        ((ofSgn true A).symm γ, 1) * ((ofSgn true A).symm g, h) := by simp
    show ((X.ω t).toSgn true) ((ofSgn true A).symm (γ * g), h) _ 0 = ((X.ω t).toSgn true) ((ofSgn true A).symm g, h) _ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hWX.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) 1 (one_mem _) _ (hWX.om_pres _ _ hF)
  have inv' : ∀ t P h, ∀ γ ∈ GQ A', ∀ g, X.ker' W.ψ W.θ t P h (γ * g) = X.ker' W.ψ W.θ t P h g := by
    intro t P h γ hγ g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := A') hψ hθ X.rA'.s X.rA'.B X.rW.s X.rW.B (thX' t) P
    have hWX : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
    have e1 : ((γ * g, h) : GA D A' × GA D WW) = (γ, 1) * (g, h) := by simp
    show (X.ω' t) (γ * g, h) _ 0 = (X.ω' t) (g, h) _ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hWX.om_aut _ hγ 1 (one_mem _) _ (hWX.om_pres _ _ hF)

  obtain ⟨r, hr0, hr⟩ := setIntegral_eq_mul X.m Y.m X.fd Y.fd hX.is.meas.1 hY.is.meas.1 hX.is.meas.2 hY.is.meas.2
  obtain ⟨r', hr0', hr'⟩ := setIntegral_eq_mul X.m' Y.m' X.fd' Y.fd' hX.is.meas'.1 hY.is.meas'.1 hX.is.meas'.2
    hY.is.meas'.2
  have hYk : ∀ t P h, Y.ker W.ψ W.θ t P h = fun g => ζ * X.ker W.ψ W.θ t P h g := fun t P h => funext (hk t P h)
  have hYk' : ∀ t P h, Y.ker' W.ψ W.θ t P h = fun g => ζ' * X.ker' W.ψ W.θ t P h g := fun t P h => funext (hk' t P h)
  have hI : ∀ t P h, X.I W.ψ W.θ t P h = r * ζ⁻¹ * Y.I W.ψ W.θ t P h := fun t P h => by
    rw [Tri.I, Tri.I, hYk, integral_const_mul, (hr _ (inv t P h)).2]
    field_simp
  have hI' : ∀ t P h, X.I' W.ψ W.θ t P h = r' * ζ'⁻¹ * Y.I' W.ψ W.θ t P h := fun t P h => by
    rw [Tri.I', Tri.I', hYk', integral_const_mul, (hr' _ (inv' t P h)).2]
    field_simp
  have hint : ∀ t P h, IntegrableOn (Y.ker W.ψ W.θ t P h) Y.fd Y.m → IntegrableOn (X.ker W.ψ W.θ t P h) X.fd X.m :=
    fun t P h hi => by
      rw [hYk, IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.2 hζ0)] at hi
      exact (hr _ (inv t P h)).1.2 hi
  have hint' : ∀ t P h, IntegrableOn (Y.ker' W.ψ W.θ t P h) Y.fd' Y.m' →
      IntegrableOn (X.ker' W.ψ W.θ t P h) X.fd' X.m' := fun t P h hi => by
    rw [hYk', IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.2 hζ0')] at hi
    exact (hr' _ (inv' t P h)).1.2 hi

  set κ : ℂ := r * ζ⁻¹ * (r' * ζ'⁻¹)⁻¹ with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact mul_ne_zero (mul_ne_zero hr0 (inv_ne_zero hζ0)) (inv_ne_zero (mul_ne_zero hr0' (inv_ne_zero hζ0')))
  obtain ⟨⟨t₁, h₁⟩, P, P', H⟩ := hc
  have hX1 : X.IsConst W.ψ W.θ fun t => κ * c t := by
    refine ⟨⟨t₁, mul_ne_zero hκ0 h₁⟩, P, P', fun t => ⟨fun h => ⟨hint t P h ((H t).1 h).1, hint' t P' h ((H t).1 h).2⟩,
      ?_, fun h => ?_⟩⟩
    · obtain ⟨h, hh⟩ := (H t).2.1
      refine ⟨h, ?_⟩
      rw [hI']
      exact mul_ne_zero (mul_ne_zero hr0' (inv_ne_zero hζ0')) hh
    · have e := (H t).2.2 h
      have e' : Y.I' W.ψ W.θ t P' h = (r' * ζ'⁻¹)⁻¹ * X.I' W.ψ W.θ t P' h := by
        rw [hI', ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hr0' (inv_ne_zero hζ0')), one_mul]
      rw [hI, e, e', hκ]
      ring
  have := GlobalTheory.BotTransfer.isConst_smul hX1 (inv_ne_zero hκ0)
  simpa only [← mul_assoc, inv_mul_cancel₀ hκ0, one_mul] using this

end GlobalTheory.BotSameRig
