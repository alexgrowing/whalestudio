import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DictionaryColumnScalarFormEqTraceColumnFormStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSumHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateRowPairingPoincareSeriesBesselPeriodsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomHypothesisMatchingCentral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierCoefficientBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFinite
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
open Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.MiTop.BotTwo

variable {D : D7}

theorem per_smul_f {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (b : ℂ) (f : GA D B.V → ℂ) :
    B.per ψ φ (b • f) = b * B.per ψ φ f := by
  simp only [BesLev.per, besPer, besFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext n; ring

theorem contAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem contAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem contAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem contAut_rTrans {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem contAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact contAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add]; exact contAut_add hx hy
  | zero => simpa using contAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact contAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact contAut_smul (h x) c

theorem lev_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) {k : GA D V} (hk : k ∈ J)
    (g : GA D V) : G x (g * k) = χ k * G x g := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x g with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on generalizing g with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      simp only [Pi.smul_apply, smul_eq_mul, hT.lev v k hk g]; ring
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]; ring
  | zero => simp
  | add T₁ T₂ _ _ h₁ h₂ => simp only [map_add, LinearMap.add_apply, Pi.add_apply, h₁, h₂]; ring
  | smul c T _ h => simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, h]; ring

theorem shift_swap {G A B : Type} [Group G] [Group A] [Group B] (ι : G ≃* A × B) (g w : G) (y : A) (x : B)
    (hw : (ι w).1 = 1) : ι.symm (ι g * (y, x)) * w = g * (ι.symm (1, x) * w) * ι.symm (y, 1) := by
  apply ι.injective
  simp only [map_mul, MulEquiv.apply_symm_apply]
  ext
  · simp [hw]
  · simp [mul_assoc]

theorem comb_integral {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (c α α' : ℂ) (F F' : Y → ℂ)
    (h : ∀ y, α * F y + α' * F' y = 0) : α * (c * ∫ y, F y ∂ν) + α' * (c * ∫ y, F' y ∂ν) = 0 := by
  have hI : ∫ y, α * F y ∂ν = ∫ y, -(α' * F' y) ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => eq_neg_of_add_eq_zero_left (h y))
  rw [integral_neg, integral_const_mul, integral_const_mul] at hI
  linear_combination c * hI

end GlobalTheory.MiTop.BotTwo

set_option maxHeartbeats 1000000 in
open GlobalTheory.MiTop.BotTwo in

theorem GlobalTheory.MiTop.botRel_two : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ u (d : BotDat W u), d.Pin z → BotRel W z d := by
  intro _ hCR D L hT Gi Gl Kc Yd cX ex W hB z hzf hzc u d hP
  obtain ⟨-, hθ, hψ, hMatch, hχ, -⟩ := GlobalTheory.MiTop.botHyp_match W hB
  obtain ⟨R, hR⟩ := GlobalTheory.T.bessel_column_form_isometry W hB u d z hP
  obtain ⟨ξ, hξspan, hξ⟩ := GlobalTheory.T.dictionaryColumnScalarForm_eq_traceColumnForm D W.S.X W.Q.instEq u W.Q.Rl.ψ d.B (F0 W u) (W.S.tr u) W.S.Y.hK W.Q.Rl.θ d.a₀
    hθ hB.idE hP.adapted hP.h0 (hB.hyp.2.1 u)
  have hRS := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D W.S.X W.Q.instEq W.Q.Rl.θ hθ hB.idE
  obtain ⟨c, hc⟩ := GlobalTheory.T.conjugateRow_pairing_poincareSeries_besselPeriods D W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0) d.B W.S.Y hψ (hB.fin.inHH u)
  have hMt := hMatch z hzf hzc
  have hf1 : (iotaX W.S.X W.Q.instEq (z * (show GA D (D.sp.Y 0) from W.Q.tS))).1 = 1 := (hRS.1 _).1 hMt.1
  have hcont : ∀ (C : Cu W.S.X u W.S.Y.hK) ξ', IsContAut (D.sp.X 0) (d.B.colForm C.1 ξ') := fun C =>
    (GlobalTheory.Core.Mi.PhCol.ph_colForm D W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0) d.B W.S.Y.hK C).1
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  let e := Formalism.L2.SG.ColDict.colDict W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u)
  have hcol : ∀ φ : D.what₂.Mu u, Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK
      (e.symm (Submodule.inclusion hram (D.eMu u φ))) = (D.eMu u φ).1 := fun φ =>
    congrArg Subtype.val (e.apply_symm_apply (Submodule.inclusion hram (D.eMu u φ)))

  have L1 : ∀ (φ : D.what₂.Mu u) (C : Cu W.S.X u W.S.Y.hK), IsCol W u C (R φ) → ∀ T ∈ ThetaLiftSpaceZero W, ∀ y v,
      d.per φ T y v = rChi W d.k * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C.1 (ξ y))
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v)) := by
    intro φ C hC T hT y v
    have hC₀ : IsCol W u (e.symm (Submodule.inclusion hram (D.eMu u φ))) φ := hcol φ
    have e1 : (chart0 (F0 W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y =
        fun g => d.B.colForm C.1 (ξ y) (g * (d.a₀ * d.a)⁻¹) := by
      rw [← hcol φ]
      funext g
      rw [hξ _ y g, hR φ C _ hC hC₀ (ξ y)]
      simp only [rTrans]
      congr 1
      rw [mul_assoc, mul_inv_rev, (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hP.cen) d.a₀⁻¹)]
    have e2 : rTrans (embA d.B.d d.B.o (d.a₀ * d.a)) (rTrans d.b (T v)) =
        rChi W d.k • rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v) := by
      funext g
      simp only [rTrans, Pi.smul_apply, smul_eq_mul]
      rw [mul_assoc g, hP.eq]
      refine Eq.trans (congrArg (T v) ?_) (lev_multT hT v hP.lev
        (g * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) : GA D (D.sp.Y 0)))
      change g * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS) * d.k)) =
        g * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) * d.k
      rw [mul_assoc g, mul_assoc ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))]
    have ea : rTrans (d.a₀ * d.a) (fun g => d.B.colForm C.1 (ξ y) (g * (d.a₀ * d.a)⁻¹)) = d.B.colForm C.1 (ξ y) := by
      funext g; simp only [rTrans, mul_inv_cancel_right]
    have hsh := GlobalTheory.Core.Mi.per_rTrans D W.Q.Rl.ψ D.R.rS d.B.lev (fun g => d.B.colForm C.1 (ξ y) (g * (d.a₀ * d.a)⁻¹))
      (rTrans d.b (T v)) (d.a₀ * d.a) hψ (contAut_rTrans _ (hcont C (ξ y))) (contAut_rTrans _ (contAut_multT hT v))
    rw [ea] at hsh
    unfold BotDat.per
    rw [e1, ← hsh, ← per_smul_f]
    exact congrArg _ e2
  refine ⟨R, ?_⟩
  intro φ φ' T hT T' hT' α α' hrel v C C' b b' hC hC' hb hb'

  have hrelξ : ∀ y v, α * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C.1 (ξ y))
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v)) +
      α' * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C'.1 (ξ y))
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T' v)) = 0 := by
    intro y v
    have h0 := hrel y v
    rw [L1 φ C hC T hT, L1 φ' C' hC' T' hT'] at h0
    refine (mul_eq_zero.1 ?_).resolve_left (hχ _ hP.lev)
    rw [← h0]; ring

  have hrelAll : ∀ ξ' v, α * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C.1 ξ')
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v)) +
      α' * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C'.1 ξ')
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T' v)) = 0 := by
    intro ξ' v
    have hmem : ξ' ∈ Submodule.span ℂ (Set.range ξ) := by rw [hξspan]; exact Submodule.mem_top
    obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
    have hlin : ∀ C₁ : Cu W.S.X u W.S.Y.hK, d.B.colForm C₁.1 ξ' = ∑ i ∈ cf.support, cf i • d.B.colForm C₁.1 (ξ i) := by
      intro C₁
      rw [← hcf]
      funext g
      simp only [SBes.colForm, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
    rw [hlin C, hlin C',
      GlobalTheory.SeeSaw.perSum_all D W.Q.Rl.ψ hψ D.R.rS d.B.lev _ (contAut_rTrans _ (contAut_multT hT v)) _ cf.support cf
        (fun i => d.B.colForm C.1 (ξ i)) (fun i _ => hcont C (ξ i)),
      GlobalTheory.SeeSaw.perSum_all D W.Q.Rl.ψ hψ D.R.rS d.B.lev _ (contAut_rTrans _ (contAut_multT hT' v)) _ cf.support cf
        (fun i => d.B.colForm C'.1 (ξ i)) (fun i _ => hcont C' (ξ i)),
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := hrelξ i v
    linear_combination cf i * this

  have hσ : ∀ y : W.S.X.B.I.Ginf, ∃ σ : SmT (W.Q.Rl.MY 0) →ₗ[ℂ] SmT (W.Q.Rl.MY 0), ∀ T ∈ ThetaLiftSpaceZero W, ∀ x,
      T (σ x) = rTrans ((iotaX W.S.X W.Q.instEq).symm (y, 1)) (T x) := by
    intro y
    obtain ⟨σ, hσ⟩ := GlobalTheory.RealTransSm.rTrans_eq_map D W.Q.Rl.θ (D.sp.Y 0) _ (W.Q.Rl.MY 0) hθ
      ((iotaX W.S.X W.Q.instEq).symm (y, 1))
      ((hRS.2.1 _).2 (congrArg Prod.snd ((iotaX W.S.X W.Q.instEq).apply_symm_apply (y, 1))))
    exact ⟨σ, fun T hT x => hσ (rJ W) (rChi W) T hT x⟩
  choose σ hσ using hσ
  have hpt : ∀ T ∈ ThetaLiftSpaceZero W, ∀ v (y : W.S.X.B.I.Ginf),
      (fun g => evS W.S.X W.Q.instEq (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T v)
        (iotaX W.S.X W.Q.instEq g * (y, W.S.X.xu u))) =
      rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T (σ y v)) := by
    intro T hT v y
    funext g
    rw [hσ y T hT v]
    simp only [evS, rTrans]
    exact congrArg (T v) (shift_swap (iotaX W.S.X W.Q.instEq).toMulEquiv g _ y (W.S.X.xu u) hf1)

  obtain ⟨φL, hφL, rfl⟩ := hb
  obtain ⟨φL', hφL', rfl⟩ := hb'
  rw [hc C _ φL (GlobalTheory.Core.Mi.rowFun_evS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (rJ W) (rChi W) _ hθ hMt T hT v).1 hφL,
    hc C' _ φL' (GlobalTheory.Core.Mi.rowFun_evS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (rJ W) (rChi W) _ hθ hMt T' hT' v).1 hφL']
  refine comb_integral _ c α α' _ _ fun y => ?_
  refine Eq.trans ?_ (hrelAll (W.S.X.Wu u y) (σ y v))
  exact congrArg₂ (fun p q => α * p + α' * q) (congrArg (d.B.lev.per W.Q.Rl.ψ _) (hpt T hT v y))
    (congrArg (d.B.lev.per W.Q.Rl.ψ _) (hpt T' hT' v y))

end
