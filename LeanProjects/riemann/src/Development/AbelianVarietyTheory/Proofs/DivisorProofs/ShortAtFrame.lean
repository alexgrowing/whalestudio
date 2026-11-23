import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseRatAtOfPhaseOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicLiftEqGeometricClassSumAllTuples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstUpToCenter
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import Development.AbelianVarietyTheory.Definitions.Divisors.ReadsOnlyOmegaFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulEqOfHatCNeZeroOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTwistBaseOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfRhoEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortValueAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleSeriesEqPhaseThetaKO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegralStandardStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section
namespace GlobalTheory.FrameShort

open GlobalTheory.PtId GlobalTheory.AdTh in
set_option maxHeartbeats 4000000 in

theorem short_at_frame : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (cc : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ka : ℂ) (δ : ℤˣ) (c0 : ℂ), GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → GlobalTheory.PtId.ClsAt R i (iotaW T.J i) δ → GlobalTheory.PtId.CovAt (O i) c0 → ‖ka‖ = 1 → ‖c0‖ = 1 → ∀ c0' : ℂ, c0' * c0⁻¹ ∈ D.what₂.embLL.range → (∃ m : ℕ, 0 < m ∧ (c0' * c0⁻¹) ^ m = 1) → (∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.ThFr.IsSympl X bas → GlobalTheory.AdTh.IdxIs T.Q.c (O i).s0 X idx e → GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → GlobalTheory.Dict.IsMark (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk → GlobalTheory.AdTh.MarkAd (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) (rank_Wc i) (iotaW T.J i) k mk → letI : Algebra (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ := ((O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)).toAlgebra; ∀ (y₂ : FrPt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ ℂ) (A₂ : GlobalTheory.Dict.AnFib X bas idx e (GlobalTheory.AdTh.frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.J.x₀ ((i : ℕ) + 1) (O i).s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).cδ y₂ = c0' * ((χ xk : Circle) : ℂ)) → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P ((F₀).1 : T.R ((i : ℕ) + 1)) → ∀ g : GA D (Wc D i), (lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ GlobalTheory.PtId.degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹) • cc) ((F₀).1 : T.R ((i : ℕ) + 1)) g = D.what₂.embLL c * singleSeries R i ω φ' h ((O i).c0' y) w g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hOP hβ hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h hSB hLa N x₀ P y hUm hTb hTd hLev hAdm hPh' hio cc ka δ c0 hcc hka hδ hcov hka1 hc01 c0' hρ hρm hcT
  have hTi : TieIn T.J R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hP := hOP.2
  have hs : (O i).s0 = T.J.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.J.Q.c (O i).s0 := hs ▸ T.J.toCore.good_σ₀
  have hmod := models_at_record_core D G Pl0 T0 A T.J R F κ v₀ hC hTi i (O i).s0 hs
  obtain ⟨hemb, hisom, hroot, hmk⟩ := dict_cast T.J hTi.laws _ (inR i) (O i).s0 hσ (Wc D i) (O i).hV (rank_Wc i)
  obtain ⟨δ', hδ'⟩ := GlobalTheory.AdTh.ShortSeriesTw.thetaKO_eq_short_series_tw D G Pl0 T0 A _ R F hC i hP.lift.std _ _ (iotaW T.J i) hemb hisom
  obtain ⟨y₀, ζ, φc, hrk, hζL, hζm, hhat, hphi, hhalf, hbadP⟩ := GlobalTheory.CoverDatum.datum_eq_hat_free D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hβ v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK x₀ hAdm
  obtain ⟨hGf, e, Ps, he, hPs0, hsupp⟩ := hSB
  have hPs : ∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP hm =>
    hPs0 PP hPP (by rw [Nat.cast_mul]; exact PP.asIdeal.mul_mem_right _ hm)
  have hPsO : ∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP hm =>
    hPs0 PP hPP (by rw [Nat.cast_mul]; exact PP.asIdeal.mul_mem_left _ hm)
  obtain ⟨yd, hyd⟩ := exists_isDetAt he (Vc D i) h
  obtain ⟨c1, hc1, hint1⟩ := GlobalTheory.T.twisted_kernel_class_scalar_integral_standard D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h N hUm hTb hTd hLev hLa e Ps yd hGf he hPs hPsO hsupp hyd
  obtain ⟨ρ, hρ'⟩ := hρ
  obtain ⟨ζL, hζL'⟩ := hζL
  have hρm' : ∃ m : ℕ, 0 < m ∧ ρ ^ m = 1 := by
    obtain ⟨m, hm, hm1⟩ := hρm
    refine ⟨m, hm, D.what₂.embLL.injective ?_⟩
    rw [map_pow, hρ', hm1, map_one]
  have hζm' : ∃ m : ℕ, 0 < m ∧ ζL ^ m = 1 := by
    obtain ⟨m, hm, hm1⟩ := hζm
    refine ⟨m, hm, D.what₂.embLL.injective ?_⟩
    rw [map_pow, hζL', hm1, map_one]
  have hroot_int : ∀ z : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → IsIntegral ℤ z ∧ IsIntegral ℤ z⁻¹ := by
    rintro z ⟨m, hm, hz⟩
    have hzI : IsIntegral ℤ z := IsIntegral.of_pow hm (hz ▸ isIntegral_one)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne'] at hz
      exact zero_ne_one hz
    refine ⟨hzI, ?_⟩
    have e : z⁻¹ = z ^ (m - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hz0, ← pow_succ, Nat.sub_add_cancel hm]
      exact hz
    rw [e]
    exact hzI.pow _
  set d := degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) with hd
  refine ⟨y₀, ((((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ) : D.what₂.LL) * ρ * ζL⁻¹ * c1, hrk, fun lam hlam => ?_, ?_⟩
  · obtain ⟨s, hs, hsi⟩ := hint1 lam hlam
    refine ⟨s, hs, ?_⟩
    have e : (s : D.what₂.LL) * (((((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ) : D.what₂.LL) * ρ * ζL⁻¹ * c1) =
        ((((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ) : D.what₂.LL) * ρ * ζL⁻¹ * ((s : D.what₂.LL) * c1) := by ring
    rw [e]
    exact (((isIntegral_algebraMap (R := ℤ) (x := (((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ))).mul (hroot_int ρ hρm').1).mul
      (hroot_int ζL hζm').2).mul hsi
  intro φ' hφ' w hw F₀ hF₀ g
  have hU' : IsUnf (T.J.U ((i : ℕ) + 1) (O i).s0) := hTi.laws.unf _ (inR i) (O i).s0 hσ
  obtain ⟨hX, hon, hinv, hp, hrk', hpq, h1, hrt, -, hbas, hD, -⟩ := hmod ((O i).dict g).1
  obtain ⟨hx, g', Dc, γ, mk, vv, ϑ, κ', B, hat, hsd, hm, hBm, hma, hϑ, hvv, hκ, hrd⟩ :=
    exists_point (T.J.U ((i : ℕ) + 1) (O i).s0) hσ hU' h1 hTi.laws.pins.2.1.2 R.θ (Vc D i) (Wc D i) (rank_Wc i) (O i).dict
      (iotaW T.J i) (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (fun Wt k => hmk R.θ hC.models.inf (fun k => (hmod k).1) h1 Wt k)
      (wtA (κ i)) hD (O i).mu (R.ωP i A.μ0) (R.vacP i) cc hcc g
  obtain ⟨hγ, hΛ, hfr⟩ := hat
  obtain ⟨xk, hxk⟩ := hroot (γ * g)
  have hζ0 : ζ ≠ 0 := by
    obtain ⟨m, hm, hm1⟩ := hζm
    rintro rfl
    rw [zero_pow hm.ne'] at hm1
    exact zero_ne_one hm1
  letI : Algebra T.Q.c.F ℂ := (O i).s0.toAlgebra
  obtain ⟨mk₂, Y, hm₂, ha₂, hY, hgeo⟩ := GlobalTheory.ShortPtVal.short_value_at_point D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP χ c0' hcT Λ N x₀ P hUm hTb hTd hLev hAdm
    hPh' ζ φc hζ0 hhat F₀.1 hF₀ _ g' Dc (γ * g) xk hxk hX hp hΛ hsd _ hx hfr mk hm hma vv ϑ κ' hvv hκ _ B hBm hϑ
  obtain ⟨vr, hvr⟩ := exists_isVarOf (Vc D i) (Wc D i) (rank_Wc i) _ hX _ Dc.hr
  have hCs := GlobalTheory.AdTh.VecSeries.singleSeries_eq_phase_thetaKO D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hIo χ ω hK.weil _ _ φ' hφ' ka hka P y hio _ g' Dc vr hX hp hvr h w hw g γ hγ
  have htw := GlobalTheory.OnCmp.weil_twist_base_of D G Pl0 T0 A _ R F hC i χ ω hK.weil (γ * g) xk hxk (R.vacP i) (hC.thP.vP i A.μ0).1.2.theta
  have hrd' : Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) ((T.J.U ((i : ℕ) + 1) (O i).s0).X ((O i).dict g).1) Dc.bas Dc.idx
      (ω (1, γ * g) (R.vacP i)) ((((χ xk : Circle) : ℂ) * (cc ((O i).dict g).1 * (O i).mu g * κ')) • vv) ((O i).dict g).2 := by
    obtain ⟨s1, s2⟩ := ((thA_heis_entire_linear_injective _ _ g' _ _ Dc.bas Dc.idx Dc.sympl hD.2 _ hx _ hrd.1).2.2 vv hvv.1).1
      ((χ xk : Circle) : ℂ) 0
    rw [zero_smul, add_zero, smul_smul] at s1 s2
    rw [zero_smul, add_zero] at s2
    refine ⟨s1, fun z hz => ?_⟩
    rw [htw, s2, Pi.smul_apply, Pi.smul_apply, hrd.2 z hz, smul_eq_mul, smul_eq_mul]
    ring
  have hH := hPh'.1
  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)).IsHomogeneous d :=
    ((isHomogeneous_of_rowDeg _ _ _ _ hH.2.2).map _).rename_isHomogeneous
  have hser := hδ' χ _ _ ω φ' hK.weil _ hK.chr hK.fin hK.ram hK.pl (GlobalTheory.OnCmp.readsOnly_omegaFree R i _ ξR y₀) hφ' _ φc hphi
    hhalf hrt g' _ _ Dc.hr Dc.bas Dc.idx _ vr hX Dc.sympl hon hinv (hbas _) hvr
    (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) N h (γ * g) Λ mk₂ e Ps yd hbadP he hPs hGf hsupp hyd hLa hTd hLev ha₂
    Y (hΛ ▸ hY) vv _ (hΛ ▸ hvv) (hfr ▸ hrd') _ d hhom
  rw [hΛ, ← hfr] at hser
  have hx0 : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hrdU : rdU (T.J.U ((i : ℕ) + 1) (O i).s0) (F₀.1 : T.R ((i : ℕ) + 1)) ((O i).dict g).1 ((O i).dict g).2 = _ :=
    (dif_pos hx).trans hgeo
  have hphiE : (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ d * c0⁻¹) • cc) (F₀.1 : T.R ((i : ℕ) + 1)) g =
      ((ka * (-((δ : ℤ) : ℂ)) ^ d * c0⁻¹) * cc ((O i).dict g).1) * (O i).mu g *
        rdU (T.J.U ((i : ℕ) + 1) (O i).s0) (F₀.1 : T.R ((i : ℕ) + 1)) ((O i).dict g).1 ((O i).dict g).2 := rfl
  have hSS := hCs.trans (congrArg (fun z => ka * z) hser)
  rw [hphiE, hrdU, hSS, GlobalTheory.AdTh.SerCore.lieFac_eq_sqrt_pow _ hx0, ← hc1]
  simp only [map_mul, map_inv₀, map_intCast, hρ', hζL']
  have hδ2 : ((δ' : ℤ) : ℂ) ^ d * ((δ' : ℤ) : ℂ) ^ d = 1 := by
    rw [← mul_pow]
    rcases Int.units_eq_one_or δ' with e | e <;> rw [e] <;> simp
  push_cast
  have alg : ∀ (s ka δc δc' c0 c0' k m x c1 a b q κ' ζ TH : ℂ) (n : ℕ), δc' ^ n * δc' ^ n = 1 →
      s ^ n * (ka * (-δc) ^ n * c0⁻¹ * k * m * (c0' * x * (c1 * (a * b * q) * κ' * ζ⁻¹ * TH))) =
        (δc * δc') ^ n * (c0' * c0⁻¹) * ζ⁻¹ * c1 * (ka * (δc' ^ n * (-1) ^ n * s ^ n * (x * (k * m * κ')) * (a * b) * q * TH)) := by
    intro s ka δc δc' c0 c0' k m x c1 a b q κ' ζ TH n hn
    rw [neg_pow, mul_pow]
    linear_combination (-(s ^ n * ka * (-1) ^ n * δc ^ n * c0⁻¹ * k * m * c0' * x * c1 * a * b * q * κ' * ζ⁻¹ * TH)) * hn
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hδ2

end GlobalTheory.FrameShort
