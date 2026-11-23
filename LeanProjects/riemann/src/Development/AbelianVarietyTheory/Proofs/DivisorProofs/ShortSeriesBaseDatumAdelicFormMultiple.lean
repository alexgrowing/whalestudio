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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShortSeriesTranslateFrameConstantMultipleStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section
namespace GlobalTheory.ExactBase

set_option maxHeartbeats 2000000 in

theorem adForm_cuspTo_eq {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : Full D} [Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F} (F : Face D A) {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T) (hU : R.LUnif) (i : Fin D.R.m)
    (w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (hw : ∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ)
    (F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (g : GA D (Wc D i)) :
    adForm R i (cuspTo hT.p fw i F₀) (fun ρ => w ρ) g =
      (lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) (F₀.1 : T.R ((i : ℕ) + 1)) g := by
  have hb := GlobalTheory.IndefiniteRowSideFullHecke.LatticePartsOverBalls.base_of_tie (T := T.J) (R := R) (κ := κ) (v₀ := v₀) (i := i) fw
  have hso : (O i).s0 = res T.J (sg0 D A) := (sOv_eq T.J.toCore (O i).c' (O i).hle).trans hb.1.symm
  have hev := GlobalTheory.evaluates_of_unif D G Pl0 T0 A T.J R F κ v₀ fw hU i (sg0 D A) hb.2.1 hb.2.2
  have hvw : (fun ρ => (w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) := funext hw
  refine Eq.trans ?_ (phi_cE T.J R O i (wtA (κ i)) _ g).symm
  have e := congrFun (hev (Submodule.inclusion (cutR_le T.J.toCore.C ((i : ℕ) + 1) (κ i)) F₀)) g
  refine Eq.trans ?_ (e.trans (congrFun (GlobalTheory.LiftRatObj.phiC_congr T.J hso.symm hb.2.2 (O i).hV _ _) g))
  simp only [adForm, cuspTo, cutTo, hvw, evAt]
  rfl

end GlobalTheory.ExactBase

noncomputable section
namespace GlobalTheory.ExactBase

open GlobalTheory.PtId GlobalTheory.AdTh in
set_option maxHeartbeats 4000000 in

theorem consts_core {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : Full D} [Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F} {F : Face D A} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T)
    (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (hOP : OMPins T.J R κ v₀ O i) (hU : R.LUnif) (hI : IoExt R) (hRow : OneMapRow0 T.J R κ v₀ O i)
    (hPh : PhaseTie T.J R κ v₀ O (fun _ => 1) i) (hSp : GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i)) :
    ∃ (cc : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ka : ℂ) (δ : ℤˣ) (c0 : ℂ),
      CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc ∧
      IoAt (O i) (v₀ i (sg0 D A)) ka ∧ ClsAt R i (iotaW T.J i) δ ∧ CovAt (O i) c0 ∧ ‖ka‖ = 1 ∧ ‖c0‖ = 1 ∧
      ∃ z ∈ Subgroup.center G, ∃ (ζ : D.what₂.LL) (n : ℕ), 0 < n ∧ ζ ^ n = 1 ∧
        ∀ f ∈ T.J.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ g,
          (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹) • cc) f g =
            D.what₂.embLL ζ * (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) (actLev T.J.toCore.Q.c (O i).lev2 z f) g := by
  have hTi : TieIn T.J R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hP := hOP.2
  obtain ⟨cc, hcc⟩ := GlobalTheory.AdTh.CcExCore.exists_ccIs_core GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T.J R F κ v₀ hC hTi i Unit (fun _ => A.μ0) (O i) hP
  have hs : (O i).s0 = T.J.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨h1, h2, -⟩ := GlobalTheory.PtId.dict_cast T.J hTi.laws _ (inR i) (O i).s0 (hs ▸ T.J.toCore.good_σ₀) (Wc D i) (O i).hV (rank_Wc i)
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.thetaKernel_oneClass_eq_classicalShortSeries D G Pl0 T0 A _ R F hC i hP.lift.std _ _ (iotaW T.J i) h1 h2
  obtain ⟨ka, hka, hio⟩ := GlobalTheory.T.fockCoefficientMap_extremal_eq_phase_smul_letters D G Pl0 T0 A T.J R F κ v₀ hC hTi hI i Unit (fun _ => A.μ0) (O i) hP
  obtain ⟨c0, hc0, hcov⟩ := GlobalTheory.AdTh.CoverVal.cover_value_core D G Pl0 T0 A T.J R F κ v₀ hC hTi i Unit (fun _ => A.μ0) (O i) hP
  have hd : ‖((δ : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or δ with rfl | rfl <;> simp
  have hu : ‖ka * (-((δ : ℤ) : ℂ)) ^ degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹‖ = 1 := by
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_inv, hka, hc0, hd]
    simp
  have hser : SerOf (O i) (κ i) (v₀ i (sg0 D A)) ((ka * (-((δ : ℤ) : ℂ)) ^ degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹) • cc) 1 := by
    refine ⟨fun k => ?_, norm_one, fun t h J' hrep y x hpl f _ hf g => ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul, norm_mul, hu, hcc.1 k, one_mul]
    have hne : c0 ≠ 0 := norm_ne_zero_iff.1 (hc0 ▸ one_ne_zero)
    have hx : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
    have key := GlobalTheory.AdTh.SerCore.exact_identity_core hC hTi (O i) hP hio hδ hcov hcc t h J' hrep y x hpl f hf g
    refine mul_left_cancel₀ hne ?_
    rw [one_mul, key, GlobalTheory.AdTh.SerCore.lieFac_eq_sqrt_pow _ hx, GlobalTheory.AdTh.SerCore.serConst, Pi.smul_apply, smul_eq_mul, neg_pow]
    have hre : rdU (GlobalTheory.PtId.unfO (O i)) f ((O i).dict g).1 ((O i).dict g).2 =
        rdU (unfBC (O i).hle (T.J.U ((i : ℕ) + 1)) (inC (O i).c')) f ((O i).dict g).1 ((O i).dict g).2 := rfl
    rw [hre]
    generalize rdU (unfBC (O i).hle (T.J.U ((i : ℕ) + 1)) (inC (O i).c')) f ((O i).dict g).1 ((O i).dict g).2 = z
    rw [Complex.ofReal_pow, Complex.ofReal_inv]
    generalize ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ GlobalTheory.PtId.degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) = s
    have e : c0 * c0⁻¹ = 1 := mul_inv_cancel₀ hne
    linear_combination (-(ka * ((-1) ^ GlobalTheory.PtId.degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * ((δ : ℤ) : ℂ) ^ GlobalTheory.PtId.degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) * cc ((O i).dict g).1 * s * (O i).mu g * z)) * e
  obtain ⟨z, hz, ζ, n, hn, hζ, hrel⟩ := GlobalTheory.OnCmp.const_upTo_center D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hU hI hRow hPh hSp cc hcc _ hser
  exact ⟨cc, ka, δ, c0, hcc, hio, hδ, hcov, hka, hc0, z, hz, ζ, n, hn, hζ, hrel⟩

end GlobalTheory.ExactBase

namespace GlobalTheory.ExactBase

set_option maxHeartbeats 4000000 in

theorem short_series_base : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P ((F₀).1 : T.R ((i : ℕ) + 1)) → adForm R i (cuspTo hT.p fw i F₀) (fun ρ => w ρ) = D.what₂.embLL c • singleSeries R i ω φ' h ((O i).c0' y) w := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hOP hβ hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h hSB hLa N x₀ P y hUm hTb hTd hLev hAdm hPh' hio
  obtain ⟨cc, ka, δ, c0, hcc, hka, hδ, hcov, hka1, hc01, z, hz, ζ, n, hn, hζ, hrel⟩ :=
    consts_core fw O hT hC i hOP hU hIo hRow hPh hSp
  obtain ⟨y₀, c, hrk, hint, hmain⟩ := GlobalTheory.T.centralShortSeriesTranslate_frameConstant_multiple D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hβ hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h hSB hLa N x₀ P y hUm hTb hTd hLev hAdm hPh' hio cc ka δ c0 hcc hka hδ hcov hka1 hc01 z hz
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hζ
    exact zero_ne_one hζ
  have hζI : IsIntegral ℤ ζ := IsIntegral.of_pow hn (hζ ▸ isIntegral_one)
  have hζi : IsIntegral ℤ ζ⁻¹ := by
    have e : ζ⁻¹ = ζ ^ (n - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hζ0, ← pow_succ, Nat.sub_add_cancel hn]
      exact hζ
    rw [e]
    exact hζI.pow _
  refine ⟨y₀, ζ⁻¹ * c, hrk, fun lam hlam => ?_, fun φ' hφ' w hw F₀ hF₀ => ?_⟩
  · obtain ⟨s, hs, hsi⟩ := hint lam hlam
    refine ⟨s, hs, ?_⟩
    rw [mul_left_comm]
    exact hζi.mul hsi
  funext g
  have hP := hOP.2
  have hmem : (F₀.1 : T.J.R ((i : ℕ) + 1)) ∈ T.J.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n :=
    (Submodule.inclusion (cutR_le T.J.toCore.C ((i : ℕ) + 1) (κ i)) F₀).2
  have hn' : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have hf := hmem
  rw [hn'] at hf
  have hnat := ((mem_cusp _ _ _ _ _ _).1 hf).1.1
  obtain ⟨k, hk, -⟩ := hP.lift.lev z⁻¹
  have hE := (hPh hRow).1
  have hfm := (hE z⁻¹ k hk _ hmem).1
  have e2 := hrel _ hfm g
  have hinv : actLev T.J.toCore.Q.c (O i).lev2 z (actLev T.J.toCore.Q.c (O i).lev2 z⁻¹ (F₀.1 : T.J.R ((i : ℕ) + 1))) =
      (F₀.1 : T.J.R ((i : ℕ) + 1)) := by
    refine (actL_mul _ _ _ hP.act.1.total hP.act.1.func hP.act.1.mul z z⁻¹ hnat).symm.trans ?_
    rw [mul_inv_cancel]
    exact actL_one _ _ _ hP.act.1.total hP.act.1.func hP.act.1.one hnat
  replace e2 := e2.trans (congrArg (fun f => D.what₂.embLL ζ * (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) f g) hinv)
  have e1 := adForm_cuspTo_eq F fw O hT hU i w hw F₀ g
  have e3 := hmain φ' hφ' w hw F₀ hF₀ g
  rw [e2] at e3
  have hz0 : D.what₂.embLL ζ ≠ 0 := (map_ne_zero _).2 hζ0
  rw [e1, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
  field_simp
  linear_combination e3

end GlobalTheory.ExactBase
