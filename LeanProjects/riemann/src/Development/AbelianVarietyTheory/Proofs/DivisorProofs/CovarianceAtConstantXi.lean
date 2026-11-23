import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfOnto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfCore
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelOfLinearMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataPinnedForms

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtIdCore

theorem exists_scalar_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W), ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0' → GlobalTheory.PtId.IoAt O (v₀ i (sg0 D A)) ka := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT hI i c0L
  by_cases hex : ∃ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup),
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) ∧ CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0'
  swap
  · exact ⟨1, norm_one, fun Tp tup O h1 h2 => absurd ⟨Tp, tup, O, h1, h2⟩ hex⟩
  obtain ⟨Tp₀, tup₀, O₀, hP₀, hB₀⟩ := hex
  obtain ⟨ka₀, hn₀, hk₀⟩ := GlobalTheory.AdTh.PhaseMap.io_eq_phase_smul_ofCore D G Pl0 T0 A T R F κ v₀ hC hT hI i Tp₀ tup₀ O₀ hP₀
  refine ⟨ka₀, hn₀, fun Tp tup O hP hB => ?_⟩
  obtain ⟨ka, -, hk⟩ := GlobalTheory.AdTh.PhaseMap.io_eq_phase_smul_ofCore D G Pl0 T0 A T R F κ v₀ hC hT hI i Tp tup O hP
  intro lt hlt u hu
  suffices h : ka = ka₀ by
    subst h
    exact hk lt hlt u hu
  have e1 := hk lt hlt u hu A.μ0 O.hw
  have e2 := hk₀ lt hlt u hu A.μ0 O₀.hw
  obtain ⟨hw1, cga, -, hinj, -, -, -, -, hio, -⟩ := hP.io
  obtain ⟨hw2, cga', -, -, -, -, -, -, hio₀, -⟩ := hP₀.io
  have hne : O.io O.hw ≠ 0 := by
    intro h0
    have h1 : O.hw = 0 := hinj (h0.trans (map_zero _).symm)
    have h2 := (GlobalTheory.AdTh.coefMap_norm_equivariant_basis_ofCore D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup O hP).1
    rw [h1, map_zero, norm_zero] at h2
    exact zero_ne_one h2
  rw [GlobalTheory.PtId.OneScalar.coefficientMap_extremalTensor_baseChange O hw1 hB] at e1
  rw [GlobalTheory.PtId.OneScalar.coefficientMap_extremalTensor_baseChange O₀ hw2 hB₀, hio₀, GlobalTheory.PtId.OneScalar.map_pG_eq O₀.c' O.c' (inC O₀.c') (inC O.c'), ← hio, e1] at e2
  have hV := hP.lift.std
  obtain ⟨f1, f2, f3, f4, f5⟩ := GlobalTheory.AdTh.VecFock.vec_fock_ofCore D G Pl0 T0 A T.Q.c.F R F hC i A.μ0 hV
  have hON : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ => by
    refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩
    · simp [gramAt, hV.1]
    · simp
  have hinjP := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) (hC.thP.ωP i A.μ0).std hC.models.inf
    (fun _ => 1) (fun _ => 1) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) _ f4 f3 hON f5
    (D.sp.V_sig _) (D.sp.W_sig _) (R.vP i A.μ0) f1 f2 (GlobalTheory.AdTh.VecNe.thetaVector_ne_zero_of_core D G Pl0 T0 A T.Q.c.F R F hC i hV)
  have hlti : Function.Injective lt := GlobalTheory.PtId.OneScalar.lt_injective (fun ρ => hT.laws.pins.1.2.2.2 ρ) lt hlt
  refine smul_left_injective ℂ (fun h0 => hne ?_) e2
  have h1 := hinjP (h0.trans (map_zero _).symm)
  have h2 := MvPolynomial.rename_injective lt hlti (h1.trans (map_zero _).symm)
  exact MvPolynomial.map_injective _ (inC O.c').injective (h2.trans (map_zero _).symm)

open GlobalTheory.AdTh.CoverVal in

theorem covAt_of_xiConst_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ c0 : ℂ, GlobalTheory.OneMapTuples.XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 → GlobalTheory.PtId.CovAt O c0 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i Tp tup O hO c0 hc
    t X g bas idx e k xk mk hX hp hs hi hL hxk hmk hk y₂ A₂ hA₂
  obtain ⟨hU, hW, g', e', F', ik, φ, th, hth, hD, hval⟩ := hc t
  obtain ⟨hlev, hA, -⟩ := hO.cov t
  obtain ⟨hX₀, hon₀, -, hp₀, -, -, h1, -, hΨ₀, -⟩ := GlobalTheory.AdTh.models_at_record_ofCore D G Pl0 T0 A T R F κ v₀ hR hT i O.s0
    (sOv_eq _ _ _) (T.dict _ O.s0 1).1
  have hσ : GoodEmb (O.dδ t).c₂ ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)) := rfl
  have hmod : ∀ j, IsMod (Wc D i) (rank_Wc i) ((O.U₂ t).X j) := fun j =>
    isMod_of _ _ _ (hW j) fun ρ => ((hU.2.1 j).2 _).2 ((hΨ₀ _).1 ((hX₀.psi _).2 ⟨ρ, rfl⟩))
  have hor : ∀ j, IsOrthogonalFrame ((O.U₂ t).X j) (T.x₀ ((i : ℕ) + 1) O.s0) := fun j τ hτ => by
    have hsp := sameSp_of (hmod j) hX₀ ((hU.2.1 j).1.trans hp₀.symm)
    rw [hsp.gm, hsp.p0]
    exact hon₀ ⟨τ, hsp.psi ▸ hτ⟩
  obtain ⟨Wt⟩ := nonempty_uw ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU)
  obtain ⟨hon, γ, ⟨hγ, hl, hf⟩, hma, -⟩ := GlobalTheory.AdTh.dict_atComp_markAd D _ _ _ _ _ _ _ (O.U₂ t) hσ hU h1 hA R.θ (Wc D i)
    (rank_Wc i) (O.dict₂ t) (iotaW T i) g' e' F' ik φ th _ hR.models.inf hmod hor hth hD Wt k
  obtain ⟨hd, hpt⟩ := point_eq (Formalism.L2.PjFree.Unf.ofPj (O.U₂ t)) hσ hU h1 hA hR.models.inf (Wc D i) (rank_Wc i) (iotaW T i)
    _ Wt (O.dict₂ t k).1 (O.dict₂ t k).2 γ k hγ (hmod _) hl hf hon hma X g bas idx e mk hX hp hs hi hL hmk hk y₂ A₂ hA₂
  obtain ⟨γ', hγ', h2, h3, -⟩ := hD.2 k
  obtain ⟨-, -, hrat, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
  obtain ⟨a, ha⟩ := hrat γ' hγ'
  have hv := hval k γ' ⟨hγ', h2, h3⟩
  rw [(hO.tuple t).xi _ _ (hmul _ _ _ _ ha hxk), map_mul, (hR.lev.xi (tup t)).1.2 a, _root_.one_mul] at hv
  exact (evR_eq_of_point _ hlev.2.2.2.2.2.2.2.1 _ y₂ hpt).trans ((dif_pos hd).symm.trans hv)

set_option maxHeartbeats 2000000 in
open Formalism.L2.DIV GlobalTheory.OneMapTuples GlobalTheory.PtId in

theorem point_identity_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → IoExt R → ∀ (i : Fin D.R.m) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ (lam : AutQ (Wc D i) → ℂ) (z : G), (∀ q, lam q ≠ 0) ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F → O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → O.lev = lev → CoefficientBaseChange R i O.jL (inC O.c') (c0L i) O.c0' → ∀ c0 : ℂ, XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 → PtIdent O (κ i) lam z c0 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ _ ⟨tie⟩ _ hio i lev gramR c0R c0L _
  have hT : TieIn T R κ v₀ := ⟨tie.laws, tie.alg_eq, tie.kap, tie.hv₀, tie.chiR, tie.x0⟩
  by_cases hex : ∃ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)
  swap
  · exact ⟨fun _ => 1, 1, fun _ => one_ne_zero, fun Tp tup O _ hP => absurd ⟨Tp, tup, O, hP⟩ hex⟩
  obtain ⟨Tp₀, tup₀, O₀, hP₀⟩ := hex
  obtain ⟨ka, hka1, hka⟩ := exists_scalar_core D G Pl0 T0 A T R F κ v₀ hC hT hio i (c0L i)
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.AdTh.CcEx.exists_ccIs_ofCore GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R F κ v₀ hC hT i Tp₀ tup₀ O₀ hP₀
  have hs₀ : O₀.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨hemb, hiso, -⟩ := dict_cast T hT.laws _ (inR i) O₀.s0 (hs₀ ▸ T.toCore.good_σ₀) (Wc D i) O₀.hV (rank_Wc i)
  obtain ⟨δ, hδ⟩ := GlobalTheory.AdTh.ShortSeries.thetaKO_eq_short_series_ofCore D G Pl0 T0 A _ R F hC i hP₀.lift.std _ _ (iotaW T i) hemb hiso
  refine ⟨fun q => cmpConst D ka δ (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) * c₀ (O₀.dict q.out).1, 1, fun q => ?_, ?_⟩
  · exact mul_ne_zero (cmpConst_ne_zero (norm_ne_zero_iff.1 (hka1 ▸ one_ne_zero)) _ _)
      (norm_ne_zero_iff.1 (hc₀.1 _ ▸ one_ne_zero))
  intro Tp tup O _ hP _ hbc c0 hxi t
  obtain ⟨cst, hcst, hceq⟩ := ccIs_transport (hs₀.trans (sOv_eq _ O.c' O.hle).symm) O₀.hV O.hV hc₀
  refine ⟨1, one_mem _, ⟨1, Nat.one_pos, one_pow _⟩, fun x hx f hf hcl q => ?_⟩
  obtain ⟨h, J', hR, -, hA, hPl⟩ := (hP.tuple t).reps
  obtain ⟨x₀, hx₀⟩ := (hPl x).1 hx
  have hL := hP.act.2
  have h1 : actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) O.c' O.lev2 1 f = f :=
    actL_one _ _ _ hL.total hL.func hL.one hf.1
  have h2 := exact_identity_ofCore hC hT O hP (hka Tp tup O hP hbc) hδ
    (covAt_of_xiConst_core D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup O hP c0 hxi) hcst t h J' hR _ x hx₀ f hcl q.out
  rw [rdQ, h1, hA _ x hx₀, one_mul]
  exact h2.trans (congrArg (fun z => _ * z * _) (hceq q.out))

end GlobalTheory.PtIdCore
