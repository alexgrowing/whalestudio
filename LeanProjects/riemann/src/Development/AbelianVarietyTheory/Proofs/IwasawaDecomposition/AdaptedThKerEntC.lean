import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormNatCastEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdOfMemSupport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntryHypOfTrueColumnChoicesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DtTiedTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelDetAdelicOfPinned
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoThreeOfOfDeterminantCharacterFiniteOrderType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowEqSpanNormOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelCharactersEqReference

noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

theorem mtType_of_hecke {D : D7} {C : CharFrame D} (Dt : DtTied D C) (ξ : HChar D.host.E) {n : ℕ} (hn : 0 < n) (hord : ξ.OrderDvd n)
    (mt : ℕ → D.Dt →* ℂˣ) (h : ∀ (j : Fin D.R.m) a, IsFinIdele a → mt (j.1 + 1) (Dt.eDt a) = (C.mu0 j * ξ).1 a) (u : D.what₂.Word) :
    MtType u mt := by
  letI := D.host.cmStar
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  intro i hi
  have hun : (C.mu0 ⟨i, hi⟩ * ξ).IsUnitary := fun x => by
    have e : (C.mu0 ⟨i, hi⟩ * ξ).1 x = (C.mu0 ⟨i, hi⟩).1 x * ξ.1 x := rfl
    rw [e, Units.val_mul, norm_mul, (C.isMu0 ⟨i, hi⟩).unitary x, CharModel.isUnitary_of_orderDvd hn hord x, one_mul]
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (Dt.UO_eq k).1 hk
    obtain ⟨m, hm, hu⟩ := GlobalTheory.UnUnitCmp.Val.finUnit_pow _ hun
    refine ⟨m, hm, Units.ext ?_⟩
    rw [← CharModel.eDt_finPart Dt a, h ⟨i, hi⟩ _ (CharModel.isFin_finPart a), Units.val_pow_eq_pow_val]
    exact hu _ (CharModel.isFin_finPart a) ha
  · choose e he using fun τ => (D.hcW u τ).e_int ⟨i, hi⟩
    refine ⟨e, fun τ => (he τ).symm, fun z => ?_⟩
    obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host z
    obtain ⟨m, hm, hinf⟩ := (C.isMu0 ⟨i, hi⟩).inf
    rw [← Dt.rat k z hk, ← CharModel.eDt_finPart Dt, h ⟨i, hi⟩ _ (CharModel.isFin_finPart _), GlobalTheory.Mem.Chr.DetGroupModel.fin_diag,
      HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one _ hn hord, mul_one, Units.val_inv_eq_inv_val, hinf k,
      ← Finset.prod_inv_distrib, ← D.eTau.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : m (D.eTau τ) = 2 * -e τ := by
      have h1 := hm (D.eTau τ)
      have h2 : eExp D ⟨i, hi⟩ (D.eTau τ) = e τ := by
        rw [← he τ, D.hcW_e]; simp [eExp]
      simp only [h2] at h1
      exact_mod_cast h1
    have h1 := congrArg (embPsi D.host (D.eTau τ)) hk
    rw [map_mul, GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    have h0 : embPsi D.host (D.eTau τ) (k : D.host.E) ≠ 0 := by simp
    show _ = embPsi D.host (D.eTau τ) z.1 ^ e τ
    generalize embPsi D.host (D.eTau τ) (k : D.host.E) = a at *
    generalize embPsi D.host (D.eTau τ) z.1 = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]

end GlobalTheory.KerJ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.KerEntTrue

open Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.KerJ

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem powRatAll_true (l : I.Laws) (Z : TC.Later B (I.cols l)) : GL3Theta.PowRatAll (I.rec7 l Z) := by
  obtain ⟨idl, h⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by
      show UOQ B.host I.SQ = _
      ext x
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy)
    (fun z => rfl)
    (fun N L L' t ht => by
      exact (trueDtPackQ_relDet I.SQ I.C N L L').trans ht)
  exact GL3Theta.powRatAll_of _ idl h (GlobalTheory.KernelScalarUnit.normOne_pow _)

theorem mtType_std (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ}
    {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)} (hO : I.StdO l Z Qp O) (u : (I.rec7 l Z).what₂.Word) (a : (I.rec7 l Z).what₂.Tup) :
    MtType u (O u a).mt := by
  obtain ⟨T, hT⟩ := TC.dtTied_true I hok hp l Z
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  have hk : KDq B.host I.SQ ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).2.2 a).1
  refine mtType_of_hecke T (I.xi a) hn ((hok.xi_reads a).orderDvd hpow) _ (fun j x hx => ?_) u
  have hm : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ B.R.m := ⟨by omega, j.2⟩
  have e1 : (O u a).mt (j.1 + 1) = (I.rec7 l Z).muTil (j.1 + 1) * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) := by
    rw [hO.mt u a]
    exact if_pos hm
  rw [e1, MonoidHom.mul_apply, T.muTil_eq j x hx, hT x]
  have e2 : (tildeQ B.host I.SQ (I.xi a)) (QuotientGroup.mk x) = (I.xi a).1 x :=
    (tildeQ_mk B.host I.SQ hk x).trans (congrArg _ (finPartI_eq_self hx))
  exact congrArg _ e2

theorem rhoAlg_std (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ}
    {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)} (hO : I.StdO l Z Qp O) (u : (I.rec7 l Z).what₂.Word) (a : (I.rec7 l Z).what₂.Tup) :
    GL3Columns.RhoAlg (O u a) := by
  have h3 := GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType _ u ((I.rec7 l Z).chTw u a) (O u a).mt (mtType_std I hok hp l Z hO u a)
  have hq := powRatAll_true I l Z
  intro i hi
  refine ⟨fun c => ?_, fun c' => ?_⟩
  · obtain ⟨h, z, hz⟩ := hq ((O u a).dt i c)
    exact ((h3 i hi).1 _ h z hz).1.1
  · obtain ⟨h, z, hz⟩ := hq ((O u a).dt (i + 1) c')
    exact ((h3 i hi).1 _ h z hz).2.1

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G in

theorem adaptedTh_kerEntC {D : D7} {P : Examples₂.EntPl D} {O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)} {Bs : PlaceMatrixFamily D} {Dx : DivX D} {Tw : TwForms D}
    (hB : BasOk P O Bs) (hA : AdaptedEnt P O Bs Dx) (h : KerEntHyp P O Bs Dx Tw) : AdaptedTh (kerEntC P O Bs h) O := by
  intro w hw u μ hl
  obtain ⟨Pm, h1, h2, h3, h4⟩ := hA w hw u μ hl
  refine ⟨Pm, h1, h2, h3, fun i hi c c' => ?_⟩
  show thAtW P O Bs u μ w i c c' = _
  unfold thAtW
  congr 1
  funext k j
  unfold adCoef
  split_ifs with hk
  · set s := Formalism.MainNotions.TaylorLogMetric.lamC (P.lam w) ((O u μ).dgen k.1) with hs
    have hs0 : s ≠ 0 := by
      intro h0
      have hd := (hB u μ w (i + 1) hi c' k.1).1
      haveI hne : Nonempty (Fin (D.R.N (i + 1))) := ⟨j.2.2⟩
      rw [h4 (i + 1) hi c' k.1, ← hs, h0, _root_.inv_zero, zero_pow (by omega), zero_smul] at hd
      exact hd Matrix.det_zero
    have hdet : ((Pm i c k.1).map (tauEmb D (P.lam w) k.1)).det ≠ 0 := (h1 i hi.le c k.1).1
    have ht : s⁻¹ ^ i ≠ 0 := pow_ne_zero _ (inv_ne_zero hs0)
    have hinv : (s⁻¹ ^ i • (Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ =
        (s⁻¹ ^ i)⁻¹ • ((Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ht, one_smul]
      exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
    rw [h4 (i + 1) hi c' k.1, h4 i hi.le c k.1, ← hs, hinv]
    simp only [Matrix.smul_apply, smul_eq_mul]
    have e : (1 : ℂ_[D.what₂.places.resChar w]) * s * s⁻¹ ^ (i + 1) * (s⁻¹ ^ i)⁻¹ = 1 := by
      rw [inv_pow, inv_pow, inv_inv, pow_succ]
      field_simp
    simp only [show (kerEntC P O Bs h).lam w = P.lam w from rfl]
    generalize ((Pm (i + 1) c' k.1).map (tauEmb D (P.lam w) k.1)) k.2.1 j.2.2 = x
    generalize ((Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ j.2.1 k.2.2 = y
    linear_combination (x * y) * e
  · rfl

end GlobalTheory.Mem.Col2.KerEntTrue

theorem GlobalTheory.Mem.Col2.TC.kerEnt_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∃ E : KerEnt (I.rec7 l Z) Y (I.tw l l0 Z), E.lam = Pl.lam ∧ EntOk E O := by
  intro B X I hok hp l Z l0 Y O Pl hq hs hu hj
  choose Pm h1 h2 h3 using AdaptedBases.exists_sys Pl O
  have hU := AdaptedBases.dgenUnitAd Pl O
  have hB : BasOk Pl O (fun u μ w i c τ => (Pm w u μ i c τ).map (Formalism.MainNotions.TaylorLogMetric.tauEmb _ (Pl.lam w) τ)) :=
    fun u μ w i hi c τ => h1 w u μ i hi c τ
  have hC := GlobalTheory.T.toy_entPl_canOnto _ Pl
  have h := GlobalTheory.T.kernelEntryHyp_of_trueColumnChoices I hok hp l Z l0 Y O Pl _ hq hs hB
    (fun u a w _ i _ c τ j k => GlobalTheory.KerRescale.tauEmb_mem Pl w τ (Pm w u a i c τ j k)) hu hj
  exact ⟨GlobalTheory.KerRescale.kerEntR Pl O _ (GlobalTheory.KerRescale.adUnit Pl O) (GlobalTheory.KerRescale.norm_adUnit Pl O hU) h, rfl,
    ⟨fun u μ w _ => GlobalTheory.KerRescale.tieR Pl O _ _ _ hB hC h u μ w,
      fun u μ w _ => GlobalTheory.KerRescale.tieR_un Pl O _ _ _ hB hC h u μ (KerEntTrue.rhoAlg_std I hok hp l Z hs u μ) w⟩,
    GlobalTheory.KerRescale.adaptedTh_kerEntR Pl O hU Pm h1 h2 h3 h⟩

end
