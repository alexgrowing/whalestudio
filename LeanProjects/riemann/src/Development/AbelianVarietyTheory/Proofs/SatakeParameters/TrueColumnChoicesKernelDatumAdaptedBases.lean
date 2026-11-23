import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormNatCastEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntryHypOfTrueColumnChoicesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedThKerEntC

noncomputable section

namespace GlobalTheory.Pdv.KerScale

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G Formalism.L2.Ker Classical

theorem colsOf_smul {k : Type} [CommRing k] {N : ℕ} (t : k) (Y : Matrix (Fin N) (Fin N) k) :
    GL3Columns.colsOf (t • Y) = fun a j => t * GL3Columns.colsOf Y a j := by
  funext a j
  unfold GL3Columns.colsOf
  split_ifs <;> simp

theorem deX_smul {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (t : Lt → k)
    (y : Lt → Fin N → ℕ → k) :
    GL3Columns.DeX N nu (fun s a j => t s * y s a j) = MvPolynomial.C (∏ s, t s ^ (nu s).card) * GL3Columns.DeX N nu y := by
  unfold GL3Columns.DeX
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [GlobalTheory.KerRescale.card_eq_sum_colLen, ← Finset.prod_pow_eq_pow_sum, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  have e : (Matrix.of fun i j : Fin ((nu s).colLen c) => ∑ a : Fin N, MvPolynomial.C (t s * y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a)) =
      (MvPolynomial.C (t s) : MvPolynomial (Lt × ℕ × Fin N) k) • Matrix.of fun i j : Fin ((nu s).colLen c) => ∑ a : Fin N, MvPolynomial.C (y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a) := by
    ext i j
    simp [Matrix.smul_apply, Finset.mul_sum, mul_assoc]
  rw [e, Matrix.det_smul, Fintype.card_fin, map_pow]

end GlobalTheory.Pdv.KerScale

namespace GlobalTheory.Pdv.KerScale

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G Formalism.L2.Ker Classical

variable {D : D7}

theorem canM_scale (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram) (t : D.what₂.Tau → Cw D w)
    {F : FrP D w N → Cw D w} (hF : F ∈ LinearMap.range (canM D w N nu)) (y : FrP D w N) :
    F (fun τ => t τ • y τ) = (∏ z, t (tauPl D z) ^ (nu z).card) * F y := by
  obtain ⟨ph, rfl⟩ := hF
  show ph (GL3Columns.DeX N nu fun s => GL3Columns.colsOf (t (tauPl D s) • y (tauPl D s))) = _ * ph (GL3Columns.DeX N nu fun s => GL3Columns.colsOf (y (tauPl D s)))
  simp only [colsOf_smul]
  have h := deX_smul N nu (fun s => t (tauPl D s)) (fun s => GL3Columns.colsOf (y (tauPl D s)))
  rw [h, MvPolynomial.C_mul', map_smul, smul_eq_mul]

theorem atBas_smul (P : Examples₂.EntPl D) (w : D.what₂.places.Pl) {N : ℕ} (t : D.what₂.Tau → Cw D w)
    (M : D.what₂.Tau → Matrix (Fin N) (Fin N) (Cw D w)) (Q : MvPolynomial (GL3Theta.FrV D N) D.what₂.LL) (y : FrP D w N) :
    atBas P w (fun τ => t τ • M τ) Q y = atBas P w M Q (fun τ => t τ • y τ) := by
  simp only [atBas, LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_mul, Matrix.mul_smul]

def scB (a : ∀ w : D.what₂.places.Pl, D.what₂.Word → D.what₂.Tup → D.what₂.Tau → Cw D w) (B : PlaceMatrixFamily D) : PlaceMatrixFamily D :=
  fun u μ w i c τ => a w u μ τ ^ i • B u μ w i c τ

variable (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D)
  (a : ∀ w : D.what₂.places.Pl, D.what₂.Word → D.what₂.Tup → D.what₂.Tau → Cw D w)

theorem srcFun_scB (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i) (v : polV D u i)
    (y : FrP D w (D.R.N i)) :
    srcFun P (scB a B) u μ w i c v y = (∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ (-(D.chTw u μ).sSharp i τ)) *
      srcFun P B u μ w i c v (fun τ => a w u μ τ ^ i • y τ) := by
  simp only [srcFun, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, scB]
  rw [show scB a B u μ w i c = fun τ => a w u μ τ ^ i • B u μ w i c τ from rfl, atBas_smul P w (fun τ => a w u μ τ ^ i)]
  simp only [Matrix.det_smul, Fintype.card_fin, mul_zpow, Finset.prod_mul_distrib, mul_assoc]

theorem tgtFun_scB (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c' : (D.chTw u μ).cls (i + 1)) (v : polV D u (i + 1))
    (y : FrP D w (D.R.N (i + 1))) :
    tgtFun P (scB a B) u μ w i c' v y = (∏ τ, ((a w u μ τ ^ (i + 1)) ^ D.R.N (i + 1)) ^ (-(D.chTw u μ).sDiv i τ)) *
      tgtFun P B u μ w i c' v (fun τ => a w u μ τ ^ (i + 1) • y τ) := by
  simp only [tgtFun, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, scB]
  rw [show scB a B u μ w (i + 1) c' = fun τ => a w u μ τ ^ (i + 1) • B u μ w (i + 1) c' τ from rfl, atBas_smul P w (fun τ => a w u μ τ ^ (i + 1))]
  simp only [Matrix.det_smul, Fintype.card_fin, mul_zpow, Finset.prod_mul_distrib, mul_assoc]

end GlobalTheory.Pdv.KerScale

namespace GlobalTheory.Pdv.KerScale

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G Formalism.L2.Ker Classical

variable {D : D7} (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D)
  (a : ∀ w : D.what₂.places.Pl, D.what₂.Word → D.what₂.Tup → D.what₂.Tau → Cw D w)

theorem prSC_scB (hC : CanOnto P) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (hi : i < D.R.m)
    (c : (D.chTw u μ).cls i) (v : ValQ O u μ i) (φ : MvPolynomial ((Bool × HH D) × ℕ × Fin (D.R.N i)) (Cw D w)) :
    prSC P O (scB a B) u μ w i c v φ = ((∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ (-(D.chTw u μ).sSharp i τ)) *
      ∏ z, (a w u μ (tauPl D z) ^ i) ^ (nuD D u i z).card) * prSC P O B u μ w i c v φ := by
  have e : srcFun P (scB a B) u μ w i c (secC O u μ i v) = ((∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ (-(D.chTw u μ).sSharp i τ)) *
      ∏ z, (a w u μ (tauPl D z) ^ i) ^ (nuD D u i z).card) • srcFun P B u μ w i c (secC O u μ i v) := by
    funext y
    rw [srcFun_scB, canM_scale w (D.R.N i) (nuD D u i) (fun τ => a w u μ τ ^ i) (canS_of P B hC u μ w i hi c _) y, Pi.smul_apply,
      smul_eq_mul, mul_assoc]
  show canInv D w (D.R.N i) (nuD D u i) (srcFun P (scB a B) u μ w i c (secC O u μ i v)) φ = _ *
    canInv D w (D.R.N i) (nuD D u i) (srcFun P B u μ w i c (secC O u μ i v)) φ
  rw [e, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem prTC_scB (hC : CanOnto P) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (hi : i < D.R.m)
    (c' : (D.chTw u μ).cls (i + 1)) (v' : ValQ O u μ (i + 1)) (I : KM.ColChoice (D.R.N (i + 1)) (nuD D u i)) :
    prTC P O (scB a B) u μ w i c' v' I = ((∏ τ, ((a w u μ τ ^ (i + 1)) ^ D.R.N (i + 1)) ^ (-(D.chTw u μ).sDiv i τ)) *
      ∏ z, (a w u μ (tauPl D z) ^ (i + 1)) ^ (nuD D u i z).card) * prTC P O B u μ w i c' v' I := by
  have e : tgtFun P (scB a B) u μ w i c' (secC O u μ (i + 1) v') = ((∏ τ, ((a w u μ τ ^ (i + 1)) ^ D.R.N (i + 1)) ^ (-(D.chTw u μ).sDiv i τ)) *
      ∏ z, (a w u μ (tauPl D z) ^ (i + 1)) ^ (nuD D u i z).card) • tgtFun P B u μ w i c' (secC O u μ (i + 1) v') := by
    funext y
    rw [tgtFun_scB, canM_scale w (D.R.N (i + 1)) (nuD D u i) (fun τ => a w u μ τ ^ (i + 1)) (canT_of P B hC u μ w i hi c' _) y,
      Pi.smul_apply, smul_eq_mul, mul_assoc]
  show onMin D w (D.R.N (i + 1)) (nuD D u i) (canInv D w (D.R.N (i + 1)) (nuD D u i) (tgtFun P (scB a B) u μ w i c' (secC O u μ (i + 1) v'))) I = _ *
    onMin D w (D.R.N (i + 1)) (nuD D u i) (canInv D w (D.R.N (i + 1)) (nuD D u i) (tgtFun P B u μ w i c' (secC O u μ (i + 1) v'))) I
  rw [e, map_smul, map_smul, Pi.smul_apply, smul_eq_mul]

theorem thAtW_scB (ha : ∀ w u μ τ, ‖a w u μ τ‖ = 1) (hB : BasOk P O B) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (i : ℕ) (hi : i < D.R.m) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) :
    thAtW P O (scB a B) u μ w i c c' = MvPowerSeries.rescale (fun z => a w u μ (tauPl D z.1)) (thAtW P O B u μ w i c c') := by
  unfold thAtW
  rw [GlobalTheory.KerRescale.rescale_atLin]
  congr 1
  funext k j
  split_ifs with hk
  · have hs0 : a w u μ k.1 ≠ 0 := norm_ne_zero_iff.1 (by rw [ha]; exact one_ne_zero)
    have h0 := (hB u μ w i hi.le c k.1).1
    have e : (a w u μ k.1 ^ i • B u μ w i c k.1)⁻¹ = (a w u μ k.1 ^ i)⁻¹ • (B u μ w i c k.1)⁻¹ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hs0), one_smul,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h0)]
    show 1 * lamC (P.lam w) ((O u μ).dgen k.1) * (a w u μ k.1 ^ (i + 1) • B u μ w (i + 1) c' k.1) k.2.1 j.2.2 *
      (a w u μ k.1 ^ i • B u μ w i c k.1)⁻¹ j.2.1 k.2.2 = _
    rw [e, hk]
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [pow_succ]
    field_simp
  · exact (mul_zero _).symm

theorem unF_scB (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) :
    unF P O (scB a B) u μ w i c c' = unF P O B u μ w i c c' * ((∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ ((D.chTw u μ).sSharp i τ)) *
      ∏ τ, ((a w u μ τ ^ (i + 1)) ^ D.R.N (i + 1)) ^ (-(D.chTw u μ).sDiv i τ)) := by
  unfold unF scB
  simp only [Matrix.det_smul, Fintype.card_fin, mul_zpow, Finset.prod_mul_distrib]
  ring

end GlobalTheory.Pdv.KerScale

namespace GlobalTheory.Pdv.KerScale

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G Formalism.L2.Ker Classical

variable {D : D7} (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D)
  (a : ∀ w : D.what₂.places.Pl, D.what₂.Word → D.what₂.Tup → D.what₂.Tau → Cw D w)

theorem basOk_scB (ha : ∀ w u μ τ, ‖a w u μ τ‖ = 1) (hB : BasOk P O B) : BasOk P O (scB a B) := fun u μ w i hi c τ =>
  GlobalTheory.Mem.Col2.TC.AdaptedBases.basR_smul (hB u μ w i hi c τ) (by rw [norm_pow, ha, one_pow])

theorem kerEntHyp_scB {Dx : DivX D} {Tw : TwForms D} (ha : ∀ w u μ τ, ‖a w u μ τ‖ = 1) (hB : BasOk P O B) (hC : CanOnto P)
    (hR : ∀ u μ, GL3Columns.RhoAlg (O u μ)) (h : KerEntHyp P O B Dx Tw) : KerEntHyp P O (scB a B) Dx Tw := by
  have hn : ∀ w u μ τ, a w u μ τ ≠ 0 := fun w u μ τ => norm_ne_zero_iff.1 (by rw [ha]; exact one_ne_zero)
  have nS : ∀ u μ w i, ‖(∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ (-(D.chTw u μ).sSharp i τ)) *
      ∏ z, (a w u μ (tauPl D z) ^ i) ^ (nuD D u i z).card‖ = 1 := fun u μ w i => by
    simp [norm_prod, norm_zpow, norm_pow, ha]
  have nT : ∀ u μ w i, ‖(∏ τ, ((a w u μ τ ^ (i + 1)) ^ D.R.N (i + 1)) ^ (-(D.chTw u μ).sDiv i τ)) *
      ∏ z, (a w u μ (tauPl D z) ^ (i + 1)) ^ (nuD D u i z).card‖ = 1 := fun u μ w i => by
    simp [norm_prod, norm_zpow, norm_pow, ha]
  refine ⟨fun u μ w hw i hi c' v' I => ?_, fun u μ w hw i hi φ => ?_, fun u μ w hw i hi φ => ?_,
    fun u μ w hw i hi c c' v v' hK I => ?_⟩
  · obtain ⟨b, hb⟩ := h.val u μ w hw i hi c' v' I
    exact ⟨b, by rw [prTC_scB P O B a hC u μ w i hi, norm_mul, nT, one_mul, hb]⟩
  · have e : ∀ c v J, ‖prSC P O (scB a B) u μ w i c v J‖ = ‖prSC P O B u μ w i c v J‖ := fun c v J => by
      rw [prSC_scB P O B a hC u μ w i hi, norm_mul, nS, one_mul]
    simp only [e]
    exact h.latS u μ w hw i hi φ
  · have e : ∀ c' v' I, ‖prTC P O (scB a B) u μ w i c' v' I‖ = ‖prTC P O B u μ w i c' v' I‖ := fun c' v' I => by
      rw [prTC_scB P O B a hC u μ w i hi, norm_mul, nT, one_mul]
    simp only [e]
    exact h.latT u μ w hw i hi φ
  · have k0 := h.kform u μ w hw i hi c c' v v' hK I
    have hF := unF_ne P O B hB u μ (hR u μ) w i hi c c'
    have hU0 : ((∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ ((D.chTw u μ).sSharp i τ)) *
        ∏ τ, ((a w u μ τ ^ (i + 1)) ^ D.R.N (i + 1)) ^ (-(D.chTw u μ).sDiv i τ)) ≠ 0 :=
      mul_ne_zero (Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ (hn w u μ τ))))
        (Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ (hn w u μ τ))))
    have hF' : unF P O (scB a B) u μ w i c c' ≠ 0 := by
      rw [unF_scB]
      exact mul_ne_zero hF hU0
    rw [prTC_scB P O B a hC u μ w i hi, k0, thAtW_scB P O B a ha hB u μ w i hi c c',
      GlobalTheory.KerRescale.applyAt0_rescale _ _ _ (fun s => a w u μ (tauPl D s)), map_smul, smul_eq_mul, prSC_scB P O B a hC u μ w i hi]
    unfold unC
    rw [if_neg hF, if_neg hF', unF_scB]
    have key : (∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ ((D.chTw u μ).sSharp i τ)) *
        (∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ (-(D.chTw u μ).sSharp i τ)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ (hn w u μ τ))))]
    have key2 : (∏ z, (a w u μ (tauPl D z) ^ i) ^ (nuD D u i z).card) * (∏ z, a w u μ (tauPl D z) ^ (nuD D u i z).card) =
        ∏ z, (a w u μ (tauPl D z) ^ (i + 1)) ^ (nuD D u i z).card := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun z _ => ?_
      rw [← mul_pow, ← pow_succ]
    generalize (∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ ((D.chTw u μ).sSharp i τ)) = U1 at *
    generalize (∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ (-(D.chTw u μ).sSharp i τ)) = S1 at *
    generalize (∏ z, (a w u μ (tauPl D z) ^ i) ^ (nuD D u i z).card) = S2 at *
    generalize (∏ z, a w u μ (tauPl D z) ^ (nuD D u i z).card) = G at *
    generalize (∏ z, (a w u μ (tauPl D z) ^ (i + 1)) ^ (nuD D u i z).card) = T2 at *
    generalize (∏ τ, ((a w u μ τ ^ (i + 1)) ^ D.R.N (i + 1)) ^ (-(D.chTw u μ).sDiv i τ)) = U2 at *
    generalize unF P O B u μ w i c c' = F at *
    generalize prSC P O B u μ w i c v _ = p
    linear_combination (-(F * U2 * p * S2 * G)) * key + (-(F * U2 * p)) * key2

end GlobalTheory.Pdv.KerScale

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Pdv.kerEntC_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∃ (Bs : PlaceMatrixFamily (I.rec7 l Z)) (h : KerEntHyp Pl O Bs Y (I.tw l l0 Z)), EntOk (kerEntC Pl O Bs h) O := by
  intro B X I hok hp l Z l0 Y O Pl hq hs hu hj
  choose Pm h1 h2 h3 using GlobalTheory.Mem.Col2.TC.AdaptedBases.exists_sys Pl O
  have hU := GlobalTheory.Mem.Col2.TC.AdaptedBases.dgenUnitAd Pl O
  have hB : BasOk Pl O (fun u μ w i c τ => (Pm w u μ i c τ).map (Formalism.MainNotions.TaylorLogMetric.tauEmb _ (Pl.lam w) τ)) :=
    fun u μ w i hi c τ => h1 w u μ i hi c τ
  have hC := GlobalTheory.T.toy_entPl_canOnto _ Pl
  have hR : ∀ u μ, GL3Columns.RhoAlg (O u μ) := fun u μ => KerEntTrue.rhoAlg_std I hok hp l Z hs u μ
  have h0 := GlobalTheory.T.kernelEntryHyp_of_trueColumnChoices I hok hp l Z l0 Y O Pl _ hq hs hB
    (fun u a w _ i _ c τ j k => GlobalTheory.KerRescale.tauEmb_mem Pl w τ (Pm w u a i c τ j k)) hu hj
  have ha := GlobalTheory.KerRescale.norm_adUnit Pl O hU
  have hBs := GlobalTheory.Pdv.KerScale.basOk_scB Pl O _ _ ha hB
  have h := GlobalTheory.Pdv.KerScale.kerEntHyp_scB Pl O _ _ ha hB hC hR h0
  have hA : AdaptedEnt Pl O (GlobalTheory.Pdv.KerScale.scB (GlobalTheory.KerRescale.adUnit Pl O)
      (fun u μ w i c τ => (Pm w u μ i c τ).map (Formalism.MainNotions.TaylorLogMetric.tauEmb _ (Pl.lam w) τ))) Y := fun w hw u μ _ =>
    ⟨Pm w u μ, h1 w u μ, h2 w u μ, h3 w u μ, fun i _ c τ => by
      show GlobalTheory.KerRescale.adUnit Pl O w u μ τ ^ i • _ = _
      unfold GlobalTheory.KerRescale.adUnit
      rw [if_pos hw]⟩
  exact ⟨_, h, ⟨fun u μ w _ => kfTieOf Pl O _ hBs hC h u μ w, fun u μ w _ => kfTieOf_un Pl O _ hBs hC h u μ (hR u μ) w⟩,
    KerEntTrue.adaptedTh_kerEntC hBs hA h⟩

end
