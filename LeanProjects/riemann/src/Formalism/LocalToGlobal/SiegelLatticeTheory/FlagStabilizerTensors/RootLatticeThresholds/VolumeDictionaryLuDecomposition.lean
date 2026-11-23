import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.SpanPerpZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.XflagEqMap
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValG
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FibreCounting

noncomputable section

open scoped Classical
open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.PairVal Formalism.L2.SG.Pf.StabilizerIndexVolumes

namespace Formalism.L2.SG.Pf.VolPinAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Basic

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def rpt (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) : X.B.I.GA :=
  (Formalism.L2.SG.Pf.ratPt_holds D X n hn).choose

theorem rpt_spec (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    RatLink X (rpt X n hn) n :=
  (Formalism.L2.SG.Pf.ratPt_holds D X n hn).choose_spec

theorem rpt_eq {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {x : X.B.I.GA}
    (hx : RatLink X x n) : rpt X n hn = x :=
  Formalism.L2.SG.TermOp.Vanish.ratLink_unique X (rpt_spec X n hn) hx

theorem ratLink_inf_one {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n) (h1 : x.1 = 1) :
    n = 1 := by
  obtain ⟨M, -, hM1, -, hM3⟩ := hx
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace X.B.I.F))
  have hu : uMat ((1 : X.B.I.GA).1 v) = 1 := by simp [uMat]
  have h := hM1 v
  rw [h1, show (1 : X.B.I.Ginf) = (1 : X.B.I.GA).1 from rfl, hu] at h
  have hMφ : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) = 1 := by
    have e := congrArg (fun A => X.B.I.P v * A * (X.B.I.P v)⁻¹) h
    simp only [Matrix.mul_one, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv] at e
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one] at e
    exact e.symm
  have hM : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = 1 := by
    ext i j
    have := congrFun (congrFun hMφ i) j
    simp only [Matrix.map_apply] at this
    apply (X.B.I.φ v).injective
    rw [this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  apply LinearEquiv.ext
  intro y
  have := hM3 y
  rw [hM, Matrix.one_mulVec] at this
  apply X.bas.equivFun.injective
  funext i
  exact X.ιE.symm.injective (congrFun this i)

end Basic

section Main

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem nr_units {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} {t : Formalism.L2.SG.TermDef.Term D u u' F0 what₂}
    {w : Point D.host.E (D.R.rS + 1)} {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {L U : MatR D}
    (hN : NormRep t w F' L U) :
    IsUnit L.det ∧ IsUnit (Zhat F0 F'.fl).det ∧ Zhat F0 F'.fl * sgnM D.R.rS = L * ptMat w * U := by
  obtain ⟨_, _, hL, hU, hZ⟩ := hN
  have hZ1 : Zhat F0 F'.fl * sgnM D.R.rS = L * ptMat w * U := by rw [← zhatOM_eq]; exact hZ
  refine ⟨by rw [lo_det hL]; exact isUnit_one, ?_, hZ1⟩
  have hZe : Zhat F0 F'.fl = L * ptMat w * U * sgnM D.R.rS := by
    rw [← hZ1, Matrix.mul_assoc, sgnM_sq, Matrix.mul_one]
  rw [isUnit_iff_ne_zero, hZe, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, lo_det hL, up_det hU, one_mul,
    mul_one]
  refine mul_ne_zero (ptMat_det w) ?_
  intro h0
  have := congrArg Matrix.det (sgnM_sq (K := D.host.E) (r := D.R.rS))
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

private theorem isUpUni_inv' {N : ℕ} {K : Type} [Field K] {U : Matrix (Fin N) (Fin N) K}
    (h : IsUpUni U) : IsUpUni U⁻¹ := by
  have h' : Formalism.DoubleCosetMeasures.IsUpUni U := by
    refine ⟨?_, fun a => (h a a).2 rfl⟩
    intro i j hij
    exact (h i j).1 hij
  have h2 := Formalism.DoubleCosetMeasures.isUpUni_inv K h'
  intro i j
  exact ⟨fun hij => h2.1 hij, fun hij => hij ▸ h2.2 i⟩

private theorem conj_lemma_2 {N : ℕ} {K : Type} [Field K] (Z L B W U b S : Matrix (Fin N) (Fin N) K)
    (hZ : IsUnit Z.det) (hL : IsUnit L.det) (hU : IsUnit U.det) (hB : IsUnit B.det)
    (hS2 : S * S = 1) (hZ1 : Z * S = L * W * U) (hBW : B * W * b = W) :
    Z⁻¹ * (L * B⁻¹ * L⁻¹) * Z = S * (U⁻¹ * b * U) * S := by
  have hBinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hLinv : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul L hL
  have hUinv : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hU
  have hZinv : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hZ
  have h1 : W * b = B⁻¹ * W := by
    conv_rhs => rw [← hBW]
    simp only [← Matrix.mul_assoc, hBinv, Matrix.one_mul]
  have hZe : Z = L * W * U * S := by
    rw [← hZ1, Matrix.mul_assoc, hS2, Matrix.mul_one]
  have hmain : L * B⁻¹ * L⁻¹ * Z = Z * (S * (U⁻¹ * b * U) * S) := by
    have e1 : Z * (S * (U⁻¹ * b * U) * S) = L * (B⁻¹ * W) * U * S := by
      calc Z * (S * (U⁻¹ * b * U) * S) = Z * S * U⁻¹ * b * U * S := by
            simp only [Matrix.mul_assoc]
        _ = L * W * (U * U⁻¹) * b * U * S := by
            rw [hZ1]; simp only [Matrix.mul_assoc]
        _ = L * (W * b) * U * S := by
            rw [hUinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = L * (B⁻¹ * W) * U * S := by rw [h1]
    rw [e1]
    conv_lhs => rw [hZe]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (L * B⁻¹) L⁻¹ L, hLinv, Matrix.mul_one]
  calc Z⁻¹ * (L * B⁻¹ * L⁻¹) * Z = Z⁻¹ * (L * B⁻¹ * L⁻¹ * Z) := by
        simp only [Matrix.mul_assoc]
    _ = Z⁻¹ * (Z * (S * (U⁻¹ * b * U) * S)) := by rw [hmain]
    _ = S * (U⁻¹ * b * U) * S := by rw [← Matrix.mul_assoc, hZinv, Matrix.one_mul]

private theorem isUpUni_sgnM_conj {r : ℕ} {K : Type} [Field K] {B : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hB : IsUpUni B) : IsUpUni ((sgnM r : Matrix (Fin (r + 1)) (Fin (r + 1)) K) * B * sgnM r) := by
  intro i j
  unfold sgnM
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [(hB i j).1 hij, mul_zero, zero_mul]
  · subst hij
    rw [(hB i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

theorem P'm_up_st {u' : D.what₂.Word} {u : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F'' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {w : Point D.host.E (D.R.rS + 1)} {L U : MatR D}
    (hL : IsLoUni L) (hU : IsUpUni U) (hZu : IsUnit (Zhat F0 F'').det)
    (hZ1 : Zhat F0 F'' * sgnM D.R.rS = L * ptMat w * U) {β : GLR D} (hβ : β ∈ StSet (ptMat w)) :
    IsUpUni (P'm F0 F'' L (β : MatR D)) := by
  obtain ⟨_, b, hb, hβW⟩ := hβ
  have hLd : IsUnit L.det := by
    have h : L.det = 1 := by
      rw [Matrix.det_of_lowerTriangular L (fun i j hij => (hL i j).1 (OrderDual.toDual_lt_toDual.mp hij))]
      exact Finset.prod_eq_one fun i _ => (hL i i).2 rfl
    rw [h]
    exact isUnit_one
  have hUd : IsUnit U.det := by
    have h : U.det = 1 := by
      rw [Matrix.det_of_upperTriangular (fun i j hij => (hU i j).1 hij)]
      exact Finset.prod_eq_one fun i _ => (hU i i).2 rfl
    rw [h]
    exact isUnit_one
  have hS2 : (sgnM D.R.rS : MatR D) * sgnM D.R.rS = 1 := by
    unfold sgnM
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  unfold P'm
  rw [conj_lemma_2 _ _ _ _ _ _ _ hZu hLd hUd (Matrix.isUnits_det_units β) hS2 hZ1 hβW]
  exact isUpUni_sgnM_conj (Formalism.L2.SG.Pf.isUpUni_mul (Formalism.L2.SG.Pf.isUpUni_mul (isUpUni_inv' hU) hb) hU)

end Main

section Phi

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {u u' : D.what₂.Word}

theorem hLu_of {L : MatR D} (hL : IsLoUni L) : IsUnit L.det := by
  have h : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L (fun i j hij => (hL i j).1 (OrderDual.toDual_lt_toDual.mp hij))]
    exact Finset.prod_eq_one fun i _ => (hL i i).2 rfl
  rw [h]
  exact isUnit_one

theorem tw_isom_st (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F'' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) {w : Point D.host.E (D.R.rS + 1)} {L U : MatR D}
    (hL : IsLoUni L) (hU : IsUpUni U) (hZu : IsUnit (Zhat F0 F'').det)
    (hZ1 : Zhat F0 F'' * sgnM D.R.rS = L * ptMat w * U) (hGr : IsUnit (gramOf (gg F0 F'')).det) (β : StG w) :
    tw F0 F'' L (hLu_of hL) hZu hGr (β : GLR D) ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  have hβ : (β : GLR D) ∈ StSet (ptMat w) := β.2
  intro x y
  exact tw_isom hL (hLu_of hL) hZu hGr (β : GLR D) hβ.1 (P'm_up_st hL hU hZu hZ1 hβ) x y

def Phi (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F'' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) {w : Point D.host.E (D.R.rS + 1)} {L U : MatR D}
    (hL : IsLoUni L) (hU : IsUpUni U) (hZu : IsUnit (Zhat F0 F'').det)
    (hZ1 : Zhat F0 F'' * sgnM D.R.rS = L * ptMat w * U) (hGr : IsUnit (gramOf (gg F0 F'')).det) :
    StG w →* X.B.I.Ginf where
  toFun β := (rpt X _ (tw_isom_st F0 F'' hL hU hZu hZ1 hGr β⁻¹)).1
  map_one' := by
    have h1 : tw F0 F'' L (hLu_of hL) hZu hGr ((1⁻¹ : StG w) : GLR D) = 1 := by
      rw [inv_one, Subgroup.coe_one, tw_one]
    have hx : RatLink X 1 (tw F0 F'' L (hLu_of hL) hZu hGr ((1⁻¹ : StG w) : GLR D)) := by
      rw [h1]; exact Formalism.L2.SG.TermOp.ratLink_one X
    show (rpt X _ _).1 = 1
    rw [rpt_eq X _ hx]; rfl
  map_mul' β γ := by
    have h1 : tw F0 F'' L (hLu_of hL) hZu hGr (((β * γ)⁻¹ : StG w) : GLR D) =
        tw F0 F'' L (hLu_of hL) hZu hGr ((β⁻¹ : StG w) : GLR D) *
          tw F0 F'' L (hLu_of hL) hZu hGr ((γ⁻¹ : StG w) : GLR D) := by
      rw [_root_.mul_inv_rev, Subgroup.coe_mul, tw_mul]
    have hx : RatLink X (rpt X _ (tw_isom_st F0 F'' hL hU hZu hZ1 hGr β⁻¹) *
        rpt X _ (tw_isom_st F0 F'' hL hU hZu hZ1 hGr γ⁻¹))
        (tw F0 F'' L (hLu_of hL) hZu hGr (((β * γ)⁻¹ : StG w) : GLR D)) := by
      rw [h1]
      exact Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (rpt_spec X _ _) (rpt_spec X _ _)
    show (rpt X _ _).1 = (rpt X _ _).1 * (rpt X _ _).1
    rw [rpt_eq X _ hx, Prod.fst_mul]

theorem Phi_apply (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F'' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) {w : Point D.host.E (D.R.rS + 1)} {L U : MatR D}
    (hL : IsLoUni L) (hU : IsUpUni U) (hZu : IsUnit (Zhat F0 F'').det)
    (hZ1 : Zhat F0 F'' * sgnM D.R.rS = L * ptMat w * U) (hGr : IsUnit (gramOf (gg F0 F'')).det) (β : StG w) :
    Phi X F0 F'' hL hU hZu hZ1 hGr β = (rpt X _ (tw_isom_st F0 F'' hL hU hZu hZ1 hGr β⁻¹)).1 := rfl

theorem Phi_inj (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F'' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) {w : Point D.host.E (D.R.rS + 1)} {L U : MatR D}
    (hL : IsLoUni L) (hU : IsUpUni U) (hZu : IsUnit (Zhat F0 F'').det)
    (hZ1 : Zhat F0 F'' * sgnM D.R.rS = L * ptMat w * U) (hGr : IsUnit (gramOf (gg F0 F'')).det)
    (hT : ((Tu D u : ℕ) : D.host.E) ≠ 0) : Function.Injective (Phi X F0 F'' hL hU hZu hZ1 hGr) := by
  rw [injective_iff_map_eq_one]
  intro β hβ
  rw [Phi_apply] at hβ
  have h1 : tw F0 F'' L (hLu_of hL) hZu hGr ((β⁻¹ : StG w) : GLR D) = 1 :=
    ratLink_inf_one X (rpt_spec X _ (tw_isom_st F0 F'' hL hU hZu hZ1 hGr β⁻¹)) hβ
  have h2 : ((β⁻¹ : StG w) : GLR D) = 1 := tw_inj hT (hLu_of hL) hZu hGr h1
  rw [← inv_eq_one]
  exact Subtype.ext h2

end Phi

section Nlam

variable {D : D7} {u u' : D.what₂.Word}

theorem gmap_bot (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap n (⊥ : Submodule (𝓞 D.host.E) (VS D).V) = ⊥ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  exact Submodule.map_bot _

theorem nlam_bot_of {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E}
    {F : LFlag (VS D) D.R.rS T} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : n ∈ NLam Λ F) : n ∈ NLam ⊥ F :=
  ⟨⟨h.1.1, gmap_bot n⟩, h.2.1, h.2.2⟩

theorem tw_nlam (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) {w : Point D.host.E (D.R.rS + 1)} {L U : MatR D}
    (hL : IsLoUni L) (hU : IsUpUni U) (hZu : IsUnit (Zhat F0 F'.fl).det)
    (hZ1 : Zhat F0 F'.fl * sgnM D.R.rS = L * ptMat w * U) (hGr : IsUnit (gramOf (gg F0 F'.fl)).det) (β : StG w) :
    tw F0 F'.fl L (hLu_of hL) hZu hGr (β : GLR D) ∈ NLam ⊥ (lf D F0) ∧
      tw F0 F'.fl L (hLu_of hL) hZu hGr (β : GLR D) ∈ NLam ⊥ F' := by
  set Z := Zhat F0 F'.fl
  set B : MatR D := ((β : GLR D) : MatR D) with hB
  have hβlo : IsLoUni B := β.2.1
  have hBu : IsUnit B.det := by rw [lo_det hβlo]; exact isUnit_one
  have hLu := hLu_of hL
  have hPu : IsUpUni (Pm L B) := Pm_up hL hβlo
  have hP'u : IsUpUni (P'm F0 F'.fl L B) := P'm_up_st hL hU hZu hZ1 β.2
  have hiso := tw_isom_st F0 F'.fl hL hU hZu hZ1 hGr β
  have hAut : IsAutLam (VS D) ⊥ (tw F0 F'.fl L hLu hZu hGr (β : GLR D)) := ⟨hiso, gmap_bot _⟩

  have hPH : (Pm L B).conjTranspose = L * B * L⁻¹ := by rw [Pm, Matrix.conjTranspose_conjTranspose]
  have hPHinv : ((Pm L B).conjTranspose)⁻¹ = L * B⁻¹ * L⁻¹ := by
    rw [hPH]
    refine Matrix.inv_eq_left_inv ?_
    calc L * B⁻¹ * L⁻¹ * (L * B * L⁻¹) = L * (B⁻¹ * ((L⁻¹ * L) * B)) * L⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul _ hLu, Matrix.one_mul, Matrix.nonsing_inv_mul _ hBu, Matrix.mul_one,
          Matrix.mul_nonsing_inv _ hLu]
  have hrel : P'm F0 F'.fl L B = Z⁻¹ * ((Pm L B).conjTranspose)⁻¹ * Z := by rw [hPHinv]; rfl
  have hPl : IsLoUni ((Pm L B).conjTranspose)⁻¹ := by
    rw [hPHinv]; exact lo_mul (lo_mul hL (lo_inv hβlo)) (lo_inv hL)
  set Q : MatR D := Z⁻¹ * (L * B * L⁻¹) * Z with hQ
  have hPQ : P'm F0 F'.fl L B * Q = 1 := by
    unfold P'm
    calc Z⁻¹ * (L * B⁻¹ * L⁻¹) * Z * (Z⁻¹ * (L * B * L⁻¹) * Z)
        = Z⁻¹ * (L * (B⁻¹ * ((L⁻¹ * ((Z * Z⁻¹) * L)) * B)) * L⁻¹) * Z := by simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [Matrix.mul_nonsing_inv _ hZu, Matrix.one_mul, Matrix.nonsing_inv_mul _ hLu, Matrix.one_mul,
            Matrix.nonsing_inv_mul _ hBu, Matrix.mul_one, Matrix.mul_nonsing_inv _ hLu, Matrix.mul_one,
            Matrix.nonsing_inv_mul _ hZu]
  have hQP : Q * P'm F0 F'.fl L B = 1 := mul_eq_one_comm.1 hPQ
  have hQup : IsUpUni Q := by
    have : Q = (P'm F0 F'.fl L B)⁻¹ := (Matrix.inv_eq_left_inv hQP).symm
    rw [this]; exact up_inv hP'u
  have hP'Hinv : ((P'm F0 F'.fl L B).conjTranspose)⁻¹ = Q.conjTranspose := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
  have hP'l : IsLoUni ((P'm F0 F'.fl L B).conjTranspose)⁻¹ := by rw [hP'Hinv]; exact lo_conjT hQup
  have hZtu : IsUnit Z.conjTranspose.det := by rw [Matrix.det_conjTranspose]; exact hZu.star
  have hrel' : Pm L B = (Z.conjTranspose)⁻¹ * ((P'm F0 F'.fl L B).conjTranspose)⁻¹ * Z.conjTranspose := by
    rw [hP'Hinv, hQ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    have hZc : (Z⁻¹).conjTranspose * Z.conjTranspose = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hZu, Matrix.conjTranspose_one]
    have hZtZ : (Z.conjTranspose)⁻¹ * Z.conjTranspose = 1 := Matrix.nonsing_inv_mul _ hZtu
    calc Pm L B = ((Z.conjTranspose)⁻¹ * Z.conjTranspose) * Pm L B * ((Z⁻¹).conjTranspose * Z.conjTranspose) := by
          rw [hZtZ, hZc, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by rw [Pm]; simp only [Matrix.mul_assoc]
  refine ⟨⟨hAut, fun j x hx => sL_Xa F0 F'.fl hGr hPu j x hx, fun x hx => ?_⟩,
    ⟨hAut, fun j x hx => sL_Xa' F0 F'.fl hGr hP'u j x hx, fun x hx => ?_⟩⟩
  · have hx0 : ∀ a, (VS D).hT (F0.e a) x = 0 := fun a =>
      (Formalism.L2.SG.Pf.mem_orth' _ x).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)
    exact sL_orth F0 F'.fl hGr hPu hZu hrel hPl x hx0
  · have hx0 : ∀ a, (VS D).hT (F'.fl.e a) x = 0 := fun a =>
      (Formalism.L2.SG.Pf.mem_orth' _ x).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)
    exact sL_orth' F0 F'.fl hGr hP'u hZtu hrel' hP'l x hx0

end Nlam

section Gen

variable {D : D7} {u u' : D.what₂.Word}

theorem gen_data (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) {w : Point D.host.E (D.R.rS + 1)} {L U : MatR D}
    (hL : IsLoUni L) (hU : IsUpUni U) (hZu : IsUnit (Zhat F0 F'.fl).det)
    (hZ1 : Zhat F0 F'.fl * sgnM D.R.rS = L * ptMat w * U) (hGr : IsUnit (gramOf (gg F0 F'.fl)).det)
    (hT : ((Tu D u : ℕ) : D.host.E) ≠ 0) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs1 : s ∈ NLam Λ (lf D F0)) (hs2 : s ∈ NLam Λ F')
    {uu : MatR D} (hu : ∀ b, s (frame (lf D F0) b) = ∑ c, uu c b • frame (lf D F0) c)
    (a : GLR D) (ha : (a : MatR D) = L⁻¹ * uu.conjTranspose * L) :
    a ∈ StSet (ptMat w) ∧ tw F0 F'.fl L (hLu_of hL) hZu hGr a = s := by
  obtain ⟨⟨hiso, _⟩, hf1, hf2⟩ := hs1
  obtain ⟨⟨_, _⟩, hg1, hg2⟩ := hs2
  obtain ⟨uu0, huu0, hu0⟩ := tri_exists F0 s hf1 hf2
  obtain ⟨uu', huu', hu'⟩ := tri_exists F'.fl s hg1 hg2
  have heq : uu = uu0 := coef_unique (frame_indep F0 hT) (fun b => s (F0.fvec b)) uu uu0 hu hu0
  subst heq
  have hZc := zhat_conj F0 F'.fl s hiso uu uu' hu0 hu'
  set Z := Zhat F0 F'.fl with hZdef
  have hLu := hLu_of hL
  have hLi : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul _ hLu
  have hLL : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ hLu
  have hUi : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [up_det hU]; exact isUnit_one)
  have huH : IsUnit uu.conjTranspose.det := by rw [Matrix.det_conjTranspose, up_det huu0, star_one]; exact isUnit_one
  constructor
  ·
    have h2 : uu.conjTranspose * (L * ptMat w * U) * (sgnM D.R.rS * uu' * sgnM D.R.rS) = L * ptMat w * U := by
      rw [← hZ1]
      rw [show uu.conjTranspose * (Z * sgnM D.R.rS) * (sgnM D.R.rS * uu' * sgnM D.R.rS) =
        uu.conjTranspose * Z * (sgnM D.R.rS * sgnM D.R.rS) * uu' * sgnM D.R.rS by simp only [Matrix.mul_assoc],
        sgnM_sq, Matrix.mul_one, ← hZc]
    refine ⟨?_, U * (sgnM D.R.rS * uu' * sgnM D.R.rS) * U⁻¹, up_mul (up_mul hU (up_sgn huu')) (up_inv hU), ?_⟩
    · rw [ha]; exact lo_mul (lo_mul (lo_inv hL) (lo_conjT huu0)) hL
    · rw [ha]
      calc L⁻¹ * uu.conjTranspose * L * ptMat w * (U * (sgnM D.R.rS * uu' * sgnM D.R.rS) * U⁻¹)
          = L⁻¹ * (uu.conjTranspose * (L * ptMat w * U) * (sgnM D.R.rS * uu' * sgnM D.R.rS)) * U⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = (L⁻¹ * L) * ptMat w * (U * U⁻¹) := by rw [h2]; simp only [Matrix.mul_assoc]
        _ = ptMat w := by rw [hLi, hUi, Matrix.one_mul, Matrix.mul_one]
  · have hPm : Pm L (a : MatR D) = uu := by
      rw [Pm, ha]
      have : L * (L⁻¹ * uu.conjTranspose * L) * L⁻¹ = uu.conjTranspose := by
        calc L * (L⁻¹ * uu.conjTranspose * L) * L⁻¹ = (L * L⁻¹) * uu.conjTranspose * (L * L⁻¹) := by
              simp only [Matrix.mul_assoc]
          _ = uu.conjTranspose := by rw [hLL, Matrix.one_mul, Matrix.mul_one]
      rw [this, Matrix.conjTranspose_conjTranspose]
    have hainv : (a : MatR D)⁻¹ = L⁻¹ * (uu.conjTranspose)⁻¹ * L := by
      rw [ha]
      refine Matrix.inv_eq_left_inv ?_
      calc L⁻¹ * (uu.conjTranspose)⁻¹ * L * (L⁻¹ * uu.conjTranspose * L)
          = L⁻¹ * ((uu.conjTranspose)⁻¹ * ((L * L⁻¹) * uu.conjTranspose)) * L := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hLL, Matrix.one_mul, Matrix.nonsing_inv_mul _ huH, Matrix.mul_one, hLi]
    have hP'm : P'm F0 F'.fl L (a : MatR D) = uu' := by
      rw [P'm, hainv]
      have e1 : L * (L⁻¹ * (uu.conjTranspose)⁻¹ * L) * L⁻¹ = (uu.conjTranspose)⁻¹ := by
        calc L * (L⁻¹ * (uu.conjTranspose)⁻¹ * L) * L⁻¹ = (L * L⁻¹) * (uu.conjTranspose)⁻¹ * (L * L⁻¹) := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hLL, Matrix.one_mul, Matrix.mul_one]
      rw [e1]

      calc Z⁻¹ * (uu.conjTranspose)⁻¹ * Z = Z⁻¹ * (uu.conjTranspose)⁻¹ * (uu.conjTranspose * Z * uu') := by
            rw [← hZc]
        _ = Z⁻¹ * ((uu.conjTranspose)⁻¹ * uu.conjTranspose) * Z * uu' := by simp only [Matrix.mul_assoc]
        _ = uu' := by rw [Matrix.nonsing_inv_mul _ huH, Matrix.mul_one, Matrix.nonsing_inv_mul _ hZu, Matrix.one_mul]
    symm
    refine tw_eq_of hLu hZu hGr a s hiso (fun b => ?_) (fun b => ?_) (fun x hx => ?_)
    · rw [hPm]; exact hu0 b
    · rw [hP'm]; exact hu' b
    · refine hf2 x ?_
      rw [Formalism.L2.SG.Pf.mem_orth']
      exact Formalism.L2.SG.Pf.hT_span_left (by rintro _ ⟨i, rfl⟩; exact hx i)

end Gen

section Dict

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem tw_inv_eq {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F'' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) {L : MatR D} (hLu : IsUnit L.det)
    (hZu : IsUnit (Zhat F0 F'').det) (hGr : IsUnit (gramOf (gg F0 F'')).det) (a : GLR D) :
    tw F0 F'' L hLu hZu hGr a⁻¹ = (tw F0 F'' L hLu hZu hGr a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← tw_mul, mul_inv_cancel, tw_one]

open Formalism.L2.SG.PackageTie2 in

theorem volume_dictionary_lu_decomposition (Y : Formalism.L2.SG.Full.Full X) {u u' : D.what₂.Word} (t : TT Y u u')
    {w : Point D.host.E (D.R.rS + 1)} {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {L U : MatR D}
    (hL : IsLoUni L) (hU : IsUpUni U) (hZu : IsUnit (Zhat (X.Fu u) F'.fl).det)
    (hZ1 : Zhat (X.Fu u) F'.fl * sgnM D.R.rS = L * ptMat w * U) (hGr : IsUnit (gramOf (gg (X.Fu u) F'.fl)).det)
    (hT : ((Tu D u : ℕ) : D.host.E) ≠ 0)
    {n0 m0 : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn0 : n0 ∈ NLam t.lam (lf D (X.Fu u)))
    (hm0 : m0 ∈ NLam t.lam t.frame) (hfr : ∀ a, frame F' a = n0 (m0 (frame t.frame a))) :
    (rpt X n0 hn0.1.1).1 ∈ X.NinfU u ∧ Function.Injective (Phi X (X.Fu u) F'.fl hL hU hZu hZ1 hGr) ∧
      (∀ β, (rpt X n0 hn0.1.1).1⁻¹ * Phi X (X.Fu u) F'.fl hL hU hZu hZ1 hGr β * (rpt X n0 hn0.1.1).1 ∈
        Formalism.L2.SG.TermOp.Vanish.Rset t) ∧
      (∀ y, (∃ β : StG w, (β : GLR D) ∈ stabAut D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L ∧
          Phi X (X.Fu u) F'.fl hL hU hZu hZ1 hGr β = y) ↔
        ∃ r ∈ Formalism.L2.SG.TermOp.ROinf t, y = (rpt X n0 hn0.1.1).1 * r * (rpt X n0 hn0.1.1).1⁻¹) := by
  have hγi : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  have hγx : RatLink X t.pt t.lin := t.rep.2.1
  have hfe : t.frame = Formalism.L2.SG.Saturated.mapL t.lin hγi (lf D (X.Fu u')) := Formalism.L2.SG.Pf.FibreCounting.frame_eq t
  set xn := rpt X n0 hn0.1.1 with hxn
  have hxnL : RatLink X xn n0 := rpt_spec X _ _
  set Φ := Phi X (X.Fu u) F'.fl hL hU hZu hZ1 hGr with hΦ

  set m0' := t.lin⁻¹ * m0 * t.lin with hm0'def
  have hm0' : m0' ∈ NLam t.lam' (lf D (X.Fu u')) :=
    (Formalism.L2.SG.Pf.mem_NLam_map t.lin hγi t.lam' (lf D (X.Fu u')) m0).1 (by rw [hγΛ, ← hfe]; exact hm0)
  set γ' := n0 * t.lin * m0' with hγ'def
  have hγ'i : γ' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (mul_mem hn0.1.1 hγi) hm0'.1.1
  have hγ'Λ : Formalism.HermitianLatticesTheory.gmap γ' t.lam' = t.lam := by
    rw [hγ'def, Formalism.L2.SG.Pf.gmap_mul_sat, Formalism.L2.SG.Pf.gmap_mul_sat, hm0'.1.2, hγΛ, hn0.1.2]
  have hNF' : ∀ n, γ'⁻¹ * n * γ' ∈ NLam t.lam' (lf D (X.Fu u')) ↔ n ∈ NLam t.lam F' := by
    intro n
    rw [← Formalism.L2.SG.Pf.mem_NLam_map γ' hγ'i t.lam' (lf D (X.Fu u')) n, hγ'Λ]
    have h1 : IsAutLam (VS D) t.lam (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) :=
      ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, Formalism.L2.SG.Pf.gmap_one_sat _⟩
    have hfr1 : ∀ a, frame F' a = (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V)
        (frame (Formalism.L2.SG.Saturated.mapL γ' hγ'i (lf D (X.Fu u'))) a) := by
      intro a
      have h2 : frame F' a = n0 (m0 (frame t.frame a)) := hfr a
      have h3 : frame t.frame a = t.lin ((X.Fu u').fvec a) := Formalism.L2.SG.Pf.FibreCounting.frame_apply t a
      have h4 : frame (Formalism.L2.SG.Saturated.mapL γ' hγ'i (lf D (X.Fu u'))) a = γ' ((X.Fu u').fvec a) :=
        Formalism.L2.SG.Saturated.frame_mapL γ' hγ'i (lf D (X.Fu u')) a
      have h5 : γ' ((X.Fu u').fvec a) = n0 (m0 (t.lin ((X.Fu u').fvec a))) := by
        show n0 (t.lin (t.lin.symm (m0 (t.lin _)))) = _
        rw [LinearEquiv.apply_symm_apply]
      exact h2.trans ((congrArg (fun v => n0 (m0 v)) h3).trans (h5.symm.trans h4.symm))
    have this2 := (Formalism.L2.SG.Pf.RelativeIndexFlags.nlam_conj h1 hfr1 n).symm
    simp only [inv_one, one_mul, mul_one] at this2
    exact this2
  have hRO : ∀ y, (∃ r ∈ Formalism.L2.SG.TermOp.ROinf t, y = xn.1 * r * xn.1⁻¹) ↔
      y ∈ ROset X (X.Fu u) (X.Fu u') t.lam t.lam' γ' := by
    intro y
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact (Formalism.L2.SG.TermOp.Vanish.roset_conj X hn0 hm0' hxnL r).1 hr
    · intro hy
      refine ⟨xn.1⁻¹ * y * xn.1, ?_, by group⟩
      refine (Formalism.L2.SG.TermOp.Vanish.roset_conj X hn0 hm0' hxnL _).2 ?_
      have e : xn.1 * (xn.1⁻¹ * y * xn.1) * xn.1⁻¹ = y := by group
      rw [e]; exact hy

  have hgen : ∀ a ∈ stabAutSet D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L,
      a ∈ StSet (ptMat w) ∧ ∃ s ∈ NLam t.lam (lf D (X.Fu u)) ∩ NLam t.lam F',
        tw (X.Fu u) F'.fl L (hLu_of hL) hZu hGr a = s := by
    rintro a ⟨s, ⟨hs1, hs2⟩, uu, hu, ha⟩
    obtain ⟨h1, h2⟩ := gen_data (X.Fu u) F' hL hU hZu hZ1 hGr hT hs1 hs2 hu a ha
    exact ⟨h1, s, ⟨hs1, hs2⟩, h2⟩
  have hsub : stabAut D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L ≤ StG w :=
    (Subgroup.closure_le _).2 fun a ha => (hgen a ha).1
  refine ⟨Formalism.L2.SG.Pf.nLamNinf_holds D X u t.lam xn n0 hxnL hn0,
    Phi_inj X (X.Fu u) F'.fl hL hU hZu hZ1 hGr hT, ?_, ?_⟩
  · intro β
    have hsβ := tw_nlam (X.Fu u) F' hL hU hZu hZ1 hGr β⁻¹
    set sβ := tw (X.Fu u) F'.fl L (hLu_of hL) hZu hGr ((β⁻¹ : StG w) : GLR D) with hsβdef
    have hxs : RatLink X (rpt X sβ (tw_isom_st (X.Fu u) F'.fl hL hU hZu hZ1 hGr β⁻¹)) sβ := rpt_spec X _ _
    set y0 := xn⁻¹ * rpt X sβ (tw_isom_st (X.Fu u) F'.fl hL hU hZu hZ1 hGr β⁻¹) * xn with hy0
    have hy0L : RatLink X y0 (n0⁻¹ * sβ * n0) :=
      Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X
        (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hxnL) hxs) hxnL
    have hn0b := nlam_bot_of hn0
    have hm1 : n0⁻¹ * sβ * n0 ∈ NLam ⊥ (lf D (X.Fu u)) :=
      Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_inv hn0b) hsβ.1) hn0b
    have he : xn.1⁻¹ * Φ β * xn.1 = y0.1 := by
      simp only [hy0, Prod.fst_mul, Prod.fst_inv]; rfl
    rw [he]
    refine ⟨Formalism.L2.SG.Pf.nLamNinf_holds D X u ⊥ y0 _ hy0L hm1, ?_⟩
    have hg : IsAutLam (VS D) ⊥ (n0 * m0) := ⟨mul_mem hn0.1.1 hm0.1.1, gmap_bot _⟩
    have hfr' : ∀ a, frame F' a = (n0 * m0) (frame t.frame a) := fun a => hfr a
    have hc1 := (Formalism.L2.SG.Pf.RelativeIndexFlags.nlam_conj hg hfr' sβ).1 hsβ.2
    have hm0b := nlam_bot_of hm0
    have hc2 : n0⁻¹ * sβ * n0 ∈ NLam ⊥ t.frame := by
      have e : n0⁻¹ * sβ * n0 = m0 * ((n0 * m0)⁻¹ * sβ * (n0 * m0)) * m0⁻¹ := by group
      rw [e]
      exact Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_mul hm0b hc1) (Formalism.L2.SG.Pf.nlamPf_inv hm0b)
    have hc3 : t.lin⁻¹ * (n0⁻¹ * sβ * n0) * t.lin ∈ NLam ⊥ (lf D (X.Fu u')) := by
      have := (Formalism.L2.SG.Pf.mem_NLam_map t.lin hγi ⊥ (lf D (X.Fu u')) (n0⁻¹ * sβ * n0)).1
      apply this
      rw [gmap_bot, ← hfe]; exact hc2
    have hz : RatLink X (t.pt⁻¹ * y0 * t.pt) (t.lin⁻¹ * (n0⁻¹ * sβ * n0) * t.lin) :=
      Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X
        (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hγx) hy0L) hγx
    have := Formalism.L2.SG.Pf.nLamNinf_holds D X u' ⊥ _ _ hz hc3
    rwa [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv] at this
  · intro y
    rw [hRO y]
    constructor
    · rintro ⟨β, hβS, rfl⟩
      have key : ∀ a (ha : a ∈ stabAut D u u' (X.Fu u) (Y.what₂ u) t.toTerm F' L) (hst : a ∈ StG w),
          Φ ⟨a, hst⟩ ∈ ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' γ' := by
        intro a ha
        induction ha using Subgroup.closure_induction with
        | mem a ha =>
          intro hst
          obtain ⟨-, s, ⟨hs1, hs2⟩, hts⟩ := hgen a ha
          have hinv : tw (X.Fu u) F'.fl L (hLu_of hL) hZu hGr ((⟨a, hst⟩⁻¹ : StG w) : GLR D) = s⁻¹ := by
            exact (tw_inv_eq (X.Fu u) F'.fl (hLu_of hL) hZu hGr a).trans (congrArg Inv.inv hts)
          have hxs : RatLink X (rpt X _ (tw_isom_st (X.Fu u) F'.fl hL hU hZu hZ1 hGr ⟨a, hst⟩⁻¹)) s⁻¹ := by
            rw [← hinv]; exact rpt_spec X _ _
          refine ⟨_, s⁻¹, hxs, rfl, Formalism.L2.SG.Pf.nlamPf_inv hs1, (hNF' s⁻¹).2 (Formalism.L2.SG.Pf.nlamPf_inv hs2)⟩
        | one =>
          intro hst
          have : (⟨1, hst⟩ : StG w) = 1 := rfl
          rw [this, map_one]; exact (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' γ').one_mem
        | mul x z hx hz ihx ihz =>
          intro hst
          have hxS := hsub hx
          have hzS := hsub hz
          have : (⟨x * z, hst⟩ : StG w) = ⟨x, hxS⟩ * ⟨z, hzS⟩ := rfl
          rw [this, map_mul]
          exact (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' γ').mul_mem (ihx hxS) (ihz hzS)
        | inv x hx ihx =>
          intro hst
          have hxS := hsub hx
          have : (⟨x⁻¹, hst⟩ : StG w) = (⟨x, hxS⟩ : StG w)⁻¹ := rfl
          rw [this, map_inv]
          exact (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' γ').inv_mem (ihx hxS)
      exact key (β : GLR D) hβS β.2
    · rintro ⟨x, n, hx, rfl, hn1, hn2⟩
      have hn2' := (hNF' n).1 hn2
      have hs1 := Formalism.L2.SG.Pf.nlamPf_inv hn1
      have hs2 := Formalism.L2.SG.Pf.nlamPf_inv hn2'
      obtain ⟨⟨_, _⟩, hf1, hf2⟩ := hs1
      obtain ⟨uu, huu, hu⟩ := tri_exists (X.Fu u) n⁻¹ hf1 hf2
      set M : MatR D := L⁻¹ * uu.conjTranspose * L with hM
      have hMdet : IsUnit M.det := by
        rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, up_det huu, star_one, mul_one,
          ← Matrix.det_mul, Matrix.nonsing_inv_mul _ (hLu_of hL), Matrix.det_one]
        exact isUnit_one
      set a : GLR D := Matrix.nonsingInvUnit M hMdet with ha
      have haM : (a : MatR D) = L⁻¹ * uu.conjTranspose * L := rfl
      obtain ⟨haS, hta⟩ := gen_data (X.Fu u) F' hL hU hZu hZ1 hGr hT (Formalism.L2.SG.Pf.nlamPf_inv hn1)
        (Formalism.L2.SG.Pf.nlamPf_inv hn2') hu a haM
      refine ⟨⟨a, haS⟩, Subgroup.subset_closure ⟨n⁻¹, ⟨Formalism.L2.SG.Pf.nlamPf_inv hn1,
        Formalism.L2.SG.Pf.nlamPf_inv hn2'⟩, uu, hu, haM⟩, ?_⟩
      have hinv : tw (X.Fu u) F'.fl L (hLu_of hL) hZu hGr ((⟨a, haS⟩⁻¹ : StG w) : GLR D) = n := by
        exact (tw_inv_eq (X.Fu u) F'.fl (hLu_of hL) hZu hGr a).trans ((congrArg Inv.inv hta).trans (inv_inv n))
      have hxL : RatLink X x (tw (X.Fu u) F'.fl L (hLu_of hL) hZu hGr ((⟨a, haS⟩⁻¹ : StG w) : GLR D)) := by
        rw [hinv]; exact hx
      exact congrArg Prod.fst (rpt_eq X _ hxL)

end Dict

end Formalism.L2.SG.Pf.VolPinAsm
