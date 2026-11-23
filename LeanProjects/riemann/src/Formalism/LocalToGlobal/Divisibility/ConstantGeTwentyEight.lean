import Mathlib
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
import Formalism.LocalToGlobal.IndefiniteForms.PairingConditionOfInverseMatrixIdentity

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
open Formalism.LatticeIndexTer (ph)

section GenericR

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}

def FoOfR (P : IndefCoreR Df0 Df1 Dc Sp N) : ℝ :=
  ∑ j, ∑ y ∈ P.base.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)

def boundBR (P : IndefCoreR Df0 Df1 Dc Sp N) (LG E3 : ℝ) (E2 : Bs.J → ℝ) : ℝ :=
  (∑ j, N.l3 j) + 2 * FoOfR P + LG + (∑ j, (N.E1 j + E2 j)) + E3

structure DivInputs0R {Pl : Type} [Fintype Pl] [DecidableEq Pl] (P : IndefCoreR Df0 Df1 Dc Sp N) (R : RecNums Bs.J Pl)
    (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ) where

  Nu_lat : Submodule.IsLattice K Nu

  sg_fin : (Function.support (shiftZ sg)).Finite

  Xc_unit : ∀ v, IsUnit (Dc.Xc u v).det

  a_pos : 0 < Dc.a u

  X0 : InfinitePlace K → Matrix (Fin (Df1.nV Bs.μ0)) (Fin (Df1.nV Bs.μ0)) ℂ

  base_matrix_det_unit : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df1.HV Bs.μ0).map v.embedding

  ch : ColChain Dc u

  hn : HtNums R (InfinitePlace K)

  nP : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
    (Pi.basisFun K (Fin (Df1.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn

  cb : CBData ch.X ch.Kj

  nKcb : ∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v

  eig6 : ∑ j, R.hX j ≤ ∑ j, N.l6 j

  eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin (Df0.dQ t) → Fin (Df0.dQ t) → K

  heb : ∀ t w, IsLocBasis (Df0.abelian₂ t) w (eb t w)

  Sy : Finset (HeightOneSpectrum (𝓞 K))

  Sy_tw : P.base.Tw ⊆ Sy

  G0 : ∀ y, y ∉ Sy → vw y (Df0.Gm eb (P.base.μ y) y) = 0

  LG : ℝ

  E3 : ℝ

  E2 : Bs.J → ℝ

  gy : HeightOneSpectrum (𝓞 K) → ℝ

  ηy : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  bi : ∀ y ∈ Sy, (vw y (Df0.Gm eb (P.base.μ y) y) : ℝ) ≤ (P.base.D : ℝ) * gy y

  bLG : ∑ y ∈ Sy, lw y * gy y ≤ LG

  biv : ∀ y ∈ P.base.Tw, ∀ j, (jw (Df0.HT j (P.base.μ y)) y (Df0.Tl j (P.base.μ y)) : ℝ) ≤
    ((ramw y : ℝ) * N.J0 (P.base.μ y) y j) * (P.base.D : ℝ) + ηy y j

  borderedMinorImage : ∀ j, ∑ y ∈ P.base.Tw, lw y * ηy y j / (P.base.D : ℝ) ≤ E2 j

  twisted_third_sum_le : ∑ y ∈ Sy, lw y * (2 / ellw y ^ 2) ≤ E3

  El3 : ℝ

  L3main : ∑ j, N.l3 j ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + El3

  errB : El3 + LG + (∑ j, (N.E1 j + E2 j)) + E3 ≤ R.errB

  Q : ℝ

  de0 : 0 ≤ N.de

  deQ : 3 * N.de * Q ≤ 1

  Q1 : 1 ≤ Q

  Qb : boundBR P LG E3 E2 + N.hh + 28 * N.la ≤ Q

  la_le : N.la ≤ R.lam0

  constant_ge_twenty_eight : 28 ≤ R.C0

structure DivInputsR {Pl : Type} [Fintype Pl] [DecidableEq Pl] (P : IndefCoreR Df0 Df1 Dc Sp N) (R : RecNums Bs.J Pl)
    (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ) extends DivInputs0R P R u Nu sg where

  val2 : ∀ w, ∀ φ ∈ Nu, ∀ F ∈ Df1.Mt (P.cols.μ w),
    Dc.Pt u (P.cols.μ w) φ F = 0 ∨ sg w ≤ (vw w (Dc.Pt u (P.cols.μ w) φ F) : ℝ)

def DivClausesR {Pl : Type} [Fintype Pl] [DecidableEq Pl] (P : IndefCoreR Df0 Df1 Dc Sp N) (R : RecNums Bs.J Pl)
    (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ) : Prop :=
  (∀ φ ∈ shiftLat Nu sg, P.cols.col.B u φ ∈ Formalism.HN.dualLat P.cols.RR) ∧
  (∃ cu : InfinitePlace K → ℝ, (∀ v, 0 < cu v ∧
      Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin P.cols.D)).dualBasis
        (Formalism.HN.dualFrame P.cols.XE) v (P.cols.col.B u) ^ 2 ≤ cu v) ∧
    (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (cu v) = R.hu - meanLog P.cols.κ) ∧
  P.cols.muCC - meanLog P.cols.κ + R.hu - 2 * FoOfR P ≤ R.rhs ∧
  Formalism.HN.muDef (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (shiftLat Nu sg) =
    Formalism.HN.muDef (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) Nu +
      2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (shiftZ sg w : ℝ)

theorem height_chain_atR {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} [Nonempty Bs.Ix] (wf : Df.WF)
    (S : IndefColsR Df Dc Sp N) (u : Dc.Mem) (hne : S.col.B u ≠ 0)
    (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df.HV Bs.μ0).map v.embedding)
    (ch : ColChain Dc u) (hP : ℝ) (hK : Bs.J → InfinitePlace K → ℝ)
    (nP : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
      (Pi.basisFun K (Fin (Df.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hP)
    (nK : ∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c j.castSucc))) (ch.X j.castSucc)
      (Pi.basisFun K (Fin (ch.c j.succ))) (ch.X j.succ) v (Matrix.mulVecLin (ch.Kj j)) ^ 2 ≤
        Real.exp (∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v)) :
    (∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin S.D)).dualBasis
        (Formalism.HN.dualFrame S.XE) v (S.col.B u) ^ 2) ≤
      hP + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v - Real.log (S.κ v) -
        minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v))) ∧
    (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, (hP + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v -
        Real.log (S.κ v) - minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v))) ≤
      hP + ∑ j, (∑ v, hK j v) / (Fintype.card (InfinitePlace K) : ℝ) - ∑ j, N.l6 j - meanLog S.κ := by
  have hc := S.l1c
  have hb := S.l1b
  have hsc : ∀ v p, IsScalarOn (Df.XQ Bs.μ0) S.XE v (S.ι Bs.μ0) (Df.Qp Bs.μ0 p)
      (S.κ v * ∏ j, S.lam j Bs.μ0 p v) := fun v p => by
    rw [← S.Qpart_base p]; exact hc.2.2.2 Bs.μ0 v (Or.inl rfl) p
  have Hv := fun v => complex_height_cast_at height_constant_bound ch.c ch.c0 (S.dQ_eq Bs.μ0) (Dc.Xc u) ch.X ch.X_unit ch.X_zero
    ch.Kj (Df.HV Bs.μ0) X0 hX0 (Df.Pq Bs.μ0) (wf.Pq_surj _) (Df.XQ Bs.μ0) (wf.XQ_quot _) S.XE S.frames (S.ι Bs.μ0) (hc.1 _)
    Bs.Ix Bs.J (Df.Qp Bs.μ0) wf.Qp_top S.κ (fun j p v => S.lam j Bs.μ0 p v) hc.2.1 (fun j p v => hc.2.2.1 j _ p v) hsc
    ch.PtL (S.col.B u)
    (fun φ F => by
      have h1 := hb.1 u Bs.μ0 φ F
      rw [hb.2.1 u, one_mul] at h1
      rw [← h1]; exact ch.fact φ F)
    hne (fun _ => Real.exp (hP / 2)) (fun j v => Real.exp ((∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v) / 2))
    (fun v => le_exp_half (nP v)) (fun j v => le_exp_half (nK j v)) v
  simp only [log_exp_half_sq] at Hv
  refine ⟨Hv, ?_⟩
  have hn : (0 : ℝ) < (Fintype.card (InfinitePlace K) : ℝ) := by
    have : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    exact_mod_cast this
  have h2 : ∑ j, N.l6 j ≤ (1 / (Fintype.card (InfinitePlace K) : ℝ)) *
      ∑ v, minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) := by
    have h3 : ∑ _v : InfinitePlace K, ∑ j, N.l6 j ≤
        ∑ v, minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) := Finset.sum_le_sum fun v _ => S.log_eigenvalue_sum_le_min v
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h3
    rw [one_div, le_inv_mul_iff₀ (by exact hn)]
    exact h3
  have h4 : (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, (hP + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v) =
      hP + ∑ j, (∑ v, hK j v) / (Fintype.card (InfinitePlace K) : ℝ) := by
    have e1 : ∀ v, ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v = ∑ j, hK j v := fun v =>
      Finset.sum_fiberwise Finset.univ ch.lf (fun l => hK l v)
    simp only [e1]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm, ← Finset.sum_div]
    field_simp
  have e : (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, (hP + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v -
        Real.log (S.κ v) - minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v))) =
      (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, (hP + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v) -
        (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) - meanLog S.κ := by
    simp only [meanLog, Finset.sum_sub_distrib]
    show _ = _ - _ - (1 / (Fintype.card (InfinitePlace K) : ℝ)) * _
    ring
  rw [e, h4]
  linarith [h2]

theorem divClausesR_of [IsTotallyComplex K] {Pl : Type} [Fintype Pl] [DecidableEq Pl] (wf0 : Df0.WF) (wf1 : Df1.WF)
    (P : IndefCoreR Df0 Df1 Dc Sp N) (R : RecNums Bs.J Pl) (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K))
    (sg : HeightOneSpectrum (𝓞 K) → ℝ) (I : DivInputsR P R u Nu sg) : DivClausesR P R u Nu sg := by
  have : Nonempty Bs.Ix := nonempty_Ix wf0 P.base.pos
  have hsh := shiftEx K (Dc.a u) Nu I.Nu_lat (shiftZ sg) I.sg_fin
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    exact P.cols.intoDual divIntoDualShift latticeGlue wf1 u Nu (shiftLat Nu sg) sg (shiftZ sg) I.val2
      (fun w => Int.floor_le_ceil _) hsh.1
  ·
    have hX := fun v => OperatorNormFrames.opNormAt_nonneg (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin P.cols.D)).dualBasis
      (Formalism.HN.dualFrame P.cols.XE) v (P.cols.col.B u)
    by_cases hne : P.cols.col.B u = 0
    · refine exists_cu _ (fun _ => R.hu - meanLog P.cols.κ) _ hX (fun v => Or.inl ?_) (le_of_eq ?_)
      · rw [hne]; simp [Formalism.HN.opNormAt]
      · have hn : (0 : ℝ) < (Fintype.card (InfinitePlace K) : ℝ) := by
          have : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
          exact_mod_cast this
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
    · have nK := nK_of_cb I.cb (fun j v => ∑ l ∈ Finset.univ.filter (fun l => I.ch.lf l = j), I.hn.sz l v) I.nKcb
      obtain ⟨Hv, Hm⟩ := height_chain_atR wf1 P.cols u hne I.X0 I.base_matrix_det_unit I.ch I.hn.hPn I.hn.sz I.nP nK
      have h1 := I.hn.le_hu (∑ j, N.l6 j) I.eig6
      refine exists_cu _ (fun v => I.hn.hPn + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => I.ch.lf l = j), I.hn.sz l v -
        Real.log (P.cols.κ v) - minOver (fun p => ∑ j, Real.log (P.cols.lam j Bs.μ0 p v))) _ hX (fun v => Or.inr (Hv v)) ?_
      linarith [Hm, h1]
  ·
    have hB := P.base.boundsMu Formalism.DivisorInequality.boundsMu specDet reduction_lemma_zero latticeGlue ramBasic wf0 P.extra.untw I.eb I.heb
      I.Sy I.Sy_tw I.G0 I.LG I.E3 I.E2 I.gy I.ηy I.bi I.bLG I.biv I.borderedMinorImage I.twisted_third_sum_le
    have de0 : 0 ≤ N.de := I.de0
    have deQ : 3 * N.de * I.Q ≤ 1 := I.deQ
    have de3 : N.de ≤ 1 / 3 := by nlinarith [I.Q1]
    have hp := (P.extra.passage de0 de3 _ P.extra.fun0).2
    have hκ : P.cols.κ = P.base.κ := P.extra.level.2.1.symm
    set mu0 : ℝ := P.base.muCC - meanLog P.base.κ with hmu0def
    have hmu0 : mu0 ≤ boundBR P I.LG I.E3 I.E2 := by
      have : P.base.muCC ≤ meanLog P.base.κ + (∑ j, N.l3 j) +
          2 * (∑ j, ∑ y ∈ P.base.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)) + I.LG +
          (∑ j, (N.E1 j + I.E2 j)) + I.E3 := hB
      simp only [boundBR, FoOfR, hmu0def]
      linarith
    have hpass : 3 * N.de * (mu0 + N.hh + 28 * N.la) + 28 * N.la ≤ 1 + R.C0 * (R.m * R.lam0) := by
      have h1 : 3 * N.de * (mu0 + N.hh + 28 * N.la) ≤ 3 * N.de * I.Q :=
        mul_le_mul_of_nonneg_left (by linarith [I.Qb]) (by linarith)
      have h2 : 28 * R.lam0 ≤ R.C0 * (R.m * R.lam0) := by
        have h3 : R.lam0 ≤ R.m * R.lam0 := by nlinarith [R.p14, R.p35]
        nlinarith [I.constant_ge_twenty_eight, R.p35, R.c1]
      linarith [I.la_le]
    have hC : P.cols.muCC - meanLog P.cols.κ ≤ mu0 + (3 * N.de * (mu0 + N.hh + 28 * N.la) + 28 * N.la) := by
      rw [hκ, hmu0def]
      have : P.cols.muCC ≤ P.base.muCC + 3 * N.de * (P.base.muCC + (N.hh - meanLog P.base.κ) + 28 * N.la) +
          28 * N.la := hp
      have e : P.base.muCC + (N.hh - meanLog P.base.κ) + 28 * N.la =
          P.base.muCC - meanLog P.base.κ + N.hh + 28 * N.la := by ring
      rw [e] at this
      linarith
    have hM : mu0 ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + 2 * FoOfR P +
        (I.El3 + I.LG + (∑ j, (N.E1 j + I.E2 j)) + I.E3) := by
      have h1 := I.L3main
      have h2 : boundBR P I.LG I.E3 I.E2 = (∑ j, N.l3 j) + 2 * FoOfR P + I.LG + (∑ j, (N.E1 j + I.E2 j)) + I.E3 := rfl
      linarith
    exact R.divIneq _ mu0 (FoOfR P) _ _ hC hM hpass I.errB
  ·
    exact ((shiftMu K (Dc.a u) (Dc.Xc u) I.Xc_unit Nu (shiftLat Nu sg) I.Nu_lat hsh.2.1 (shiftZ sg) hsh.1).2 I.a_pos).2

theorem divClausesR_toR {Pl : Type} [Fintype Pl] [DecidableEq Pl] (P : IndefCore Df0 Df1 Dc Sp N) (R : RecNums Bs.J Pl)
    (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ) :
    DivClausesR P.toR R u Nu sg ↔ DivClauses P R u Nu sg :=
  Iff.rfl

def DivInputs.toR {Pl : Type} [Fintype Pl] [DecidableEq Pl] {P : IndefCore Df0 Df1 Dc Sp N} {R : RecNums Bs.J Pl}
    {u : Dc.Mem} {Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)} {sg : HeightOneSpectrum (𝓞 K) → ℝ} (I : DivInputs P R u Nu sg) :
    DivInputsR P.toR R u Nu sg :=
  { I with }

end GenericR

section ConcreteR

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

theorem linkDIV_L2R_clauses [IsTotallyComplex K] (A : FamIn K G Pl0 T m) {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep)
    (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (cf : ConvFace A.fam.base) (C CH : ℝ)
    (Pk : IndefPkgR A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A.fam.base.J Pl) (u : (Dc Pk.Zs).Mem)
    (Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ)
    (I : DivInputsR Pk.core R u Nu sg) : DivClausesR Pk.core R u Nu sg :=
  divClausesR_of (A.side_WF hOk P0 ψ0 Pk.Zs Pk.stable Pk.inBlock hsep)
    (A.side_WF hOk P1 ψ1 Pk.Zs Pk.stable Pk.inBlock hsep) Pk.core R u Nu sg I

end ConcreteR

section ConcreteColR

open Formalism.BasicNotions Formalism.L2.Col

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}
  {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

theorem linkDIV_L2R [IsTotallyComplex X.K] (A : FamIn X.K G Pl0 T m) {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep)
    (P0 : Subgroup G) (ψ0 : P0 →* X.Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* X.Kˣ) (hX : X.Ok)
    {P : LevFam X.E X.K Rk.r Pr.vGs} (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K)) {m2 : ℕ} {Gc : ChGlob X Rk.m}
    (mu : A.fam.base.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (Am : Formalism.L2.Ker.Amb X) (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok) (hE : ∀ x, (evGSD W Ch sel (mu A.fam.base.μ0) P (wd x)).Ok)
    (ev : ∀ (Zs : DefSub A.fam.amb) t, (Fin ((A.side P1 ψ1 Zs).nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P)
    (Sp : ∀ Zs : DefSub A.fam.amb, SPer (colFace hX (A.side P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY (kerRec mu cst L wd b hY Am hK) hF (ev Zs)))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (cf : ConvFace A.fam.base) (C CH : ℝ)
    (Pk : IndefPkgR A.fam.amb
      (faceOf A P0 ψ0 P1 ψ1 (fun Zs => colFace hX (A.side P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY (kerRec mu cst L wd b hY Am hK) hF (ev Zs)) Sp Zsc)
      cf C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A.fam.base.J Pl) (x : Mem)
    (Nu : Submodule (𝓞 X.K) (Fin (ramDim W Ch hX (wd x)) → X.K)) (sg : HeightOneSpectrum (𝓞 X.K) → ℝ)
    (I : DivInputsR Pk.core R x Nu sg)
    (hQ : ChainTie I.ch (memQ (A := kerRec mu cst L wd b hY Am hK) (hF := hF) hE (x := x))) (h0 : FirstCols hE hQ) :
    DivClausesR Pk.core R x Nu sg ∧
      (∀ y : Fin (I.ch.c 0) → X.K,
        hQ.coL ((chainMat I.ch.Kj ⟨(memQ (A := kerRec mu cst L wd b hY Am hK) (hF := hF) hE (x := x)).n + 1, by have := hQ.hmm; omega⟩).mulVec y) =
          Formalism.L2.Ker.colMu W Ch sel (mu A.fam.base.μ0) (cst A.fam.base.μ0) (L A.fam.base.μ0) Am (wd x) m2 (b A.fam.base.μ0 x) (hY A.fam.base.μ0 x) P
            (hK A.fam.base.μ0 x) (hF A.fam.base.μ0 x) (hL A.fam.base.μ0) (colOfCoord W Ch hX (wd x) fun i => y (Fin.cast I.ch.c0.symm i))) ∧
      ∀ (φ : Fin (ramDim W Ch hX (wd x)) → X.K) (F : Fin ((A.side P1 ψ1 Pk.Zs).nV A.fam.base.μ0) → X.K),
        I.ch.PtL ((chainMat I.ch.Kj (Fin.last I.ch.mm)).mulVec fun i => φ (Fin.cast I.ch.c0 i)) F =
          colPerL (hP A.fam.base.μ0) Xg (wd x) (ev Pk.Zs A.fam.base.μ0)
            (Formalism.L2.Ker.colMu W Ch sel (mu A.fam.base.μ0) (cst A.fam.base.μ0) (L A.fam.base.μ0) Am (wd x) m2 (b A.fam.base.μ0 x) (hY A.fam.base.μ0 x) P
              (hK A.fam.base.μ0 x) (hF A.fam.base.μ0 x) (hL A.fam.base.μ0) (colOfCoord W Ch hX (wd x) φ)) F :=
  ⟨divClausesR_of (A.side_WF hOk P0 ψ0 Pk.Zs Pk.stable Pk.inBlock hsep)
    (A.side_WF hOk P1 ψ1 Pk.Zs Pk.stable Pk.inBlock hsep) Pk.core R x Nu sg I, FirstCols.chain hE h0, fun φ F => (I.ch.fact φ F).symm⟩

end ConcreteColR

end Formalism.L2.DIV
