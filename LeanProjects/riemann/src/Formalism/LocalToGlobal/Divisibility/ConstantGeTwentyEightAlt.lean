import Formalism.LocalToGlobal.Divisibility.TwistedPlaceEtaSumLeExtended

noncomputable section

open Module NumberField IsDedekindDomain

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

section Arith

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

structure ArithAt (A3 : FamIn3 K G Pl0 I0 Ty T m) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (cf : ConvFace A3.fam3.base3) (C CH : ℝ)
    (Pk : IndefPkgR A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A3.fam3.base3.J Pl) (bd : Fin m → ℝ) (dg : ℕ) : Prop where
  eig6 : ∑ j, R.hX j ≤ ∑ j, ((Zsc Pk.Zs).num C CH).l6 j
  hG0 : Real.log (Fintype.card G) ≤ R.lam0
  l3 : ∃ El3 : ℝ, ∑ j, ((Zsc Pk.Zs).num C CH).l3 j ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + El3 ∧
    El3 + lgDef R s + (∑ j, (((Zsc Pk.Zs).num C CH).E1 j + etaSumBound bd dg s j)) + 1 ≤ R.errB
  q : ∃ Q : ℝ, 0 ≤ ((Zsc Pk.Zs).num C CH).de ∧ 3 * ((Zsc Pk.Zs).num C CH).de * Q ≤ 1 ∧ 1 ≤ Q ∧
    boundBR Pk.core (lgDef R s) 1 (etaSumBound bd dg s) + ((Zsc Pk.Zs).num C CH).hh + 28 * ((Zsc Pk.Zs).num C CH).la ≤ Q
  la_le : ((Zsc Pk.Zs).num C CH).la ≤ R.lam0
  constant_ge_twenty_eight : 28 ≤ R.C0

variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {s : ℕ} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G}
  {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {cf : ConvFace A3.fam3.base3} {C CH : ℝ}
  {Pk : IndefPkgR A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH}
  {Pl : Type} [Fintype Pl] [DecidableEq Pl] {R : RecNums A3.fam3.base3.J Pl} {u : (Dc Pk.Zs).Mem}
  {Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)} {sg : HeightOneSpectrum (𝓞 K) → ℝ} {bd : Fin m → ℝ}

def DivisionInputsWithoutNorm.ofRows (hNu : Submodule.IsLattice K Nu) (hsg : (Function.support (shiftZ sg)).Finite)
    (hXc : ∀ v, IsUnit ((Dc Pk.Zs).Xc u v).det) (ha : 0 < (Dc Pk.Zs).a u)
    (X0 : InfinitePlace K → Matrix (Fin ((A3.side3 P1 ψ1 Pk.Zs).nV A3.fam3.base3.μ0))
      (Fin ((A3.side3 P1 ψ1 Pk.Zs).nV A3.fam3.base3.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧
      ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((A3.side3 P1 ψ1 Pk.Zs).HV A3.fam3.base3.μ0).map v.embedding)
    (ch : ColChain (Dc Pk.Zs) u) (hn : HtNums R (InfinitePlace K))
    (nP : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
      (Pi.basisFun K (Fin ((A3.side3 P1 ψ1 Pk.Zs).nV A3.fam3.base3.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤
        Real.exp hn.hPn)
    (cb : CBData ch.X ch.Kj) (nKcb : ∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v)
    (h11 : LiftExponentAtTwisted A3.A P0 ψ0 (A3.fam3.toSub2 Pk.Zs) Pk.core.base.μ Pk.core.base.Tw (Zsc Pk.Zs).J0)
    (dg : ℕ) (hdg : 0 < dg) (hdvd : ∀ j t, (A3.A.fam.L j t).DG (A3.A.fam.lvlA P0 ψ0) ∣ dg)
    (hA : ArithAt A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc cf C CH Pk R bd dg) :
    DivisionInputsWithoutNorm A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc cf C CH Pk R u Nu sg bd where
  Nu_lat := hNu
  sg_fin := hsg
  Xc_unit := hXc
  a_pos := ha
  X0 := X0
  base_matrix_det_unit := hX0
  ch := ch
  hn := hn
  nP := nP
  cb := cb
  nKcb := nKcb
  eig6 := hA.eig6
  h11 := h11
  dg := dg
  dg_pos := hdg
  dg_dvd := hdvd
  hG0 := hA.hG0
  El3 := Classical.choose hA.l3
  L3main := (Classical.choose_spec hA.l3).1
  errB := (Classical.choose_spec hA.l3).2
  Q := Classical.choose hA.q
  de0 := (Classical.choose_spec hA.q).1
  deQ := (Classical.choose_spec hA.q).2.1
  Q1 := (Classical.choose_spec hA.q).2.2.1
  Qb := (Classical.choose_spec hA.q).2.2.2
  la_le := hA.la_le
  constant_ge_twenty_eight := hA.constant_ge_twenty_eight

end Arith

end Formalism.L2.DIV

end
