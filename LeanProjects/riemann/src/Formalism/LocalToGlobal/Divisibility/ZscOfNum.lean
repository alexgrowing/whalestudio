import Mathlib
import Formalism.LocalToGlobal.Divisibility.LinkDef
import Formalism.LocalToGlobal.Divisibility.NumbersLink

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions

def NumDatum.unitE (Nd : NumDatum) (Nc : ℝ) : ℝ := Nd.sc.x ^ Nd.sc.eps * (Nd.B0 + Nc)

theorem NumDatum.logLog_le (Nd : NumDatum) (h : Real.log Nd.sc.x ≤ Nd.sc.L) :
    Real.log (Real.log Nd.sc.x) ≤ Nd.sc.x ^ Nd.sc.eps := by
  have hl : 0 < Real.log Nd.sc.x := Real.log_pos Nd.sc.one_lt_alt
  have h1 := Real.log_le_sub_one_of_pos hl
  have h2 : Nd.sc.L = Nd.sc.x ^ Nd.sc.eps := rfl
  linarith

theorem NumDatum.loss_bound_nonneg (Nd : NumDatum) : 0 ≤ Nd.B0 := by
  unfold NumDatum.B0
  have := Nd.b_pos
  have := Real.rpow_nonneg Nd.x_pos.le Nd.sc.eps
  positivity

theorem NumDatum.one_le_B0 (Nd : NumDatum) : 1 ≤ Nd.B0 := by
  unfold NumDatum.B0
  have hf : (1 : ℝ) ≤ Nd.R.f := by
    have : 1 ≤ Nd.R.f := by
      have h1 : Nd.R.f = 2 * Nd.R.ord := rfl
      have h2 := Nd.R.ord_pos
      omega
    exact_mod_cast this
  have hm : (1 : ℝ) ≤ Nd.R.m := by
    have := Nd.R.two_le_m
    exact_mod_cast (show 1 ≤ Nd.R.m by omega)
  have hb := Nd.one_le_b
  have hx : 1 ≤ Nd.sc.x ^ Nd.sc.eps := Real.one_le_rpow Nd.sc.one_lt_alt.le Nd.sc.eps_pos.le
  have h1 := one_le_mul_of_one_le_of_one_le hf hm
  have h2 := one_le_mul_of_one_le_of_one_le h1 hb
  exact one_le_mul_of_one_le_of_one_le h2 hx

theorem NumDatum.one_le_m_unitE (Nd : NumDatum) {Nc : ℝ} (hNc : 0 ≤ Nc) : 1 ≤ (Nd.R.m : ℝ) * Nd.unitE Nc := by
  unfold NumDatum.unitE
  have hm : (1 : ℝ) ≤ Nd.R.m := by
    have := Nd.R.two_le_m
    exact_mod_cast (show 1 ≤ Nd.R.m by omega)
  have hx : 1 ≤ Nd.sc.x ^ Nd.sc.eps := Real.one_le_rpow Nd.sc.one_lt_alt.le Nd.sc.eps_pos.le
  have hB : 1 ≤ Nd.B0 + Nc := by linarith [Nd.one_le_B0]
  exact one_le_mul_of_one_le_of_one_le hm (one_le_mul_of_one_le_of_one_le hx hB)

section Scale

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def ZscOfNum (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum) (eJ : A.fam.base.J ≃ Fin Nd.R.m)
    (Nc : ℝ) (Zs : DefSub A.fam.amb) : IndefScale A.fam.base where
  F0 y j := Nd.Fj ((eJ j).1 + 1) y
  J0 t y j := ((A.fam.JJ P0 ψ0 Zs j t y : ℚ) : ℝ)
  E1u := Nd.unitE Nc
  l3m j := ∑ ρ : RPl Nd.R, (((Nd.R.k : ℝ) + (((eJ j).1 + 1 : ℕ) : ℝ) - 1) - ((Nd.R.m : ℝ) - (((eJ j).1 + 1 : ℕ) : ℝ))) *
    Nd.w ((eJ j).1 + 1) ρ * Nd.logOm
  l3u := Nd.B0 * Real.log (Real.log Nd.sc.x)
  l6m j := ∑ ρ : RPl Nd.R, Nd.logHook ((eJ j).1 + 1) ρ
  l6u := (Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp
  x := Nd.sc.x
  b := Nd.sc.b
  la := Real.log (Fintype.card G)
  de := 8 * (Nd.R.f : ℝ) * (Nd.R.r : ℝ) / ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ)

variable (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum) (eJ : A.fam.base.J ≃ Fin Nd.R.m) (Nc : ℝ)

theorem eigen_sum_le_of_numeric (Zs : DefSub A.fam.amb) (C CH : ℝ) (δ : Code Nd) (Tl : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ)
    (H : Nd.NumFacts δ Nc lam0 C0 ce Ch Sw C1) (hC : C ≤ Ch) :
    ∑ j, (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).hX j ≤ ∑ j, ((ZscOfNum A P0 ψ0 Nd eJ Nc Zs).num C CH).l6 j := by
  refine eigen_sum_le_of_scale _ C CH _ (fun _ => le_refl _) ?_
  show C * ((Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp) ≤ Ch * (Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp
  have h0 : 0 ≤ (Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp := mul_nonneg (by positivity) Nd.Lp_nonneg
  have := mul_le_mul_of_nonneg_right hC h0
  linarith

theorem l3main_ofNum (Zs : DefSub A.fam.amb) (C CH : ℝ) (δ : Code Nd) (Tl : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ)
    (H : Nd.NumFacts δ Nc lam0 C0 ce Ch Sw C1) :
    ∑ j, ((ZscOfNum A P0 ψ0 Nd eJ Nc Zs).num C CH).l3 j ≤
      (∑ j, ∑ ρ, (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).pq j *
          (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).w j ρ *
          (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).logOm) +
        (Nd.R.m : ℝ) * (C * (ZscOfNum A P0 ψ0 Nd eJ Nc Zs).l3u) :=
  l3main_of_scale _ C CH (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H) (fun _ => le_refl _)

theorem lift_exponent_of_numeric {s : ℕ} (hOk : A.fam.Ok s) (Zs : DefSub A.fam.amb) (μ : HeightOneSpectrum (𝓞 K) → T)
    (Tw : Finset (HeightOneSpectrum (𝓞 K))) : LiftExponentAtTwisted A P0 ψ0 Zs μ Tw (ZscOfNum A P0 ψ0 Nd eJ Nc Zs).J0 :=
  lift_exponent_of_least A hOk P0 ψ0 Zs μ Tw _ (fun _ _ _ => rfl)

theorem numeric_scale_offset_nonneg (Zs : DefSub A.fam.amb) (C CH : ℝ) : 0 ≤ ((ZscOfNum A P0 ψ0 Nd eJ Nc Zs).num C CH).de := by
  show 0 ≤ 8 * (Nd.R.f : ℝ) * (Nd.R.r : ℝ) / ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ)
  positivity

def bdOf (Zs : DefSub A.fam.amb) (μ : HeightOneSpectrum (𝓞 K) → T) (Tw : Finset (HeightOneSpectrum (𝓞 K)))
    (j : A.fam.base.J) : ℝ :=
  (∑ w ∈ Tw, lw w * (A.fam.etaJW P0 ψ0 Zs j (μ w) w : ℝ)) /
    ((A.fam.R A.fam.μ0).dZ (A.fam.lvl P0 ψ0) (Zs.Z A.fam.μ0) : ℝ)

theorem inEta_bdOf (Zs : DefSub A.fam.amb) (μ : HeightOneSpectrum (𝓞 K) → T) (Tw : Finset (HeightOneSpectrum (𝓞 K)))
    (hD : 0 < (A.fam.R A.fam.μ0).dZ (A.fam.lvl P0 ψ0) (Zs.Z A.fam.μ0)) :
    InEta A.fam P0 ψ0 Zs μ Tw (bdOf A P0 ψ0 Zs μ Tw) := by
  intro j
  have hD' : (0 : ℝ) < ((A.fam.R A.fam.μ0).dZ (A.fam.lvl P0 ψ0) (Zs.Z A.fam.μ0) : ℝ) := by exact_mod_cast hD
  unfold bdOf
  rw [div_mul_cancel₀ _ hD'.ne']

theorem inEta_bdOf_rows (Zs : DefSub A.fam.amb) (S : IndefRows (A.side P0 ψ0 Zs)) :
    InEta A.fam P0 ψ0 Zs S.μ S.Tw (bdOf A P0 ψ0 Zs S.μ S.Tw) := by
  refine inEta_bdOf A P0 ψ0 Zs S.μ S.Tw ?_
  have e : (A.fam.R A.fam.μ0).dZ (A.fam.lvl P0 ψ0) (Zs.Z A.fam.μ0) = S.D := S.dQ_eq A.fam.base.μ0
  rw [e]
  exact S.D_pos

def dgOf (hT : Finite T) : ℕ :=
  letI := Fintype.ofFinite T
  Finset.univ.lcm fun p : Fin m × T => (A.fam.L p.1 p.2).DG (A.fam.lvlA P0 ψ0)

theorem dgOf_dvd (hT : Finite T) (j : Fin m) (t : T) : (A.fam.L j t).DG (A.fam.lvlA P0 ψ0) ∣ dgOf A P0 ψ0 hT := by
  letI := Fintype.ofFinite T
  exact Finset.dvd_lcm (f := fun p : Fin m × T => (A.fam.L p.1 p.2).DG (A.fam.lvlA P0 ψ0)) (Finset.mem_univ (j, t))

theorem dgOf_pos (hT : Finite T) : 0 < dgOf A P0 ψ0 hT := by
  letI := Fintype.ofFinite T
  have hpos : ∀ j t, 0 < (A.fam.L j t).DG (A.fam.lvlA P0 ψ0) := by
    intro j t
    unfold BlockDat.DG
    refine Nat.mul_pos Nat.card_pos (Nat.pos_of_ne_zero ?_)
    unfold CSD.DGam
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨c, -, hc⟩
    exact (Fintype.card_pos (α := ((A.fam.L j t).S.Gam c))).ne' hc
  refine Nat.pos_of_ne_zero ?_
  unfold dgOf
  rw [Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨p, -, hp⟩
  exact (hpos p.1 p.2).ne' hp

end Scale

section Q

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1}
  {Sp : SPer Dc} {N : IndefNum Bs}

def QOf (P : IndefCore Df0 Df1 Dc Sp N) (LG E3 : ℝ) (E2 : Bs.J → ℝ) : ℝ :=
  max 1 (boundB P LG E3 E2 + N.hh + 28 * N.la)

theorem QOf_one (P : IndefCore Df0 Df1 Dc Sp N) (LG E3 : ℝ) (E2 : Bs.J → ℝ) : 1 ≤ QOf P LG E3 E2 := le_max_left _ _

theorem QOf_ge (P : IndefCore Df0 Df1 Dc Sp N) (LG E3 : ℝ) (E2 : Bs.J → ℝ) :
    boundB P LG E3 E2 + N.hh + 28 * N.la ≤ QOf P LG E3 E2 := le_max_right _ _

end Q

section Sizes

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
variable (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum) (eJ : A.fam.base.J ≃ Fin Nd.R.m) (Nc : ℝ)

def NormBoundSize (Zs : DefSub A.fam.amb) (μ : HeightOneSpectrum (𝓞 K) → T) (Tw : Finset (HeightOneSpectrum (𝓞 K))) (c : ℝ) :
    Prop :=
  ∀ j, bdOf A P0 ψ0 Zs μ Tw j ≤ c * Nd.unitE Nc

def LamSizeAt (s : ℕ) (cG : ℝ) : Prop :=
  Real.log (Fintype.card G) + Real.log (s : ℝ) ≤ cG * ((Nd.R.m : ℝ) * Nd.unitE Nc)

def DGamSize (hT : Finite T) (s : ℕ) (cD : ℝ) : Prop :=
  Real.log (dgOf A P0 ψ0 hT : ℝ) + Real.log (s : ℝ) ≤ cD * Nd.unitE Nc

theorem errB_ofNum (Zs : DefSub A.fam.amb) (C CH : ℝ) (δ : Code Nd) (Tl : ℕ) (C0 ce Ch Sw C1 : ℝ)
    (H : Nd.NumFacts δ Nc (Real.log (Fintype.card G)) C0 ce Ch Sw C1) (hC : 0 ≤ C) (bd : A.fam.base.J → ℝ) (dg s : ℕ)
    (c13 cG cD : ℝ) (hbd : ∀ j, bd j ≤ c13 * Nd.unitE Nc) (hLam : LamSizeAt (G := G) Nd Nc s cG)
    (hdg : Real.log (dg : ℝ) + Real.log (s : ℝ) ≤ cD * Nd.unitE Nc) (hce : C + cG + C + (c13 + cD) + 1 ≤ ce) :
    (Nd.R.m : ℝ) * (C * (ZscOfNum A P0 ψ0 Nd eJ Nc Zs).l3u) +
        lgDef (RecNums.ofNum Nd eJ δ Tl Nc (Real.log (Fintype.card G)) C0 ce Ch Sw C1 H) s +
        (∑ j, (((ZscOfNum A P0 ψ0 Nd eJ Nc Zs).num C CH).E1 j + etaSumBound bd dg s j)) + 1 ≤
      (RecNums.ofNum Nd eJ δ Tl Nc (Real.log (Fintype.card G)) C0 ce Ch Sw C1 H).errB := by
  have key := errB_of_units (ZscOfNum A P0 ψ0 Nd eJ Nc Zs) C CH
    (RecNums.ofNum Nd eJ δ Tl Nc (Real.log (Fintype.card G)) C0 ce Ch Sw C1 H)
    (lgDef (RecNums.ofNum Nd eJ δ Tl Nc (Real.log (Fintype.card G)) C0 ce Ch Sw C1 H) s) 1 (etaSumBound bd dg s)
    C cG (c13 + cD) 1 hC (le_refl (Nd.unitE Nc)) ?_ ?_ ?_ ?_ hce
  · exact key
  ·
    show C * (Nd.B0 * Real.log (Real.log Nd.sc.x)) ≤ C * Nd.unitE Nc
    refine mul_le_mul_of_nonneg_left ?_ hC
    have hll := Nd.logLog_le H.logx
    have hB := Nd.loss_bound_nonneg
    have hx : 0 ≤ Nd.sc.x ^ Nd.sc.eps := Real.rpow_nonneg Nd.x_pos.le _
    have h1 : Nd.B0 * Real.log (Real.log Nd.sc.x) ≤ Nd.B0 * Nd.sc.x ^ Nd.sc.eps := mul_le_mul_of_nonneg_left hll hB
    have h2 : 0 ≤ Nd.sc.x ^ Nd.sc.eps * Nc := mul_nonneg hx H.Nc0
    unfold NumDatum.unitE
    nlinarith
  · show Real.log (Fintype.card G) + Real.log (s : ℝ) ≤ cG * ((Nd.R.m : ℝ) * Nd.unitE Nc)
    exact hLam
  · intro j
    show bd j + Real.log (dg : ℝ) + Real.log (s : ℝ) ≤ (c13 + cD) * Nd.unitE Nc
    have := hbd j
    linarith
  · show (1 : ℝ) ≤ 1 * ((Nd.R.m : ℝ) * Nd.unitE Nc)
    rw [one_mul]
    exact Nd.one_le_m_unitE H.Nc0

end Sizes

section Assemble

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def divInputsDefOfNum (A : FamIn K G Pl0 T m) {s : ℕ} (hOk : A.fam.Ok s) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
    (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)) (Nd : NumDatum) (eJ : A.fam.base.J ≃ Fin Nd.R.m) (Nc C CH : ℝ)
    (Pk : IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp (ZscOfNum A P0 ψ0 Nd eJ Nc)) C CH)
    (δ : Code Nd) (Tl : ℕ) (C0 ce Ch Sw C1 : ℝ) (H : Nd.NumFacts δ Nc (Real.log (Fintype.card G)) C0 ce Ch Sw C1)
    (u : (Dc Pk.Zs).Mem) (Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ)
    (Nu_lat : Submodule.IsLattice K Nu)
    (sg_fin : (Function.support (shiftZ sg)).Finite)
    (Xc_unit : ∀ v, IsUnit ((Dc Pk.Zs).Xc u v).det)
    (a_pos : 0 < (Dc Pk.Zs).a u)
    (X0 : InfinitePlace K → Matrix (Fin ((A.side P1 ψ1 Pk.Zs).nV A.fam.base.μ0))
      (Fin ((A.side P1 ψ1 Pk.Zs).nV A.fam.base.μ0)) ℂ)
    (base_matrix_det_unit : ∀ v, IsUnit (X0 v).det ∧
      ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((A.side P1 ψ1 Pk.Zs).HV A.fam.base.μ0).map v.embedding)
    (ch : ColChain (Dc Pk.Zs) u)
    (hn : HtNums (RecNums.ofNum Nd eJ δ Tl Nc (Real.log (Fintype.card G)) C0 ce Ch Sw C1 H) (InfinitePlace K))
    (nP : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
      (Pi.basisFun K (Fin ((A.side P1 ψ1 Pk.Zs).nV A.fam.base.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤
        Real.exp hn.hPn)
    (cb : CBData ch.X ch.Kj)
    (nKcb : ∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v)
    (hC0 : 0 ≤ C) (hCh : C ≤ Ch) (h28 : 28 ≤ C0)
    (c13 cG cD : ℝ)
    (hH13 : NormBoundSize A P0 ψ0 Nd Nc Pk.Zs Pk.core.base.μ Pk.core.base.Tw c13)
    (hLam : LamSizeAt (G := G) Nd Nc s cG)
    (hDG : DGamSize A P0 ψ0 Nd Nc hOk.tup_fin s cD)
    (hce : C + cG + C + (c13 + cD) + 1 ≤ ce)
    (hdeQ : 3 * ((ZscOfNum A P0 ψ0 Nd eJ Nc Pk.Zs).num C CH).de *
      QOf Pk.core (lgDef (RecNums.ofNum Nd eJ δ Tl Nc (Real.log (Fintype.card G)) C0 ce Ch Sw C1 H) s) 1
        (etaSumBound (bdOf A P0 ψ0 Pk.Zs Pk.core.base.μ Pk.core.base.Tw) (dgOf A P0 ψ0 hOk.tup_fin) s) ≤ 1) :
    DivInputsDef A s P0 ψ0 P1 ψ1 Dc Sp (ZscOfNum A P0 ψ0 Nd eJ Nc) C CH Pk
      (RecNums.ofNum Nd eJ δ Tl Nc (Real.log (Fintype.card G)) C0 ce Ch Sw C1 H) u Nu sg where
  Nu_lat := Nu_lat
  sg_fin := sg_fin
  Xc_unit := Xc_unit
  a_pos := a_pos
  X0 := X0
  base_matrix_det_unit := base_matrix_det_unit
  ch := ch
  hn := hn
  nP := nP
  cb := cb
  nKcb := nKcb
  eig6 := eigen_sum_le_of_numeric A P0 ψ0 Nd eJ Nc Pk.Zs C CH δ Tl _ C0 ce Ch Sw C1 H hCh
  bd := bdOf A P0 ψ0 Pk.Zs Pk.core.base.μ Pk.core.base.Tw
  hN := inEta_bdOf_rows A P0 ψ0 Pk.Zs Pk.core.base.toIndefRows
  h11 := lift_exponent_of_numeric A P0 ψ0 Nd eJ Nc hOk Pk.Zs Pk.core.base.μ Pk.core.base.Tw
  dg := dgOf A P0 ψ0 hOk.tup_fin
  dg_pos := dgOf_pos A P0 ψ0 hOk.tup_fin
  dg_dvd := dgOf_dvd A P0 ψ0 hOk.tup_fin
  hG0 := le_refl _
  El3 := (Nd.R.m : ℝ) * (C * (ZscOfNum A P0 ψ0 Nd eJ Nc Pk.Zs).l3u)
  L3main := l3main_ofNum A P0 ψ0 Nd eJ Nc Pk.Zs C CH δ Tl _ C0 ce Ch Sw C1 H
  errB := errB_ofNum A P0 ψ0 Nd eJ Nc Pk.Zs C CH δ Tl C0 ce Ch Sw C1 H hC0 _ _ s c13 cG cD hH13 hLam hDG hce
  Q := QOf Pk.core (lgDef (RecNums.ofNum Nd eJ δ Tl Nc (Real.log (Fintype.card G)) C0 ce Ch Sw C1 H) s) 1
    (etaSumBound (bdOf A P0 ψ0 Pk.Zs Pk.core.base.μ Pk.core.base.Tw) (dgOf A P0 ψ0 hOk.tup_fin) s)
  de0 := numeric_scale_offset_nonneg A P0 ψ0 Nd eJ Nc Pk.Zs C CH
  deQ := hdeQ
  Q1 := QOf_one _ _ _ _
  Qb := QOf_ge _ _ _ _
  la_le := le_refl _
  constant_ge_twenty_eight := h28

end Assemble

end Formalism.L2.DIV
