import Mathlib
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}

open Classical in

def SyOf (Df : DefSide Bs) (S : IndefData Df) : Finset (HeightOneSpectrum (𝓞 K)) :=
  S.Tw ∪ (if h : (Function.support fun y => vw y (GmOf Df Bs.μ0 y)).Finite then h.toFinset else ∅)

theorem gm_support_finite [IsTotallyComplex K] {Df : DefSide Bs} (wf : Df.WF) (t : Bs.Tup) :
    (Function.support fun y => vw y (GmOf Df t y)).Finite := by
  have h := (reduction_lemma_second K Bs.K0 wf.cm Bs.v0 wf.conj (Df.nV t) (Df.dQ t) (Df.HV t) (wf.HV_rat t) (wf.HV_pos t)
    (Df.Pq t) (wf.Pq_surj t) (Df.XQ t) (wf.XQ_quot t) (Df.Mt t) (wf.Mt_lat t) (fun y => ebOf Df t y)
    (fun y => ebOf_spec wf t y)).1
  refine h.subset fun y hy => ?_
  rw [Function.mem_support] at hy ⊢
  exact mul_ne_zero (PlaceSumConjugation.lw_pos y).ne' (by exact_mod_cast hy)

theorem tw_sub_SyOf (Df : DefSide Bs) (S : IndefData Df) : S.Tw ⊆ SyOf Df S := by
  classical
  intro x hx
  unfold SyOf
  exact Finset.mem_union_left _ hx

theorem gram_det_unit_outside [IsTotallyComplex K] {Df : DefSide Bs} (wf : Df.WF) (S : IndefData Df) (hH0 : S.H0)
    (y : HeightOneSpectrum (𝓞 K)) (hy : y ∉ SyOf Df S) : vw y (Df.Gm (ebOf Df) (S.μ y) y) = 0 := by
  unfold SyOf at hy
  rw [dif_pos (gm_support_finite wf Bs.μ0)] at hy
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hy
  have hμ : S.μ y = Bs.μ0 := by
    by_contra h
    exact hy.1 ((hH0.2 y).2 h)
  rw [hμ]
  exact hy.2

theorem vw_nat_le_of_dvd (w : HeightOneSpectrum (𝓞 K)) {a b : ℕ} (hb : 0 < b) (h : a ∣ b) :
    vw w (a : K) ≤ vw w (b : K) := by
  obtain ⟨c, rfl⟩ := h
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hb
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hb
  have ha : (a : K) ≠ 0 := by exact_mod_cast ha0
  have hc : (c : K) ≠ 0 := by exact_mod_cast hc0
  have hcnn : 0 ≤ FractionalIdeal.count K w
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (c : K)) := by
    have e : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (c : K) =
        ((Ideal.span {(c : 𝓞 K)} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
      rw [FractionalIdeal.coeIdeal_span_singleton, map_natCast]
    rw [e]
    exact FractionalIdeal.count_coe_nonneg K w _
  unfold vw
  rw [Nat.cast_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K w (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hc)]
  linarith

end Generic

section Concrete

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def LiftExponentAtTwisted (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Zs : DefSub A.fam.amb)
    (μ : HeightOneSpectrum (𝓞 K) → T) (Tw : Finset (HeightOneSpectrum (𝓞 K)))
    (J0 : T → HeightOneSpectrum (𝓞 K) → Fin m → ℝ) : Prop :=
  ∀ y ∈ Tw, ∀ j : Fin m, ∃ Jn : ℕ, (Jn : ℝ) ≤ (ramw y : ℝ) * J0 (μ y) y j ∧
    ∀ a ∈ y.asIdeal ^ Jn, ∀ z ∈ (A.fam.L j (μ y)).cutZ (A.fam.lvlA P0 ψ0) (Zs.Zl j (μ y)),
      a • z ∈ Formalism.HermitianLatticesTheory.localization₂ y.asIdeal ((A.fam.L j (μ y)).delZ (A.fam.lvlA P0 ψ0) (Zs.Zl j (μ y)))

def etaYOf (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Zs : DefSub A.fam.amb) (s : ℕ)
    (μ : HeightOneSpectrum (𝓞 K) → T) (D : ℕ) (y : HeightOneSpectrum (𝓞 K)) (j : Fin m) : ℝ :=
  (A.fam.etaJW P0 ψ0 Zs j (μ y) y : ℝ) +
    (D : ℝ) * ((vw y (((A.fam.L j (μ y)).DG (A.fam.lvlA P0 ψ0) : ℕ) : K) : ℝ) + (vw y (s : K) : ℝ))

def lgDef {J Pl : Type} [Fintype J] [Fintype Pl] [DecidableEq Pl] (R : RecNums J Pl) (s : ℕ) : ℝ :=
  R.lam0 + Real.log (s : ℝ)

def etaSumBound {J : Type} (bd : J → ℝ) (dg s : ℕ) (j : J) : ℝ :=
  bd j + Real.log (dg : ℝ) + Real.log (s : ℝ)

theorem lift_exponent_of_least (A : FamIn K G Pl0 T m) {s : ℕ} (hOk : A.fam.Ok s) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
    (Zs : DefSub A.fam.amb) (μ : HeightOneSpectrum (𝓞 K) → T) (Tw : Finset (HeightOneSpectrum (𝓞 K)))
    (J0 : T → HeightOneSpectrum (𝓞 K) → Fin m → ℝ)
    (hJ0 : ∀ y ∈ Tw, ∀ j, J0 (μ y) y j = ((A.fam.JJ P0 ψ0 Zs j (μ y) y : ℚ) : ℝ)) :
    LiftExponentAtTwisted A P0 ψ0 Zs μ Tw J0 := by
  intro y hy j
  have hlat := lift_lattices K G Pl0 (A.fam.L j (μ y)) (A.fam.lvlA P0 ψ0) (Zs.Zl j (μ y)) A.fam.v0 s
    (A.fam.blockHyp_lift hOk P0 ψ0 j (μ y))
  refine ⟨A.fam.JJW P0 ψ0 Zs j (μ y) y, ?_, ?_⟩
  · rw [hJ0 y hy j, mul_comm, A.fam.JJ_ramw P0 ψ0 Zs j (μ y) y]
  · exact (exponent_weight_spectral K _ y ((A.fam.L j (μ y)).cutZ (A.fam.lvlA P0 ψ0) (Zs.Zl j (μ y)))
      ((A.fam.L j (μ y)).delZ (A.fam.lvlA P0 ψ0) (Zs.Zl j (μ y))) hlat.2.1 hlat.2.2.1).1

theorem bi_def [IsTotallyComplex K] (A : FamIn K G Pl0 T m) {s : ℕ} (hOk : A.fam.Ok s) (P0 : Subgroup G)
    (ψ0 : P0 →* Kˣ) (Zs : DefSub A.fam.amb) (S : IndefRows (A.side P0 ψ0 Zs)) (y : HeightOneSpectrum (𝓞 K)) :
    (vw y ((A.side P0 ψ0 Zs).Gm (ebOf (A.side P0 ψ0 Zs)) (S.μ y) y) : ℝ) ≤
      (S.D : ℝ) * (vw y ((Fintype.card G * s : ℕ) : K) : ℝ) := by
  have h : vw y (GmOf (A.side P0 ψ0 Zs) (S.μ y) y) ≤
      (((A.side P0 ψ0 Zs).dQ (S.μ y) : ℕ) : ℤ) * vw y ((Fintype.card G * s : ℕ) : K) :=
    A.fam.GmOf_le hOk P0 ψ0 Zs (S.μ y) y
  rw [S.dQ_eq] at h
  exact_mod_cast h

theorem bLG_def {J Pl : Type} [Fintype J] [Fintype Pl] [DecidableEq Pl] (R : RecNums J Pl) {s : ℕ} (hs : 0 < s)
    (hG0 : Real.log (Fintype.card G) ≤ R.lam0) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ y ∈ S, lw y * (vw y ((Fintype.card G * s : ℕ) : K) : ℝ) ≤ lgDef R s := by
  have hn : 0 < Fintype.card G * s := Nat.mul_pos Fintype.card_pos hs
  have h1 := (place_sum_natural K (Fintype.card G * s) hn).2.2 S
  have h2 : Real.log (((Fintype.card G * s : ℕ)) : ℝ) = Real.log (Fintype.card G : ℝ) + Real.log (s : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast Fintype.card_ne_zero) (by exact_mod_cast hs.ne')]
  unfold lgDef
  linarith

theorem biv_def (A : FamIn K G Pl0 T m) {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep) (P0 : Subgroup G)
    (ψ0 : P0 →* Kˣ) (Zs : DefSub A.fam.amb) (hst : Zs.Stable) (hin : Zs.InBlock) (S : IndefRows (A.side P0 ψ0 Zs))
    (J0 : T → HeightOneSpectrum (𝓞 K) → Fin m → ℝ) (h11 : LiftExponentAtTwisted A P0 ψ0 Zs S.μ S.Tw J0)
    (y : HeightOneSpectrum (𝓞 K)) (hy : y ∈ S.Tw) (j : Fin m) :
    (jw ((A.side P0 ψ0 Zs).HT j (S.μ y)) y ((A.side P0 ψ0 Zs).Tl j (S.μ y)) : ℝ) ≤
      ((ramw y : ℝ) * J0 (S.μ y) y j) * (S.D : ℝ) + etaYOf A P0 ψ0 Zs s S.μ S.D y j := by
  obtain ⟨Jn, hJn, hinc⟩ := h11 y hy j
  have wf := A.side_WF hOk P0 ψ0 Zs hst hin hsep
  have hD : (A.side P0 ψ0 Zs).dZ j (S.μ y) = S.D := S.rankZ wf j (S.μ y)
  have hlat := lift_lattices K G Pl0 (A.fam.L j (S.μ y)) (A.fam.lvlA P0 ψ0) (Zs.Zl j (S.μ y)) A.fam.v0 s
    (A.fam.blockHyp_lift hOk P0 ψ0 j (S.μ y))
  have hJ : A.fam.JJW P0 ψ0 Zs j (S.μ y) y ≤ Jn :=
    (exponent_weight_spectral K _ y ((A.fam.L j (S.μ y)).cutZ (A.fam.lvlA P0 ψ0) (Zs.Zl j (S.μ y)))
      ((A.fam.L j (S.μ y)).delZ (A.fam.lvlA P0 ψ0) (Zs.Zl j (S.μ y))) hlat.2.1 hlat.2.2.1).2 Jn hinc
  have h1 : jw ((A.side P0 ψ0 Zs).HT j (S.μ y)) y ((A.side P0 ψ0 Zs).Tl j (S.μ y)) ≤
      (A.fam.etaJW P0 ψ0 Zs j (S.μ y) y : ℤ) + ((A.side P0 ψ0 Zs).dZ j (S.μ y) : ℤ) *
        ((A.fam.JJW P0 ψ0 Zs j (S.μ y) y : ℤ) + vw y (((A.fam.L j (S.μ y)).DG (A.fam.lvlA P0 ψ0) : ℕ) : K) +
          vw y (s : K)) :=
    A.fam.jw_le hOk P0 ψ0 Zs j (S.μ y) y
  have h2 : (jw ((A.side P0 ψ0 Zs).HT j (S.μ y)) y ((A.side P0 ψ0 Zs).Tl j (S.μ y)) : ℝ) ≤
      (A.fam.etaJW P0 ψ0 Zs j (S.μ y) y : ℝ) + (((A.side P0 ψ0 Zs).dZ j (S.μ y) : ℕ) : ℝ) *
        ((A.fam.JJW P0 ψ0 Zs j (S.μ y) y : ℝ) + (vw y (((A.fam.L j (S.μ y)).DG (A.fam.lvlA P0 ψ0) : ℕ) : K) : ℝ) +
          (vw y (s : K) : ℝ)) := by
    exact_mod_cast h1
  have hDr : (((A.side P0 ψ0 Zs).dZ j (S.μ y) : ℕ) : ℝ) = (S.D : ℝ) := by exact_mod_cast hD
  rw [hDr] at h2
  have h3 : (A.fam.JJW P0 ψ0 Zs j (S.μ y) y : ℝ) ≤ (ramw y : ℝ) * J0 (S.μ y) y j :=
    le_trans (by exact_mod_cast hJ) hJn
  have hD0 : (0 : ℝ) ≤ S.D := Nat.cast_nonneg _
  have h4 := mul_le_mul_of_nonneg_left h3 hD0
  unfold etaYOf
  nlinarith

theorem twisted_place_eta_sum_le (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Zs : DefSub A.fam.amb) {s : ℕ}
    (hs : 0 < s) (S : IndefRows (A.side P0 ψ0 Zs)) (bd : Fin m → ℝ) (hN : InEta A.fam P0 ψ0 Zs S.μ S.Tw bd)
    (dg : ℕ) (hdg : 0 < dg) (hdvd : ∀ j t, (A.fam.L j t).DG (A.fam.lvlA P0 ψ0) ∣ dg) (j : Fin m) :
    ∑ y ∈ S.Tw, lw y * etaYOf A P0 ψ0 Zs s S.μ S.D y j / (S.D : ℝ) ≤ etaSumBound bd dg s j := by
  have hDpos : (0 : ℝ) < S.D := by exact_mod_cast S.D_pos
  have e : (A.fam.R A.fam.μ0).dZ (A.fam.lvl P0 ψ0) (Zs.Z A.fam.μ0) = S.D := S.dQ_eq A.fam.base.μ0
  have hN' : ∑ y ∈ S.Tw, lw y * (A.fam.etaJW P0 ψ0 Zs j (S.μ y) y : ℝ) ≤ bd j * (S.D : ℝ) := by
    have h := hN j
    rw [e] at h
    exact h
  have hsplit : ∑ y ∈ S.Tw, lw y * etaYOf A P0 ψ0 Zs s S.μ S.D y j / (S.D : ℝ) =
      (∑ y ∈ S.Tw, lw y * (A.fam.etaJW P0 ψ0 Zs j (S.μ y) y : ℝ)) / (S.D : ℝ) +
        ((∑ y ∈ S.Tw, lw y * (vw y (((A.fam.L j (S.μ y)).DG (A.fam.lvlA P0 ψ0) : ℕ) : K) : ℝ)) +
          (∑ y ∈ S.Tw, lw y * (vw y (s : K) : ℝ))) := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold etaYOf
    field_simp
  have hA : (∑ y ∈ S.Tw, lw y * (A.fam.etaJW P0 ψ0 Zs j (S.μ y) y : ℝ)) / (S.D : ℝ) ≤ bd j := by
    rw [div_le_iff₀ hDpos]
    exact hN'
  have hB : ∑ y ∈ S.Tw, lw y * (vw y (((A.fam.L j (S.μ y)).DG (A.fam.lvlA P0 ψ0) : ℕ) : K) : ℝ) ≤
      Real.log (dg : ℝ) := by
    refine le_trans (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (W5.lw_nonneg y))
      ((place_sum_natural K dg hdg).2.2 S.Tw)
    exact_mod_cast vw_nat_le_of_dvd y hdg (hdvd j (S.μ y))
  have hC := (place_sum_natural K s hs).2.2 S.Tw
  rw [hsplit]
  unfold etaSumBound
  linarith

theorem exists_dg (A : FamIn K G Pl0 T m) {s : ℕ} (hOk : A.fam.Ok s) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) :
    ∃ dg : ℕ, 0 < dg ∧ ∀ j t, (A.fam.L j t).DG (A.fam.lvlA P0 ψ0) ∣ dg := by
  have : Finite T := hOk.tup_fin
  have := Fintype.ofFinite T
  have hpos : ∀ j t, 0 < (A.fam.L j t).DG (A.fam.lvlA P0 ψ0) := by
    intro j t
    unfold BlockDat.DG
    refine Nat.mul_pos Nat.card_pos (Nat.pos_of_ne_zero ?_)
    unfold CSD.DGam
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨c, -, hc⟩
    exact (Fintype.card_pos (α := ((A.fam.L j t).S.Gam c))).ne' hc
  exact ⟨∏ p : Fin m × T, (A.fam.L p.1 p.2).DG (A.fam.lvlA P0 ψ0), Finset.prod_pos fun p _ => hpos p.1 p.2,
    fun j t => Finset.dvd_prod_of_mem (fun p : Fin m × T => (A.fam.L p.1 p.2).DG (A.fam.lvlA P0 ψ0))
      (Finset.mem_univ (j, t))⟩

end Concrete

section Inputs

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

structure DivInputsDef (A : FamIn K G Pl0 T m) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)) (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (C CH : ℝ)
    (Pk : IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A.fam.base.J Pl) (u : (Dc Pk.Zs).Mem)
    (Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ) where

  Nu_lat : Submodule.IsLattice K Nu

  sg_fin : (Function.support (shiftZ sg)).Finite

  Xc_unit : ∀ v, IsUnit ((Dc Pk.Zs).Xc u v).det

  a_pos : 0 < (Dc Pk.Zs).a u

  X0 : InfinitePlace K → Matrix (Fin ((A.side P1 ψ1 Pk.Zs).nV A.fam.base.μ0))
    (Fin ((A.side P1 ψ1 Pk.Zs).nV A.fam.base.μ0)) ℂ

  base_matrix_det_unit : ∀ v, IsUnit (X0 v).det ∧
    ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((A.side P1 ψ1 Pk.Zs).HV A.fam.base.μ0).map v.embedding

  ch : ColChain (Dc Pk.Zs) u

  hn : HtNums R (InfinitePlace K)

  nP : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
    (Pi.basisFun K (Fin ((A.side P1 ψ1 Pk.Zs).nV A.fam.base.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤
      Real.exp hn.hPn

  cb : CBData ch.X ch.Kj

  nKcb : ∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v

  eig6 : ∑ j, R.hX j ≤ ∑ j, ((Zsc Pk.Zs).num C CH).l6 j

  bd : A.fam.base.J → ℝ

  hN : InEta A.fam P0 ψ0 Pk.Zs Pk.core.base.μ Pk.core.base.Tw bd

  h11 : LiftExponentAtTwisted A P0 ψ0 Pk.Zs Pk.core.base.μ Pk.core.base.Tw (Zsc Pk.Zs).J0

  dg : ℕ

  dg_pos : 0 < dg

  dg_dvd : ∀ j t, (A.fam.L j t).DG (A.fam.lvlA P0 ψ0) ∣ dg

  hG0 : Real.log (Fintype.card G) ≤ R.lam0

  El3 : ℝ

  L3main : ∑ j, ((Zsc Pk.Zs).num C CH).l3 j ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + El3

  errB : El3 + lgDef R s + (∑ j, (((Zsc Pk.Zs).num C CH).E1 j + etaSumBound bd dg s j)) + 1 ≤ R.errB

  Q : ℝ

  de0 : 0 ≤ ((Zsc Pk.Zs).num C CH).de

  deQ : 3 * ((Zsc Pk.Zs).num C CH).de * Q ≤ 1

  Q1 : 1 ≤ Q

  Qb : boundB Pk.core (lgDef R s) 1 (etaSumBound bd dg s) + ((Zsc Pk.Zs).num C CH).hh + 28 * ((Zsc Pk.Zs).num C CH).la ≤ Q

  la_le : ((Zsc Pk.Zs).num C CH).la ≤ R.lam0

  constant_ge_twenty_eight : 28 ≤ R.C0

variable [IsTotallyComplex K] {A : FamIn K G Pl0 T m} {s : ℕ} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G}
  {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
  {Zsc : DefSub A.fam.amb → IndefScale A.fam.base} {C CH : ℝ} {Pk : IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH}
  {Pl : Type} [Fintype Pl] [DecidableEq Pl] {R : RecNums A.fam.base.J Pl} {u : (Dc Pk.Zs).Mem}
  {Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)} {sg : HeightOneSpectrum (𝓞 K) → ℝ}

def DivInputsDef.toDivInputs0 (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep)
    (I : DivInputsDef A s P0 ψ0 P1 ψ1 Dc Sp Zsc C CH Pk R u Nu sg) : DivInputs0 Pk.core R u Nu sg where
  Nu_lat := I.Nu_lat
  sg_fin := I.sg_fin
  Xc_unit := I.Xc_unit
  a_pos := I.a_pos
  X0 := I.X0
  base_matrix_det_unit := I.base_matrix_det_unit
  ch := I.ch
  hn := I.hn
  nP := I.nP
  cb := I.cb
  nKcb := I.nKcb
  eig6 := I.eig6
  eb := ebOf (A.side P0 ψ0 Pk.Zs)
  heb := ebOf_spec (A.side_WF hOk P0 ψ0 Pk.Zs Pk.stable Pk.inBlock hsep)
  Sy := SyOf (A.side P0 ψ0 Pk.Zs) Pk.core.base.toIndefData
  Sy_tw := tw_sub_SyOf _ _
  G0 := gram_det_unit_outside (A.side_WF hOk P0 ψ0 Pk.Zs Pk.stable Pk.inBlock hsep) Pk.core.base.toIndefData Pk.core.base.h0
  LG := lgDef R s
  E3 := 1
  E2 := etaSumBound I.bd I.dg s
  gy := fun y => (vw y ((Fintype.card G * s : ℕ) : K) : ℝ)
  ηy := etaYOf A P0 ψ0 Pk.Zs s Pk.core.base.μ Pk.core.base.D
  bi := fun y _ => bi_def A hOk P0 ψ0 Pk.Zs Pk.core.base.toIndefRows y
  bLG := bLG_def R (hOk.what₂ A.fam.μ0).good.s_pos I.hG0 _
  biv := fun y hy j => biv_def A hOk hsep P0 ψ0 Pk.Zs Pk.stable Pk.inBlock Pk.core.base.toIndefRows _ I.h11 y hy j
  borderedMinorImage := twisted_place_eta_sum_le A P0 ψ0 Pk.Zs (hOk.what₂ A.fam.μ0).good.s_pos Pk.core.base.toIndefRows I.bd I.hN I.dg I.dg_pos I.dg_dvd
  twisted_third_sum_le := Formalism.DivisorInequality.places_ell_weighted_sum_le_one K _
  El3 := I.El3
  L3main := I.L3main
  errB := I.errB
  Q := I.Q
  de0 := I.de0
  deQ := I.deQ
  Q1 := I.Q1
  Qb := I.Qb
  la_le := I.la_le
  constant_ge_twenty_eight := I.constant_ge_twenty_eight

theorem DivInputsDef.eb_eq (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep)
    (I : DivInputsDef A s P0 ψ0 P1 ψ1 Dc Sp Zsc C CH Pk R u Nu sg) :
    (I.toDivInputs0 hOk hsep).eb = ebOf (A.side P0 ψ0 Pk.Zs) := rfl

theorem DivInputsDef.defs_eq (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep)
    (I : DivInputsDef A s P0 ψ0 P1 ψ1 Dc Sp Zsc C CH Pk R u Nu sg) :
    (I.toDivInputs0 hOk hsep).Sy = SyOf (A.side P0 ψ0 Pk.Zs) Pk.core.base.toIndefData ∧
      (I.toDivInputs0 hOk hsep).gy = (fun y => (vw y ((Fintype.card G * s : ℕ) : K) : ℝ)) ∧
      (I.toDivInputs0 hOk hsep).LG = R.lam0 + Real.log (s : ℝ) ∧
      (I.toDivInputs0 hOk hsep).ηy = etaYOf A P0 ψ0 Pk.Zs s Pk.core.base.μ Pk.core.base.D ∧
      (I.toDivInputs0 hOk hsep).E2 = (fun j => I.bd j + Real.log (I.dg : ℝ) + Real.log (s : ℝ)) ∧
      (I.toDivInputs0 hOk hsep).E3 = 1 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Inputs

section Corollary

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

theorem division_height_bound_definite [IsTotallyComplex K] (A : FamIn K G Pl0 T m) {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep)
    (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (C CH : ℝ)
    (Pk : IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A.fam.base.J Pl) (u : (Dc Pk.Zs).Mem)
    (Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ)
    (I : DivInputsDef A s P0 ψ0 P1 ψ1 Dc Sp Zsc C CH Pk R u Nu sg)
    (val2 : ∀ w, ∀ φ ∈ Nu, ∀ F ∈ (A.side P1 ψ1 Pk.Zs).Mt (Pk.core.cols.μ w),
      (Dc Pk.Zs).Pt u (Pk.core.cols.μ w) φ F = 0 ∨ sg w ≤ (vw w ((Dc Pk.Zs).Pt u (Pk.core.cols.μ w) φ F) : ℝ)) :
    DivClauses Pk.core R u Nu sg := by
  exact division_height_bound_clauses A hOk hsep P0 ψ0 P1 ψ1 Dc Sp Zsc C CH Pk R u Nu sg
    ⟨I.toDivInputs0 hOk hsep, val2⟩

end Corollary

end Formalism.L2.DIV
