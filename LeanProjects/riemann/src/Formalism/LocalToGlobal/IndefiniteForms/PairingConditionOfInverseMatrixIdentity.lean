import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.L2.Indef

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem vw_inv (w : HeightOneSpectrum (𝓞 K)) (a : K) : vw w a⁻¹ = - vw w a := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv]

namespace ColData

variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {S : IndefData Df} (C : ColData Dc Sp S)

def invZ : ColData Dc Sp S where
  B := C.B
  ζ := fun u t => (C.ζ u t)⁻¹
  sE := C.sE

@[simp] theorem invZ_B : C.invZ.B = C.B := rfl

@[simp] theorem invZ_ζ (u : Dc.Mem) (t : Bs.Tup) : C.invZ.ζ u t = (C.ζ u t)⁻¹ := rfl

@[simp] theorem invZ_sE : C.invZ.sE = C.sE := rfl

theorem invZ_invZ : C.invZ.invZ = C := by
  cases C
  simp only [invZ, inv_inv]

def MatrixIdentityOffBase : Prop :=
  (∀ u t (φ : Fin (Dc.a u) → K) (F : Fin (Df.nV t) → K),
    C.ζ u t * Dc.Pt u t φ F = C.B u φ ((S.ι t).mulVec ((Df.Pq t).mulVec F))) ∧
  (∀ u, C.ζ u Bs.μ0 = 1) ∧ (∀ u t, C.ζ u t ≠ 0) ∧
  ∀ u w, vw w (C.ζ u (S.μ w)) = 0 ∧ vw (conjPl w) (C.ζ u (S.μ w)) = 0

theorem pairing_condition_of_inverse_matrix_identity (h : C.MatrixIdentityOffBase) : C.invZ.PairingFactorsThroughPeriods := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun u t φ F => ?_, fun u => ?_, fun u t => ?_, fun u w => ?_⟩
  · simp only [invZ_ζ, invZ_B]
    rw [← h1 u t φ F, ← mul_assoc, inv_mul_cancel₀ (h3 u t), one_mul]
  · simp [h2 u]
  · simpa using h3 u t
  · simp only [invZ_ζ]
    rw [vw_inv, (h4 u w).1, neg_zero]

theorem inverse_matrix_identity_of_pairing (h0 : S.H0) (h : C.PairingFactorsThroughPeriods) : C.invZ.MatrixIdentityOffBase := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun u t φ F => ?_, fun u => ?_, fun u t => ?_, fun u w => ⟨?_, ?_⟩⟩
  · simp only [invZ_ζ, invZ_B]
    rw [h1 u t φ F, ← mul_assoc, inv_mul_cancel₀ (h3 u t), one_mul]
  · simp [h2 u]
  · simpa using h3 u t
  · simp only [invZ_ζ]
    rw [vw_inv, h4 u w, neg_zero]
  · simp only [invZ_ζ]
    have := h4 u (conjPl w)
    rw [h0.1 w] at this
    rw [vw_inv, this, neg_zero]

theorem pairing_iff_inverse_matrix_identity (h0 : S.H0) : C.PairingFactorsThroughPeriods ↔ C.invZ.MatrixIdentityOffBase :=
  ⟨C.inverse_matrix_identity_of_pairing h0, fun h => by simpa only [invZ_invZ] using C.invZ.pairing_condition_of_inverse_matrix_identity h⟩

end ColData

structure ConvFace (Bs : DefBase K) where

  primes : Prop

  symLevel : Prop

  sg0 : K →+* ℂ

  Hk : Type

  ev : Bs.Ix → Hk → K

  ev_inj : Function.Injective ev

structure IndefConv (Bs : DefBase K) (μ : HeightOneSpectrum (𝓞 K) → Bs.Tup) (cf : ConvFace Bs) : Prop where

  c1 : cf.primes

  c2 : ∀ t : Bs.Tup, t = Bs.μ0 ∨ ∃ w, μ w = t

  c3 : cf.symLevel

  c4 : Bs.v0.embedding = cf.sg0

structure HeckeRows {Bs : DefBase K} (cf : ConvFace Bs) {Df : DefSide Bs} (S : IndefData Df) where

  hE : cf.Hk → Module.End K (Fin S.D → K)

  eigE : ∀ c, S.Ep c = ⨅ T, LinearMap.ker (hE T - cf.ev c T • LinearMap.id)

structure HeckeAll {Bs : DefBase K} (cf : ConvFace Bs) {Df : DefSide Bs} (S : IndefData Df) extends HeckeRows cf S where

  hW : ∀ j, cf.Hk → Module.End K (Fin (S.dW j) → K)

  eigW : ∀ j c, S.Wp j c = ⨅ T, LinearMap.ker (hW j T - cf.ev c T • LinearMap.id)

structure IndefPkg2 {Bs : DefBase K} (A : DefAmb Bs) (fc : DefSub A → DefFace Bs) (cf : ConvFace Bs) (C CH : ℝ)
    extends IndefPkg A fc C CH where

  conv : IndefConv Bs toIndefPkg.core.base.μ cf

  heckeB : HeckeAll cf toIndefPkg.core.base.toIndefData

  heckeC : HeckeAll cf toIndefPkg.core.cols.toIndefData

abbrev IndefPkg2.forget {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
    (P : IndefPkg2 A fc cf C CH) : IndefPkg A fc C CH :=
  P.toIndefPkg

theorem conj_ne_embedding (v : InfinitePlace K) (hv : v.IsComplex) :
    ComplexEmbedding.conjugate v.embedding ≠ v.embedding := by
  intro h
  exact (InfinitePlace.isComplex_iff.1 hv) (ComplexEmbedding.isReal_iff.2 h)

structure IndefFace2 extends IndefFace where

  cf : ConvFace Bs

def IndefLink2 (Ix : ℝ → Type) (F : ∀ x, Ix x → IndefFace2) (CH : ℝ)
    (Q : ∀ x (i : Ix x), ℝ → DefSub (F x i).A → (HeightOneSpectrum (𝓞 (F x i).K) → (F x i).Bs.Tup) → Prop) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Ix x, ∃ P : IndefPkg2 (F x i).A (F x i).fc (F x i).cf C CH, Q x i C P.Zs P.core.base.μ

theorem IndefLink2.forget {Ix : ℝ → Type} {F : ∀ x, Ix x → IndefFace2} {CH : ℝ}
    {Q : ∀ x (i : Ix x), ℝ → DefSub (F x i).A → (HeightOneSpectrum (𝓞 (F x i).K) → (F x i).Bs.Tup) → Prop}
    (h : IndefLink2 Ix F CH Q) : IndefLink Ix (fun x i => (F x i).toIndefFace) CH Q := by
  obtain ⟨C, x0, hC⟩ := h
  exact ⟨C, x0, fun x hx i => by
    obtain ⟨P, hP⟩ := hC x hx i
    exact ⟨P.forget, hP⟩⟩

namespace IndefPkg2

variable {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
  (P : IndefPkg2 A fc cf C CH)

theorem mi0 : P.core.cols.col.invZ.MatrixIdentityOffBase :=
  P.core.cols.col.inverse_matrix_identity_of_pairing P.core.cols.h0 P.core.cols.l1b

theorem tuple_is_base_or_member : ∀ t : Bs.Tup, t = Bs.μ0 ∨ ∃ w, P.core.cols.μ w = t := by
  intro t
  rcases P.conv.c2 t with h | ⟨w, hw⟩
  · exact Or.inl h
  · exact Or.inr ⟨w, by rw [← P.core.extra.level.1]; exact hw⟩

theorem base_level_log_eigenvalue_bound : P.core.base.toIndefData.L6 ((fc P.Zs).Z.num C CH) := P.core.base_level_log_eigenvalue_bound

theorem fun1 (hde : 0 ≤ ((fc P.Zs).Z.num C CH).de) (hde3 : ((fc P.Zs).Z.num C CH).de ≤ 1 / 3) :
    P.core.cols.muMaxRR ≤ ((fc P.Zs).Z.num C CH).hh - meanLog P.core.cols.κ + 14 * ((fc P.Zs).Z.num C CH).la :=
  P.core.fun1 hde hde3

theorem period_images_surjective (hD : 0 < P.core.cols.D) (z : (fc P.Zs).Sp.HH) (hz : z ∈ (fc P.Zs).Sp.Rw) :
    ∃ y, P.core.cols.col.sE y = z :=
  P.core.cols.col.period_images_surjective P.core.cols.l1e (P.core.cols.frames.1 Bs.v0) hD z hz

theorem divCore [IsTotallyComplex K] (hM : Formalism.DivisorInequality.BoundsMu) (hS : SpecDet) (hR0 : GramDeterminantQuotientMetric)
    (hG : LatticeGlue) (hRam : RamBasic) (hH : HeightBoundConstant) [Nonempty Bs.Ix] (wf0 : (fc P.Zs).Df0.WF)
    (wf1 : (fc P.Zs).Df1.WF)
    (hde : 0 ≤ ((fc P.Zs).Z.num C CH).de) (hde3 : ((fc P.Zs).Z.num C CH).de ≤ 1 / 3)
    (eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin ((fc P.Zs).Df0.dQ t) → Fin ((fc P.Zs).Df0.dQ t) → K)
    (heb : ∀ t w, IsLocBasis ((fc P.Zs).Df0.abelian₂ t) w (eb t w))
    (Sy : Finset (HeightOneSpectrum (𝓞 K))) (hSy : P.core.base.Tw ⊆ Sy)
    (hG0 : ∀ y, y ∉ Sy → vw y ((fc P.Zs).Df0.Gm eb (P.core.base.μ y) y) = 0)
    (LG E3 : ℝ) (E2 : Bs.J → ℝ) (gy : HeightOneSpectrum (𝓞 K) → ℝ) (ηy : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ)
    (hi : ∀ y ∈ Sy, (vw y ((fc P.Zs).Df0.Gm eb (P.core.base.μ y) y) : ℝ) ≤ (P.core.base.D : ℝ) * gy y)
    (hLG : ∑ y ∈ Sy, lw y * gy y ≤ LG)
    (hiv : ∀ y ∈ P.core.base.Tw, ∀ j, (jw ((fc P.Zs).Df0.HT j (P.core.base.μ y)) y ((fc P.Zs).Df0.Tl j (P.core.base.μ y)) : ℝ) ≤
      ((ramw y : ℝ) * ((fc P.Zs).Z.num C CH).J0 (P.core.base.μ y) y j) * (P.core.base.D : ℝ) + ηy y j)
    (hE2 : ∀ j, ∑ y ∈ P.core.base.Tw, lw y * ηy y j / (P.core.base.D : ℝ) ≤ E2 j)
    (hE3 : ∑ y ∈ Sy, lw y * (2 / ellw y ^ 2) ≤ E3)
    (u : (fc P.Zs).Dc.Mem) (hXc : ∀ v, IsUnit (((fc P.Zs).Dc.Xc u v).det)) (hne : P.core.cols.col.B u ≠ 0)
    (X0 : InfinitePlace K → Matrix (Fin ((fc P.Zs).Df1.nV Bs.μ0)) (Fin ((fc P.Zs).Df1.nV Bs.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((fc P.Zs).Df1.HV Bs.μ0).map v.embedding)
    (pU : InfinitePlace K → ℝ)
    (hpU : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin ((fc P.Zs).Dc.a u))) ((fc P.Zs).Dc.Xc u)
      (Pi.basisFun K (Fin ((fc P.Zs).Df1.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ((fc P.Zs).Dc.Pt u Bs.μ0) ≤ pU v)
    (X : ℝ)
    (hX : X = (∑ j, ((fc P.Zs).Z.num C CH).l3 j) +
      2 * (∑ j, ∑ y ∈ P.core.base.Tw, lw y * ((ramw y : ℝ) * ((fc P.Zs).Z.num C CH).F0 y j)) + LG +
      (∑ j, (((fc P.Zs).Z.num C CH).E1 j + E2 j)) + E3) :
    P.core.cols.muCC + Formalism.HN.htMap (Pi.basisFun K (Fin ((fc P.Zs).Dc.a u))) ((fc P.Zs).Dc.Xc u)
        (Pi.basisFun K (Fin P.core.cols.D)).dualBasis (Formalism.HN.dualFrame P.core.cols.XE) (P.core.cols.col.B u) ≤
      X + 3 * ((fc P.Zs).Z.num C CH).de * (X + ((fc P.Zs).Z.num C CH).hh + 28 * ((fc P.Zs).Z.num C CH).la) +
        28 * ((fc P.Zs).Z.num C CH).la +
        ((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (pU v ^ 2) - ∑ j, ((fc P.Zs).Z.num C CH).l6 j) :=
  P.forget.core.divCore hM hS hR0 hG hRam hH wf0 wf1 hde hde3 eb heb Sy hSy hG0 LG E3 E2 gy ηy hi hLG hiv hE2 hE3
    u hXc hne X0 hX0 pU hpU X hX

end IndefPkg2

namespace IndefData

variable {Bs : DefBase K} {Df : DefSide Bs} (S : IndefData Df)

def FramesR : Prop := ∀ v, IsUnit (S.XE v).det

def BaseTypeSubspacesMapOnto : Prop := ∀ p, (Df.Qp Bs.μ0 p).map (S.ι Bs.μ0).mulVecLin = S.Ep p

def BijectivityAndPositivity : Prop :=
  (∀ t, Function.Bijective (S.ι t).mulVec) ∧ (∀ v, 0 < S.κ v) ∧ (∀ j t p v, 0 < S.lam j t p v) ∧
  ∀ t v, (t = Bs.μ0 ∨ v = Bs.v0) → ∀ p,
    IsScalarOn (Df.XQ t) S.XE v (S.ι t) (S.Qpart t p) (S.κ v * ∏ j, S.lam j t p v)

end IndefData

structure IndefColsR {Bs : DefBase K} (Df : DefSide Bs) (Dc : DefCols Df) (Sp : SPer Dc) (N : IndefNum Bs)
    extends IndefData Df where

  pos : Df.Pos

  h0 : toIndefData.H0

  frames : toIndefData.FramesR

  l1a : toIndefData.BaseTypeSubspacesMapOnto

  l1c : toIndefData.BijectivityAndPositivity

  l6 : toIndefData.L6 N

  col : ColData Dc Sp toIndefData

  l1b : col.PairingFactorsThroughPeriods

  l1e : col.L1e

structure IndefExtraR {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}
    (S0 : IndefSide Df0 N) (S1 : IndefColsR Df1 Dc Sp N) : Prop where

  untw : S0.toIndefData.Untwisted N

  level : LevelLink S0.toIndefData S1.toIndefData

  passage : Passage N S0.toIndefData S1.toIndefData

  fun0 : S0.toIndefData.FUN N

structure IndefCoreR {Bs : DefBase K} (Df0 Df1 : DefSide Bs) (Dc : DefCols Df1) (Sp : SPer Dc) (N : IndefNum Bs) where

  base : IndefSide Df0 N

  cols : IndefColsR Df1 Dc Sp N

  extra : IndefExtraR base cols

structure IndefPkgR {Bs : DefBase K} (A : DefAmb Bs) (fc : DefSub A → DefFace Bs) (cf : ConvFace Bs) (C CH : ℝ) where

  Zs : DefSub A

  stable : Zs.Stable

  inBlock : Zs.InBlock

  core : IndefCoreR (fc Zs).Df0 (fc Zs).Df1 (fc Zs).Dc (fc Zs).Sp ((fc Zs).Z.num C CH)

  conv : IndefConv Bs core.base.μ cf

  heckeB : HeckeAll cf core.base.toIndefData

  heckeC : HeckeRows cf core.cols.toIndefData

def IndefCols.toR {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
    (S : IndefCols Df Dc Sp N) : IndefColsR Df Dc Sp N where
  toIndefData := S.toIndefData
  pos := S.pos
  h0 := S.h0
  frames := S.frames.1
  l1a := S.l1a.1
  l1c := ⟨S.l1c.1, S.l1c.2.2.1, S.l1c.2.2.2.1, S.l1c.2.2.2.2.1⟩
  l6 := S.l6
  col := S.col
  l1b := S.l1b
  l1e := S.l1e

def IndefCore.toR {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}
    (P : IndefCore Df0 Df1 Dc Sp N) : IndefCoreR Df0 Df1 Dc Sp N where
  base := P.base
  cols := P.cols.toR
  extra := ⟨P.extra.untw, P.extra.level, P.extra.passage, P.extra.fun0⟩

def IndefPkg2.toR {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
    (P : IndefPkg2 A fc cf C CH) : IndefPkgR A fc cf C CH where
  Zs := P.Zs
  stable := P.stable
  inBlock := P.inBlock
  core := P.core.toR
  conv := P.conv
  heckeB := P.heckeB
  heckeC := P.heckeC.toHeckeRows

def IndefLinkR (Ix : ℝ → Type) (F : ∀ x, Ix x → IndefFace2) (CH : ℝ)
    (Q : ∀ x (i : Ix x), ℝ → DefSub (F x i).A → (HeightOneSpectrum (𝓞 (F x i).K) → (F x i).Bs.Tup) → Prop) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Ix x, ∃ P : IndefPkgR (F x i).A (F x i).fc (F x i).cf C CH, Q x i C P.Zs P.core.base.μ

theorem IndefLink2.toR {Ix : ℝ → Type} {F : ∀ x, Ix x → IndefFace2} {CH : ℝ}
    {Q : ∀ x (i : Ix x), ℝ → DefSub (F x i).A → (HeightOneSpectrum (𝓞 (F x i).K) → (F x i).Bs.Tup) → Prop}
    (h : IndefLink2 Ix F CH Q) : IndefLinkR Ix F CH Q := by
  obtain ⟨C, x0, hC⟩ := h
  exact ⟨C, x0, fun x hx i => by
    obtain ⟨P, hP⟩ := hC x hx i
    exact ⟨P.toR, hP⟩⟩

namespace IndefColsR

variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
  (S : IndefColsR Df Dc Sp N)

theorem dQ_eq (t : Bs.Tup) : Df.dQ t = S.D := dim_of_bij _ (S.l1c.1 t)

theorem Qpart_base (p : Bs.Ix) : S.Qpart Bs.μ0 p = Df.Qp Bs.μ0 p := by
  rw [IndefData.Qpart, ← S.l1a p]
  exact Submodule.comap_map_eq_of_injective (f := (S.ι Bs.μ0).mulVecLin) (S.l1c.1 _).1 _

theorem D_pos : 0 < S.D := S.dQ_eq Bs.μ0 ▸ S.pos

theorem log_eigenvalue_sum_le_min [Nonempty Bs.Ix] (v : InfinitePlace K) :
    ∑ j, N.l6 j ≤ minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) :=
  Finset.le_inf' _ _ fun p _ => Finset.sum_le_sum fun j _ => S.l6 j p v

theorem RR_spec (hG : LatticeGlue) (wf : Df.WF) :
    Submodule.IsLattice K S.RR ∧ ∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal S.RR =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))) := by
  have hfin : {w | S.μ w ≠ Bs.μ0}.Finite := S.Tw.finite_toSet.subset fun w hw => (S.h0.2 w).2 hw
  refine hG K S.D (matLat (S.ι Bs.μ0) (Df.abelian₂ Bs.μ0)) (fun w => matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w)))
    (matLat_lattice _ (S.l1c.1 _).2 _ (wf.Lam_lat _)) (fun w => matLat_lattice _ (S.l1c.1 _).2 _ (wf.Lam_lat _))
    (hfin.subset fun w hw => ?_)
  intro h
  apply hw
  show Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))) = _
  rw [h]

theorem height (hH : HeightBoundConstant) [Nonempty Bs.Ix] (wf : Df.WF) (u : Dc.Mem) (hXc : ∀ v, IsUnit (Dc.Xc u v).det)
    (hne : S.col.B u ≠ 0)
    (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df.HV Bs.μ0).map v.embedding)
    (pU : InfinitePlace K → ℝ)
    (hpU : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u)
      (Pi.basisFun K (Fin (Df.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v (Dc.Pt u Bs.μ0) ≤ pU v) :
    Formalism.HN.htMap (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin S.D)).dualBasis
              (Formalism.HN.dualFrame S.XE) (S.col.B u) ≤
      (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (pU v ^ 2) - ∑ j, N.l6 j - meanLog S.κ := by
  have hQ := S.dQ_eq
  have hfr := S.frames
  have hc := S.l1c
  have hb := S.l1b
  have hmin := S.log_eigenvalue_sum_le_min
  have hsc : ∀ v p, IsScalarOn (Df.XQ Bs.μ0) S.XE v (S.ι Bs.μ0) (Df.Qp Bs.μ0 p)
      (S.κ v * ∏ j, S.lam j Bs.μ0 p v) := fun v p => by
    rw [← S.Qpart_base p]; exact hc.2.2.2 Bs.μ0 v (Or.inl rfl) p
  obtain ⟨⟨μ, Tw, D, XE, Ep, ι, dW, XW, Wp, M, θ, κ, lam, err0⟩, _p1, _g0, _g1, _g2, _g3, _g5, ⟨B, ζ, sE⟩, _g6, _g7⟩ := S
  obtain ⟨HH, nHH, iHH, Pu, Rw⟩ := Sp
  obtain ⟨Mem, a, Xc, Pt⟩ := Dc
  obtain ⟨nV, HV, Mt, dQ, Pq, XQ, Qp, dZ, HT, XT, Tl, Zp⟩ := Df
  dsimp only at hQ hfr hc hb hmin hsc hXc hne X0 hX0 hpU u
  obtain rfl : dQ = fun _ => D := funext hQ
  have H := (hH K (nV Bs.μ0) D 0 (fun _ => a u) (fun _ => Xc u) (fun _ => hXc) (fun j => j.elim0) (HV Bs.μ0) X0 hX0
    (Pq Bs.μ0) (wf.Pq_surj _) (XQ Bs.μ0) (wf.XQ_quot _) XE hfr (ι Bs.μ0) (isUnit_det_of_bij _ (hc.1 _))
    Bs.Ix Bs.J (Qp Bs.μ0) wf.Qp_top κ (fun j p v => lam j Bs.μ0 p v) (fun j p v => lam j Bs.μ0 p v)
    hc.2.1 (fun j p v => hc.2.2.1 j _ p v) (fun _ _ _ => le_rfl)
    hsc (Pt u Bs.μ0) (B u)
    (fun φ F => by
      have h1 := hb.1 u Bs.μ0 φ F
      rw [hb.2.1 u, one_mul] at h1
      rw [← h1]
      show _ = Pt u Bs.μ0 ((1 : Matrix (Fin (a u)) (Fin (a u)) K).mulVec φ) F
      rw [Matrix.one_mulVec])
    hne pU (fun j => j.elim0) hpU (fun j => j.elim0)).2
  have hn : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    exact_mod_cast this
  have h2 : ∑ j, N.l6 j ≤ (1 / (Formalism.HN.nPl K : ℝ)) *
      ∑ v, minOver (fun p => ∑ j, Real.log (lam j Bs.μ0 p v)) := by
    have h3 : ∑ _v : InfinitePlace K, ∑ j, N.l6 j ≤
        ∑ v, minOver (fun p => ∑ j, Real.log (lam j Bs.μ0 p v)) := Finset.sum_le_sum fun v _ => hmin v
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h3
    rw [one_div, le_inv_mul_iff₀ hn]
    exact h3
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at H
  linarith [H, h2]

theorem intoDual (hD : DivIntoDualShift) (hG : LatticeGlue) (wf : Df.WF) (u : Dc.Mem)
    (Nu Nu' : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (σ : HeightOneSpectrum (𝓞 K) → ℝ)
    (τ : HeightOneSpectrum (𝓞 K) → ℤ)
    (hL2 : ∀ w, ∀ φ ∈ Nu, ∀ F ∈ Df.Mt (S.μ w),
      Dc.Pt u (S.μ w) φ F = 0 ∨ σ w ≤ (vw w (Dc.Pt u (S.μ w) φ F) : ℝ))
    (hτ : ∀ w, τ w ≤ ⌈σ w⌉) (hsh : IsShift Nu Nu' τ) :
    ∀ φ ∈ Nu', S.col.B u φ ∈ Formalism.HN.dualLat S.RR := by
  intro φ hφ x hx
  refine hD K (Dc.a u) S.D S.RR (S.col.B u) (fun w => Df.nV (S.μ w)) (fun w => Df.Mt (S.μ w))
    (fun w => S.ι (S.μ w) * Df.Pq (S.μ w)) (fun _ => 1) (fun w => Dc.Pt u (S.μ w))
    (fun w => S.col.ζ u (S.μ w)) (fun w => S.l1b.2.2.1 u _) (fun w => S.l1b.2.2.2 u w)
    (fun w φ F => ?_) Nu Nu' σ τ hL2 hτ hsh (fun w => ?_) φ hφ x hx
  · rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    exact S.l1b.1 u _ φ F
  · rw [matLat_one, matLat_mul]
    exact (S.RR_spec hG wf).2 w

end IndefColsR

namespace IndefCoreR

variable {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}
  (P : IndefCoreR Df0 Df1 Dc Sp N)

include P

theorem base_level_log_eigenvalue_bound : P.base.toIndefData.L6 N := fun j p v => by
  rw [P.extra.level.2.2]; exact P.cols.l6 j p v

theorem fun1 (hde : 0 ≤ N.de) (hde3 : N.de ≤ 1 / 3) :
    P.cols.muMaxRR ≤ N.hh - meanLog P.cols.κ + 14 * N.la := by
  rw [← P.extra.level.2.1]; exact (P.extra.passage hde hde3 _ P.extra.fun0).1

theorem tuple_is_base_or_member (h : ∀ t : Bs.Tup, t = Bs.μ0 ∨ ∃ w, P.base.μ w = t) : ∀ t : Bs.Tup, t = Bs.μ0 ∨ ∃ w, P.cols.μ w = t := by
  intro t
  rcases h t with h | ⟨w, hw⟩
  · exact Or.inl h
  · exact Or.inr ⟨w, by rw [← P.extra.level.1]; exact hw⟩

end IndefCoreR

theorem IndefCoreR.divCore [IsTotallyComplex K] (hM : Formalism.DivisorInequality.BoundsMu) (hS : SpecDet) (hR0 : GramDeterminantQuotientMetric)
    (hG : LatticeGlue) (hRam : RamBasic) (hH : HeightBoundConstant) {Bs : DefBase K} {Df0 Df1 : DefSide Bs}
    {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs} [Nonempty Bs.Ix] (wf0 : Df0.WF) (wf1 : Df1.WF)
    (P : IndefCoreR Df0 Df1 Dc Sp N) (hde : 0 ≤ N.de) (hde3 : N.de ≤ 1 / 3)
    (eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin (Df0.dQ t) → Fin (Df0.dQ t) → K)
    (heb : ∀ t w, IsLocBasis (Df0.abelian₂ t) w (eb t w))
    (Sy : Finset (HeightOneSpectrum (𝓞 K))) (hSy : P.base.Tw ⊆ Sy)
    (hG0 : ∀ y, y ∉ Sy → vw y (Df0.Gm eb (P.base.μ y) y) = 0)
    (LG E3 : ℝ) (E2 : Bs.J → ℝ) (gy : HeightOneSpectrum (𝓞 K) → ℝ) (ηy : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ)
    (hi : ∀ y ∈ Sy, (vw y (Df0.Gm eb (P.base.μ y) y) : ℝ) ≤ (P.base.D : ℝ) * gy y)
    (hLG : ∑ y ∈ Sy, lw y * gy y ≤ LG)
    (hiv : ∀ y ∈ P.base.Tw, ∀ j, (jw (Df0.HT j (P.base.μ y)) y (Df0.Tl j (P.base.μ y)) : ℝ) ≤
      ((ramw y : ℝ) * N.J0 (P.base.μ y) y j) * (P.base.D : ℝ) + ηy y j)
    (hE2 : ∀ j, ∑ y ∈ P.base.Tw, lw y * ηy y j / (P.base.D : ℝ) ≤ E2 j)
    (hE3 : ∑ y ∈ Sy, lw y * (2 / ellw y ^ 2) ≤ E3)
    (u : Dc.Mem) (hXc : ∀ v, IsUnit (Dc.Xc u v).det) (hne : P.cols.col.B u ≠ 0)
    (X0 : InfinitePlace K → Matrix (Fin (Df1.nV Bs.μ0)) (Fin (Df1.nV Bs.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df1.HV Bs.μ0).map v.embedding)
    (pU : InfinitePlace K → ℝ)
    (hpU : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u)
      (Pi.basisFun K (Fin (Df1.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v (Dc.Pt u Bs.μ0) ≤ pU v)
    (X : ℝ)
    (hX : X = (∑ j, N.l3 j) + 2 * (∑ j, ∑ y ∈ P.base.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)) + LG +
      (∑ j, (N.E1 j + E2 j)) + E3) :
    P.cols.muCC + Formalism.HN.htMap (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin P.cols.D)).dualBasis
        (Formalism.HN.dualFrame P.cols.XE) (P.cols.col.B u) ≤
      X + 3 * N.de * (X + N.hh + 28 * N.la) + 28 * N.la +
        ((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (pU v ^ 2) - ∑ j, N.l6 j) := by
  have h0 : P.base.muCC ≤ _ :=
    P.base.boundsMu hM hS hR0 hG hRam wf0 P.extra.untw eb heb Sy hSy hG0 LG E3 E2 gy ηy hi hLG hiv hE2 hE3
  have hp := (P.extra.passage hde hde3 _ P.extra.fun0).2
  have hh := P.cols.height hH wf1 u hXc hne X0 hX0 pU hpU
  have hκ : meanLog P.cols.κ = meanLog P.base.κ := by rw [P.extra.level.2.1]
  rw [hκ] at hh
  have h1 : P.base.muCC - meanLog P.base.κ ≤ X := by rw [hX]; linarith [h0]
  have h2 : 3 * N.de * (P.base.muCC + (N.hh - meanLog P.base.κ) + 28 * N.la) ≤
      3 * N.de * (X + N.hh + 28 * N.la) :=
    mul_le_mul_of_nonneg_left (by linarith [h1]) (by linarith [hde])
  linarith [hp, hh, h1, h2]

theorem IndefColsR.period_images_surjective {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
    (S : IndefColsR Df Dc Sp N) (z : Sp.HH) (hz : z ∈ Sp.Rw) : ∃ y, S.col.sE y = z :=
  S.col.period_images_surjective S.l1e (S.frames Bs.v0) S.D_pos z hz

theorem IndefColsR.mi0 {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
    (S : IndefColsR Df Dc Sp N) : S.col.invZ.MatrixIdentityOffBase :=
  S.col.inverse_matrix_identity_of_pairing S.h0 S.l1b

end Formalism.L2.Indef
