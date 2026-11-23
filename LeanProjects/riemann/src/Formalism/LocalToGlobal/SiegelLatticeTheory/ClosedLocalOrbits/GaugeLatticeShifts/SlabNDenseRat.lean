import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipReal

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section CayInv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [Invertible (2 : K)]

theorem half_add_half' (M : Matrix ι ι K) : (⅟2 : K) • M + (⅟2 : K) • M = M := by
  rw [← add_smul, invOf_two_add_invOf_two, one_smul]

theorem cay_eq {N : ℕ} {Z : Matrix ι ι K} (hN : ((⅟2 : K) • Z) ^ N = 0) :
    cay N Z = (1 + (⅟2 : K) • Z) * geo N ((⅟2 : K) • Z) := by
  set Y : Matrix ι ι K := (⅟2 : K) • Z with hY
  set G := geo N Y with hG
  have hBG : (1 - Y) * G = 1 := by rw [hG, geo, mul_neg_geom_sum, hN, sub_zero]
  have e1 : G = 1 + Y * G := by
    have := hBG
    rw [Matrix.sub_mul, Matrix.one_mul] at this
    rw [← this]; abel
  have e2 : Z = Y + Y := by rw [hY, half_add_half']
  have e3 : cay N Z = 1 + Z * G := rfl
  rw [e3, Matrix.add_mul, Matrix.one_mul]
  calc 1 + Z * G = (1 + Y * G) + Y * G := by rw [e2, Matrix.add_mul]; abel
    _ = G + Y * G := by rw [← e1]

theorem cay_neg_mul {N : ℕ} {Z : Matrix ι ι K} (hN : ((⅟2 : K) • Z) ^ N = 0) : cay N (-Z) * cay N Z = 1 := by
  have hN' : ((⅟2 : K) • -Z) ^ N = 0 := by rw [smul_neg, neg_pow, hN, mul_zero]
  rw [cay_eq hN, cay_eq hN', smul_neg]
  set Y : Matrix ι ι K := (⅟2 : K) • Z with hY
  have h1 : geo N (-Y) * (1 + Y) = 1 := by
    have := geom_sum_mul_neg (-Y) N
    rw [sub_neg_eq_add] at this
    rw [geo, this, neg_pow, hN, mul_zero, sub_zero]
  have h2 : (1 - Y) * geo N Y = 1 := by rw [geo, mul_neg_geom_sum, hN, sub_zero]
  calc (1 + -Y) * geo N (-Y) * ((1 + Y) * geo N Y) = (1 - Y) * (geo N (-Y) * (1 + Y)) * geo N Y := by
        rw [← sub_eq_add_neg]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, h2]

end CayInv

def mkUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.UJ ε :=
  ⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_comm_one (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, Formalism.REAL.Jm_mul_self]⟩, hg⟩

theorem uMat_mkUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) :
    uMat (mkUJ ε g hg) = g := rfl

section RatEl

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev N0 (D : D7) : ℕ := 2 * D.R.rS + 2

theorem lvk_lt (k : Kap X) : lvk X k < N0 D := by show lvk X k < 2 * D.R.rS + 2; have := lvk_le X k; omega

theorem nil_of_pat {K : Type*} [CommRing K] {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) K}
    (hY : InPat (lvk X) k Y) (c : K) : (c • Y) ^ N0 D = 0 :=
  pow_eq_zero_of_inPat hk (lvk_lt X) (inPat_smul c hY)

def gE (Y : Matrix (Kap X) (Kap X) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  Bm X * cay (N0 D) Y * Bm' X

theorem gE_mul {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    gE X (-Y) * gE X Y = 1 := by
  unfold gE
  have e : Bm X * cay (N0 D) (-Y) * Bm' X * (Bm X * cay (N0 D) Y * Bm' X) =
      Bm X * (cay (N0 D) (-Y) * ((Bm' X * Bm X) * cay (N0 D) Y)) * Bm' X := by simp only [Matrix.mul_assoc]
  rw [e, Bm'_mul_Bm, Matrix.one_mul, cay_neg_mul (nil_of_pat X hk hY _), Matrix.mul_one, Bm_mul_Bm']

theorem gE_mul' {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    gE X Y * gE X (-Y) = 1 := by
  have := gE_mul X hk (inPat_neg hY)
  rwa [neg_neg] at this

theorem cT_eq {m p : Type} (M : Matrix m p X.B.I.E) : Formalism.UG.cT (starRingEnd X.B.I.E) M = Mᴴ := by
  ext i j
  simp only [Formalism.UG.cT, conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
  rfl

theorem gE_unitary {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : (gE X Y)ᴴ * X.B.I.J * gE X Y = X.B.I.J := by
  have hc := cay_unitary hYs (nil_of_pat X hk hY (⅟2 : X.B.I.E))
  have hh : (Bm' X)ᴴ * (Bm X)ᴴ = 1 := by rw [← conjTranspose_mul, Bm_mul_Bm', conjTranspose_one]
  have hJB := JB_eq X
  unfold gE
  calc (Bm X * cay (N0 D) Y * Bm' X)ᴴ * X.B.I.J * (Bm X * cay (N0 D) Y * Bm' X)
      = (Bm' X)ᴴ * ((cay (N0 D) Y)ᴴ * ((Bm X)ᴴ * X.B.I.J * Bm X) * cay (N0 D) Y) * Bm' X := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (Bm' X)ᴴ * (Bm X)ᴴ * X.B.I.J * (Bm X * Bm' X) := by
        rw [← hJB, hc, hJB]; simp only [Matrix.mul_assoc]
    _ = X.B.I.J := by rw [hh, Bm_mul_Bm', Matrix.one_mul, Matrix.mul_one]

def gGL {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    GL (Fin X.B.I.n) X.B.I.E :=
  ⟨gE X Y, gE X (-Y), gE_mul' X hk hY, gE_mul X hk hY⟩

theorem gGL_mem {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : gGL X hk hY ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J := by
  show Formalism.UG.cT (starRingEnd X.B.I.E) (gE X Y) * X.B.I.J * gE X Y = X.B.I.J
  rw [cT_eq]
  exact gE_unitary X hk hY hYs

theorem sig_eq : (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) = starRingEnd X.B.I.E := RingHom.ext fun _ => rfl

theorem gE_real (v : InfinitePlace X.B.I.F) (Y : Matrix (Kap X) (Kap X) X.B.I.E) :
    (X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v =
      Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v := by
  unfold gE Bv Bv'
  rw [Matrix.map_mul, Matrix.map_mul, cay_map]
  simp only [Matrix.mul_assoc]

theorem skew_map (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hYs : Yᴴ * JB X = -(JB X * Y)) :
    (Y.map (X.B.I.φ v))ᴴ * JBv X v = -(JBv X v * Y.map (X.B.I.φ v)) := by
  rw [JBv, map_conjTranspose, ← Matrix.map_mul, hYs, ← Matrix.map_mul, Matrix.map_neg]
  exact fun a => map_neg _ a

theorem inUJ_real {k : ℕ} (hk : 1 ≤ k) (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hY : InPat (lvk X) k Y) (hYs : Yᴴ * JB X = -(JB X * Y)) :
    Formalism.REAL.inUJ (X.B.I.ε v) ((X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v) := by
  rw [gE_real]
  unfold Formalism.REAL.inUJ
  have hc := cay_unitary (skew_map X v hYs) (nil_of_pat X hk (inPat_map (X.B.I.φ v) hY) (⅟2 : ℂ))
  have hh : (Bv' X v)ᴴ * (Bv X v)ᴴ = 1 := by rw [← conjTranspose_mul, Bv_mul_Bv', conjTranspose_one]
  calc (Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) *
        (Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v)
      = (Bv' X v)ᴴ * ((cay (N0 D) (Y.map (X.B.I.φ v)))ᴴ * ((Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v) *
        cay (N0 D) (Y.map (X.B.I.φ v))) * Bv' X v := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (Bv' X v)ᴴ * ((Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v) * Bv' X v := by rw [Bv_gram, hc]
    _ = ((Bv' X v)ᴴ * (Bv X v)ᴴ) * Formalism.REAL.Jm (X.B.I.ε v) * (Bv X v * Bv' X v) := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε v) := by rw [hh, Bv_mul_Bv', Matrix.one_mul, Matrix.mul_one]

def gA {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : X.B.I.GA :=
  (fun v => mkUJ (X.B.I.ε v) _ (inUJ_real X hk v hY hYs),
    Formalism.L2.SG.ColsDim.ratHom X.B.I.cm.sig X.B.I.J (Af X.B.I.F)
      ⟨gGL X hk hY, by rw [sig_eq]; exact gGL_mem X hk hY hYs⟩)

theorem gA_GF {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : gA X hk hY hYs ∈ X.B.I.GFset :=
  ⟨gGL X hk hY, gGL_mem X hk hY hYs, fun v => rfl, rfl⟩

theorem Mv_gA {k : ℕ} (hk : 1 ≤ k) (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hY : InPat (lvk X) k Y) (hYs : Yᴴ * JB X = -(JB X * Y)) :
    Mv X v (gA X hk hY hYs).1 = cay (N0 D) (Y.map (X.B.I.φ v)) := by
  unfold Mv
  show Bv' X v * ((X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v) * Bv X v = _
  rw [gE_real]
  simp only [← Matrix.mul_assoc, Bv'_mul_Bv, Matrix.one_mul]
  rw [Matrix.mul_assoc, Bv'_mul_Bv, Matrix.mul_one]

theorem gA_ninf {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : (gA X hk hY hYs).1 ∈ X.NinfU u := by
  intro v
  apply inN_of_pat X u v
  have := Mv_gA X hk v hY hYs
  unfold Mv at this
  rw [this]
  exact inPat_mono hk (cay_sub_one _ (inPat_map (X.B.I.φ v) hY))

end RatEl
