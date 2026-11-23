import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormaliseMeanSquareOfCocompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixModel

variable {D : D7}

theorem mulVec_of_kill {R : Type} [CommRing R] {k l n : ℕ} (J : Matrix (Fin n) (Fin k) R) (A : Matrix (Fin k) (Fin n) R)
    (Z : Matrix (Fin n) (Fin l) R) (P : Matrix (Fin l) (Fin n) R) (v : Fin n → R) (h : P *ᵥ v = 0) :
    (J * A + Z * P) *ᵥ v = J *ᵥ (A *ᵥ v) := by
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, add_zero]

theorem mul_trace_smul {R : Type} [CommRing R] {n : ℕ} {a c : R} (h : a * c = 1) (M : Matrix (Fin n) (Fin n) R) :
    a * (c • M).trace = M.trace := by
  rw [trace_smul, smul_eq_mul, ← mul_assoc, h, one_mul]

theorem eq_of_add_self {F R : Type} [Field F] [CharZero F] [CommRing R] [Algebra F R] {a b : R} (h : a + a = b + b) :
    a = b := by
  have h4 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]; norm_num
  rw [← one_mul a, ← one_mul b, ← h4, mul_assoc, mul_assoc, two_mul, two_mul, h]

def skewA (D : D7) (ρ : ℕ) : AddSubgroup (Mx D ρ ρ) where
  carrier := {c | adj c = -c}
  zero_mem' := adj_zero.trans neg_zero.symm
  add_mem' := fun {a b} ha hb => by
    change adj (a + b) = _
    rw [adj_add, ha, hb, neg_add]
  neg_mem' := fun {a} ha => by
    change adj (-a) = _
    rw [adj_neg, ha]

theorem mem_skewA {ρ : ℕ} {c : Mx D ρ ρ} : c ∈ skewA D ρ ↔ adj c = -c := Iff.rfl

def plus (S₀ : HSp D) {ρ : ℕ} (b : Mx D ρ S₀.rank) : Mx D S₀.rank ρ := giA S₀ ⬝ adj b

section Plus

variable (S₀ : HSp D) {ρ : ℕ}

theorem adj_plus (b : Mx D ρ S₀.rank) : adj (plus S₀ b) = b ⬝ giA S₀ := by rw [plus, adj_mul, adj_adj, adj_giA]

theorem adj_plus_gA (b : Mx D ρ S₀.rank) : adj (plus S₀ b) ⬝ gA S₀ = b := by
  rw [adj_plus, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one]

theorem gA_plus (b : Mx D ρ S₀.rank) : gA S₀ ⬝ plus S₀ b = adj b := gA_giA_cancel S₀ _

theorem plus_add (b b' : Mx D ρ S₀.rank) : plus S₀ (b + b') = plus S₀ b + plus S₀ b' := by
  rw [plus, adj_add, Matrix.mul_add]; rfl

theorem plus_neg (b : Mx D ρ S₀.rank) : plus S₀ (-b) = -plus S₀ b := by
  rw [plus, adj_neg, Matrix.mul_neg]; rfl

theorem plus_zero : plus S₀ (0 : Mx D ρ S₀.rank) = 0 := by rw [plus, adj_zero, Matrix.mul_zero]

theorem adj_mul_plus (b b' : Mx D ρ S₀.rank) : adj (b ⬝ plus S₀ b') = b' ⬝ plus S₀ b := by
  rw [adj_mul, adj_plus, Matrix.mul_assoc]; rfl

theorem plus_mul_left (a : Mx D ρ ρ) (b : Mx D ρ S₀.rank) : plus S₀ (a ⬝ b) = plus S₀ b ⬝ adj a := by
  rw [plus, adj_mul, ← Matrix.mul_assoc]; rfl

theorem plus_mul_inv (g : GA D S₀) (b : Mx D ρ S₀.rank) : plus S₀ (b ⬝ mt S₀ g⁻¹) = mt S₀ g ⬝ plus S₀ b := by
  have h := mt_inv S₀ g⁻¹
  rw [inv_inv] at h
  rw [h, plus, plus, adj_mul]
  simp only [Matrix.mul_assoc, gA_giA_cancel]

def cComm (b₁ b₂ : Mx D ρ S₀.rank) : skewA D ρ :=
  ⟨half D • (b₂ ⬝ plus S₀ b₁ - b₁ ⬝ plus S₀ b₂), by
    rw [mem_skewA, adj_smul, cA_half, adj_sub, adj_mul_plus, adj_mul_plus, ← smul_neg, neg_sub]⟩

end Plus

def skewConj {ρ : ℕ} (a : Mx D ρ ρ) (c : skewA D ρ) : skewA D ρ :=
  ⟨a ⬝ c.1 ⬝ adj a, by
    rw [mem_skewA, adj_mul, adj_mul, adj_adj, mem_skewA.1 c.2, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]⟩

structure HypDec (S S₀ : HSp D) (ρ : ℕ) where

  e : Matrix (Fin S.rank) (Fin ρ) D.host.E

  e' : Matrix (Fin S.rank) (Fin ρ) D.host.E

  i₀ : Matrix (Fin S.rank) (Fin S₀.rank) D.host.E
  ee : eᴴ * S.gram * e = 0
  e'e' : e'ᴴ * S.gram * e' = 0
  e'e : e'ᴴ * S.gram * e = 1
  iso : i₀ᴴ * S.gram * i₀ = S₀.gram
  i₀e : i₀ᴴ * S.gram * e = 0
  i₀e' : i₀ᴴ * S.gram * e' = 0
  rank_add : S₀.rank + 2 * ρ = S.rank

namespace HypDec

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

def qX : Matrix (Fin ρ) (Fin S.rank) D.host.E := d.e'ᴴ * S.gram

def qY : Matrix (Fin ρ) (Fin S.rank) D.host.E := d.eᴴ * S.gram

def q0 : Matrix (Fin S₀.rank) (Fin S.rank) D.host.E := S₀.gram⁻¹ * (d.i₀ᴴ * S.gram)

def jX : Mx D S.rank ρ := rat d.e

def jY : Mx D S.rank ρ := rat d.e'

def j0 : Mx D S.rank S₀.rank := rat d.i₀

def pX : Mx D ρ S.rank := rat d.qX

def pY : Mx D ρ S.rank := rat d.qY

def p0 : Mx D S₀.rank S.rank := rat d.q0

theorem pX_eq : d.pX = adj d.jY ⬝ gA S := by rw [pX, qX, rat_mul, rat_conjTranspose]; rfl

theorem pY_eq : d.pY = adj d.jX ⬝ gA S := by rw [pY, qY, rat_mul, rat_conjTranspose]; rfl

theorem p0_eq : d.p0 = giA S₀ ⬝ (adj d.j0 ⬝ gA S) := by rw [p0, q0, rat_mul, rat_mul, rat_conjTranspose]; rfl

theorem gram_XX : adj d.jX ⬝ (gA S ⬝ d.jX) = 0 := (gram_rat S d.ee).trans rat_zero

theorem gram_YY : adj d.jY ⬝ (gA S ⬝ d.jY) = 0 := (gram_rat S d.e'e').trans rat_zero

theorem gram_YX : adj d.jY ⬝ (gA S ⬝ d.jX) = 1 := (gram_rat S d.e'e).trans rat_one

theorem gram_XY : adj d.jX ⬝ (gA S ⬝ d.jY) = 1 := (gram_swap S d.gram_YX).trans adj_one

theorem gram_00 : adj d.j0 ⬝ (gA S ⬝ d.j0) = gA S₀ := gram_rat S d.iso

theorem gram_0X : adj d.j0 ⬝ (gA S ⬝ d.jX) = 0 := (gram_rat S d.i₀e).trans rat_zero

theorem gram_0Y : adj d.j0 ⬝ (gA S ⬝ d.jY) = 0 := (gram_rat S d.i₀e').trans rat_zero

theorem wittDecomp_gram_X_anisotropic : adj d.jX ⬝ (gA S ⬝ d.j0) = 0 := (gram_swap S d.gram_0X).trans adj_zero

theorem gramR_Y0_eq_TI : adj d.jY ⬝ (gA S ⬝ d.j0) = 0 := (gram_swap S d.gram_0Y).trans adj_zero

@[simp] theorem pX_jX : d.pX ⬝ d.jX = 1 := by rw [pX_eq, Matrix.mul_assoc, gram_YX]

@[simp] theorem pX_j0 : d.pX ⬝ d.j0 = 0 := by rw [pX_eq, Matrix.mul_assoc, gramR_Y0_eq_TI]

@[simp] theorem pX_jY : d.pX ⬝ d.jY = 0 := by rw [pX_eq, Matrix.mul_assoc, gram_YY]

@[simp] theorem pY_jX : d.pY ⬝ d.jX = 0 := by rw [pY_eq, Matrix.mul_assoc, gram_XX]

@[simp] theorem pY_j0 : d.pY ⬝ d.j0 = 0 := by rw [pY_eq, Matrix.mul_assoc, wittDecomp_gram_X_anisotropic]

@[simp] theorem pY_jY : d.pY ⬝ d.jY = 1 := by rw [pY_eq, Matrix.mul_assoc, gram_XY]

@[simp] theorem p0_jX : d.p0 ⬝ d.jX = 0 := by
  rw [p0_eq, Matrix.mul_assoc, Matrix.mul_assoc, gram_0X, Matrix.mul_zero]

@[simp] theorem p0_j0 : d.p0 ⬝ d.j0 = 1 := by
  rw [p0_eq, Matrix.mul_assoc, Matrix.mul_assoc, gram_00, giA_mul_gA]

@[simp] theorem p0_jY : d.p0 ⬝ d.jY = 0 := by
  rw [p0_eq, Matrix.mul_assoc, Matrix.mul_assoc, gram_0Y, Matrix.mul_zero]

theorem sum_eq_one : d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY = 1 := by
  have h : fromRows (fromRows d.pX d.p0) d.pY * fromCols (fromCols d.jX d.j0) d.jY = 1 := by
    rw [fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols, pX_jX, pX_j0, pX_jY, pY_jX, pY_j0,
      pY_jY, p0_jX, p0_j0, p0_jY, fromBlocks_one, fromRows_zero, fromCols_zero, fromBlocks_one]
  rw [← fromCols_mul_fromRows, ← fromCols_mul_fromRows]
  exact (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [← d.rank_add]; ring)).1 h

theorem sum_eq_one_rat : d.e * d.qX + d.i₀ * d.q0 + d.e' * d.qY = 1 := by
  apply rat_injective
  rw [rat_add, rat_add, rat_mul, rat_mul, rat_mul, rat_one]
  exact d.sum_eq_one

theorem mat_ext {k : ℕ} {x y : Mx D k S.rank} (hX : x ⬝ d.jX = y ⬝ d.jX) (h0 : x ⬝ d.j0 = y ⬝ d.j0)
    (hY : x ⬝ d.jY = y ⬝ d.jY) : x = y := by
  rw [← Matrix.mul_one x, ← Matrix.mul_one y, ← d.sum_eq_one]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, hX, h0, hY]

theorem ga_ext {g h : GA D S} (hX : mt S g ⬝ d.jX = mt S h ⬝ d.jX) (h0 : mt S g ⬝ d.j0 = mt S h ⬝ d.j0)
    (hY : mt S g ⬝ d.jY = mt S h ⬝ d.jY) : g = h := mt_injective S (d.mat_ext hX h0 hY)

structure Images (S S₀ : HSp D) {ρ : ℕ} (E : Mx D S.rank ρ) (I : Mx D S.rank S₀.rank) (E' : Mx D S.rank ρ) : Prop where
  XX : adj E ⬝ (gA S ⬝ E) = 0
  YY : adj E' ⬝ (gA S ⬝ E') = 0
  YX : adj E' ⬝ (gA S ⬝ E) = 1
  OO : adj I ⬝ (gA S ⬝ I) = gA S₀
  OX : adj I ⬝ (gA S ⬝ E) = 0
  OY : adj I ⬝ (gA S ⬝ E') = 0

theorem images_self : Images S S₀ d.jX d.j0 d.jY :=
  ⟨d.gram_XX, d.gram_YY, d.gram_YX, d.gram_00, d.gram_0X, d.gram_0Y⟩

theorem gram_images {E : Mx D S.rank ρ} {I : Mx D S.rank S₀.rank} {E' : Mx D S.rank ρ} (h : Images S S₀ E I E') :
    adj (E ⬝ d.pX + I ⬝ d.p0 + E' ⬝ d.pY) ⬝ (gA S ⬝ (E ⬝ d.pX + I ⬝ d.p0 + E' ⬝ d.pY)) =
      adj d.pY ⬝ d.pX + adj d.p0 ⬝ (gA S₀ ⬝ d.p0) + adj d.pX ⬝ d.pY := by
  have h1 := gram_swap S h.YX
  have h2 := gram_swap S h.OX
  have h3 := gram_swap S h.OY
  simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, cancel₃ h.XX, cancel₃ h.YY,
    cancel₃ h.YX, cancel₃ h.OO, cancel₃ h.OX, cancel₃ h.OY, cancel₃ h1, cancel₃ h2, cancel₃ h3, adj_zero, adj_one,
    Matrix.zero_mul, Matrix.one_mul, Matrix.mul_zero, add_zero, zero_add]

theorem gA_eq : gA S = adj d.pY ⬝ d.pX + adj d.p0 ⬝ (gA S₀ ⬝ d.p0) + adj d.pX ⬝ d.pY := by
  rw [← d.gram_images d.images_self, sum_eq_one, adj_one, Matrix.one_mul, Matrix.mul_one]

theorem giA_eq : giA S = d.jX ⬝ adj d.jY + d.j0 ⬝ (giA S₀ ⬝ adj d.j0) + d.jY ⬝ adj d.jX := by
  rw [← Matrix.one_mul (giA S), ← d.sum_eq_one, pX_eq, pY_eq, p0_eq]
  simp only [Matrix.add_mul, Matrix.mul_assoc, gA_mul_giA, Matrix.mul_one]

def ofImages (E : Mx D S.rank ρ) (I : Mx D S.rank S₀.rank) (E' : Mx D S.rank ρ) (h : Images S S₀ E I E') : GA D S :=
  ofMat S (E ⬝ d.pX + I ⬝ d.p0 + E' ⬝ d.pY) ((d.gram_images h).trans d.gA_eq.symm)

section Images

variable {E : Mx D S.rank ρ} {I : Mx D S.rank S₀.rank} {E' : Mx D S.rank ρ} (h : Images S S₀ E I E')

theorem mt_ofImages : mt S (d.ofImages E I E' h) = E ⬝ d.pX + I ⬝ d.p0 + E' ⬝ d.pY := rfl

theorem ofImages_jX : mt S (d.ofImages E I E' h) ⬝ d.jX = E := by
  simp only [mt_ofImages, Matrix.add_mul, Matrix.mul_assoc, pX_jX, p0_jX, pY_jX, Matrix.mul_one, Matrix.mul_zero,
    add_zero]

theorem wittDecomp_ofImages_inclAnisotropic : mt S (d.ofImages E I E' h) ⬝ d.j0 = I := by
  simp only [mt_ofImages, Matrix.add_mul, Matrix.mul_assoc, pX_j0, p0_j0, pY_j0, Matrix.mul_one, Matrix.mul_zero,
    add_zero, zero_add]

theorem ofImages_jY : mt S (d.ofImages E I E' h) ⬝ d.jY = E' := by
  simp only [mt_ofImages, Matrix.add_mul, Matrix.mul_assoc, pX_jY, p0_jY, pY_jY, Matrix.mul_one, Matrix.mul_zero,
    add_zero, zero_add]

theorem ofImages_mem_GQ (h1 : E ∈ ratMx D _ _) (h2 : I ∈ ratMx D _ _) (h3 : E' ∈ ratMx D _ _) :
    d.ofImages E I E' h ∈ GQ S :=
  (mem_GQ_iff S _).2 (add_mem (add_mem (ratMx_mul h1 (rat_mem _)) (ratMx_mul h2 (rat_mem _))) (ratMx_mul h3 (rat_mem _)))

end Images

theorem images_levi (a : GL (Fin ρ) (AE D)) : Images S S₀ (d.jX ⬝ a.1) d.j0 (d.jY ⬝ adj (a⁻¹).1) where
  XX := by rw [adj_mul, Matrix.mul_assoc, cancel₃ d.gram_XX, Matrix.zero_mul, Matrix.mul_zero]
  YY := by rw [adj_mul, Matrix.mul_assoc, cancel₃ d.gram_YY, Matrix.zero_mul, Matrix.mul_zero]
  YX := by rw [adj_mul, Matrix.mul_assoc, cancel₃ d.gram_YX, Matrix.one_mul, adj_adj, Units.inv_mul]
  OO := d.gram_00
  OX := by rw [cancel₃ d.gram_0X, Matrix.zero_mul]
  OY := by rw [cancel₃ d.gram_0Y, Matrix.zero_mul]

def levi : GL (Fin ρ) (AE D) →* GA D S where
  toFun a := d.ofImages _ _ _ (d.images_levi a)
  map_one' := d.ga_ext (by rw [ofImages_jX, Units.val_one, Matrix.mul_one, mt_one, Matrix.one_mul])
    (by rw [wittDecomp_ofImages_inclAnisotropic, mt_one, Matrix.one_mul])
    (by rw [ofImages_jY, inv_one, Units.val_one, adj_one, Matrix.mul_one, mt_one, Matrix.one_mul])
  map_mul' a b := d.ga_ext
    (by rw [mt_mul, Matrix.mul_assoc, ofImages_jX, ofImages_jX, cancel₂ (d.ofImages_jX _), Units.val_mul,
      Matrix.mul_assoc])
    (by rw [mt_mul, Matrix.mul_assoc, wittDecomp_ofImages_inclAnisotropic, wittDecomp_ofImages_inclAnisotropic, wittDecomp_ofImages_inclAnisotropic])
    (by rw [mt_mul, Matrix.mul_assoc, ofImages_jY, ofImages_jY, cancel₂ (d.ofImages_jY _), _root_.mul_inv_rev,
      Units.val_mul, adj_mul, Matrix.mul_assoc])

section Levi

variable (a : GL (Fin ρ) (AE D))

theorem mt_levi : mt S (d.levi a) = d.jX ⬝ a.1 ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ adj (a⁻¹).1 ⬝ d.pY := rfl

theorem levi_jX : mt S (d.levi a) ⬝ d.jX = d.jX ⬝ a.1 := d.ofImages_jX (d.images_levi a)

theorem wittDecomp_levi_inclAnisotropic : mt S (d.levi a) ⬝ d.j0 = d.j0 := d.wittDecomp_ofImages_inclAnisotropic (d.images_levi a)

theorem levi_jY : mt S (d.levi a) ⬝ d.jY = d.jY ⬝ adj (a⁻¹).1 := d.ofImages_jY (d.images_levi a)

theorem pX_levi : d.pX ⬝ mt S (d.levi a) = a.1 ⬝ d.pX :=
  d.mat_ext (by simp only [levi_jX, cancel₂ d.pX_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]) (by simp only [wittDecomp_levi_inclAnisotropic,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])
    (by simp only [levi_jY, cancel₂ d.pX_jY,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])

theorem wittDecomp_projAnisotropic_levi : d.p0 ⬝ mt S (d.levi a) = d.p0 :=
  d.mat_ext (by simp only [levi_jX, cancel₂ d.p0_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]) (by simp only [wittDecomp_levi_inclAnisotropic,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])
    (by simp only [levi_jY, cancel₂ d.p0_jY,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])

theorem pY_levi : d.pY ⬝ mt S (d.levi a) = adj (a⁻¹).1 ⬝ d.pY :=
  d.mat_ext (by simp only [levi_jX, cancel₂ d.pY_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]) (by simp only [wittDecomp_levi_inclAnisotropic,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])
    (by simp only [levi_jY, cancel₂ d.pY_jY,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])

theorem levi_mem_GQ {a : GL (Fin ρ) (AE D)} (h : a.1 ∈ ratMx D ρ ρ) (h' : (a⁻¹).1 ∈ ratMx D ρ ρ) : d.levi a ∈ GQ S :=
  d.ofImages_mem_GQ (d.images_levi a) (ratMx_mul (rat_mem _) h) (rat_mem _) (ratMx_mul (rat_mem _) (ratMx_adj h'))

theorem continuous_levi : Continuous d.levi :=
  continuous_of_mt S ((((continuous_const.matrix_mul Units.continuous_val).matrix_mul continuous_const).add
    continuous_const).add ((continuous_const.matrix_mul (continuous_adj.comp Units.continuous_coe_inv)).matrix_mul
      continuous_const))

end Levi

theorem wittDecomp_frameImages_anisotropicEmbedding (g : GA D S₀) : Images S S₀ d.jX (d.j0 ⬝ mt S₀ g) d.jY where
  XX := d.gram_XX
  YY := d.gram_YY
  YX := d.gram_YX
  OO := by rw [adj_mul, Matrix.mul_assoc, cancel₃ d.gram_00, mt_unitary]
  OX := by rw [adj_mul, Matrix.mul_assoc, d.gram_0X, Matrix.mul_zero]
  OY := by rw [adj_mul, Matrix.mul_assoc, d.gram_0Y, Matrix.mul_zero]

def emb0 : GA D S₀ →* GA D S where
  toFun g := d.ofImages _ _ _ (d.wittDecomp_frameImages_anisotropicEmbedding g)
  map_one' := d.ga_ext (by rw [ofImages_jX, mt_one, Matrix.one_mul])
    (by rw [wittDecomp_ofImages_inclAnisotropic, mt_one, mt_one, Matrix.one_mul, Matrix.mul_one])
    (by rw [ofImages_jY, mt_one, Matrix.one_mul])
  map_mul' a b := d.ga_ext
    (by rw [mt_mul S, Matrix.mul_assoc, ofImages_jX, ofImages_jX, ofImages_jX])
    (by rw [mt_mul S, Matrix.mul_assoc, wittDecomp_ofImages_inclAnisotropic, wittDecomp_ofImages_inclAnisotropic, cancel₂ (d.wittDecomp_ofImages_inclAnisotropic _), mt_mul, Matrix.mul_assoc])
    (by rw [mt_mul S, Matrix.mul_assoc, ofImages_jY, ofImages_jY, ofImages_jY])

section Emb

variable (g : GA D S₀)

theorem unitaryMatrix_wittCoreEmbedding : mt S (d.emb0 g) = d.jX ⬝ d.pX + d.j0 ⬝ mt S₀ g ⬝ d.p0 + d.jY ⬝ d.pY := rfl

theorem wittDecomp_anisotropicEmbedding_inclX : mt S (d.emb0 g) ⬝ d.jX = d.jX := d.ofImages_jX (d.wittDecomp_frameImages_anisotropicEmbedding g)

theorem wittDecomp_anisotropicEmbedding_inclAnisotropic : mt S (d.emb0 g) ⬝ d.j0 = d.j0 ⬝ mt S₀ g := d.wittDecomp_ofImages_inclAnisotropic (d.wittDecomp_frameImages_anisotropicEmbedding g)

theorem wittDecomp_anisotropicEmbedding_inclY : mt S (d.emb0 g) ⬝ d.jY = d.jY := d.ofImages_jY (d.wittDecomp_frameImages_anisotropicEmbedding g)

theorem wittDecomp_projX_anisotropicEmbedding : d.pX ⬝ mt S (d.emb0 g) = d.pX :=
  d.mat_ext (by simp only [wittDecomp_anisotropicEmbedding_inclX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]) (by simp only [wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.pX_j0,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])
    (by simp only [wittDecomp_anisotropicEmbedding_inclY,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])

theorem wittDecomp_projAnisotropic_anisotropicEmbedding : d.p0 ⬝ mt S (d.emb0 g) = mt S₀ g ⬝ d.p0 :=
  d.mat_ext (by simp only [wittDecomp_anisotropicEmbedding_inclX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]) (by simp only [wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.p0_j0,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])
    (by simp only [wittDecomp_anisotropicEmbedding_inclY,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])

theorem wittDecomp_projY_anisotropicEmbedding : d.pY ⬝ mt S (d.emb0 g) = d.pY :=
  d.mat_ext (by simp only [wittDecomp_anisotropicEmbedding_inclX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]) (by simp only [wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.pY_j0,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])
    (by simp only [wittDecomp_anisotropicEmbedding_inclY,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])

theorem wittDecomp_anisotropicEmbedding_mem_rationalPoints {g : GA D S₀} (h : g ∈ GQ S₀) : d.emb0 g ∈ GQ S :=
  d.ofImages_mem_GQ (d.wittDecomp_frameImages_anisotropicEmbedding g) (rat_mem _) (ratMx_mul (rat_mem _) ((mem_GQ_iff S₀ g).1 h)) (rat_mem _)

theorem continuous_embed : Continuous d.emb0 :=
  continuous_of_mt S ((continuous_const.add ((continuous_const.matrix_mul (continuous_mt S₀)).matrix_mul
    continuous_const)).add continuous_const)

theorem wittDecomp_anisotropicEmbedding_injective : Function.Injective d.emb0 := fun g g' h => mt_injective S₀ (by
  have h1 : d.p0 ⬝ (mt S (d.emb0 g) ⬝ d.j0) = d.p0 ⬝ (mt S (d.emb0 g') ⬝ d.j0) := by rw [h]
  rwa [wittDecomp_anisotropicEmbedding_inclAnisotropic, wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.p0_j0, cancel₂ d.p0_j0, Matrix.one_mul, Matrix.one_mul] at h1)

theorem embRel_isometric_embedding (ι : S₀.V →ₗ[D.host.E] S.V) (hι : frameMat S S₀ ι = d.i₀) : EmbRel S S₀ ι (d.emb0 g) g := by
  rw [EmbRel, hι]
  refine ⟨d.wittDecomp_anisotropicEmbedding_inclAnisotropic g, fun x hx => ?_⟩
  have h1 : d.q0 *ᵥ x = 0 := by
    rw [q0, ← Matrix.mulVec_mulVec]
    exact (congrArg (S₀.gram⁻¹ *ᵥ ·) hx).trans (Matrix.mulVec_zero _)
  have h2 : d.p0 *ᵥ (fun i => incA D (x i)) = 0 := by
    funext i
    have := RingHom.map_mulVec (incA D) d.q0 x i
    rw [h1, Pi.zero_apply, map_zero] at this
    exact this.symm
  have h3 := congrArg (· *ᵥ fun i => incA D (x i)) d.sum_eq_one
  change mt S (d.emb0 g) *ᵥ _ = _
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero, Matrix.one_mulVec] at h3
  simp only [unitaryMatrix_wittCoreEmbedding, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero, h3]

end Emb

theorem images_nB (b : Mx D ρ S₀.rank) : Images S S₀ d.jX (d.j0 + d.jX ⬝ b)
    (d.jY - d.j0 ⬝ plus S₀ b - d.jX ⬝ (half D • (b ⬝ plus S₀ b))) := by
  refine ⟨d.gram_XX, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [adj_add, adj_sub, adj_mul d.jX, adj_mul d.j0, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc, d.gram_XX, d.gram_YY, d.gram_YX, d.gram_XY, d.gram_00, d.gram_0X, d.gram_0Y, d.wittDecomp_gram_X_anisotropic,
      d.gramR_Y0_eq_TI, cancel₃ d.gram_XX, cancel₃ d.gram_YX, cancel₃ d.gram_00, cancel₃ d.gram_0X, cancel₃ d.wittDecomp_gram_X_anisotropic,
      cancel₃ d.gramR_Y0_eq_TI, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, add_zero, sub_zero, zero_add,
      gA_plus]
  · rw [adj_smul, cA_half, adj_mul_plus, adj_plus, Matrix.mul_assoc]
    have := half_smul_add (b ⬝ plus S₀ b)
    rw [show giA S₀ ⬝ adj b = plus S₀ b from rfl]
    generalize half D • (b ⬝ plus S₀ b) = u at this ⊢
    rw [← this]
    abel
  · abel

def nB (b : Mx D ρ S₀.rank) : GA D S := d.ofImages _ _ _ (d.images_nB b)

theorem images_nC (c : skewA D ρ) : Images S S₀ d.jX d.j0 (d.jY + d.jX ⬝ c.1) := by
  refine ⟨d.gram_XX, ?_, ?_, d.gram_00, d.gram_0X, ?_⟩ <;>
    simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, d.gram_XX, d.gram_YY, d.gram_YX,
      d.gram_XY, d.gram_0Y, cancel₃ d.gram_XX, cancel₃ d.gram_YX, cancel₃ d.gram_0X, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, mem_skewA.1 c.2, neg_add_cancel]

def nC (c : skewA D ρ) : GA D S := d.ofImages _ _ _ (d.images_nC c)

section Unip

variable (b : Mx D ρ S₀.rank) (c : skewA D ρ)

theorem nB_jX : mt S (d.nB b) ⬝ d.jX = d.jX := d.ofImages_jX (d.images_nB b)

theorem nB_j0 : mt S (d.nB b) ⬝ d.j0 = d.j0 + d.jX ⬝ b := d.wittDecomp_ofImages_inclAnisotropic (d.images_nB b)

theorem nB_jY : mt S (d.nB b) ⬝ d.jY = d.jY - d.j0 ⬝ plus S₀ b - d.jX ⬝ (half D • (b ⬝ plus S₀ b)) :=
  d.ofImages_jY (d.images_nB b)

theorem nC_jX : mt S (d.nC c) ⬝ d.jX = d.jX := d.ofImages_jX (d.images_nC c)

theorem nC_j0 : mt S (d.nC c) ⬝ d.j0 = d.j0 := d.wittDecomp_ofImages_inclAnisotropic (d.images_nC c)

theorem nC_jY : mt S (d.nC c) ⬝ d.jY = d.jY + d.jX ⬝ c.1 := d.ofImages_jY (d.images_nC c)

theorem pX_nB : d.pX ⬝ mt S (d.nB b) = d.pX + b ⬝ d.p0 - (half D • (b ⬝ plus S₀ b)) ⬝ d.pY :=
  d.mat_ext (by simp only [nB_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])
    (by simp only [nB_j0, cancel₂ d.pX_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])
    (by simp only [nB_jY, cancel₂ d.pX_jX, cancel₂ d.pX_j0,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])

theorem wittDecomp_projAnisotropic_unipotentMixed : d.p0 ⬝ mt S (d.nB b) = d.p0 - plus S₀ b ⬝ d.pY :=
  d.mat_ext (by simp only [nB_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])
    (by simp only [nB_j0, cancel₂ d.p0_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])
    (by simp only [nB_jY, cancel₂ d.p0_jX, cancel₂ d.p0_j0,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])

theorem pY_nB : d.pY ⬝ mt S (d.nB b) = d.pY :=
  d.mat_ext (by simp only [nB_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]) (by simp only [nB_j0, cancel₂ d.pY_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])
    (by simp only [nB_jY, cancel₂ d.pY_jX, cancel₂ d.pY_j0,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])

theorem pX_nC : d.pX ⬝ mt S (d.nC c) = d.pX + c.1 ⬝ d.pY :=
  d.mat_ext (by simp only [nC_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]) (by simp only [nC_j0,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])
    (by simp only [nC_jY, cancel₂ d.pX_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])

theorem wittDecomp_projAnisotropic_unipotentSkew : d.p0 ⬝ mt S (d.nC c) = d.p0 :=
  d.mat_ext (by simp only [nC_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]) (by simp only [nC_j0,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])
    (by simp only [nC_jY, cancel₂ d.p0_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])

theorem pY_nC : d.pY ⬝ mt S (d.nC c) = d.pY :=
  d.mat_ext (by simp only [nC_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]) (by simp only [nC_j0,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])
    (by simp only [nC_jY, cancel₂ d.pY_jX,
      Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, pX_jX, pX_j0, pX_jY, p0_jX, p0_j0, p0_jY, pY_jX, pY_j0, pY_jY, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub])

end Unip

end HypDec

end GlobalTheory.MixModel

end
