import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Vf

open Matrix GlobalTheory.WeilM

variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype β] [DecidableEq β]

def Adj (J M M' : Matrix β β A) : Prop := Mᵀ * J = J * M'.map c

variable {c} {J : Matrix β β A}

theorem mapc_mul {ι κ μ : Type} [Fintype κ] (M : Matrix ι κ A) (N : Matrix κ μ A) : (M * N).map c = M.map c * N.map c :=
  Matrix.map_mul (f := (c : A →+* A))

theorem mapc_add {ι κ : Type} (M N : Matrix ι κ A) : (M + N).map c = M.map c + N.map c := Matrix.map_add _ (map_add c) _ _

theorem mapc_neg {ι κ : Type} (M : Matrix ι κ A) : (-M).map c = -M.map c := Matrix.map_neg _ (map_neg c) _

theorem mapc_sub {ι κ : Type} (M N : Matrix ι κ A) : (M - N).map c = M.map c - N.map c := by
  rw [sub_eq_add_neg, mapc_add, mapc_neg, ← sub_eq_add_neg]

theorem mapc_one {ι : Type} [DecidableEq ι] : (1 : Matrix ι ι A).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)

theorem mapc_zero {ι κ : Type} : (0 : Matrix ι κ A).map c = 0 := Matrix.map_zero _ (map_zero c)

theorem mapc_smul {ι κ : Type} (a : A) (M : Matrix ι κ A) : (a • M).map c = c a • M.map c := by
  ext i j; simp

theorem Adj.one : Adj c J 1 1 := by simp [Adj, mapc_one]

theorem Adj.add {M M' N N' : Matrix β β A} (h : Adj c J M M') (h' : Adj c J N N') : Adj c J (M + N) (M' + N') := by
  unfold Adj at *; rw [transpose_add, Matrix.add_mul, h, h', mapc_add, Matrix.mul_add]

theorem Adj.sub {M M' N N' : Matrix β β A} (h : Adj c J M M') (h' : Adj c J N N') : Adj c J (M - N) (M' - N') := by
  unfold Adj at *; rw [transpose_sub, Matrix.sub_mul, h, h', mapc_sub, Matrix.mul_sub]

theorem Adj.mul {M M' N N' : Matrix β β A} (h : Adj c J M M') (h' : Adj c J N N') : Adj c J (M * N) (N' * M') := by
  unfold Adj at *
  rw [transpose_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, h', mapc_mul, Matrix.mul_assoc]

theorem Adj.smul {M M' : Matrix β β A} (h : Adj c J M M') {a a' : A} (ha : c a' = a) : Adj c J (a • M) (a' • M') := by
  unfold Adj at *; rw [transpose_smul, Matrix.smul_mul, h, mapc_smul, ha, Matrix.mul_smul]

theorem Adj.pow {M : Matrix β β A} (h : Adj c J M M) (N : ℕ) : Adj c J (M ^ N) (M ^ N) := by
  induction N with
  | zero => simpa using Adj.one
  | succ N ih => have := ih.mul h; rwa [← pow_succ, ← pow_succ'] at this

theorem adj_unit (k : UG c J) : Adj c J (k.1 : Matrix β β A) (k⁻¹).1 := by
  have h : (k.1 : Matrix β β A)ᵀ * J * (k.1 : Matrix β β A).map c = J := k.2
  have h1 : (k.1 : Matrix β β A) * ((k⁻¹).1 : Matrix β β A) = 1 := k.1.mul_inv
  unfold Adj
  calc (k.1 : Matrix β β A)ᵀ * J = (k.1 : Matrix β β A)ᵀ * J * ((k.1 : Matrix β β A).map c * ((k⁻¹).1 : Matrix β β A).map c) := by
        rw [← mapc_mul, h1, mapc_one, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h]

theorem skew_alt {Ji k k' b b' f' : Matrix β β A} (hJ : J * Ji = 1) (hk : k * k' = 1) (a1 : Adj c J k k') (a2 : Adj c J k' k)
    (b1 : Adj c J b b') (b2 : Adj c J b' b) (hb : b + b' = -1) (hf : (1 + (1 - k) * b) * f' = 1) :
    (-(f' * (1 - k)))ᵀ * J + J * (-(f' * (1 - k))).map c = 0 := by
  set m := 1 - k with hm
  set m' := 1 - k' with hm'
  set T := -(f' * m) with hT
  have hJ' : Ji * J = 1 := mul_eq_one_comm.1 hJ
  have am : Adj c J m m' := Adj.one.sub a1
  have am' : Adj c J m' m := Adj.one.sub a2
  have af : Adj c J (1 + m * b) (1 + b' * m') := Adj.one.add (am.mul b1)
  have af' : Adj c J (1 + b' * m') (1 + m * b) := Adj.one.add (b2.mul am')
  set f := 1 + m * b with hfd
  set g := 1 + b' * m' with hg
  have hfT : f * T = -m := by rw [hT, Matrix.mul_neg, ← Matrix.mul_assoc, hf, Matrix.one_mul]
  have z : f * m' + m * g = 0 := by
    have e : m * m' = m + m' := by
      rw [hm, hm', Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hk]; simp; abel
    have : f * m' + m * g = m' + m + m * (b + b') * m' := by rw [hfd, hg]; noncomm_ring
    rw [this, hb, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, e]; abel
  have e1 : Tᵀ * J * g.map c = -(J * m'.map c) := by
    rw [Matrix.mul_assoc, ← af, ← Matrix.mul_assoc, ← transpose_mul, hfT, transpose_neg, Matrix.neg_mul, am]
  have e2 : gᵀ * J * T.map c = -(J * m.map c) := by
    rw [af', Matrix.mul_assoc, ← mapc_mul, hfT, mapc_neg, Matrix.mul_neg]
  have e3 : gᵀ * (Tᵀ * J + J * T.map c) * g.map c = 0 := by
    have : gᵀ * (Tᵀ * J + J * T.map c) * g.map c = gᵀ * (Tᵀ * J * g.map c) + gᵀ * J * T.map c * g.map c := by noncomm_ring
    rw [this, e1, e2, Matrix.mul_neg, ← Matrix.mul_assoc, af', Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← mapc_mul,
      ← mapc_mul, ← neg_add, ← Matrix.mul_add, ← mapc_add, z, mapc_zero, Matrix.mul_zero, neg_zero]
  have hf' : f' * f = 1 := mul_eq_one_comm.1 hf
  have l : J * f'.map c * Ji * gᵀ = 1 := by
    have : gᵀ = J * f.map c * Ji := by rw [← af', Matrix.mul_assoc, hJ, Matrix.mul_one]
    rw [this]
    calc J * f'.map c * Ji * (J * f.map c * Ji) = J * (f'.map c * (Ji * J) * f.map c) * Ji := by noncomm_ring
      _ = 1 := by rw [hJ', Matrix.mul_one, ← mapc_mul, hf', mapc_one, Matrix.mul_one, hJ]
  have r : g.map c * (Ji * f'ᵀ * J) = 1 := by
    have : g.map c = Ji * (fᵀ * J) := by rw [af, ← Matrix.mul_assoc, hJ', Matrix.one_mul]
    rw [this]
    calc Ji * (fᵀ * J) * (Ji * f'ᵀ * J) = Ji * (fᵀ * (J * Ji) * f'ᵀ) * J := by noncomm_ring
      _ = 1 := by rw [hJ, Matrix.mul_one, ← transpose_mul, hf', transpose_one, Matrix.mul_one, hJ']
  calc Tᵀ * J + J * T.map c = (J * f'.map c * Ji * gᵀ) * (Tᵀ * J + J * T.map c) * (g.map c * (Ji * f'ᵀ * J)) := by
        rw [l, r, Matrix.one_mul, Matrix.mul_one]
    _ = J * f'.map c * Ji * (gᵀ * (Tᵀ * J + J * T.map c) * g.map c) * (Ji * f'ᵀ * J) := by noncomm_ring
    _ = 0 := by rw [e3, Matrix.mul_zero, Matrix.zero_mul]

def CC (b : Matrix β β A) : Matrix (β ⊕ β) (β ⊕ β) A := fromBlocks 1 (1 + b) 1 b

def Ci (b : Matrix β β A) : Matrix (β ⊕ β) (β ⊕ β) A := fromBlocks (-b) (1 + b) 1 (-1)

theorem Ci_CC (b : Matrix β β A) : Ci b * CC b = 1 := by
  rw [Ci, CC, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> noncomm_ring

theorem CC_Ci (b : Matrix β β A) : CC b * Ci b = 1 := mul_eq_one_comm.1 (Ci_CC b)

theorem gram_CC {b b' : Matrix β β A} (b1 : Adj c J b b') (hb : b + b' = -1) :
    (CC b)ᵀ * dbl J * (CC b).map c = fromBlocks 0 J J 0 := by
  have e : b'.map c = -1 - b.map c := by
    rw [← mapc_one (c := c), ← mapc_neg, ← mapc_sub, ← hb]; congr 1; abel
  have b1' : bᵀ * J = -J - J * b.map c := by rw [b1, e]; noncomm_ring
  rw [CC, dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, mapc_add, mapc_one, transpose_add,
    transpose_one]
  congr 1
  · noncomm_ring
  · noncomm_ring
  · noncomm_ring
  · have : ((1 + bᵀ) * J + bᵀ * 0) * (1 + b.map c) + ((1 + bᵀ) * 0 + bᵀ * -J) * b.map c = J + J * b.map c + bᵀ * J := by
      noncomm_ring
    rw [this, b1']; abel

def mkU {b b' : Matrix β β A} (b1 : Adj c J b b') (hb : b + b' = -1) (g g' : Matrix (β ⊕ β) (β ⊕ β) A) (h : g * g' = 1)
    (hg : gᵀ * fromBlocks 0 J J 0 * g.map c = fromBlocks 0 J J 0) : UG c (dbl J) :=
  have e : CC b * g * Ci b * (CC b * g' * Ci b) = 1 := by
    calc CC b * g * Ci b * (CC b * g' * Ci b) = CC b * (g * (Ci b * CC b) * g') * Ci b := by noncomm_ring
      _ = 1 := by rw [Ci_CC, Matrix.mul_one, h, Matrix.mul_one, CC_Ci]
  ⟨⟨CC b * g * Ci b, CC b * g' * Ci b, e, mul_eq_one_comm.1 e⟩, by
    change (CC b * g * Ci b)ᵀ * dbl J * (CC b * g * Ci b).map c = dbl J
    have e2 : (Ci b)ᵀ * fromBlocks 0 J J 0 * (Ci b).map c = dbl J := by
      rw [← gram_CC b1 hb]
      calc (Ci b)ᵀ * ((CC b)ᵀ * dbl J * (CC b).map c) * (Ci b).map c
          = ((Ci b)ᵀ * (CC b)ᵀ) * dbl J * ((CC b).map c * (Ci b).map c) := by noncomm_ring
        _ = dbl J := by rw [← transpose_mul, ← mapc_mul, CC_Ci, transpose_one, mapc_one, Matrix.one_mul, Matrix.mul_one]
    rw [mapc_mul, mapc_mul, transpose_mul, transpose_mul]
    calc (Ci b)ᵀ * (gᵀ * (CC b)ᵀ) * dbl J * ((CC b).map c * g.map c * (Ci b).map c)
        = (Ci b)ᵀ * (gᵀ * ((CC b)ᵀ * dbl J * (CC b).map c) * g.map c) * (Ci b).map c := by noncomm_ring
      _ = dbl J := by rw [gram_CC b1 hb, hg, e2]⟩

def SS (ε : A) : Matrix (β ⊕ β) (β ⊕ β) A := fromBlocks ((1 - ε) • 1) (ε • 1) (ε • 1) ((1 - ε) • 1)

theorem exists_decomp {Ji b b' f' : Matrix β β A} (hJ : J * Ji = 1) (k : UG c J) (b1 : Adj c J b b') (b2 : Adj c J b' b)
    (hb : b + b' = -1) (hf : (1 + (1 - (k.1 : Matrix β β A)) * b) * f' = 1) {ε : A} (he : ε * ε = ε) (hc : c ε = ε)
    (hm : ε • (1 - (k.1 : Matrix β β A)) = 1 - (k.1 : Matrix β β A)) (gd : UG c (dbl J))
    (hgd : (gd.1 : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks k.1 0 0 1) :
    ∃ (s n p : UG c (dbl J)) (t : GL β A), s * s = 1 ∧ gd = s * n * s * p ∧
      (s.1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * SS ε * Ci b ∧
      (n.1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * fromBlocks 1 (-(f' * (1 - (k.1 : Matrix β β A)))) 0 1 * Ci b ∧
      ((n⁻¹).1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * fromBlocks 1 (f' * (1 - (k.1 : Matrix β β A))) 0 1 * Ci b ∧
      (n.1 : Matrix (β ⊕ β) (β ⊕ β) A) * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * ((1 : GL β A) : Matrix β β A) ∧
      (p.1 : Matrix (β ⊕ β) (β ⊕ β) A) * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * (t : Matrix β β A) ∧
      (t : Matrix β β A) = 1 + b * (1 - (k.1 : Matrix β β A)) ∧ ((t⁻¹ : GL β A) : Matrix β β A) = 1 - b * (f' * (1 - (k.1 : Matrix β β A))) := by
  have hk : (k.1 : Matrix β β A) * ((k⁻¹).1 : Matrix β β A) = 1 := k.1.mul_inv
  have sk := skew_alt hJ hk (adj_unit k) (by simpa using adj_unit k⁻¹) b1 b2 hb hf
  set m : Matrix β β A := 1 - k.1 with hmd
  set T := -(f' * m) with hT
  have e0 : ε * (1 - ε) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have e0' : (1 - ε) * ε = 0 := by rw [mul_comm, e0]
  have e1 : (1 - ε) * (1 - ε) = 1 - ε := by rw [sub_mul, one_mul, e0, sub_zero]
  have hS : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A) * SS ε = 1 := by
    rw [SS, fromBlocks_multiply, ← fromBlocks_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, e0, e0', e1, he, ← add_smul]
    simp
  have hSu : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * fromBlocks 0 J J 0 * (SS ε : Matrix (β ⊕ β) (β ⊕ β) A).map c =
      fromBlocks 0 J J 0 := by
    rw [SS, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp only [mapc_smul, mapc_one, map_sub, map_one, hc, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, smul_zero, zero_add, add_zero, smul_smul, e0, e0', e1, he, ← add_smul]
    simp
  have hU : (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks 1 (f' * m) 0 1 = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one, hT]; simp
  have hUu : (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * fromBlocks 0 J J 0 *
      (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A).map c = fromBlocks 0 J J 0 := by
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, mapc_one, mapc_zero]
    simp only [transpose_one, transpose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
    rw [add_comm (J * _), sk]
  have hf' : f' * (1 + m * b) = 1 := mul_eq_one_comm.1 hf
  have hTt : T * (1 + b * m) = -m := by
    have : T * (1 + b * m) = -(f' * (1 + m * b) * m) := by rw [hT]; noncomm_ring
    rw [this, hf', Matrix.one_mul]
  have ht : (1 - b * (f' * m)) * (1 + b * m) = 1 := by
    have : (1 - b * (f' * m)) * (1 + b * m) = 1 + b * m + b * (T * (1 + b * m)) := by rw [hT]; noncomm_ring
    rw [this, hTt]; noncomm_ring
  let s := mkU b1 hb _ _ hS hSu
  let n := mkU b1 hb _ _ hU hUu
  have hs : (s.1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * SS ε * Ci b := rfl
  have hn : (n.1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * fromBlocks 1 T 0 1 * Ci b := rfl
  have hεT : ε • T = T := by rw [hT, smul_neg, ← Matrix.mul_smul, hm]
  have hεT' : (1 - ε) • T = 0 := by rw [sub_smul, one_smul, hεT, sub_self]
  have hL : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks 1 T 0 1 * SS ε = fromBlocks 1 0 T 1 := by
    rw [SS, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, smul_zero, add_zero, hεT, hεT',
      zero_add, Matrix.add_mul, smul_add, smul_smul, e0, e0', e1, he, zero_smul, ← add_smul]
    simp
  have hD : Ci b * (diagCols β : Matrix (β ⊕ β) β A) = (fromRows 1 0 : Matrix (β ⊕ β) β A) := by
    rw [Ci, diagCols, fromBlocks_mul_fromRows]; simp
  have hD' : CC b * (fromRows 1 0 : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) := by
    rw [CC, diagCols, fromBlocks_mul_fromRows]; simp
  refine ⟨s, n, (s * n * s)⁻¹ * gd, ⟨1 + b * m, 1 - b * (f' * m), mul_eq_one_comm.1 ht, ht⟩, ?_, by group, hs, hn, rfl, ?_, ?_,
    rfl, rfl⟩
  · refine Subtype.ext (Units.ext ?_)
    exact s.1.mul_inv
  · rw [hn, Matrix.mul_assoc _ (Ci b), hD, Matrix.mul_assoc (CC b), fromBlocks_mul_fromRows]
    simpa using hD'
  · have e : ((s * n * s).1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * fromBlocks 1 0 T 1 * Ci b := by
      change (s.1 : Matrix (β ⊕ β) (β ⊕ β) A) * (n.1 : Matrix (β ⊕ β) (β ⊕ β) A) * (s.1 : Matrix (β ⊕ β) (β ⊕ β) A) = _
      rw [hs, hn, ← hL]
      calc CC b * SS ε * Ci b * (CC b * fromBlocks 1 T 0 1 * Ci b) * (CC b * SS ε * Ci b)
          = CC b * (SS ε * (Ci b * CC b) * fromBlocks 1 T 0 1 * (Ci b * CC b) * SS ε) * Ci b := by noncomm_ring
        _ = _ := by rw [Ci_CC, Matrix.mul_one, Matrix.mul_one]
    have e2 : (gd.1 : Matrix (β ⊕ β) (β ⊕ β) A) * (diagCols β : Matrix (β ⊕ β) β A) = ((s * n * s).1 : Matrix (β ⊕ β) (β ⊕ β) A) * ((diagCols β : Matrix (β ⊕ β) β A) * (1 + b * m)) := by
      rw [e, hgd, ← Matrix.mul_assoc _ (diagCols β : Matrix (β ⊕ β) β A), Matrix.mul_assoc _ (Ci b), hD, Matrix.mul_assoc (CC b), fromBlocks_mul_fromRows, CC,
        fromBlocks_mul_fromRows, fromRows_mul, diagCols, fromBlocks_mul_fromRows]
      congr 1
      · have : (1 * (1 * 1 + 0 * 0) + (1 + b) * (T * 1 + 1 * 0)) * (1 + b * m) = 1 + b * m + (1 + b) * (T * (1 + b * m)) := by
          noncomm_ring
        rw [this, hTt, hmd]; noncomm_ring
      · have : (1 * (1 * 1 + 0 * 0) + b * (T * 1 + 1 * 0)) * (1 + b * m) = 1 + b * m + b * (T * (1 + b * m)) := by
          noncomm_ring
        rw [this, hTt]; noncomm_ring
    change (((s * n * s)⁻¹).1 : Matrix (β ⊕ β) (β ⊕ β) A) * (gd.1 : Matrix (β ⊕ β) (β ⊕ β) A) * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * (1 + b * m)
    rw [Matrix.mul_assoc _ (gd.1 : Matrix (β ⊕ β) (β ⊕ β) A), e2, ← Matrix.mul_assoc]
    have : (((s * n * s)⁻¹).1 : Matrix (β ⊕ β) (β ⊕ β) A) * ((s * n * s).1 : Matrix (β ⊕ β) (β ⊕ β) A) = 1 := (s * n * s).1.inv_mul
    rw [this, Matrix.one_mul]

theorem exists_pow_idem {M : Type} [Monoid M] [Finite M] (x : M) : ∃ N, 0 < N ∧ x ^ N * x ^ N = x ^ N := by
  obtain ⟨a, b, hab, e⟩ : ∃ a b : ℕ, a < b ∧ x ^ a = x ^ b := by
    obtain ⟨a, b, hne, e⟩ := Finite.exists_ne_map_eq_of_infinite fun i : ℕ => x ^ i
    rcases lt_or_gt_of_ne hne with h | h
    exacts [⟨a, b, h, e⟩, ⟨b, a, h, e.symm⟩]
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_lt hab
  have h1 : ∀ j, x ^ (a + j * (p + 1)) = x ^ a := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show a + (j + 1) * (p + 1) = (a + p + 1) + j * (p + 1) by ring, pow_add, ← e, ← pow_add, ih]
  refine ⟨(a + 1) * (p + 1), by positivity, ?_⟩
  obtain ⟨r, hr⟩ : ∃ r, (a + 1) * (p + 1) = a + r := Nat.exists_eq_add_of_le (by nlinarith)
  rw [← pow_add, show (a + 1) * (p + 1) + (a + 1) * (p + 1) = (a + (a + 1) * (p + 1)) + r by omega, pow_add, h1, ← pow_add, hr]

theorem exists_det_ne {K : Type} [Field K] [Finite K] {k k' : Matrix β β K} (hk : k' * k = 1) {h δ : K} (hh : h + h = 1)
    (hδ : δ ≠ 0) : ∃ N, (1 + (1 - k) * ((-h) • 1 + δ • (1 - (1 + 1 + k + k') ^ N))).det ≠ 0 := by
  obtain ⟨N, hN, he⟩ := exists_pow_idem (1 + 1 + k + k')
  refine ⟨N, fun h0 => ?_⟩
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hk' : k * k' = 1 := mul_eq_one_comm.1 hk
  set x := 1 + 1 + k + k' with hx
  set u := 1 + k with hu
  have hxu : x = k' * (u * u) := by
    have : k' * (u * u) = k' + (k' * k) + (k' * k) + (k' * k) * k := by rw [hu]; noncomm_ring
    rw [this, hk, hx]; noncomm_ring
  have ck : Commute k x := by
    rw [hx]
    exact (((Commute.one_right k).add_right (Commute.one_right k)).add_right (Commute.refl k)).add_right (hk'.trans hk.symm)
  have cu : Commute u x := (Commute.one_left x).add_left ck
  set e := x ^ N with hed
  have ce : Commute k e := ck.pow_right N
  have h2 : (2 : K) * h = 1 := by rw [two_mul, hh]
  have hh0 : h ≠ 0 := fun h0 => by simp [h0] at hh
  have f1 : e * (1 + (1 - k) * ((-h) • 1 + δ • (1 - e))) = h • (u * e) := by
    have a1 : e * ((1 - k) * (1 - e)) = 0 := by
      rw [← Matrix.mul_assoc, ← ((Commute.one_left e).sub_left ce).eq, Matrix.mul_assoc, Matrix.mul_sub, he]; simp
    have a2 : e * (1 - k) = e - k * e := by rw [Matrix.mul_sub, ce.eq, Matrix.mul_one]
    rw [Matrix.mul_add (1 - k), Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, a1,
      Matrix.mul_one, Matrix.mul_one, a2, hu, Matrix.add_mul, Matrix.one_mul]
    have : e = (h + h) • e := by rw [hh, one_smul]
    conv_lhs => rw [smul_zero, add_zero]; enter [1]; rw [this]
    module
  have y1 : (u * e) *ᵥ y = 0 := by
    have := congrArg (e *ᵥ ·) hy
    simp only [Matrix.mulVec_mulVec, f1, Matrix.mulVec_zero, Matrix.smul_mulVec] at this
    exact (smul_eq_zero.1 this).resolve_left hh0
  have y2 : e *ᵥ y = 0 := by
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have : e = x ^ N' * k' * u * (u * e) := by
      conv_lhs => rw [← he]
      rw [hed, pow_succ x N', hxu]; noncomm_ring
    rw [this, ← Matrix.mulVec_mulVec, y1, Matrix.mulVec_zero]
  have y3 : y = ((δ - h) / (2 * δ)) • (u *ᵥ y) := by
    have h20 : (2 : K) ≠ 0 := fun h0 => by simp [h0] at h2
    have a : (1 + (1 - k) * ((-h) • 1 + δ • (1 - e))) = (2 * δ) • 1 - (δ - h) • u - δ • ((1 - k) * e) := by
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, hu]
      have : (1 : Matrix β β K) = (h + h) • 1 := by rw [hh, one_smul]
      conv_lhs => enter [1]; rw [this]
      module
    rw [a, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec, y2, Matrix.mulVec_zero, smul_zero, sub_zero, Matrix.one_mulVec, sub_eq_zero] at hy
    rw [div_eq_inv_mul, mul_smul, ← hy, smul_smul, inv_mul_cancel₀ (mul_ne_zero h20 hδ), one_smul]
  have y4 : ∀ j : ℕ, y = ((δ - h) / (2 * δ)) ^ j • (u ^ j *ᵥ y) := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ u, ← Matrix.mulVec_mulVec, pow_succ, mul_smul, ← Matrix.mulVec_smul, ← y3]; exact ih
  have hux : u * u = k * x := by rw [hxu, ← Matrix.mul_assoc, hk', Matrix.one_mul]
  have : u ^ (2 * N) = k ^ N * e := by rw [pow_mul, pow_two, hux, ck.mul_pow]
  apply hy0
  rw [y4 (2 * N), this, ← Matrix.mulVec_mulVec, y2, Matrix.mulVec_zero, smul_zero]

end PositivityTheory.ThKG.Loc.Cone.Vf

end
