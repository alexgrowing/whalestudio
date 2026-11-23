import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7}

theorem mulVec_colMul {m n k : ℕ} (M : Mx D m n) (X : Mx D n k) (i : Fin k) (a : AE D) :
    M *ᵥ colMul X i a = fun r => a * (M ⬝ X) r i := by
  funext r
  simp only [colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem adj_diagonal {n : ℕ} (f : Fin n → AE D) :
    adj (Matrix.diagonal f) = Matrix.diagonal (fun i => cA D (f i)) := by
  ext i j; simp [adj, Matrix.diagonal_apply]; split_ifs <;> simp_all [eq_comm]

theorem mul_tail {a m n k : ℕ} {A : Mx D a m} {B : Mx D m n} {C : Mx D a n} (h : A ⬝ B = C) (X : Mx D n k) :
    A ⬝ (B ⬝ X) = C ⬝ X := by
  rw [← Matrix.mul_assoc, h]

theorem mul_tail₃ {a m n p k : ℕ} {A : Mx D a m} {B : Mx D m n} {B' : Mx D n p} {C : Mx D a p}
    (h : A ⬝ (B ⬝ B') = C) (X : Mx D p k) :
    A ⬝ (B ⬝ (B' ⬝ X)) = C ⬝ X := by
  rw [← h]; simp only [Matrix.mul_assoc]

theorem mul_tail₄ {a m n p q k : ℕ} {A : Mx D a m} {B : Mx D m n} {B' : Mx D n p} {B'' : Mx D p q} {C : Mx D a q}
    (h : A ⬝ (B ⬝ (B' ⬝ B'')) = C) (X : Mx D q k) :
    A ⬝ (B ⬝ (B' ⬝ (B'' ⬝ X))) = C ⬝ X := by
  rw [← h]; simp only [Matrix.mul_assoc]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem gXX {k : ℕ} (X : Mx D ρ k) : adj d.jX ⬝ (gA S ⬝ (d.jX ⬝ X)) = 0 := by
  rw [mul_tail₃ d.gram_XX, Matrix.zero_mul]
theorem gYY {k : ℕ} (X : Mx D ρ k) : adj d.jY ⬝ (gA S ⬝ (d.jY ⬝ X)) = 0 := by
  rw [mul_tail₃ d.gram_YY, Matrix.zero_mul]
theorem gYX {k : ℕ} (X : Mx D ρ k) : adj d.jY ⬝ (gA S ⬝ (d.jX ⬝ X)) = X := by
  rw [mul_tail₃ d.gram_YX, Matrix.one_mul]
theorem gXY {k : ℕ} (X : Mx D ρ k) : adj d.jX ⬝ (gA S ⬝ (d.jY ⬝ X)) = X := by
  rw [mul_tail₃ d.gram_XY, Matrix.one_mul]
theorem g0X {k : ℕ} (X : Mx D ρ k) : adj d.j0 ⬝ (gA S ⬝ (d.jX ⬝ X)) = 0 := by
  rw [mul_tail₃ d.gram_0X, Matrix.zero_mul]
theorem g0Y {k : ℕ} (X : Mx D ρ k) : adj d.j0 ⬝ (gA S ⬝ (d.jY ⬝ X)) = 0 := by
  rw [mul_tail₃ d.gram_0Y, Matrix.zero_mul]
theorem adjoint_jX_gram_j_zero_eq_zero {k : ℕ} (X : Mx D S₀.rank k) : adj d.jX ⬝ (gA S ⬝ (d.j0 ⬝ X)) = 0 := by
  rw [mul_tail₃ d.wittDecomp_gram_X_anisotropic, Matrix.zero_mul]
theorem g00 {k : ℕ} (X : Mx D S₀.rank k) : adj d.j0 ⬝ (gA S ⬝ (d.j0 ⬝ X)) = gA S₀ ⬝ X :=
  mul_tail₃ d.gram_00 X

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem smul_eq_of_mem {P : Pl D → Prop} {ε : AE D} (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a)
    {m n : ℕ} {x : Mx D m n} (hx : ∀ i j, x i j ∈ idAt D P) : ε • x = x := by
  ext i j; rw [Matrix.smul_apply, smul_eq_mul, (hε _).1 (hx i j)]

theorem one_sub_mul_self {ε : AE D} (hεε : ε * ε = ε) : (1 - ε) * ε = 0 := by
  rw [sub_mul, one_mul, hεε, sub_self]

theorem one_sub_sq {ε : AE D} (hεε : ε * ε = ε) : (1 - ε) * (1 - ε) = 1 - ε := by
  rw [mul_sub, mul_one, one_sub_mul_self hεε, sub_zero]

theorem kill_left {ε : AE D} (hεε : ε * ε = ε) {m n k : ℕ} {x : Mx D m n} (hx : ε • x = x) (X : Mx D n k) :
    (1 - ε) • (x ⬝ X) = 0 := by
  rw [← Matrix.smul_mul, ← hx, smul_smul, one_sub_mul_self hεε, zero_smul, Matrix.zero_mul]

theorem kill_right {ε : AE D} (hεε : ε * ε = ε) {m n k : ℕ} {x : Mx D n k} (hx : ε • x = x) (X : Mx D m n) :
    (1 - ε) • (X ⬝ x) = 0 := by
  rw [← Matrix.mul_smul, ← hx, smul_smul, one_sub_mul_self hεε, zero_smul, Matrix.mul_zero]

theorem diag_absorb {ε : AE D} {n : ℕ} {α : Fin n → AE D} (hαε : ∀ i, ε * α i = α i) :
    ε • Matrix.diagonal α = Matrix.diagonal α := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with h
  · exact hαε i
  · rw [mul_zero]

theorem diag_const {ε : AE D} {n : ℕ} {α β : Fin n → AE D} (hαβ : ∀ i, α i * β i = ε) :
    (Matrix.diagonal fun i => α i * β i) = ε • (1 : Mx D n n) := by
  have : (fun i => α i * β i) = fun _ => ε := funext hαβ
  rw [this]
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

set_option maxHeartbeats 1000000 in
theorem imYX {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) {α β : Fin ρ → AE D} (hαε : ∀ i, ε * α i = α i)
    (hαβ : ∀ i, α i * β i = ε) {b : Mx D ρ ρ} (hb : ε • b = b) {c' : Mx D S.rank ρ} (hc : ε • c' = c')
    (H1 : adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ)) :
    adj (c' ⬝ Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY) ⬝
      (gA S ⬝ (d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))) = 1 := by
  have hcA1 : cA D (1 - ε) = 1 - ε := by rw [map_sub, map_one, hεc]
  have hadjc : ε • adj c' = adj c' := by
    conv_rhs => rw [← hc]
    rw [adj_smul, hεc]
  simp only [adj_add, adj_mul, adj_smul, adj_diagonal, cA_cA, hcA1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  simp only [mul_tail₄ H1, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, gYX d, d.gram_YX, kill_left hεε (diag_absorb hαε), kill_left hεε hb, add_zero, smul_smul]
  rw [zero_add, Matrix.diagonal_mul_diagonal, one_sub_sq hεε]
  rw [diag_const hαβ, smul_smul, hεε, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem kill_mid₂ {ε : AE D} (hεε : ε * ε = ε) {m n p q k : ℕ} {x : Mx D p q} (hx : ε • x = x)
    (A : Mx D m n) (B : Mx D n p) (X : Mx D q k) : (1 - ε) • (A ⬝ (B ⬝ (x ⬝ X))) = 0 := by
  rw [← Matrix.mul_smul, ← Matrix.mul_smul, kill_left hεε hx, Matrix.mul_zero, Matrix.mul_zero]

theorem absorb_mul {ε : AE D} {m n k : ℕ} {x : Mx D m n} (hx : ε • x = x) (X : Mx D n k) :
    x ⬝ (ε • X) = x ⬝ X := by
  rw [Matrix.mul_smul, ← Matrix.smul_mul, hx]

theorem imXX {ε : AE D} {β : Fin ρ → AE D} {b : Mx D ρ ρ} :
    adj (d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ))) ⬝
      (gA S ⬝ (d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))) = 0 := by
  rw [adj_mul, Matrix.mul_assoc, gXX, Matrix.mul_zero]

set_option maxHeartbeats 1000000 in
theorem imYY {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) {α : Fin ρ → AE D} (hαε : ∀ i, ε * α i = α i)
    {c' : Mx D S.rank ρ} (hc : ε • c' = c') (H2 : adj c' ⬝ (gA S ⬝ c') = 0) :
    adj (c' ⬝ Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY) ⬝
      (gA S ⬝ (c' ⬝ Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY)) = 0 := by
  have hcA1 : cA D (1 - ε) = 1 - ε := by rw [map_sub, map_one, hεc]
  have hadjc : ε • adj c' = adj c' := by
    conv_rhs => rw [← hc]
    rw [adj_smul, hεc]
  simp only [adj_add, adj_mul, adj_smul, adj_diagonal, cA_cA, hcA1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  simp only [mul_tail₃ H2, Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul, smul_smul, d.gram_YY, smul_zero,
    kill_mid₂ hεε hc, kill_left hεε (diag_absorb hαε), add_zero, Matrix.zero_mul]

set_option maxHeartbeats 1000000 in
theorem imOO {b : Mx D ρ ρ} {c' : Mx D S.rank ρ} :
    adj (d.j0 - (d.jX ⬝ b) ⬝ (adj c' ⬝ (gA S ⬝ d.j0))) ⬝ (gA S ⬝ (d.j0 - (d.jX ⬝ b) ⬝ (adj c' ⬝ (gA S ⬝ d.j0)))) = gA S₀ := by
  simp only [adj_sub, adj_mul, adj_gA, adj_adj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, d.gram_00, d.wittDecomp_gram_X_anisotropic,
    gXX, g0X, Matrix.mul_zero, sub_zero]

set_option maxHeartbeats 1000000 in
theorem imOX {ε : AE D} {β : Fin ρ → AE D} {b : Mx D ρ ρ} {c' : Mx D S.rank ρ} :
    adj (d.j0 - (d.jX ⬝ b) ⬝ (adj c' ⬝ (gA S ⬝ d.j0))) ⬝ (gA S ⬝ (d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))) = 0 := by
  simp only [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, gXX, g0X, Matrix.mul_zero, sub_zero]

set_option maxHeartbeats 1000000 in
theorem imOY {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) {α : Fin ρ → AE D} {b : Mx D ρ ρ} (hb : ε • b = b)
    {c' : Mx D S.rank ρ} (hc : ε • c' = c')
    (H1 : adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ)) :
    adj (d.j0 - (d.jX ⬝ b) ⬝ (adj c' ⬝ (gA S ⬝ d.j0))) ⬝ (gA S ⬝ (c' ⬝ Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY)) = 0 := by
  have adjH1 : adj b ⬝ (adj d.jX ⬝ (gA S ⬝ c')) = ε • (1 : Mx D ρ ρ) := by
    have := congrArg adj H1
    simpa only [adj_mul, adj_gA, adj_adj, adj_smul, adj_one, hεc, Matrix.mul_assoc] using this
  simp only [adj_sub, adj_mul, adj_gA, adj_adj, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_assoc]
  rw [mul_tail₄ adjH1, Matrix.smul_mul, Matrix.one_mul, absorb_mul hc, sub_self, zero_add]
  simp only [Matrix.mul_smul, d.gram_0Y, d.gram_XY, Matrix.mul_one, smul_zero, kill_mid₂ hεε hc, sub_zero]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

set_option maxHeartbeats 1000000 in

theorem smul_sub_one {ε : AE D} (M : Mx D S.rank S.rank)
    (hX : ε • (M ⬝ d.jX - d.jX) = M ⬝ d.jX - d.jX) (h0 : ε • (M ⬝ d.j0 - d.j0) = M ⬝ d.j0 - d.j0)
    (hY : ε • (M ⬝ d.jY - d.jY) = M ⬝ d.jY - d.jY) : ε • (M - 1) = M - 1 := by
  have e : M - 1 = (M ⬝ d.jX - d.jX) ⬝ d.pX + (M ⬝ d.j0 - d.j0) ⬝ d.p0 + (M ⬝ d.jY - d.jY) ⬝ d.pY := by
    have e1 : M - 1 = (M - 1) ⬝ (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY) := by
      rw [d.sum_eq_one, Matrix.mul_one]
    rw [e1]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
  rw [e, smul_add, smul_add, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, hX, h0, hY]

theorem smul_shift {ε : AE D} (hεε : ε * ε = ε) {m n : ℕ} {x : Mx D m n} (hx : ε • x = x) (y : Mx D m n) :
    ε • (x + (1 - ε) • y - y) = x + (1 - ε) • y - y := by
  have e : x + (1 - ε) • y - y = x - ε • y := by
    rw [sub_smul, one_smul]; abel
  rw [e, smul_sub, hx, smul_smul, hεε]

theorem scalar_X {R : Type*} [CommRing R] {ε a b x y : R} (ha : ε * a = a) (hab : a * b = ε) (hx : ε * x = x) :
    a * (x * b + (1 - ε) * y) = x := by
  linear_combination x * hab + hx - y * ha

end GlobalTheory.IwaPlace.BuildQ

open GlobalTheory.IwaPlace.BuildQ in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.IwaPlace.exists_grpAt_of_dual_frames : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (α β : Fin ρ → AE D) (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i, α i ∈ idAt D (· = v)) → (∀ i, β i ∈ idAt D (· = v)) → (∀ i, α i * β i = ε) → (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i j, c' i j ∈ idAt D (· = v)) → adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) → adj c' ⬝ (gA S ⬝ c') = 0 → ∃ q ∈ grpAt S (· = v), mt S q ⬝ d.jX = d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)) ∧ (∀ i, mt S q *ᵥ colMul d.jX i (α i) = fun k => (d.jX ⬝ b) k i) ∧ (∀ i, mt S q *ᵥ colMul d.jY i (cA D (β i)) = fun k => c' k i) := by
  intro D S S₀ ρ d v ε hεε hεc _ hε α β b c' hα hβ hαβ hb hc' H1 H2
  have hb' : ε • b = b := smul_eq_of_mem hε hb
  have hc : ε • c' = c' := smul_eq_of_mem hε hc'
  have hαε : ∀ i, ε * α i = α i := fun i => (hε _).1 (hα i)
  have hβε : ∀ i, ε * β i = β i := fun i => (hε _).1 (hβ i)
  have h : HypDec.Images S S₀ (d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))
      (d.j0 - (d.jX ⬝ b) ⬝ (adj c' ⬝ (gA S ⬝ d.j0)))
      (c' ⬝ Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY) :=
    ⟨imXX d, imYY d hεε hεc hαε hc H2, imYX d hεε hεc hαε hαβ hb' hc H1, imOO d, imOX d, imOY d hεε hεc hb' hc H1⟩
  have hjb : ε • (d.jX ⬝ b) = d.jX ⬝ b := by rw [← Matrix.mul_smul, hb']
  have hE : d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ))
      = (d.jX ⬝ b) ⬝ Matrix.diagonal β + (1 - ε) • d.jX := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]
  refine ⟨d.ofImages _ _ _ h, ?_, d.ofImages_jX h, fun i => ?_, fun i => ?_⟩
  · have key := smul_sub_one d (ε := ε) (Formalism.L2.Theta.mt S (d.ofImages _ _ _ h))
      (by rw [d.ofImages_jX h, hE]; exact smul_shift hεε (by rw [← Matrix.smul_mul, hjb]) _)
      (by rw [d.wittDecomp_ofImages_inclAnisotropic h, sub_sub_cancel_left, smul_neg, ← Matrix.smul_mul, hjb])
      (by rw [d.ofImages_jY h]; exact smul_shift hεε (by rw [← Matrix.smul_mul, hc]) _)
    refine (mem_congGrp_iff S _ _).2 fun i j => (hε _).2 ?_
    exact congrFun (congrFun key i) j
  · rw [mulVec_colMul, d.ofImages_jX h, hE]
    funext k
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    exact scalar_X (hαε i) (hαβ i) (congrFun (congrFun hjb k) i)
  · rw [mulVec_colMul, d.ofImages_jY h]
    funext k
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    refine scalar_X ?_ ?_ (congrFun (congrFun hc k) i)
    · rw [← hεc, ← map_mul, hβε]
    · rw [← map_mul, mul_comm, hαβ, hεc]
