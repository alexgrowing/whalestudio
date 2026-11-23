import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightWith
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SlopeStepG

noncomputable section

namespace GlobalTheory.Core.Ht2

open NumberField Formalism.BasicNotions

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

abbrev nrm (A : HLat K) (v : InfinitePlace K) (x : A.V) : ℝ := Formalism.HermitianLatticesTheory.normAt A.b A.X v x

def Framed (A : HLat K) : Prop := ∀ v, IsUnit (A.X v).det

def IsoAll (N A : HLat K) (e : N.V →ₗ[K] A.V) : Prop := ∀ v x, nrm A v (e x) = nrm N v x

def Norming (B M : HLat K) (pr : B.V →ₗ[K] Module.Dual K M.V) : Prop :=
  ∀ (w : B.V) (v : InfinitePlace K), ∃ z, v (pr w z) = nrm B v w ^ 2 ∧ nrm M v z = nrm B v w

def Reads (N B A M : HLat K) (Ψ : N.V →ₗ[K] B.V) (Φ : A.V →ₗ[K] Module.Dual K M.V) : Prop :=
  ∃ (e : N.V →ₗ[K] A.V) (pr : B.V →ₗ[K] Module.Dual K M.V),
    IsoAll N A e ∧ Norming B M pr ∧ ∀ x, Φ (e x) = pr (Ψ x)

def PairLe (A M : HLat K) (Φ : A.V →ₗ[K] Module.Dual K M.V) (h : ℝ) : Prop :=
  ∃ c : InfinitePlace K → ℝ, (∀ v x y, v (Φ x y) ^ 2 ≤ Real.exp (c v) * nrm A v x ^ 2 * nrm M v y ^ 2) ∧
    (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, c v ≤ h

def ValLe (N B : HLat K) (Ψ : N.V →ₗ[K] B.V) (h : ℝ) : Prop :=
  ∃ c : InfinitePlace K → ℝ, (∀ v x, nrm B v (Ψ x) ^ 2 ≤ Real.exp (c v) * nrm N v x ^ 2) ∧
    (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, c v ≤ h

theorem nrm_nonneg (A : HLat K) (v : InfinitePlace K) (x : A.V) : 0 ≤ nrm A v x :=
  Real.sqrt_nonneg _

theorem Norming.nrm_le {B M : HLat K} {pr : B.V →ₗ[K] Module.Dual K M.V} (hn : Norming B M pr) (w : B.V) (v : InfinitePlace K)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ y, v (pr w y) ≤ C * nrm M v y) : nrm B v w ≤ C := by
  obtain ⟨z, hz, hzn⟩ := hn w v
  have hw := nrm_nonneg B v w
  have hle := h z
  rw [hz, hzn] at hle
  nlinarith

theorem Reads.exists_nrm_le {N B A M : HLat K} {Ψ : N.V →ₗ[K] B.V} {Φ : A.V →ₗ[K] Module.Dual K M.V}
    (hr : Reads N B A M Ψ Φ) : ∃ e : N.V →ₗ[K] A.V, IsoAll N A e ∧ ∀ x v (C : ℝ), 0 ≤ C →
      (∀ y, v (Φ (e x) y) ≤ C * nrm M v y) → nrm B v (Ψ x) ≤ C := by
  obtain ⟨e, pr, he, hn, hΦ⟩ := hr
  refine ⟨e, he, fun x v C hC hb => hn.nrm_le (Ψ x) v hC fun y => ?_⟩
  rw [← hΦ x]
  exact hb y

theorem valLe_of_reads {N B A M : HLat K} {Ψ : N.V →ₗ[K] B.V} {Φ : A.V →ₗ[K] Module.Dual K M.V} {h : ℝ}
    (hr : Reads N B A M Ψ Φ) (hp : PairLe A M Φ h) : ValLe N B Ψ h := by
  obtain ⟨c, hc, hmean⟩ := hp
  obtain ⟨e, he, hbd⟩ := hr.exists_nrm_le
  refine ⟨c, fun v x => ?_, hmean⟩

  have hs : Real.exp (c v / 2) ^ 2 = Real.exp (c v) := by
    rw [sq, ← Real.exp_add, add_halves]
  have hE : 0 ≤ Real.exp (c v / 2) := (Real.exp_pos _).le
  have hN := nrm_nonneg N v x
  have key : nrm B v (Ψ x) ≤ Real.exp (c v / 2) * nrm N v x := by
    refine hbd x v _ (mul_nonneg hE hN) fun y => ?_
    have h1 := hc v (e x) y
    rw [he v x, ← hs] at h1
    have hM := nrm_nonneg M v y
    have hb : 0 ≤ Real.exp (c v / 2) * nrm N v x * nrm M v y := mul_nonneg (mul_nonneg hE hN) hM
    nlinarith
  have hk := nrm_nonneg B v (Ψ x)
  calc nrm B v (Ψ x) ^ 2 ≤ (Real.exp (c v / 2) * nrm N v x) ^ 2 := by nlinarith
    _ = Real.exp (c v) * nrm N v x ^ 2 := by rw [mul_pow, hs]

end Generic

namespace Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)

@[reducible] def lat : HLat K where
  V := Fin n → K
  ι := Fin n
  b := Pi.basisFun K (Fin n)
  X := fun _ => 1
  L := Submodule.pi Set.univ (fun _ => (1 : Submodule (𝓞 K) K))

def dot : (lat K n).V →ₗ[K] Module.Dual K (lat K n).V := dotProductBilin K K

variable {K n}

theorem dot_apply (x y : Fin n → K) : dot K n x y = ∑ i, x i * y i := rfl

theorem nrm_sq (v : InfinitePlace K) (x : Fin n → K) : nrm (lat K n) v x ^ 2 = ∑ i, ‖v.embedding (x i)‖ ^ 2 := by
  unfold nrm Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, lat]

theorem norming_dot [IsGalois ℚ K] : Norming (lat K n) (lat K n) (dot K n) := by
  intro w v

  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) v.embedding
    (NumberField.ComplexEmbedding.conjugate v.embedding) (RingHom.ext_rat _ _)
  have hc : ∀ a, v.embedding (σ.symm a) = starRingEnd ℂ (v.embedding a) := fun a =>
    RingHom.congr_fun hσ a
  refine ⟨fun i => σ.symm (w i), ?_, ?_⟩
  · rw [nrm_sq, dot_apply, ← NumberField.InfinitePlace.norm_embedding_eq, map_sum]
    simp only [map_mul, hc, Complex.mul_conj]
    rw [← Complex.ofReal_sum, Complex.norm_of_nonneg (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)]
    simp only [Complex.normSq_eq_norm_sq]
  · have h2 : nrm (lat K n) v (fun i => σ.symm (w i)) ^ 2 = nrm (lat K n) v w ^ 2 := by
      rw [nrm_sq, nrm_sq]
      simp only [hc, Complex.norm_conj]
    rw [← Real.sqrt_sq (nrm_nonneg _ v w), ← h2, Real.sqrt_sq (nrm_nonneg _ _ _)]

theorem reads_dot [IsGalois ℚ K] {m : ℕ} (Ψ : (lat K n).V →ₗ[K] (lat K m).V) :
    Reads (lat K n) (lat K m) (lat K n) (lat K m) Ψ (dot K m ∘ₗ Ψ) :=
  ⟨LinearMap.id, dot K m, fun _ _ => rfl, norming_dot, fun _ => rfl⟩

theorem pairLe_dot : PairLe (lat K n) (lat K n) (dot K n) 0 := by
  refine ⟨fun _ => 0, fun v x y => ?_, by simp⟩
  rw [Real.exp_zero, one_mul, nrm_sq, nrm_sq, dot_apply,
    ← NumberField.InfinitePlace.norm_embedding_eq, map_sum]

  have h1 : ‖∑ i, v.embedding (x i * y i)‖ ≤ ∑ i, ‖v.embedding (x i)‖ * ‖v.embedding (y i)‖ :=
    (norm_sum_le _ _).trans_eq (by simp only [map_mul, norm_mul])
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖v.embedding (x i)‖)
    (fun i => ‖v.embedding (y i)‖)
  have h0 := norm_nonneg (∑ i, v.embedding (x i * y i))
  calc ‖∑ i, v.embedding (x i * y i)‖ ^ 2 ≤ (∑ i, ‖v.embedding (x i)‖ * ‖v.embedding (y i)‖) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2

example [IsGalois ℚ K] : ValLe (lat K 2) (lat K 2) LinearMap.id 0 := valLe_of_reads (reads_dot LinearMap.id) pairLe_dot

end Std

def PsiReads (D : D7) (u : D.what₂.Word) (A M : HLat D.what₂.LL) (Φ : A.V →ₗ[D.what₂.LL] Module.Dual D.what₂.LL M.V) : Prop :=
  Reads (D.div.Nu u) (Rk.Pt D u) A M (Rk.Psi D u) Φ

end GlobalTheory.Core.Ht2

end
