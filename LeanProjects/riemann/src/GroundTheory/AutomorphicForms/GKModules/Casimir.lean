import Mathlib
import GroundTheory.AutomorphicForms.GKModules.ZKFinite

namespace GroundTheory.Automorphic

open Set Filter Topology

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

section Casimir

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem mem_center_of_forall_ι_commute {z : UniversalEnvelopingAlgebra ℝ L}
    (hz : ∀ x : L, UniversalEnvelopingAlgebra.ι ℝ x * z = z * UniversalEnvelopingAlgebra.ι ℝ x) :
    z ∈ Subalgebra.center ℝ (UniversalEnvelopingAlgebra ℝ L) := by
  rw [Subalgebra.mem_center_iff]
  intro u
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ L t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ L) u
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r z
  | ι x => exact hz x
  | mul a b ha hb => rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [map_add, add_mul, mul_add, ha, hb]

variable (B : LinearMap.BilinForm ℝ L)
variable {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ L) (ε : ι → ℝ)

noncomputable def casimir : UniversalEnvelopingAlgebra ℝ L :=
  ∑ i, ε i • (UniversalEnvelopingAlgebra.ι ℝ (b i) * UniversalEnvelopingAlgebra.ι ℝ (b i))

variable {B b ε}

theorem eq_sum_of_orthogonal [DecidableEq ι] (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0) (Y : L) :
    Y = ∑ j, (ε j * B (b j) Y) • b j := by
  conv_lhs => rw [← b.sum_repr Y]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have e : B (b j) Y = b.repr Y j * ε j := by
    have := congrArg (B (b j)) (b.sum_repr Y)
    rw [← this, map_sum]
    simp [horth]
  rw [e, ← mul_assoc, mul_comm (ε j), mul_assoc, hε, mul_one]

theorem casimir_mem_center [DecidableEq ι] (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y : L, B X Y = B Y X) (hinv : ∀ X Y Z : L, B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆) :
    casimir b ε ∈ Subalgebra.center ℝ (UniversalEnvelopingAlgebra ℝ L) := by
  apply mem_center_of_forall_ι_commute
  intro X
  rw [← sub_eq_zero]
  set ιu := UniversalEnvelopingAlgebra.ι ℝ (L := L)
  set a : ι → ι → ℝ := fun i j => ε i * (ε j * B (b j) ⁅X, b i⁆)
  set T : ι → ι → UniversalEnvelopingAlgebra ℝ L := fun i j => ιu (b j) * ιu (b i) + ιu (b i) * ιu (b j)
  have hanti : ∀ i j, a j i = -a i j := by
    intro i j
    simp only [a]
    rw [hsymm (b i), hinv, hsymm]
    ring
  have hT : ∀ i j, T j i = T i j := by intro i j; simp only [T]; abel
  have hcomm : ∀ i, ιu X * (ιu (b i) * ιu (b i)) - ιu (b i) * ιu (b i) * ιu X =
      ∑ j, (ε j * B (b j) ⁅X, b i⁆) • T i j := by
    intro i
    have e1 : ιu X * (ιu (b i) * ιu (b i)) - ιu (b i) * ιu (b i) * ιu X =
        ιu ⁅X, b i⁆ * ιu (b i) + ιu (b i) * ιu ⁅X, b i⁆ := by
      rw [LieHom.map_lie, Ring.lie_def]
      noncomm_ring
    rw [e1]
    conv_lhs => rw [eq_sum_of_orthogonal hε horth ⁅X, b i⁆]
    simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      ← Finset.sum_add_distrib, ← smul_add, T]
  have hS : ∑ i, ∑ j, a i j • T i j = 0 := by
    set S := ∑ i, ∑ j, a i j • T i j
    have : S = -S := by
      conv_lhs => rw [show S = ∑ i, ∑ j, a i j • T i j from rfl, Finset.sum_comm]
      simp only [S, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hanti, hT, neg_smul]
    have h2 : (2 : ℝ) • S = 0 := by rw [two_smul]; nth_rewrite 2 [this]; exact add_neg_cancel S
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  simp only [casimir, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    ← Finset.sum_sub_distrib, ← smul_sub]
  calc ∑ i, ε i • (ιu X * (ιu (b i) * ιu (b i)) - ιu (b i) * ιu (b i) * ιu X)
      = ∑ i, ∑ j, a i j • T i j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcomm, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul]
    _ = 0 := hS

end Casimir

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {ι : Type*} [Fintype ι]

noncomputable def laplacian (b : Module.Basis ι ℝ h.lieSubalgebra) :
    Module.End ℂ (h.smoothFuns (F := F)) :=
  ∑ i, h.rightDerivEnd (h.ofLie (b i)) * h.rightDerivEnd (h.ofLie (b i))

theorem exists_aeval_laplacian_eq_zero [DecidableEq ι] (K : Subgroup G)
    (B : LinearMap.BilinForm ℝ h.lieSubalgebra) (b : Module.Basis ι ℝ h.lieSubalgebra) (ε : ι → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y : h.lieSubalgebra, B X Y = B Y X)
    (hinv : ∀ X Y Z : h.lieSubalgebra, B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆)
    (hK : ∀ i, ε i = -1 → ∀ t : ℝ, h.expG (t • h.ofLie (b i)) ∈ K)
    (f : h.smoothFuns (F := F)) (hfK : IsRightKFinite K (f : G → F)) (hfZ : h.IsZFinite f) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ Polynomial.aeval (h.laplacian (F := F) b) P f = 0 := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  set V := h.zkSpan K f
  haveI : FiniteDimensional ℂ V := h.finiteDimensional_zkSpan K f hfK hfZ
  have hVK : ∀ (k : K), ∀ w ∈ V, h.rightTranslateEnd (k : G) w ∈ V :=
    fun k w hw => h.rightTranslate_mem_zkSpan K f k hw

  have hΔ : h.laplacian (F := F) b = h.rightUAction (casimir b ε) +
      ∑ i, (1 - ε i) • (h.rightDerivEnd (h.ofLie (b i)) * h.rightDerivEnd (h.ofLie (b i))) := by
    simp only [laplacian, casimir, map_sum, map_smul, map_mul, rightUAction_ι,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul, add_sub_cancel, one_smul]
  have hΩ := casimir_mem_center (hε2) horth hsymm hinv (b := b)
  have hmapsto : ∀ w ∈ V, h.laplacian (F := F) b w ∈ V := by
    intro w hw
    rw [hΔ, LinearMap.add_apply, LinearMap.sum_apply]
    refine Submodule.add_mem _ (h.rightUAction_mem_zkSpan K f hΩ hw) (Submodule.sum_mem _ fun i _ => ?_)
    rw [LinearMap.smul_apply, Module.End.mul_apply]
    rcases hε i with e | e
    · rw [e, sub_self, zero_smul]; exact Submodule.zero_mem _
    · refine Submodule.smul_of_tower_mem _ _ ?_
      exact h.rightDeriv_mem_of_isKStable K hVK (hK i e)
        (h.rightDeriv_mem_of_isKStable K hVK (hK i e) hw)
  have hf : f ∈ V := h.self_mem_zkSpan K f
  by_cases hf0 : f = 0
  · refine ⟨Polynomial.X, Polynomial.monic_X, by simp, ?_⟩
    simp [hf0]
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ, Δ = h.laplacian (F := F) b := ⟨_, rfl⟩
  rw [← hΔdef]
  rw [← hΔdef] at hmapsto
  have hmemk : ∀ k : ℕ, (Δ ^ k) f ∈ V := by
    intro k
    induction k with
    | zero => simpa using hf
    | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hmapsto _ ih
  set n := Module.finrank ℂ V
  let u : Fin (n + 1) → h.smoothFuns (F := F) := fun i => (Δ ^ (i : ℕ)) f
  have hspan : Submodule.span ℂ (range u) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmemk i
  have hnot : ¬ LinearIndependent ℂ u := fun hli => by
    have h1 := finrank_span_eq_card hli
    have h2 := Submodule.finrank_mono hspan
    rw [h1, Fintype.card_fin] at h2
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hnot
  obtain ⟨Q, hQdef⟩ : ∃ Q : Polynomial ℂ,
      Q = ∑ j : Fin (n + 1), Polynomial.C (g j) * Polynomial.X ^ (j : ℕ) := ⟨_, rfl⟩
  have hQf : Polynomial.aeval Δ Q f = 0 := by
    have e1 : Polynomial.aeval Δ Q f = ∑ j : Fin (n + 1), g j • (Δ ^ (j : ℕ)) f := by
      rw [hQdef, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, Module.End.mul_apply,
        Module.algebraMap_end_apply]
    rw [e1]
    exact hg
  have hQ0 : Q ≠ 0 := by
    intro h0
    apply hi
    have := congrArg (fun P => P.coeff (i : ℕ)) h0
    simp only [hQdef, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single i] at this
    · simpa using this
    · intro j _ hj
      have : (i : ℕ) ≠ (j : ℕ) := fun e => hj (Fin.ext e).symm
      simp [this]
    · simp
  refine ⟨Q * Polynomial.C Q.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hQ0, ?_, ?_⟩
  · rw [Polynomial.natDegree_mul_C (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hQ0))]
    by_contra hdeg
    push_neg at hdeg
    have hQc := Polynomial.eq_C_of_natDegree_le_zero hdeg
    have hc : Q.coeff 0 ≠ 0 := by
      intro hc; apply hQ0; rw [hQc, hc, map_zero]
    rw [hQc, Polynomial.aeval_C, Module.algebraMap_end_apply] at hQf
    exact hf0 ((smul_eq_zero.1 hQf).resolve_left hc)
  · rw [map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul,
      hQf, smul_zero]

end IsExpLieAlgebra

end GroundTheory.Automorphic
