import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistTildeSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace TwistTildeProof

theorem smul_mem_of_mem_span {R A M : Type*} [CommRing R] [Ring A] [AddCommGroup M] [Module R A]
    [Module A M] [Module R M] [IsScalarTower R A M] [SMulCommClass A R M] {s : Set A} {t : Set M}
    {T : Submodule R M} (h : ∀ a ∈ s, ∀ b ∈ t, a • b ∈ T) {q : A} (hq : q ∈ Submodule.span R s)
    {m : M} (hm : m ∈ Submodule.span R t) : q • m ∈ T := by
  refine Submodule.span_induction (p := fun q _ => q • m ∈ T) ?_ ?_ ?_ ?_ hq
  · intro a ha
    refine Submodule.span_induction (p := fun m _ => a • m ∈ T) ?_ ?_ ?_ ?_ hm
    · exact fun b hb => h a ha b hb
    · rw [smul_zero]; exact T.zero_mem
    · intro b c _ _ hb hc; rw [smul_add]; exact T.add_mem hb hc
    · intro r b _ hb; rw [smul_comm]; exact T.smul_mem r hb
  · rw [zero_smul]; exact T.zero_mem
  · intro a b _ _ ha hb; rw [add_smul]; exact T.add_mem ha hb
  · intro r a _ ha; rw [smul_assoc]; exact T.smul_mem r ha

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

def prodSet (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω) (c : ℤ) :
    Set E :=
  {z | ∃ (a b : ℤ) (q : Ω) (m : E), q ∈ Q.piece a ∧ m ∈ M.piece b ∧ a + b = c ∧ z = q • m}

def prod (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω) :
    FinGradedSub (S := S) (x := x) E where
  piece c := Submodule.span S (prodSet M Q c)
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span S
      (prodSet M Q (c + d))) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨a, b, q, m, hq, hm, hab, rfl⟩
      refine Submodule.subset_span ⟨a, b + d, q, aeval x f • m, hq, M.smul_mem d b f m hf hm,
        by omega, ?_⟩
      rw [smul_smul, smul_smul, mul_comm]
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha
  fg := by
    obtain ⟨n, deg, gen, hgen, hspan⟩ := M.fg
    obtain ⟨n', deg', gen', hgen', hspan'⟩ := Q.fg
    let e := (finProdFinEquiv : Fin n' × Fin n ≃ Fin (n' * n))
    refine ⟨n' * n, fun k => deg' (e.symm k).1 + deg (e.symm k).2,
      fun k => gen' (e.symm k).1 • gen (e.symm k).2, fun k => Submodule.subset_span
        ⟨_, _, _, _, hgen' _, hgen _, rfl, rfl⟩, fun c => Submodule.span_le.mpr ?_⟩
    rintro _ ⟨a, b, q, m, hq, hm, hab, rfl⟩
    refine smul_mem_of_mem_span ?_ (hspan' a hq) (hspan b hm)
    rintro _ ⟨l, f', e', hf', he', rfl⟩ _ ⟨j, f, e'', hf, he'', rfl⟩
    refine Submodule.subset_span ⟨e (l, j), f' * f, e' + e'', hf'.mul hf, ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply]; push_cast; omega
    · simp only [Equiv.symm_apply_apply, smul_eq_mul, map_mul, smul_smul]
      congr 1; ring

theorem twist_eq (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω)
    (I : Chart x) : ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I = (prod M Q).tilde 0 I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ Q.tilde 0 I at hq
    change y ∈ M.tilde 0 I at hy
    refine smul_mem_of_mem_span ?_ hq hy
    rintro _ ⟨q, s₁, a₁, e₁, hs₁, hse₁, hq, ha₁, rfl⟩ _ ⟨m, s₂, a₂, e₂, hs₂, hse₂, hm, ha₂, rfl⟩
    refine Submodule.subset_span ⟨q • m, s₁ * s₂, a₁ + a₂, e₁ + e₂, mul_mem hs₁ hs₂, hse₁.mul hse₂,
      Submodule.subset_span ⟨a₁, a₂, q, m, hq, hm, rfl, rfl⟩, by push_cast; omega, ?_⟩
    simp only [smul_eq_mul, smul_smul, map_mul, mul_inv]
    congr 1; ring
  · obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, s, a, e, hs, hse, hp, hae, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    refine Submodule.span_induction (p := fun p _ => (aeval x s)⁻¹ • p ∈
      ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I) ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨a', b', q, m, hq, hm, hab, rfl⟩
      set k := a'.toNat
      set j := (-a').toNat
      have hkj : (k : ℤ) - j = a' := Int.toNat_sub_toNat_neg a'
      have hq' : (aeval x (X i ^ k : Poly S N))⁻¹ • (aeval x (X i ^ j : Poly S N) • q) ∈
          Q.tilde 0 I := by
        have h := Q.smul_mem j a' _ q (isHomogeneous_X_pow i j) hq
        rw [show a' + (j : ℤ) = k by omega] at h
        exact Submodule.subset_span ⟨_, X i ^ k, k, k, pow_mem (X_mem_monos hi) k,
          isHomogeneous_X_pow i k, h, by simp, rfl⟩
      have hm' : (aeval x (s * X i ^ j))⁻¹ • (aeval x (X i ^ k : Poly S N) • m) ∈ M.tilde 0 I := by
        have h := M.smul_mem k b' _ m (isHomogeneous_X_pow i k) hm
        exact Submodule.subset_span ⟨_, s * X i ^ j, b' + k, e + j,
          mul_mem hs (pow_mem (X_mem_monos hi) j), hse.mul (isHomogeneous_X_pow i j), h,
          by push_cast; omega, rfl⟩
      have heq : (aeval x s)⁻¹ • (q • m) = ((aeval x (X i ^ k : Poly S N))⁻¹ •
          (aeval x (X i ^ j : Poly S N) • q)) • ((aeval x (s * X i ^ j))⁻¹ •
          (aeval x (X i ^ k : Poly S N) • m)) := by
        simp only [smul_eq_mul, smul_smul, map_mul, map_pow, aeval_X]
        congr 1
        field_simp
      rw [heq]
      exact Submodule.subset_span ⟨_, hq', _, hm', rfl⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_of_tower_mem _ r ha

end TwistTildeProof

open TwistTildeProof in

theorem TwistTilde.proof : TwistTilde.Statement := by
  intro S _ Ω _ _ N x E _ _ _ _ M Q
  exact ⟨prod M Q, fun c => rfl, twist_eq M Q⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
