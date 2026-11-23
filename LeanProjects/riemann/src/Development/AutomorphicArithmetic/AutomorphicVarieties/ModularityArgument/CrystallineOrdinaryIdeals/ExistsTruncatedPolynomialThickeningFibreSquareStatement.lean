import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_truncated_polynomial_thickening_fibre_square : ∀ {E B : Type} [Field E] [CommRing B] [Algebra E B] [Module.Finite E B] (π : B →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ J : ℕ, ∃ (C : Type) (_ : CommRing C) (_ : Algebra E C) (_ : Module.Finite E C) (T : Type) (_ : CommRing T) (_ : Algebra E T) (_ : Module.Finite E T) (πC : C →ₐ[E] E) (p₁ : T →ₐ[E] B) (p₂ : T →ₐ[E] C) (t : C), IsNilpotent t ∧ (∀ a, πC a = 0 → IsNilpotent a) ∧ (∀ a, π (p₁ a) = 0 → IsNilpotent a) ∧ π.comp p₁ = πC.comp p₂ ∧ (∀ b c, π b = πC c → ∃ s, p₁ s = b ∧ p₂ s = c) ∧ ∀ (P y : T) (j : ℕ) (v : Cˣ), j ≤ J → p₂ P = t ^ j * v → P * y = 0 → p₁ y = 0 := by
  intro E B _ _ _ _ π hπ J
  classical
  haveI : IsArtinianRing B := IsArtinianRing.of_finite E B
  obtain ⟨e, he⟩ : IsNilpotent (RingHom.ker (π : B →+* E)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro c hc
    exact mem_nilradical.mpr (hπ c (by simpa using hc))
  set I := RingHom.ker (π : B →+* E) with hIdef
  set N := J * e + 1 with hN
  have hN0 : N ≠ 0 := by omega
  haveI : Module.Finite E (AdjoinRoot ((X : E[X]) ^ N)) :=
    (AdjoinRoot.powerBasis' (monic_X_pow N)).finite
  haveI : Module.Finite B (AdjoinRoot ((X : B[X]) ^ N)) :=
    (AdjoinRoot.powerBasis' (monic_X_pow N)).finite
  haveI : Module.Finite E (AdjoinRoot ((X : B[X]) ^ N)) := Module.Finite.trans B _
  have hrootE : (AdjoinRoot.root ((X : E[X]) ^ N)) ^ N = 0 := by
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  have hrootB : (AdjoinRoot.root ((X : B[X]) ^ N)) ^ N = 0 := by
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  let πC : AdjoinRoot ((X : E[X]) ^ N) →ₐ[E] E :=
    AdjoinRoot.liftAlgHom _ (AlgHom.id E E) 0 (by simp [hN0])
  let p1 : AdjoinRoot ((X : B[X]) ^ N) →ₐ[E] B :=
    AdjoinRoot.liftAlgHom _ (AlgHom.id E B) 0 (by simp [hN0])
  let p2 : AdjoinRoot ((X : B[X]) ^ N) →ₐ[E] AdjoinRoot ((X : E[X]) ^ N) :=
    AdjoinRoot.liftAlgHom _ ((Algebra.ofId E _).comp π) (AdjoinRoot.root _)
      (by rw [eval₂_X_pow]; exact hrootE)
  have hp1 : ∀ q : B[X], p1 (AdjoinRoot.mk _ q) = q.coeff 0 := by
    intro q
    simp [p1, AdjoinRoot.liftAlgHom_mk, eval₂_at_zero]
  have hp1of : ∀ b : B, p1 (AdjoinRoot.of _ b) = b := fun b =>
    AdjoinRoot.liftAlgHom_of _ _ _ _ _
  have hπC : ∀ q : E[X], πC (AdjoinRoot.mk _ q) = q.coeff 0 := by
    intro q
    simp [πC, AdjoinRoot.liftAlgHom_mk, eval₂_at_zero]
  have hp2 : ∀ q : B[X], p2 (AdjoinRoot.mk _ q) = AdjoinRoot.mk _ (q.map (π : B →+* E)) := by
    intro q
    rw [AdjoinRoot.liftAlgHom_mk, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map]
    rfl
  have hp2root : p2 (AdjoinRoot.root _) = AdjoinRoot.root _ := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hp2map : ∀ q : E[X], p2 (AdjoinRoot.mk _ (q.map (algebraMap E B))) = AdjoinRoot.mk _ q := by
    intro q
    rw [hp2, Polynomial.map_map]
    congr 1
    conv_rhs => rw [← Polynomial.map_id (p := q)]
    congr 1
    ext r
    simp
  have hnilT : ∀ a, π (p1 a) = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hp1] at ha
    obtain ⟨r, hr⟩ : X ∣ q - C (q.coeff 0) := X_dvd_iff.mpr (by simp)
    have hq : q = C (q.coeff 0) + X * r := by rw [← hr]; ring
    rw [hq, map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    exact Commute.isNilpotent_add (Commute.all _ _) ((hπ _ ha).map _)
      ⟨N, by rw [mul_pow, hrootB, zero_mul]⟩
  have hnilC : ∀ a, πC a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hπC] at ha
    obtain ⟨r, rfl⟩ := X_dvd_iff.mpr ha
    exact ⟨N, by rw [map_mul, AdjoinRoot.mk_X, mul_pow, hrootE, zero_mul]⟩
  have hcomm : π.comp p1 = πC.comp p2 := by
    refine AlgHom.ext fun a => ?_
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    simp only [AlgHom.comp_apply, hp1, hp2, hπC, coeff_map]
    rfl
  have hsurj : ∀ b c, π b = πC c → ∃ s, p1 s = b ∧ p2 s = c := by
    intro b c hbc
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective c
    rw [hπC] at hbc
    refine ⟨AdjoinRoot.of _ b + AdjoinRoot.mk _ (q.map (algebraMap E B)) -
      AdjoinRoot.of _ (algebraMap E B (q.coeff 0)), ?_, ?_⟩
    · rw [map_sub, map_add, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C, hp1, hp1, hp1]
      simp
    · rw [map_sub, map_add, hp2map, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C, hp2, hp2]
      simp [hbc]
  have hker : ∀ Q, p2 Q = 0 → Q ∈ I.map (AdjoinRoot.of ((X : B[X]) ^ N)) := by
    intro Q hQ
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective Q
    rw [hp2, AdjoinRoot.mk_eq_zero] at hQ
    have hmod : (q %ₘ (X ^ N)).map (π : B →+* E) = 0 := by
      rw [map_modByMonic _ (monic_X_pow N), Polynomial.map_pow, map_X]
      exact (modByMonic_eq_zero_iff_dvd (monic_X_pow N)).mpr hQ
    have hmk : AdjoinRoot.mk ((X : B[X]) ^ N) q = AdjoinRoot.mk _ (q %ₘ (X ^ N)) := by
      conv_lhs => rw [← modByMonic_add_div q (X ^ N)]
      rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
    rw [hmk]
    have hin : q %ₘ (X ^ N) ∈ I.map (C : B →+* B[X]) := by
      rw [Ideal.mem_map_C_iff]
      intro n
      rw [hIdef, RingHom.mem_ker]
      have := congrArg (fun p => p.coeff n) hmod
      simpa using this
    have := Ideal.mem_map_of_mem (AdjoinRoot.mk ((X : B[X]) ^ N)) hin
    rw [Ideal.map_map] at this
    exact this
  refine ⟨AdjoinRoot ((X : E[X]) ^ N), inferInstance, inferInstance, inferInstance,
    AdjoinRoot ((X : B[X]) ^ N), inferInstance, inferInstance, inferInstance, πC, p1, p2,
    AdjoinRoot.root _, ⟨N, hrootE⟩, hnilC, hnilT, hcomm, hsurj, ?_⟩
  intro P y j v hj hP hPy
  obtain ⟨qv, hqv⟩ := AdjoinRoot.mk_surjective (v : AdjoinRoot ((X : E[X]) ^ N))
  set V := AdjoinRoot.mk ((X : B[X]) ^ N) (qv.map (algebraMap E B)) with hVdef
  have hV : p2 V = v := by rw [hVdef, hp2map, hqv]
  have hVu : IsUnit V := by
    have hw : π (p1 V) ≠ 0 := by
      rw [← AlgHom.comp_apply, hcomm, AlgHom.comp_apply, hV]
      exact (v.isUnit.map πC).ne_zero
    have h1 : IsNilpotent (V - AdjoinRoot.of _ (algebraMap E B (π (p1 V)))) := by
      apply hnilT
      rw [map_sub, map_sub, hp1of, AlgHom.commutes]
      simp
    have h2 : IsUnit (AdjoinRoot.of ((X : B[X]) ^ N) (algebraMap E B (π (p1 V)))) :=
      ((Ne.isUnit hw).map (algebraMap E B)).map _
    have := h1.isUnit_add_left_of_commute h2 (Commute.all _ _)
    simpa using this
  obtain ⟨Vi, hVi⟩ : ∃ Vi, V * Vi = 1 := hVu.exists_right_inv
  set Q := P - AdjoinRoot.root ((X : B[X]) ^ N) ^ j * V with hQdef
  have hQ2 : p2 Q = 0 := by
    rw [hQdef, map_sub, map_mul, map_pow, hV, hP, hp2root, sub_self]
  set K := I.map (AdjoinRoot.of ((X : B[X]) ^ N)) with hK
  have hQK : Q ∈ K := hker Q hQ2
  set R := -(Q * Vi) with hR
  have hRK : R ∈ K := K.neg_mem (K.mul_mem_right _ hQK)
  have hxR : AdjoinRoot.root ((X : B[X]) ^ N) ^ j * y = R * y := by
    rw [hR]
    linear_combination (-(AdjoinRoot.root ((X : B[X]) ^ N) ^ j * y)) * hVi + Vi * hPy +
      (Vi * y) * hQdef
  have hpow : ∀ k : ℕ, AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * y = R ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hsplit : AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * (k + 1)) =
          AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * AdjoinRoot.root ((X : B[X]) ^ N) ^ j := by
        rw [← pow_add]
        congr 1
      calc AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * (k + 1)) * y
          = AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) *
              (AdjoinRoot.root ((X : B[X]) ^ N) ^ j * y) := by
            rw [hsplit, mul_assoc]
        _ = R * (AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * y) := by rw [hxR]; ring
        _ = R ^ (k + 1) * y := by rw [ih]; ring
  have hRe : R ^ e = 0 := by
    have h3 : R ^ e ∈ K ^ e := Ideal.pow_mem_pow hRK e
    rw [hK, ← Ideal.map_pow, he, Ideal.zero_eq_bot, Ideal.map_bot] at h3
    exact (Ideal.mem_bot).1 h3
  have hy0 : AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * e) * y = 0 := by
    rw [hpow, hRe, zero_mul]
  have hlt : j * e < N := by
    have := Nat.mul_le_mul_right e hj
    omega
  obtain ⟨qy, rfl⟩ := AdjoinRoot.mk_surjective y
  rw [hp1]
  rw [← AdjoinRoot.mk_X, ← map_pow, ← map_mul, AdjoinRoot.mk_eq_zero] at hy0
  obtain ⟨s, hs⟩ := hy0
  have h4 := congrArg (fun p => p.coeff (j * e)) hs
  simp only [coeff_X_pow_mul'] at h4
  simpa [Nat.not_le.mpr hlt] using h4
