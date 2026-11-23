import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocHomAlgebraMap
open IsLocalRing

namespace GlobalTheory.AbhyankarLocal

open TensorProduct

set_option maxHeartbeats 1000000 in

theorem exists_kummer_element (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ)
    (D : Type) [CommRing D] [Algebra S D]
    (ψ : D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) :
    Irreducible π → 0 < e → ∀ [IsDomain D] [IsDiscreteValuationRing D]
    (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal] (m k : ℕ)
    (ϖ : Localization.AtPrime (Q.comap (GlobalTheory.AbhyankarLocal.toNorm S L D)))
    (u : (Localization.AtPrime (Q.comap (GlobalTheory.AbhyankarLocal.toNorm S L D)))ˣ), m * k = e →
    algebraMap S _ π = ϖ ^ m *
      (u : Localization.AtPrime (Q.comap (GlobalTheory.AbhyankarLocal.toNorm S L D))) →
    ∃ y : Localization.AtPrime Q, y ^ m = GlobalTheory.AbhyankarLocal.locHom Q u ∧
      (algebraMap D (Localization.AtPrime Q)
        (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))) ^ k =
        GlobalTheory.AbhyankarLocal.locHom Q ϖ * y := by
  intro hπ he _ _ Q _ m k ϖ u hmk hrel
  generalize hU : (u : Localization.AtPrime (Q.comap (toNorm S L D))) = U at hrel ⊢
  have hm : m ≠ 0 := by rintro rfl; simp at hmk; omega
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  set t := ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) with ht_def
  have ht : t ^ e = algebraMap S D π := by
    have h0 := AdjoinRoot.eval₂_root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h0
    have h1 : AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S) ^ e =
        algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) π := by
      rw [AdjoinRoot.algebraMap_eq]; exact sub_eq_zero.mp h0
    have := congrArg ψ.symm h1
    rw [map_pow, AlgEquiv.commutes] at this
    exact this
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (Q.comap (toNorm S L D)).primeCompl ϖ
  obtain ⟨⟨a', s'⟩, hs'⟩ := IsLocalization.mk'_surjective (Q.comap (toNorm S L D)).primeCompl
    U
  simp only at hs hs'
  have hsA : ϖ * algebraMap _ (Localization.AtPrime (Q.comap (toNorm S L D))) (s : integralClosure S L) =
      algebraMap _ _ a := by rw [← hs]; exact IsLocalization.mk'_spec _ a s
  have hs'A : U *
      algebraMap _ (Localization.AtPrime (Q.comap (toNorm S L D))) (s' : integralClosure S L) =
      algebraMap _ _ a' := by rw [← hs']; exact IsLocalization.mk'_spec _ a' s'
  have hinj : Function.Injective (algebraMap (integralClosure S L)
      (Localization.AtPrime (Q.comap (toNorm S L D)))) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors (Q.comap (toNorm S L D)))
  have hO : algebraMap S (integralClosure S L) π * (s : integralClosure S L) ^ (n + 1) *
      (s' : integralClosure S L) = a ^ (n + 1) * a' := by
    apply hinj
    rw [map_mul, map_mul, map_pow, map_mul, map_pow, ← IsScalarTower.algebraMap_apply, hrel,
      ← hsA, ← hs'A]
    ring
  have hL := congrArg (fun x : integralClosure S L => (x : L)) hO
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap] at hL
  have hSL : Function.Injective (algebraMap S L) := by
    rw [IsScalarTower.algebraMap_eq S K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
  have hπL : algebraMap S L π ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap S L)]; exact fun h => hπ.ne_zero (hSL h)
  have hne : ∀ x : (Q.comap (toNorm S L D)).primeCompl, ((x : integralClosure S L) : L) ≠ 0 := by
    intro x hx
    apply x.2
    have : (x : integralClosure S L) = 0 := Subtype.ext hx
    rw [this]; exact Ideal.zero_mem _
  have haL : (a : L) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.succ_ne_zero n), zero_mul] at hL
    exact mul_ne_zero (mul_ne_zero hπL (pow_ne_zero _ (hne s))) (hne s') hL
  set w : TensorProduct S D L := (t ^ k) ⊗ₜ[S] (((s' : integralClosure S L) : L) *
    ((s : integralClosure S L) : L) / (a : L)) with hw
  have hwm : w ^ (n + 1) = ((toNorm S L D ((s' : integralClosure S L) ^ n * a') :
      integralClosure D (TensorProduct S D L)) : TensorProduct S D L) := by
    rw [toNorm_coe, hw, Algebra.TensorProduct.tmul_pow, ← pow_mul, mul_comm k, hmk, ht,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    push_cast
    rw [div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero _ haL)]
    linear_combination ((s' : integralClosure S L) : L) ^ n * hL
  have hwint : IsIntegral D w := IsIntegral.of_pow (Nat.succ_pos n)
    (by rw [hwm]; exact (toNorm S L D _).2)
  let b : integralClosure D (TensorProduct S D L) := ⟨w, hwint⟩
  have hbm : b ^ (n + 1) = toNorm S L D ((s' : integralClosure S L) ^ n * a') :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hwm)
  have hbrel : toNorm S L D a * b = toNorm S L D ((s : integralClosure S L) * s') *
      algebraMap D (integralClosure D (TensorProduct S D L)) (t ^ k) := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, toNorm_coe, toNorm_coe, Subalgebra.coe_algebraMap,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show ((1 : D) ⊗ₜ[S] (a : L)) * w = _
    rw [hw, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    congr 1
    push_cast
    rw [mul_comm (a : L), div_mul_cancel₀ _ haL]
    ring
  have hσ : toNorm S L D (s' : integralClosure S L) ∈ Q.primeCompl := s'.2
  have hσ2 : toNorm S L D (s : integralClosure S L) ∈ Q.primeCompl := s.2
  obtain ⟨y, hy⟩ : ∃ y : Localization.AtPrime Q,
      y * algebraMap _ (Localization.AtPrime Q) (toNorm S L D s') = algebraMap _ _ b :=
    ⟨_, IsLocalization.mk'_spec _ b (⟨_, hσ⟩ : Q.primeCompl)⟩
  have hu1 : IsUnit (algebraMap _ (Localization.AtPrime Q) (toNorm S L D s')) :=
    IsLocalization.map_units _ (⟨_, hσ⟩ : Q.primeCompl)
  have hu2 : IsUnit (algebraMap _ (Localization.AtPrime Q) (toNorm S L D s)) :=
    IsLocalization.map_units _ (⟨_, hσ2⟩ : Q.primeCompl)
  have hϖW : locHom Q ϖ * algebraMap _ (Localization.AtPrime Q) (toNorm S L D s) =
      algebraMap _ _ (toNorm S L D a) := by
    have := congrArg (locHom Q) hsA
    rw [map_mul, locHom_algebraMap Q (s : integralClosure S L), locHom_algebraMap Q a] at this
    exact this
  have huW : locHom Q U *
      algebraMap _ (Localization.AtPrime Q) (toNorm S L D s') =
      algebraMap _ _ (toNorm S L D a') := by
    have := congrArg (locHom Q) hs'A
    rw [map_mul, locHom_algebraMap Q (s' : integralClosure S L), locHom_algebraMap Q a'] at this
    exact this
  refine ⟨y, ?_, ?_⟩
  · rw [← (hu1.pow (n + 1)).mul_left_inj, ← mul_pow, hy, ← map_pow, hbm, pow_succ'
      (algebraMap _ (Localization.AtPrime Q) (toNorm S L D s')), ← mul_assoc, huW]
    simp only [map_mul, map_pow]
    ring
  · rw [← (hu1.mul hu2).mul_left_inj]
    calc _ = algebraMap _ (Localization.AtPrime Q) (toNorm S L D ((s : integralClosure S L) * s') *
          algebraMap D (integralClosure D (TensorProduct S D L)) (t ^ k)) := by
          simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
          ring
      _ = algebraMap _ (Localization.AtPrime Q) (toNorm S L D a * b) := by rw [hbrel]
      _ = (locHom Q ϖ * algebraMap _ (Localization.AtPrime Q) (toNorm S L D s)) *
          (y *
            algebraMap _ (Localization.AtPrime Q) (toNorm S L D s')) := by
          rw [hϖW, hy, map_mul]
      _ = _ := by ring

end GlobalTheory.AbhyankarLocal
