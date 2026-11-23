import Mathlib

namespace LateralTheory.E.E4

open Polynomial

def LeafOrdInfLocal : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 →
    ∃ h : Polynomial k, h.eval 0 ≠ 0 ∧
    IsIntegral (Algebra.adjoin k {(algebraMap B (FractionRing B) (g Polynomial.X))⁻¹,
        (Polynomial.aeval (algebraMap B (FractionRing B) (g Polynomial.X))⁻¹ h)⁻¹})
      (algebraMap B (FractionRing B) (u : B))

def LeafLocGlobInf : Prop := ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (t : L), Transcendental k t →
  ∀ (x : L) (h : Polynomial k), h.eval 0 ≠ 0 → IsIntegral (Algebra.adjoin k {t}) x →
  IsIntegral (Algebra.adjoin k {t⁻¹, (Polynomial.aeval t⁻¹ h)⁻¹}) x → IsIntegral (Algebra.adjoin k {t⁻¹}) x

theorem LeafOrdInfHom_of (hO : LeafOrdInfLocal) (hG : LeafLocGlobInf) : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 →
    IsIntegral (Algebra.adjoin k {(algebraMap B (FractionRing B) (g Polynomial.X))⁻¹})
      (algebraMap B (FractionRing B) (u : B)) := by
  intro k B _ _ _ _ _ _ g hg hf
  obtain ⟨n, φ, hφ⟩ := hO k B g hg hf
  refine ⟨n, φ, fun u hu => ?_⟩
  obtain ⟨h, h0, hloc⟩ := hφ u hu
  set L := FractionRing B
  set T : L := algebraMap B L (g Polynomial.X)
  have hinjL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  let G : Polynomial k →ₐ[k] L := (IsScalarTower.toAlgHom k B L).comp g
  have hG' : Function.Injective G := hinjL.comp hg
  have hT : Transcendental k T := by
    intro ⟨p, hp0, hp⟩
    apply hp0
    apply hG'
    rw [map_zero]
    have : G p = Polynomial.aeval T p := by
      rw [show G p = G (Polynomial.aeval Polynomial.X p) by simp, ← Polynomial.aeval_algHom_apply]; rfl
    rw [this]; exact hp
  have hint : IsIntegral (Algebra.adjoin k {T}) (algebraMap B L (u : B)) := by
    obtain ⟨p, hpm, hp⟩ := (RingHom.IsIntegral.of_finite hf) (u : B)
    let f : Polynomial k →ₐ[k] Algebra.adjoin k {T} := Polynomial.aeval ⟨T, Algebra.subset_adjoin rfl⟩
    have hfG : ((algebraMap (Algebra.adjoin k {T}) L).comp f.toRingHom) = (algebraMap B L).comp g.toRingHom := by
      have : (IsScalarTower.toAlgHom k (Algebra.adjoin k {T}) L).comp f = G := by
        apply Polynomial.algHom_ext; simp [f, G, T]
      exact congrArg AlgHom.toRingHom this
    refine ⟨p.map f.toRingHom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hfG, ← Polynomial.hom_eval₂]
    change algebraMap B L (Polynomial.eval₂ g.toRingHom (u : B) p) = 0
    rw [hp, map_zero]
  exact hG k L T hT _ h h0 hint hloc

open Polynomial

def lgiDen {k L : Type} [Field k] [Field L] [Algebra k L] (R : Subalgebra k L) (c : L) (hc : c ∈ R) :
    Subalgebra k L where
  carrier := {y | ∃ m : ℕ, c ^ m * y ∈ R}
  mul_mem' := by
    rintro y z ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    have : c ^ (m + n) * (y * z) = (c ^ m * y) * (c ^ n * z) := by ring
    rw [this]; exact R.mul_mem hm hn
  add_mem' := by
    rintro y z ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    have : c ^ (m + n) * (y + z) = c ^ n * (c ^ m * y) + c ^ m * (c ^ n * z) := by ring
    rw [this]; exact R.add_mem (R.mul_mem (R.pow_mem hc _) hm) (R.mul_mem (R.pow_mem hc _) hn)
  algebraMap_mem' := fun a => ⟨0, by simpa using R.algebraMap_mem a⟩

theorem lgi_adjoin_le {k L : Type} [Field k] [Field L] [Algebra k L] (s c : L) (hc : c ∈ Algebra.adjoin k {s})
    (hc0 : c ≠ 0) : Algebra.adjoin k {s, c⁻¹} ≤ lgiDen (Algebra.adjoin k {s}) c hc := by
  rw [Algebra.adjoin_le_iff]
  rintro y (rfl | rfl)
  · exact ⟨0, by simpa using Algebra.subset_adjoin rfl⟩
  · exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hc0]; exact Subalgebra.one_mem _⟩

theorem lgi_mult {k L : Type} [Field k] [Field L] [Algebra k L] (s c : L) (hc : c ∈ Algebra.adjoin k {s})
    (hc0 : c ≠ 0) (x : L) (hx : IsIntegral (Algebra.adjoin k {s, c⁻¹}) x) :
    ∃ M : ℕ, IsIntegral (Algebra.adjoin k {s}) (c ^ M * x) := by
  set R := Algebra.adjoin k {s}
  set A := Algebra.adjoin k {s, c⁻¹}
  obtain ⟨p, hpm, hp⟩ := hx
  have hD : ∀ i, ∃ m : ℕ, c ^ m * (p.coeff i : L) ∈ R := fun i => lgi_adjoin_le s c hc hc0 (p.coeff i).2
  choose m hm using hD
  set M := ∑ i ∈ Finset.range (p.natDegree + 1), m i
  have hM : ∀ i, c ^ M * (p.coeff i : L) ∈ R := by
    intro i
    by_cases hi : i ≤ p.natDegree
    · have hle : m i ≤ M := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      rw [show M = (M - m i) + m i by omega, pow_add, mul_assoc]
      exact R.mul_mem (R.pow_mem hc _) (hm i)
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  set q : L[X] := C (c ^ M) * p.map (algebraMap A L)
  have hl : q ∈ lifts (algebraMap R L) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine ⟨⟨c ^ M * (p.coeff n : L), hM n⟩, ?_⟩
    show _ = (C (c ^ M) * p.map (algebraMap A L)).coeff n
    rw [coeff_C_mul, coeff_map]; rfl
  obtain ⟨Q, hQ0⟩ := hl
  have hQ : Q.map (algebraMap R L) = q := hQ0
  have hinj : Function.Injective (algebraMap R L) := Subtype.val_injective
  have hlc : (algebraMap R L) Q.leadingCoeff = c ^ M := by
    rw [← leadingCoeff_map_of_injective hinj, hQ]
    simp only [q, leadingCoeff_mul, leadingCoeff_C, (hpm.map (algebraMap A L)).leadingCoeff, mul_one]
  have hQx : aeval x Q = 0 := by
    rw [aeval_def, ← eval_map, hQ]
    simp only [q, eval_mul, eval_C, eval_map]
    rw [hp, mul_zero]
  refine ⟨M, ?_⟩
  have := isIntegral_leadingCoeff_smul Q x hQx
  rw [Algebra.smul_def, hlc] at this
  exact this

theorem lgi_mono {k L : Type} [Field k] [Field L] [Algebra k L] {S T : Subalgebra k L} (hST : S ≤ T) (x : L)
    (hx : IsIntegral S x) : IsIntegral T x := by
  obtain ⟨p, hm, hp⟩ := hx
  refine ⟨p.map (Subalgebra.inclusion hST).toRingHom, hm.map _, ?_⟩
  rw [eval₂_map]
  exact hp

theorem integral_over_inverse_transcendental_of_local_at_infinity_holds : LeafLocGlobInf := by
  intro k L _ _ _ t ht x h h0 hx hloc
  have ht0 : t ≠ 0 := by rintro rfl; exact ht isAlgebraic_zero
  set s := t⁻¹
  have hs' : Transcendental k s := fun hh => ht (by simpa [s] using hh.inv)
  set R := Algebra.adjoin k {s}
  have hsR : s ∈ R := Algebra.subset_adjoin rfl
  have hs0 : s ≠ 0 := inv_ne_zero ht0

  have h1 : IsIntegral (Algebra.adjoin k {s, s⁻¹}) x := by
    refine lgi_mono ?_ x hx
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact Algebra.subset_adjoin (by simp [s])
  obtain ⟨M1, hM1⟩ := lgi_mult s s hsR hs0 x h1
  have hcR : aeval s h ∈ R := Polynomial.aeval_mem_adjoin_singleton k s
  have hh0 : h ≠ 0 := by rintro rfl; simp at h0
  have hc0 : aeval s h ≠ 0 := fun e => hs' ⟨h, hh0, e⟩
  obtain ⟨M2, hM2⟩ := lgi_mult s (aeval s h) hcR hc0 x hloc
  have hcop : IsCoprime ((X : k[X]) ^ M1) (h ^ M2) := by
    apply IsCoprime.pow
    rw [Irreducible.coprime_iff_not_dvd irreducible_X, X_dvd_iff, coeff_zero_eq_eval_zero]
    exact h0
  obtain ⟨a, b, hab⟩ := hcop
  have hab' : aeval s a * s ^ M1 + aeval s b * (aeval s h) ^ M2 = 1 := by
    have := congrArg (aeval s) hab
    simpa using this
  have hxe : x = aeval s a * (s ^ M1 * x) + aeval s b * ((aeval s h) ^ M2 * x) := by
    linear_combination (-x) * hab'
  have hA : ∀ f : k[X], IsIntegral R (aeval s f) := fun f => by
    have : aeval s f ∈ R := Polynomial.aeval_mem_adjoin_singleton k s
    exact isIntegral_algebraMap (x := (⟨_, this⟩ : R))
  rw [hxe]
  exact ((hA a).mul hM1).add ((hA b).mul hM2)

theorem LeafOrdInfHom_of_local (hO : LeafOrdInfLocal) : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 →
    IsIntegral (Algebra.adjoin k {(algebraMap B (FractionRing B) (g Polynomial.X))⁻¹})
      (algebraMap B (FractionRing B) (u : B)) :=
  LeafOrdInfHom_of hO integral_over_inverse_transcendental_of_local_at_infinity_holds

end LateralTheory.E.E4
