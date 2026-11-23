import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

variable (k : Type*) [CommRing k] (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S₁ : Type*) [CommRing S₁] [Algebra k S₁] [Algebra (MvPolynomial ι k) S₁]
  [IsScalarTower k (MvPolynomial ι k) S₁] [Algebra.FormallyEtale (MvPolynomial ι k) S₁]
  (φ : S →ₐ[k] S₁) (T : Finset ι) (s : ι)

theorem partialDeriv_map_of_mem
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (i : ι) (hiT : i ∈ T) (his : i ≠ s) (f : S) :
    partialDeriv k ι S₁ i (φ f)
      = coord k ι S₁ s * φ (partialDeriv k ι S i f) := by
  let _ : Algebra S S₁ := φ.toRingHom.toAlgebra
  have : IsScalarTower k S S₁ := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show algebraMap k S₁ x = φ (algebraMap k S x)
    exact (φ.commutes x).symm
  have hsmul : ∀ (a : S) (z : S₁), a • z = φ a * z := fun _ _ => rfl
  let L₁ : S →ₗ[k] S₁ := (partialDeriv k ι S₁ i).toLinearMap.comp φ.toLinearMap
  let L₂ : S →ₗ[k] S₁ :=
    (LinearMap.mulLeft k (coord k ι S₁ s)).comp
      (φ.toLinearMap.comp (partialDeriv k ι S i).toLinearMap)
  have h₁ : ∀ a b : S, L₁ (a * b) = a • L₁ b + b • L₁ a := by
    intro a b
    show partialDeriv k ι S₁ i (φ (a * b))
        = a • partialDeriv k ι S₁ i (φ b) + b • partialDeriv k ι S₁ i (φ a)
    simp only [hsmul, map_mul, (partialDeriv k ι S₁ i).leibniz, smul_eq_mul]
  have h₂ : ∀ a b : S, L₂ (a * b) = a • L₂ b + b • L₂ a := by
    intro a b
    show coord k ι S₁ s * φ (partialDeriv k ι S i (a * b))
        = a • (coord k ι S₁ s * φ (partialDeriv k ι S i b))
          + b • (coord k ι S₁ s * φ (partialDeriv k ι S i a))
    simp only [hsmul, (partialDeriv k ι S i).leibniz, smul_eq_mul, map_add, map_mul]
    ring
  have hD : Derivation.mk' L₁ h₁ = Derivation.mk' L₂ h₂ := by
    refine derivation_ext_of_coord k ι S S₁ _ _ ?_
    intro j
    show partialDeriv k ι S₁ i (φ (coord k ι S j))
        = coord k ι S₁ s * φ (partialDeriv k ι S i (coord k ι S j))
    by_cases hjT : j ∈ T
    · by_cases hjs : j = s
      · subst hjs
        rw [hs]
        simp only [partialDeriv_coord, if_neg his, map_zero, mul_zero]
      · rw [hin j hjT hjs, (partialDeriv k ι S₁ i).leibniz]
        simp only [smul_eq_mul, partialDeriv_coord, if_neg his, mul_zero, zero_add]
        by_cases hij : i = j
        · simp [hij]
        · simp [hij]
    · rw [hout j hjT]
      have hij : i ≠ j := by rintro rfl; exact hjT hiT
      simp only [partialDeriv_coord, if_neg hij, map_zero, mul_zero]
  exact DFunLike.congr_fun hD f

theorem partialDeriv_map_of_notMem
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (i : ι) (hiT : i ∉ T) (f : S) :
    partialDeriv k ι S₁ i (φ f) = φ (partialDeriv k ι S i f) := by
  let _ : Algebra S S₁ := φ.toRingHom.toAlgebra
  have halg : ∀ x : S, algebraMap S S₁ x = φ x := fun x => rfl
  have : IsScalarTower k S S₁ :=
    IsScalarTower.of_algebraMap_eq fun x => by rw [halg]; exact (φ.commutes x).symm
  have hsmul : ∀ (a : S) (x : S₁), a • x = φ a * x := by
    intro a x
    rw [Algebra.smul_def, halg]
  have his : i ≠ s := fun h => hiT (by rw [h]; exact hsT)
  have h₁ : ∀ a b : S,
      ((partialDeriv k ι S₁ i).toLinearMap.comp (φ.toLinearMap : S →ₗ[k] S₁)) (a * b)
        = a • ((partialDeriv k ι S₁ i).toLinearMap.comp (φ.toLinearMap : S →ₗ[k] S₁)) b
          + b • ((partialDeriv k ι S₁ i).toLinearMap.comp (φ.toLinearMap : S →ₗ[k] S₁)) a := by
    intro a b
    show partialDeriv k ι S₁ i (φ (a * b))
        = a • partialDeriv k ι S₁ i (φ b) + b • partialDeriv k ι S₁ i (φ a)
    rw [map_mul, Derivation.leibniz]
    simp only [hsmul, smul_eq_mul]
  have h₂ : ∀ a b : S,
      ((φ.toLinearMap : S →ₗ[k] S₁).comp (partialDeriv k ι S i).toLinearMap) (a * b)
        = a • ((φ.toLinearMap : S →ₗ[k] S₁).comp (partialDeriv k ι S i).toLinearMap) b
          + b • ((φ.toLinearMap : S →ₗ[k] S₁).comp (partialDeriv k ι S i).toLinearMap) a := by
    intro a b
    show φ (partialDeriv k ι S i (a * b))
        = a • φ (partialDeriv k ι S i b) + b • φ (partialDeriv k ι S i a)
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, hsmul]
  have key :
      Derivation.mk' ((partialDeriv k ι S₁ i).toLinearMap.comp (φ.toLinearMap : S →ₗ[k] S₁)) h₁
        = Derivation.mk' ((φ.toLinearMap : S →ₗ[k] S₁).comp
            (partialDeriv k ι S i).toLinearMap) h₂ := by
    refine derivation_ext_of_coord k ι S S₁ _ _ ?_
    intro j
    show partialDeriv k ι S₁ i (φ (coord k ι S j)) = φ (partialDeriv k ι S i (coord k ι S j))
    by_cases hj : j ∈ T
    · by_cases hjs : j = s
      · rw [hjs, hs, partialDeriv_coord_of_ne k ι S₁ i s his,
          partialDeriv_coord_of_ne k ι S i s his, map_zero]
      · have hij : i ≠ j := fun h => hiT (by rw [h]; exact hj)
        rw [hin j hj hjs, Derivation.leibniz, partialDeriv_coord_of_ne k ι S₁ i s his,
          partialDeriv_coord_of_ne k ι S₁ i j hij, partialDeriv_coord_of_ne k ι S i j hij,
          smul_zero, smul_zero, add_zero, map_zero]
    · rw [hout j hj, partialDeriv_coord, partialDeriv_coord]
      split_ifs with h
      · exact (map_one φ).symm
      · exact (map_zero φ).symm
  exact DFunLike.congr_fun key f

theorem coord_mul_partialDeriv_map_eq_map_sum
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (f : S) :
    coord k ι S₁ s * partialDeriv k ι S₁ s (φ f)
      = φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i f) := by
  let _ : Algebra S S₁ := φ.toRingHom.toAlgebra
  have : IsScalarTower k S S₁ :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have hsmul : ∀ (a : S) (z : S₁), a • z = φ a * z := fun a z => Algebra.smul_def a z
  have hsum_add : ∀ x y : S,
      (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (x + y))
        = (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
          + (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i y) := by
    intro x y
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, mul_add]
  have hsum_smul : ∀ (c : k) (x : S),
      (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (c • x))
        = c • (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x) := by
    intro c x
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.map_smul, mul_smul_comm]
  have hsum_leib : ∀ a b : S,
      (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (a * b))
        = a * (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i b)
          + b * (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i a) := by
    intro a b
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  let L₁ : S →ₗ[k] S₁ :=
    { toFun := fun x => coord k ι S₁ s * partialDeriv k ι S₁ s (φ x)
      map_add' := by
        intro x y
        show coord k ι S₁ s * partialDeriv k ι S₁ s (φ (x + y))
          = coord k ι S₁ s * partialDeriv k ι S₁ s (φ x)
            + coord k ι S₁ s * partialDeriv k ι S₁ s (φ y)
        rw [map_add, map_add, mul_add]
      map_smul' := by
        intro c x
        show coord k ι S₁ s * partialDeriv k ι S₁ s (φ (c • x))
          = c • (coord k ι S₁ s * partialDeriv k ι S₁ s (φ x))
        rw [map_smul, Derivation.map_smul, mul_smul_comm] }
  let L₂ : S →ₗ[k] S₁ :=
    { toFun := fun x => φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
      map_add' := by
        intro x y
        show φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (x + y))
          = φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
            + φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i y)
        rw [hsum_add, map_add]
      map_smul' := by
        intro c x
        show φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (c • x))
          = c • φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
        rw [hsum_smul, map_smul] }
  have hleib1 : ∀ a b : S, L₁ (a * b) = a • L₁ b + b • L₁ a := by
    intro a b
    show coord k ι S₁ s * partialDeriv k ι S₁ s (φ (a * b))
      = a • (coord k ι S₁ s * partialDeriv k ι S₁ s (φ b))
        + b • (coord k ι S₁ s * partialDeriv k ι S₁ s (φ a))
    rw [map_mul, Derivation.leibniz, hsmul a, hsmul b]
    simp only [smul_eq_mul]
    ring
  have hleib2 : ∀ a b : S, L₂ (a * b) = a • L₂ b + b • L₂ a := by
    intro a b
    show φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (a * b))
      = a • φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i b)
        + b • φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i a)
    rw [hsum_leib, map_add, map_mul, map_mul, hsmul a, hsmul b]
  have hD : Derivation.mk' L₁ hleib1 = Derivation.mk' L₂ hleib2 := by
    refine derivation_ext_of_coord k ι S S₁ _ _ fun j => ?_
    show coord k ι S₁ s * partialDeriv k ι S₁ s (φ (coord k ι S j))
      = φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (coord k ι S j))
    have hsum : (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (coord k ι S j))
        = if j ∈ T then coord k ι S j else 0 := by
      have hterm : ∀ i ∈ T, coord k ι S i * partialDeriv k ι S i (coord k ι S j)
          = if i = j then coord k ι S j else 0 := by
        intro i _
        rw [partialDeriv_coord]
        by_cases h : i = j
        · subst h
          simp
        · simp [h]
      rw [Finset.sum_congr rfl hterm]
      by_cases hj : j ∈ T
      · rw [Finset.sum_eq_single j]
        · simp [hj]
        · intro i _ hij
          rw [if_neg hij]
        · intro h
          exact absurd hj h
      · rw [if_neg hj]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hij : i ≠ j := by
          rintro rfl
          exact hj hi
        rw [if_neg hij]
    rw [hsum]
    by_cases hjs : j = s
    · subst hjs
      rw [hs, if_pos hsT, hs, partialDeriv_coord_self, mul_one]
    · by_cases hjT : j ∈ T
      · have h1 : partialDeriv k ι S₁ s (coord k ι S₁ s) = 1 :=
          partialDeriv_coord_self k ι S₁ s
        have h2 : partialDeriv k ι S₁ s (coord k ι S₁ j) = 0 :=
          partialDeriv_coord_of_ne k ι S₁ s j (Ne.symm hjs)
        rw [if_pos hjT, hin j hjT hjs, Derivation.leibniz, h1, h2]
        simp only [smul_eq_mul]
        ring
      · have hne : s ≠ j := by
          rintro rfl
          exact hjT hsT
        rw [if_neg hjT, map_zero, hout j hjT,
          partialDeriv_coord_of_ne k ι S₁ s j hne, mul_zero]
  exact DFunLike.congr_fun hD f

theorem coord_mul_partialDeriv_map_eq_map_add_sum_erase
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (f : S) :
    coord k ι S₁ s * partialDeriv k ι S₁ s (φ f)
      = φ (coord k ι S s * partialDeriv k ι S s f
          + ∑ i ∈ T.erase s, coord k ι S i * partialDeriv k ι S i f) := by
  rw [coord_mul_partialDeriv_map_eq_map_sum k ι S S₁ φ T s hin hs hout hsT f]
  refine congrArg φ ?_
  exact (Finset.add_sum_erase T (fun i => coord k ι S i * partialDeriv k ι S i f) hsT).symm

theorem map_partialDeriv_eq_pow_mul_of_mem
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (i : ι) (hiT : i ∈ T) (his : i ≠ s)
    (f : S) (g : S₁) (e : ℕ) (hfg : φ f = coord k ι S₁ s ^ (e + 1) * g) :
    φ (partialDeriv k ι S i f) = coord k ι S₁ s ^ e * partialDeriv k ι S₁ i g := by
  have h1 : partialDeriv k ι S₁ i (φ f)
      = coord k ι S₁ s * φ (partialDeriv k ι S i f) :=
    partialDeriv_map_of_mem k ι S S₁ φ T s hin hs hout i hiT his f
  have hy : partialDeriv k ι S₁ i (coord k ι S₁ s) = 0 :=
    partialDeriv_coord_of_ne k ι S₁ i s his
  have hpow : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (e + 1)) = 0 := by
    rw [Derivation.leibniz_pow, hy, smul_zero, smul_zero]
  rw [hfg, Derivation.leibniz, hpow, smul_zero, add_zero, smul_eq_mul] at h1
  have key : (φ (partialDeriv k ι S i f)
      - coord k ι S₁ s ^ e * partialDeriv k ι S₁ i g) * coord k ι S₁ s = 0 := by
    linear_combination -h1
  have h3 : φ (partialDeriv k ι S i f)
      - coord k ι S₁ s ^ e * partialDeriv k ι S₁ i g = 0 :=
    (mem_nonZeroDivisors_iff.mp hnzd).2 _ key
  linear_combination h3

theorem map_partialDeriv_eq_pow_mul_of_notMem
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (i : ι) (hiT : i ∉ T)
    (f : S) (g : S₁) (e : ℕ) (hfg : φ f = coord k ι S₁ s ^ (e + 1) * g) :
    φ (partialDeriv k ι S i f) = coord k ι S₁ s ^ (e + 1) * partialDeriv k ι S₁ i g := by
  have his : i ≠ s := fun h => hiT (by rw [h]; exact hsT)
  have hz : partialDeriv k ι S₁ i (coord k ι S₁ s) = 0 :=
    partialDeriv_coord_of_ne k ι S₁ i s his
  have hpow : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (e + 1)) = 0 := by
    rw [Derivation.leibniz_pow, hz, smul_zero, smul_zero]
  rw [← partialDeriv_map_of_notMem k ι S S₁ φ T s hin hs hout hsT i hiT f, hfg,
    Derivation.leibniz, hpow, smul_zero, add_zero, smul_eq_mul]

theorem map_partialDeriv_self_eq_pow_mul
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (f : S) (g : S₁) (e : ℕ) (hfg : φ f = coord k ι S₁ s ^ (e + 1) * g) :
    φ (partialDeriv k ι S s f)
      = coord k ι S₁ s ^ e
        * (coord k ι S₁ s * partialDeriv k ι S₁ s g + ((e + 1 : ℕ) : S₁) * g
            - ∑ i ∈ T.erase s, coord k ι S₁ i * partialDeriv k ι S₁ i g) := by
  have hpow : partialDeriv k ι S₁ s (coord k ι S₁ s ^ (e + 1))
      = ((e + 1 : ℕ) : S₁) * coord k ι S₁ s ^ e := by
    rw [Derivation.leibniz_pow, partialDeriv_coord_self, Nat.add_sub_cancel]
    simp only [smul_eq_mul, mul_one, nsmul_eq_mul]
  have h2 : partialDeriv k ι S₁ s (φ f)
      = coord k ι S₁ s ^ (e + 1) * partialDeriv k ι S₁ s g
        + ((e + 1 : ℕ) : S₁) * coord k ι S₁ s ^ e * g := by
    rw [hfg, Derivation.leibniz, hpow]
    simp only [smul_eq_mul]
    ring
  have hsum2 : ∑ i ∈ T.erase s, φ (coord k ι S i * partialDeriv k ι S i f)
      = coord k ι S₁ s ^ (e + 1)
        * ∑ i ∈ T.erase s, coord k ι S₁ i * partialDeriv k ι S₁ i g := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiT : i ∈ T := Finset.mem_of_mem_erase hi
    have his : i ≠ s := Finset.ne_of_mem_erase hi
    rw [map_mul, hin i hiT his,
      map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd i hiT his f g e hfg]
    ring
  have h1 : coord k ι S₁ s * partialDeriv k ι S₁ s (φ f)
      = coord k ι S₁ s * φ (partialDeriv k ι S s f)
        + coord k ι S₁ s ^ (e + 1)
          * ∑ i ∈ T.erase s, coord k ι S₁ i * partialDeriv k ι S₁ i g := by
    rw [coord_mul_partialDeriv_map_eq_map_add_sum_erase k ι S S₁ φ T s hin hs hout hsT f, map_add, map_mul, hs, map_sum, hsum2]
  rw [h2] at h1
  have h0 : (φ (partialDeriv k ι S s f)
      - coord k ι S₁ s ^ e
        * (coord k ι S₁ s * partialDeriv k ι S₁ s g + ((e + 1 : ℕ) : S₁) * g
            - ∑ i ∈ T.erase s, coord k ι S₁ i * partialDeriv k ι S₁ i g))
      * coord k ι S₁ s = 0 := by
    linear_combination -h1
  have h3 := (mem_nonZeroDivisors_iff.mp hnzd).2 _ h0
  linear_combination h3

private theorem mul_mem_span_singleton_mul {R : Type*} [CommRing R] (a : R) (I : Ideal R)
    {g : R} (hg : g ∈ I) : a * g ∈ Ideal.span ({a} : Set R) * I :=
  Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl)) hg

private theorem finset_sum_smul_derivation_apply {k : Type*} [CommRing k] {S : Type*} [CommRing S]
    [Algebra k S] {ι : Type*} (t : Finset ι) (c : ι → S) (D : ι → Derivation k S S) (x : S) :
    (∑ i ∈ t, c i • D i) x = ∑ i ∈ t, c i * D i x := by
  refine Finset.cons_induction_on t ?_ ?_
  · simp
  · intro a u ha ih
    rw [Finset.sum_cons, Finset.sum_cons]
    simp [ih]

theorem map_derivIdeal_le_span_pow_mul [Fintype ι]
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (J : Ideal S) (J₁ : Ideal S₁) (m : ℕ) (hm : 1 ≤ m)
    (hJ : Ideal.map φ J ≤ Ideal.span {coord k ι S₁ s ^ m} * J₁) :
    Ideal.map φ (derivIdeal k J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - 1)} * derivIdeal k J₁ := by
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, m = e + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hmem : ∀ x ∈ J, ∃ g ∈ J₁, φ x = coord k ι S₁ s ^ (e + 1) * g := by
    intro x hx
    obtain ⟨g, hg, hgx⟩ := Ideal.mem_span_singleton_mul.1 (hJ (Ideal.mem_map_of_mem φ hx))
    exact ⟨g, hg, hgx.symm⟩
  have hkey : ∀ x ∈ J, ∀ i : ι,
      φ (partialDeriv k ι S i x) ∈ Ideal.span {coord k ι S₁ s ^ e} * derivIdeal k J₁ := by
    intro x hx i
    obtain ⟨g, hg, hgx⟩ := hmem x hx
    by_cases hiT : i ∈ T
    · by_cases his : i = s
      · have hbr : coord k ι S₁ s * partialDeriv k ι S₁ s g + ((e + 1 : ℕ) : S₁) * g
            - ∑ j ∈ T.erase s, coord k ι S₁ j * partialDeriv k ι S₁ j g
              ∈ derivIdeal k J₁ := by
          refine sub_mem (add_mem ?_ ?_) ?_
          · exact Ideal.mul_mem_left _ _
              (derivation_apply_mem_derivIdeal k J₁ (partialDeriv k ι S₁ s) hg)
          · exact Ideal.mul_mem_left _ _ (le_derivIdeal k J₁ hg)
          · refine sum_mem fun j _ => ?_
            exact Ideal.mul_mem_left _ _
              (derivation_apply_mem_derivIdeal k J₁ (partialDeriv k ι S₁ j) hg)
        rw [his, map_partialDeriv_self_eq_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd x g e hgx]
        exact mul_mem_span_singleton_mul _ _ hbr
      · rw [map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd i hiT his x g e hgx]
        exact mul_mem_span_singleton_mul _ _
          (derivation_apply_mem_derivIdeal k J₁ (partialDeriv k ι S₁ i) hg)
    · rw [map_partialDeriv_eq_pow_mul_of_notMem k ι S S₁ φ T s hin hs hout hsT i hiT x g e hgx,
        pow_succ, mul_assoc]
      exact mul_mem_span_singleton_mul _ _
        (Ideal.mul_mem_left _ _
          (derivation_apply_mem_derivIdeal k J₁ (partialDeriv k ι S₁ i) hg))
  rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨g, hg, hgx⟩ := hmem x hx
    refine Ideal.mem_comap.mpr ?_
    rw [hgx, pow_succ, mul_assoc]
    exact mul_mem_span_singleton_mul _ _
      (Ideal.mul_mem_left _ _ (le_derivIdeal k J₁ hg))
  · intro D x hx
    refine Ideal.mem_comap.mpr ?_
    have h1 : D x = (∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i) x :=
      congrArg (fun E : Derivation k S S => E x) (eq_sum_smul_partialDeriv k ι S D)
    have hDx : D x = ∑ i : ι, D (coord k ι S i) * partialDeriv k ι S i x := by
      rw [h1]
      exact finset_sum_smul_derivation_apply Finset.univ (fun i => D (coord k ι S i))
        (fun i => partialDeriv k ι S i) x
    rw [hDx, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (hkey x hx i)

theorem map_derivIdealIterate_le_span_pow_mul [Fintype ι]
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (J : Ideal S) (J₁ : Ideal S₁) (m : ℕ)
    (hJ : Ideal.map φ J ≤ Ideal.span {coord k ι S₁ s ^ m} * J₁)
    (j : ℕ) (hj : j ≤ m) :
    Ideal.map φ (derivIdealIterate k j J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - j)} * derivIdealIterate k j J₁ := by
  have key : ∀ r : ℕ, r ≤ m → Ideal.map φ (derivIdealIterate k r J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - r)} * derivIdealIterate k r J₁ := by
    intro r
    induction r with
    | zero =>
        intro _
        rw [derivIdealIterate_zero k J, derivIdealIterate_zero k J₁, Nat.sub_zero]
        exact hJ
    | succ r ih =>
        intro hr
        have hrm : r ≤ m := Nat.le_of_succ_le hr
        have h1 : 1 ≤ m - r := by omega
        have hstep := map_derivIdeal_le_span_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd
          (derivIdealIterate k r J) (derivIdealIterate k r J₁) (m - r) h1 (ih hrm)
        have hmm : m - r - 1 = m - (r + 1) := by omega
        rw [hmm] at hstep
        rw [derivIdealIterate_succ k r J, derivIdealIterate_succ k r J₁]
        exact hstep
  exact key j hj

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
