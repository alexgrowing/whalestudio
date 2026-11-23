import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
namespace FunctorialResolution.EmbeddedResolution
namespace DerivIdealBaseChange

open FunctorialResolution.EmbeddedResolution.EtaleCoordinates

private theorem apply_mem_of_forall_partialDeriv_mem {k : Type*} [CommRing k] {ι : Type*} [Finite ι]
    {S : Type*} [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (X : Set S) (K : Ideal S)
    (h : ∀ i : ι, ∀ x ∈ X, partialDeriv k ι S i x ∈ K)
    (D : Derivation k S S) {x : S} (hx : x ∈ X) : D x ∈ K := by
  classical
  let N : Submodule S (Derivation k S S) :=
    { carrier := {D : Derivation k S S | ∀ y ∈ X, D y ∈ K}
      add_mem' := by
        intro a b ha hb
        show ∀ y ∈ X, (a + b) y ∈ K
        intro y hy
        have hab : (a + b) y = a y + b y := rfl
        rw [hab]
        exact Ideal.add_mem K (ha y hy) (hb y hy)
      zero_mem' := by
        show ∀ y ∈ X, (0 : Derivation k S S) y ∈ K
        intro y _
        have h0 : (0 : Derivation k S S) y = 0 := rfl
        rw [h0]
        exact Ideal.zero_mem K
      smul_mem' := by
        intro c a ha
        show ∀ y ∈ X, (c • a) y ∈ K
        intro y hy
        have hc : (c • a) y = c * a y := rfl
        rw [hc]
        exact Ideal.mul_mem_left K _ (ha y hy) }
  have hspan : (⊤ : Submodule S (Derivation k S S)) ≤ N := by
    rw [← span_range_partialDeriv k ι S, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  have hDN : D ∈ N := hspan Submodule.mem_top
  exact hDN x hx

section

variable (k : Type*) [CommRing k] (L : Type*) [CommRing L] [Algebra k L]
  (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S' : Type*) [CommRing S'] [Algebra L S'] [Algebra (MvPolynomial ι L) S']
  [IsScalarTower L (MvPolynomial ι L) S'] [Algebra.FormallyEtale (MvPolynomial ι L) S']
  [Algebra k S'] [IsScalarTower k L S']

theorem partialDeriv_algHom_apply (φ : S →ₐ[k] S')
    (hφ : ∀ i : ι, φ (coord k ι S i) = coord L ι S' i) (i : ι) (f : S) :
    partialDeriv L ι S' i (φ f) = φ (partialDeriv k ι S i f) := by
  let _ : Algebra S S' := φ.toRingHom.toAlgebra
  have htow : IsScalarTower k S S' := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have hsmul : ∀ (s : S) (x : S'), s • x = φ s * x := fun _ _ => rfl
  have hφsmul : ∀ (c : k) (x : S), φ (c • x) = c • φ x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, φ.commutes]
  have hcomp : ∀ (c : k) (y : S'), c • y = (algebraMap k L c) • y := by
    intro c y
    rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply k L S']
  have hadd1 : ∀ x y : S', partialDeriv L ι S' i (x + y)
      = partialDeriv L ι S' i x + partialDeriv L ι S' i y :=
    fun x y => (partialDeriv L ι S' i).toLinearMap.map_add x y
  have hadd2 : ∀ x y : S, partialDeriv k ι S i (x + y)
      = partialDeriv k ι S i x + partialDeriv k ι S i y :=
    fun x y => (partialDeriv k ι S i).toLinearMap.map_add x y
  have hsm1 : ∀ (c : L) (y : S'), partialDeriv L ι S' i (c • y) = c • partialDeriv L ι S' i y :=
    fun c y => (partialDeriv L ι S' i).toLinearMap.map_smul c y
  have hsm2 : ∀ (c : k) (x : S), partialDeriv k ι S i (c • x) = c • partialDeriv k ι S i x :=
    fun c x => (partialDeriv k ι S i).toLinearMap.map_smul c x
  have hpsmul : ∀ (c : k) (y : S'),
      partialDeriv L ι S' i (c • y) = c • partialDeriv L ι S' i y := by
    intro c y
    rw [hcomp c y, hsm1, ← hcomp]
  let F₁ : S →ₗ[k] S' :=
    { toFun := fun s => partialDeriv L ι S' i (φ s)
      map_add' := by
        intro x y
        show partialDeriv L ι S' i (φ (x + y))
            = partialDeriv L ι S' i (φ x) + partialDeriv L ι S' i (φ y)
        rw [map_add, hadd1]
      map_smul' := by
        intro c x
        show partialDeriv L ι S' i (φ (c • x)) = c • partialDeriv L ι S' i (φ x)
        rw [hφsmul, hpsmul] }
  let F₂ : S →ₗ[k] S' :=
    { toFun := fun s => φ (partialDeriv k ι S i s)
      map_add' := by
        intro x y
        show φ (partialDeriv k ι S i (x + y))
            = φ (partialDeriv k ι S i x) + φ (partialDeriv k ι S i y)
        rw [hadd2, map_add]
      map_smul' := by
        intro c x
        show φ (partialDeriv k ι S i (c • x)) = c • φ (partialDeriv k ι S i x)
        rw [hsm2, hφsmul] }
  let D₁ : Derivation k S S' := Derivation.mk' F₁ (by
    intro a b
    show partialDeriv L ι S' i (φ (a * b))
        = a • partialDeriv L ι S' i (φ b) + b • partialDeriv L ι S' i (φ a)
    rw [map_mul, (partialDeriv L ι S' i).leibniz]
    simp only [hsmul, smul_eq_mul])
  let D₂ : Derivation k S S' := Derivation.mk' F₂ (by
    intro a b
    show φ (partialDeriv k ι S i (a * b))
        = a • φ (partialDeriv k ι S i b) + b • φ (partialDeriv k ι S i a)
    rw [(partialDeriv k ι S i).leibniz]
    simp only [hsmul, smul_eq_mul, map_add, map_mul])
  have hcoords : ∀ j : ι, D₁ (coord k ι S j) = D₂ (coord k ι S j) := by
    intro j
    show partialDeriv L ι S' i (φ (coord k ι S j)) = φ (partialDeriv k ι S i (coord k ι S j))
    rw [hφ j, partialDeriv_coord, partialDeriv_coord]
    split_ifs with hij
    · exact (map_one φ).symm
    · exact (map_zero φ).symm
  have hD : D₁ = D₂ := derivation_ext_of_coord k ι S S' D₁ D₂ hcoords
  exact DFunLike.congr_fun hD f

theorem map_derivIdeal_le [Fintype ι] (φ : S →ₐ[k] S')
    (hφ : ∀ i : ι, φ (coord k ι S i) = coord L ι S' i) (J : Ideal S) :
    Ideal.map φ (derivIdeal k J) ≤ derivIdeal L (Ideal.map φ J) := by
  rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
  constructor
  · intro y hy
    rw [Ideal.mem_comap]
    exact le_derivIdeal L (Ideal.map φ J) (Ideal.mem_map_of_mem φ hy)
  · intro D x hx
    have key : ∀ i : ι, ∀ y ∈ (J : Set S),
        partialDeriv k ι S i y ∈ Ideal.comap φ (derivIdeal L (Ideal.map φ J)) := by
      intro i y hy
      rw [Ideal.mem_comap,
        ← partialDeriv_algHom_apply (k := k) (L := L) (ι := ι) (S := S) (S' := S') φ hφ i y]
      exact derivation_apply_mem_derivIdeal L (Ideal.map φ J) (partialDeriv L ι S' i)
        (Ideal.mem_map_of_mem φ (show y ∈ J from hy))
    exact apply_mem_of_forall_partialDeriv_mem (ι := ι) (J : Set S)
      (Ideal.comap φ (derivIdeal L (Ideal.map φ J))) key D (show x ∈ (J : Set S) from hx)

theorem partialDeriv_mem_map_derivIdeal (φ : S →ₐ[k] S')
    (hφ : ∀ i : ι, φ (coord k ι S i) = coord L ι S' i) (i : ι) (J : Ideal S)
    {g : S'} (hg : g ∈ Ideal.map φ J) :
    partialDeriv L ι S' i g ∈ Ideal.map φ (derivIdeal k J) := by
  have hle : Ideal.map φ J ≤ Ideal.span (⇑φ '' (J : Set S)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap]
    exact Ideal.subset_span ⟨y, hy, rfl⟩
  have hGT : Ideal.span (⇑φ '' (J : Set S)) ≤ Ideal.map φ (derivIdeal k J) := by
    rw [Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact Ideal.mem_map_of_mem φ (le_derivIdeal k J (show y ∈ J from hy))
  have hD : ∀ z ∈ (⇑φ '' (J : Set S)),
      partialDeriv L ι S' i z ∈ Ideal.map φ (derivIdeal k J) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [partialDeriv_algHom_apply (k := k) (L := L) (ι := ι) (S := S) (S' := S') φ hφ i y]
    exact Ideal.mem_map_of_mem φ
      (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) (show y ∈ J from hy))
  exact derivation_apply_mem_of_mem_span (partialDeriv L ι S' i) hGT hD (hle hg)

theorem derivIdeal_map_le [Fintype ι] (φ : S →ₐ[k] S')
    (hφ : ∀ i : ι, φ (coord k ι S i) = coord L ι S' i) (J : Ideal S) :
    derivIdeal L (Ideal.map φ J) ≤ Ideal.map φ (derivIdeal k J) := by
  rw [derivIdeal_le_iff]
  refine ⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩
  intro D g hg
  have key : ∀ i : ι, ∀ y ∈ ((Ideal.map φ J : Ideal S') : Set S'),
      partialDeriv L ι S' i y ∈ Ideal.map φ (derivIdeal k J) := by
    intro i y hy
    exact partialDeriv_mem_map_derivIdeal (k := k) (L := L) (ι := ι) (S := S) (S' := S')
      φ hφ i J (show y ∈ Ideal.map φ J from hy)
  exact apply_mem_of_forall_partialDeriv_mem (ι := ι) ((Ideal.map φ J : Ideal S') : Set S')
    (Ideal.map φ (derivIdeal k J)) key D
    (show g ∈ ((Ideal.map φ J : Ideal S') : Set S') from hg)

theorem map_derivIdeal [Fintype ι] (φ : S →ₐ[k] S')
    (hφ : ∀ i : ι, φ (coord k ι S i) = coord L ι S' i) (J : Ideal S) :
    Ideal.map φ (derivIdeal k J) = derivIdeal L (Ideal.map φ J) :=
  le_antisymm
    (map_derivIdeal_le (k := k) (L := L) (ι := ι) (S := S) (S' := S') φ hφ J)
    (derivIdeal_map_le (k := k) (L := L) (ι := ι) (S := S) (S' := S') φ hφ J)

end

end DerivIdealBaseChange
end FunctorialResolution.EmbeddedResolution
