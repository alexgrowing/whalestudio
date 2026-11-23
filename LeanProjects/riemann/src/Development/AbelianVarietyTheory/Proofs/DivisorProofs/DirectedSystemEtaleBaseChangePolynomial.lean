import Mathlib
open IsLocalRing Polynomial TensorProduct

namespace GlobalTheory

theorem tensor_directedSystem_of_flat (R : Type) [CommRing R] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] (k₀ : ι) (P : ι → Type) [∀ k, CommRing (P k)]
    [instP : ∀ k, Algebra R (P k)] (Q : Type) [CommRing Q] [Algebra R Q]
    (E₀ : Type) [CommRing E₀] [Algebra R E₀] [Module.Flat R E₀]
    (inc : ∀ k l, k ≤ l → P k →ₐ[R] P l) (sub : ∀ k, P k →ₐ[R] Q)
    (hinc_id : ∀ k (hkk : k ≤ k) (p : P k), inc k k hkk p = p)
    (hinc_comp : ∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (p : P k),
      inc k m hkm p = inc l m hlm (inc k l hkl p))
    (hsub_comp : ∀ k l (hkl : k ≤ l) (p : P k), sub l (inc k l hkl p) = sub k p)
    (hsub_inj : ∀ k, Function.Injective (sub k))
    (hcov : ∀ q : Q, ∃ k p, sub k p = q) :
    ∃ (h : ∀ k l, k ≤ l → P k ⊗[R] E₀ →+* P l ⊗[R] E₀) (e : ∀ k, P k ⊗[R] E₀ →+* Q ⊗[R] E₀),
      (∀ k l (hkl : k ≤ l) (p : P k) (y : E₀), h k l hkl (p ⊗ₜ y) = inc k l hkl p ⊗ₜ y) ∧
      (∀ k (p : P k) (y : E₀), e k (p ⊗ₜ y) = sub k p ⊗ₜ y) ∧
      (∀ k l (hkl : k ≤ l) (y : P k ⊗[R] E₀), e l (h k l hkl y) = e k y) ∧
      (∀ k (hkk : k ≤ k) (y : P k ⊗[R] E₀), h k k hkk y = y) ∧
      (∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (y : P k ⊗[R] E₀),
          h k m hkm y = h l m hlm (h k l hkl y)) ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ z : Q ⊗[R] E₀, ∃ k y, e k y = z) := by
  let h : ∀ k l, k ≤ l → P k ⊗[R] E₀ →+* P l ⊗[R] E₀ := fun k l hkl =>
    (Algebra.TensorProduct.map (inc k l hkl) (AlgHom.id R E₀)).toRingHom
  let e : ∀ k, P k ⊗[R] E₀ →+* Q ⊗[R] E₀ := fun k =>
    (Algebra.TensorProduct.map (sub k) (AlgHom.id R E₀)).toRingHom
  have hh : ∀ k l (hkl : k ≤ l) (p : P k) (y : E₀), h k l hkl (p ⊗ₜ y) = inc k l hkl p ⊗ₜ y :=
    fun k l hkl p y => by simp [h]
  have he : ∀ k (p : P k) (y : E₀), e k (p ⊗ₜ y) = sub k p ⊗ₜ y :=
    fun k p y => by simp [e]
  have hcompat : ∀ k l (hkl : k ≤ l) (y : P k ⊗[R] E₀), e l (h k l hkl y) = e k y := by
    intro k l hkl y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p z => rw [hh, he, he, hsub_comp]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  refine ⟨h, e, hh, he, hcompat, ?_, ?_, ?_, ?_⟩
  · intro k hkk y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p z => rw [hh, hinc_id]
    | add a b ha hb => rw [map_add, ha, hb]
  · intro k l m hkl hlm hkm y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p z => rw [hh, hh, hh, hinc_comp k l m hkl hlm hkm]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  · intro k
    have hfun : ⇑(e k) = ⇑(LinearMap.rTensor E₀ (sub k).toLinearMap) := by
      funext z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul p y => rw [he, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
      | add a b ha hb => rw [map_add, map_add, ha, hb]
    rw [hfun]
    exact Module.Flat.rTensor_preserves_injective_linearMap _ (hsub_inj k)
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨k₀, 0, map_zero _⟩
    | tmul q y =>
      obtain ⟨k, p, rfl⟩ := hcov q
      exact ⟨k, p ⊗ₜ y, he k p y⟩
    | add a b ha hb =>
      obtain ⟨k₁, y₁, rfl⟩ := ha
      obtain ⟨k₂, y₂, rfl⟩ := hb
      obtain ⟨m, h₁, h₂⟩ := directed_of (· ≤ ·) k₁ k₂
      exact ⟨m, h k₁ m h₁ y₁ + h k₂ m h₂ y₂, by rw [map_add, hcompat, hcompat]⟩

theorem directedSystem_etaleBaseChange : ∀ (T : Type) [CommRing T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T) (hA : Monotone 𝒜), (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (i₀ : ι), (∀ k, i₀ ≤ k) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E]
      (E₀ : Type) [CommRing E₀] [Algebra (Polynomial (𝒜 i₀)) E₀] [Algebra.Etale (Polynomial (𝒜 i₀)) E₀],
      (letI : Algebra (Polynomial (𝒜 i₀)) (Polynomial T) :=
          (Polynomial.mapRingHom (𝒜 i₀).subtype).toAlgebra
       Nonempty (TensorProduct (Polynomial (𝒜 i₀)) (Polynomial T) E₀ ≃ₐ[Polynomial T] E)) →
    ∃ (Ek : ι → Type) (_ : ∀ k, CommRing (Ek k)) (_ : ∀ k, Algebra (Polynomial (𝒜 k)) (Ek k))
      (_ : ∀ k, Algebra (𝒜 k) (Ek k)) (_ : ∀ k, IsScalarTower (𝒜 k) (Polynomial (𝒜 k)) (Ek k))
      (_ : ∀ k, Algebra.Etale (Polynomial (𝒜 k)) (Ek k))
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k, (e k).comp (algebraMap (Polynomial (𝒜 k)) (Ek k)) =
          (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 k).subtype)) ∧
      (∀ k l (hkl : k ≤ l) (a : 𝒜 k), h k l hkl (algebraMap (𝒜 k) (Ek k) a) =
          algebraMap (𝒜 l) (Ek l) (Subring.inclusion (hA hkl) a)) ∧
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) ∧
      (∀ k (hkk : k ≤ k) (y : Ek k), h k k hkk y = y) ∧
      (∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (y : Ek k),
          h k m hkm y = h l m hlm (h k l hkl y)) ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ x : E, ∃ k y, e k y = x) := by
  intro T _ ι _ _ 𝒜 hA hcov i₀ h₀ E _ _ E₀ _ _ _ hφ
  obtain ⟨φ⟩ := hφ
  letI instA : ∀ k, Algebra (𝒜 i₀)[X] (𝒜 k)[X] := fun k =>
    (mapRingHom (Subring.inclusion (hA (h₀ k)))).toAlgebra
  letI instT : Algebra (𝒜 i₀)[X] T[X] := (mapRingHom (𝒜 i₀).subtype).toAlgebra
  have hincl : ∀ {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c),
      (Subring.inclusion (hA hbc)).comp (Subring.inclusion (hA hab)) =
        Subring.inclusion (hA (hab.trans hbc)) := by
    intro a b c hab hbc; ext x; rfl
  have hsub : ∀ {a b : ι} (hab : a ≤ b),
      (𝒜 b).subtype.comp (Subring.inclusion (hA hab)) = (𝒜 a).subtype := by
    intro a b hab; ext x; rfl
  let inc : ∀ k l, k ≤ l → (𝒜 k)[X] →ₐ[(𝒜 i₀)[X]] (𝒜 l)[X] := fun k l hkl =>
    { toRingHom := mapRingHom (Subring.inclusion (hA hkl))
      commutes' := fun p => by
        change Polynomial.map _ (Polynomial.map _ p) = Polynomial.map _ p
        rw [Polynomial.map_map, hincl (h₀ k) hkl] }
  let sub : ∀ k, (𝒜 k)[X] →ₐ[(𝒜 i₀)[X]] T[X] := fun k =>
    { toRingHom := mapRingHom (𝒜 k).subtype
      commutes' := fun p => by
        change Polynomial.map _ (Polynomial.map _ p) = Polynomial.map _ p
        rw [Polynomial.map_map, hsub (h₀ k)] }
  haveI : Module.Flat (𝒜 i₀)[X] E₀ := inferInstance
  have hcovT : ∀ q : T[X], ∃ k p, sub k p = q := by
    intro q
    have hq : ∃ k, ∀ n, q.coeff n ∈ 𝒜 k := by
      induction q using Polynomial.induction_on' with
      | add p q hp hq =>
        obtain ⟨k₁, h₁⟩ := hp
        obtain ⟨k₂, h₂⟩ := hq
        obtain ⟨m, hm₁, hm₂⟩ := directed_of (· ≤ ·) k₁ k₂
        exact ⟨m, fun n => by
          rw [coeff_add]; exact add_mem (hA hm₁ (h₁ n)) (hA hm₂ (h₂ n))⟩
      | monomial n c =>
        obtain ⟨j, hj⟩ := hcov c
        refine ⟨j, fun m => ?_⟩
        rw [coeff_monomial]
        split_ifs
        · exact hj
        · exact zero_mem _
    obtain ⟨k, hk⟩ := hq
    have hsubset : (↑q.coeffs : Set T) ⊆ 𝒜 k := by
      intro c hc
      obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
      exact hk n
    refine ⟨k, q.toSubring (𝒜 k) hsubset, ?_⟩
    show Polynomial.map (𝒜 k).subtype _ = q
    exact Polynomial.map_toSubring _ _ _
  obtain ⟨h, e', hh, he, hcompat, hid, hcomp, hinj, hcov'⟩ :=
    tensor_directedSystem_of_flat (𝒜 i₀)[X] i₀ (fun k => (𝒜 k)[X]) (instP := instA) T[X] E₀ inc sub
      (fun k hkk p => by
        have hid : Subring.inclusion (hA hkk) = RingHom.id _ := by ext; rfl
        show Polynomial.map _ p = p
        rw [hid, Polynomial.map_id])
      (fun k l m hkl hlm hkm p => by
        show Polynomial.map _ p = Polynomial.map _ (Polynomial.map _ p)
        rw [Polynomial.map_map, hincl hkl hlm])
      (fun k l hkl p => by
        show Polynomial.map _ (Polynomial.map _ p) = Polynomial.map _ p
        rw [Polynomial.map_map, hsub hkl])
      (fun k p q hpq => Polynomial.map_injective _ Subtype.val_injective hpq)
      hcovT
  let instC : ∀ k, Algebra (𝒜 k) (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀) := fun k =>
    ((algebraMap (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀)).comp (Polynomial.C)).toAlgebra
  have instS : ∀ k, @IsScalarTower (𝒜 k) (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀) _ _
      (instC k).toSMul := fun k =>
    letI := instC k
    IsScalarTower.of_algebraMap_eq (fun a => by
        change (algebraMap (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀)) (Polynomial.C a) =
          (algebraMap (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀)) (algebraMap (𝒜 k) (𝒜 k)[X] a)
        rw [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply])
  refine ⟨fun k => TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀, fun k => inferInstance,
    fun k => inferInstance, instC, instS, fun k => inferInstance,
    fun k => φ.toRingHom.comp (e' k), h, ?_, ?_, ?_, hid, hcomp, ?_, ?_⟩
  · intro k
    refine RingHom.ext fun p => ?_
    show φ (e' k (p ⊗ₜ 1)) = algebraMap T[X] E (Polynomial.map (𝒜 k).subtype p)
    rw [he, ← φ.commutes]
    rfl
  · intro k l hkl a
    show h k l hkl (C a ⊗ₜ 1) = C (Subring.inclusion (hA hkl) a) ⊗ₜ 1
    rw [hh]
    show Polynomial.map _ (C a) ⊗ₜ 1 = _
    rw [Polynomial.map_C]
  · intro k l hkl y
    exact congrArg φ (hcompat k l hkl y)
  · intro k
    exact φ.injective.comp (hinj k)
  · intro x
    obtain ⟨k, y, hy⟩ := hcov' (φ.symm x)
    refine ⟨k, y, ?_⟩
    show φ (e' k y) = x
    rw [hy, AlgEquiv.apply_symm_apply]

end GlobalTheory
