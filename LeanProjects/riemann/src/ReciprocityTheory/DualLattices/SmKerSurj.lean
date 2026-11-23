import ReciprocityTheory.DualLattices.NilSurjOfSqZero

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

section

variable {R' R : LAlg R₀} (π : LHom R' R) (ξ : (R' : Type u)) (hsurj : Function.Surjective π.1)

def ell (r : (R : Type u)) : (R' : Type u) := Function.surjInv hsurj r * ξ

end

section

variable {R' R : LAlg R₀} {π : LHom R' R} {ξ : (R' : Type u)}
  (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)

include hker in
lemma π_ξ : π.1 ξ = 0 := by
  have h : ξ ∈ RingHom.ker π.1 := by
    rw [hker]
    exact Ideal.mem_span_singleton_self ξ
  exact (RingHom.mem_ker).1 h

include hker hsq in
lemma ell_spec (a : (R' : Type u)) : ell π ξ hsurj (π.1 a) = a * ξ := by
  have h1 : π.1 (Function.surjInv hsurj (π.1 a)) = π.1 a := Function.surjInv_eq hsurj _
  have h2 : Function.surjInv hsurj (π.1 a) - a ∈ Ideal.span {ξ} := by
    rw [← hker, RingHom.mem_ker, map_sub, h1, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h2
  show Function.surjInv hsurj (π.1 a) * ξ = a * ξ
  have e : Function.surjInv hsurj (π.1 a) = a + c * ξ := by
    rw [hc]
    ring
  rw [e, add_mul, mul_assoc, hsq, mul_zero, add_zero]

include hker in
lemma ell_π (r : (R : Type u)) : π.1 (ell π ξ hsurj r) = 0 := by
  show π.1 (Function.surjInv hsurj r * ξ) = 0
  rw [map_mul, π_ξ hker, mul_zero]

include hker hsq in
lemma ell_add (r r' : (R : Type u)) :
    ell π ξ hsurj (r + r') = ell π ξ hsurj r + ell π ξ hsurj r' := by
  obtain ⟨a, rfl⟩ := hsurj r
  obtain ⟨a', rfl⟩ := hsurj r'
  rw [← map_add, ell_spec hsurj hker hsq, ell_spec hsurj hker hsq, ell_spec hsurj hker hsq, add_mul]

include hker hsq in
lemma ell_mul (a : (R' : Type u)) (r : (R : Type u)) :
    ell π ξ hsurj (π.1 a * r) = a * ell π ξ hsurj r := by
  obtain ⟨b, rfl⟩ := hsurj r
  rw [← map_mul, ell_spec hsurj hker hsq, ell_spec hsurj hker hsq, mul_assoc]

include hker hsq in
lemma ell_zero : ell π ξ hsurj 0 = 0 := by
  have h := ell_spec hsurj hker hsq 0
  rw [map_zero, zero_mul] at h
  exact h

include hker hsq in
lemma ell_mul_ell (r r' : (R : Type u)) : ell π ξ hsurj r * ell π ξ hsurj r' = 0 := by
  obtain ⟨a, rfl⟩ := hsurj r
  obtain ⟨b, rfl⟩ := hsurj r'
  rw [ell_spec hsurj hker hsq, ell_spec hsurj hker hsq]
  calc a * ξ * (b * ξ) = a * b * (ξ * ξ) := by ring
    _ = 0 := by rw [hsq, mul_zero]

end

section

variable {R' R : LAlg R₀} (π : LHom R' R) (Dp : DualPair R) (ξ : (R' : Type u))
  (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)

def smAlg : (FP π Dp.π : Type u) →ₐ[R₀] (R' : Type u) where
  toFun x := x.1.1 + ell π ξ hsurj (Dp.κ x.1.2)
  map_one' := by
    show (1 : (R' : Type u)) + ell π ξ hsurj (Dp.κ 1) = 1
    rw [Dp.κ_one, ell_zero hsurj hker hsq, add_zero]
  map_mul' x y := by
    show x.1.1 * y.1.1 + ell π ξ hsurj (Dp.κ (x.1.2 * y.1.2)) =
      (x.1.1 + ell π ξ hsurj (Dp.κ x.1.2)) * (y.1.1 + ell π ξ hsurj (Dp.κ y.1.2))
    rw [Dp.κ_mul, ← FP.mem π Dp.π x, ← FP.mem π Dp.π y, ell_add hsurj hker hsq,
      ell_mul hsurj hker hsq, ell_mul hsurj hker hsq]
    linear_combination (-1 : (R' : Type u)) *
      ell_mul_ell hsurj hker hsq (Dp.κ x.1.2) (Dp.κ y.1.2)
  map_zero' := by
    show (0 : (R' : Type u)) + ell π ξ hsurj (Dp.κ 0) = 0
    rw [Dp.κ_zero, ell_zero hsurj hker hsq, add_zero]
  map_add' x y := by
    show (x.1.1 + y.1.1) + ell π ξ hsurj (Dp.κ (x.1.2 + y.1.2)) =
      (x.1.1 + ell π ξ hsurj (Dp.κ x.1.2)) + (y.1.1 + ell π ξ hsurj (Dp.κ y.1.2))
    rw [Dp.κ_add, ell_add hsurj hker hsq]; ring
  commutes' c := by
    show algebraMap R₀ (R' : Type u) c + ell π ξ hsurj (Dp.κ (algebraMap R₀ (Dp.D : Type u) c)) =
      algebraMap R₀ (R' : Type u) c
    rw [Dp.κ_algebraMap, ell_zero hsurj hker hsq, add_zero]

def sm : LHom (FP π Dp.π) R' :=
  ⟨smAlg π Dp ξ hsurj hker hsq, ⟨fun x hx => fp_isUnit π Dp.π x (π.2.map_nonunit _ (by
    convert hx.map π.1 using 1
    show _ = π.1 (x.1.1 + ell π ξ hsurj (Dp.κ x.1.2))
    rw [map_add, ell_π hsurj hker, add_zero]; rfl))⟩⟩

lemma π_comp_sm : π.comp (sm π Dp ξ hsurj hker hsq) = π.comp (FP.p₁ π Dp.π) := by
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  show π.1 (x.1.1 + ell π ξ hsurj (Dp.κ x.1.2)) = π.1 x.1.1
  rw [map_add, ell_π hsurj hker, add_zero]

end

section

variable {R' R : LAlg R₀} (π : LHom R' R) (Dp : DualPair R)

def ι₁ : LHom R' (FP π Dp.π) :=
  FP.lift π Dp.π (LHom.id R') (Dp.σ.comp π) (fun t => (Dp.sect (π.1 t)).symm)

lemma p₁_comp_ι₁ : (FP.p₁ π Dp.π).comp (ι₁ π Dp) = LHom.id R' := Subtype.ext (AlgHom.ext fun _ => rfl)

lemma p₂_comp_ι₁ : (FP.p₂ π Dp.π).comp (ι₁ π Dp) = Dp.σ.comp π := Subtype.ext (AlgHom.ext fun _ => rfl)

lemma sm_comp_ι₁ {ξ : (R' : Type u)} (hsurj : Function.Surjective π.1)
    (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0) :
    (sm π Dp ξ hsurj hker hsq).comp (ι₁ π Dp) = LHom.id R' := by
  apply Subtype.ext
  apply AlgHom.ext
  intro t
  show t + ell π ξ hsurj (Dp.κ (Dp.σ.1 (π.1 t))) = t
  rw [Dp.κ_σ, ell_zero hsurj hker hsq, add_zero]

lemma p₁_sqZero : (FP.p₁ π Dp.π).SqZero := by
  refine ⟨fun a => ⟨(ι₁ π Dp).1 a, rfl⟩, ?_⟩
  rw [sq, ← le_bot_iff]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  rw [RingHom.mem_ker] at hx hy
  have hx0 : x.1.1 = 0 := hx
  have hy0 : y.1.1 = 0 := hy
  have hx2 : x.1.2 ∈ Ideal.span {Dp.η} := by
    rw [← Dp.ker_eq, RingHom.mem_ker, ← FP.mem π Dp.π x, hx0, map_zero]
  have hy2 : y.1.2 ∈ Ideal.span {Dp.η} := by
    rw [← Dp.ker_eq, RingHom.mem_ker, ← FP.mem π Dp.π y, hy0, map_zero]
  rw [Ideal.mem_bot]
  apply Subtype.ext
  apply Prod.ext
  · show x.1.1 * y.1.1 = 0
    rw [hx0, zero_mul]
  · show x.1.2 * y.1.2 = 0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hx2
    obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 hy2
    rw [← hc, ← hc']
    calc c * Dp.η * (c' * Dp.η) = c * c' * (Dp.η * Dp.η) := by ring
      _ = 0 := by rw [Dp.η_sq, mul_zero]

lemma p₂_ker : ∀ a ∈ (FP.p₁ π Dp.π).ker, (FP.p₂ π Dp.π).1.toLinearMap a ∈ Dp.π.ker := by
  intro a ha
  have ha0 : a.1.1 = 0 := ha
  show Dp.π.1 a.1.2 = 0
  rw [← FP.mem π Dp.π a, ha0, map_zero]

variable {ξ : (R' : Type u)} (hsurj : Function.Surjective π.1)
  (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)

lemma sm_ker : ∀ a ∈ (FP.p₁ π Dp.π).ker, (sm π Dp ξ hsurj hker hsq).1.toLinearMap a ∈ π.ker := by
  intro a ha
  have ha0 : a.1.1 = 0 := ha
  show π.1 (a.1.1 + ell π ξ hsurj (Dp.κ a.1.2)) = 0
  rw [map_add, ell_π hsurj hker, ha0, map_zero, add_zero]

lemma sm_ker_surj :
    Function.Surjective ((sm π Dp ξ hsurj hker hsq).1.toLinearMap.restrict
      (sm_ker π Dp hsurj hker hsq)) := by
  rintro ⟨b, hb⟩
  have hb' : b ∈ RingHom.ker π.1 := hb
  have hbξ : b ∈ Ideal.span {ξ} := by
    rw [← hker]
    exact hb'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hbξ
  have hmem : ((0 : (R' : Type u)), Dp.σ.1 (π.1 c) * Dp.η) ∈ fpSub π Dp.π := by
    rw [mem_fpSub]
    show π.1 0 = Dp.π.1 (Dp.σ.1 (π.1 c) * Dp.η)
    rw [map_zero, map_mul, Dp.π_η, mul_zero]
  have hk : (⟨_, hmem⟩ : (FP π Dp.π : Type u)) ∈ (FP.p₁ π Dp.π).ker := by
    show (0 : (R' : Type u)) = 0
    rfl
  refine ⟨⟨⟨_, hmem⟩, hk⟩, ?_⟩
  apply Subtype.ext
  show (0 : (R' : Type u)) + ell π ξ hsurj (Dp.κ (Dp.σ.1 (π.1 c) * Dp.η)) = c * ξ
  rw [Dp.κ_ση, ell_spec hsurj hker hsq, zero_add]

end

end ReciprocityTheory.PGsh
