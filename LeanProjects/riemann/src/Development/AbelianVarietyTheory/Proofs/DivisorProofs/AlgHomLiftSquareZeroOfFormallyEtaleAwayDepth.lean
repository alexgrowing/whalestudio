import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing

namespace GlobalTheory.SquareZeroLift

theorem localLift (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (g : R)
    [Algebra.FormallyEtale (Localization.Away g) (TensorProduct R (Localization.Away g) A)]
    (C : Type) [CommRing C] [Algebra R C] (hg : IsUnit (algebraMap R C g)) (J : Ideal C)
    (hJ : J ^ 2 = ⊥) (f : A →ₐ[R] C ⧸ J) :
    ∃! α : A →ₐ[R] C, (Ideal.Quotient.mkₐ R J).comp α = f := by
  haveI : Algebra.FormallyEtale R (Localization.Away g) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g)
  haveI : Algebra.FormallyEtale R (TensorProduct R (Localization.Away g) A) :=
    Algebra.FormallyEtale.comp R (Localization.Away g) _
  have unit : ∀ (P : Type) [CommRing P] [Algebra R P], IsUnit (algebraMap R P g) →
      ∀ y : Submonoid.powers g, IsUnit ((Algebra.ofId R P) (y : R)) := by
    intro P _ _ h y
    obtain ⟨n, hn⟩ := y.2
    rw [← hn]; simp only [map_pow]; exact h.pow n
  let e : Localization.Away g →ₐ[R] C :=
    IsLocalization.liftAlgHom (M := Submonoid.powers g) (unit C hg)
  have hg' : IsUnit (algebraMap R (C ⧸ J) g) := by
    rw [IsScalarTower.algebraMap_apply R C (C ⧸ J)]; exact hg.map _
  let e' : Localization.Away g →ₐ[R] C ⧸ J :=
    IsLocalization.liftAlgHom (M := Submonoid.powers g) (unit (C ⧸ J) hg')
  let F : TensorProduct R (Localization.Away g) A →ₐ[R] C ⧸ J :=
    Algebra.TensorProduct.lift e' f (fun _ _ => Commute.all _ _)
  have hsurj : Function.Surjective (Ideal.Quotient.mkₐ R J) := Ideal.Quotient.mkₐ_surjective R J
  have hnil : IsNilpotent (RingHom.ker (Ideal.Quotient.mkₐ R J : C →+* C ⧸ J)) := by
    refine ⟨2, ?_⟩
    have : RingHom.ker (Ideal.Quotient.mkₐ R J : C →+* C ⧸ J) = J := by
      ext x; simp [Ideal.Quotient.eq_zero_iff_mem]
    rw [this, hJ]; rfl
  refine ⟨(Algebra.FormallySmooth.liftOfSurjective F _ hsurj hnil).comp
    Algebra.TensorProduct.includeRight, ?_, ?_⟩
  · show (Ideal.Quotient.mkₐ R J).comp ((Algebra.FormallySmooth.liftOfSurjective F _ hsurj hnil).comp
      Algebra.TensorProduct.includeRight) = f
    rw [← AlgHom.comp_assoc, Algebra.FormallySmooth.comp_liftOfSurjective]
    ext a; simp [F]
  · intro α hα
    let E1 : TensorProduct R (Localization.Away g) A →ₐ[R] C :=
      Algebra.TensorProduct.lift e α (fun _ _ => Commute.all _ _)
    let E2 : TensorProduct R (Localization.Away g) A →ₐ[R] C :=
      Algebra.FormallySmooth.liftOfSurjective F _ hsurj hnil
    have hE : E1 = E2 := by
      apply Algebra.FormallyUnramified.comp_injective J hJ
      apply Algebra.TensorProduct.ext
      · exact (IsLocalization.algHom_subsingleton (Submonoid.powers g)).elim _ _
      · rw [show E2 = Algebra.FormallySmooth.liftOfSurjective F _ hsurj hnil from rfl]
        ext a
        have h2 := congrArg (fun φ => φ (Algebra.TensorProduct.includeRight a))
          (Algebra.FormallySmooth.comp_liftOfSurjective F _ hsurj hnil)
        simp only [AlgHom.comp_apply] at h2
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, h2]
        simp [E1, F, ← hα]
    have : α = E1.comp Algebra.TensorProduct.includeRight := by ext a; simp [E1]
    rw [this, hE]

end GlobalTheory.SquareZeroLift

namespace GlobalTheory.SquareZeroLift

open RingTheory.Sequence
open scoped Pointwise

theorem pow_dvd_of_weaklyRegular {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (x y : R)
    (h : IsWeaklyRegular M [x, y]) (a b : ℕ) (s u : M) (hsu : y ^ b • s = x ^ a • u) :
    ∃ v : M, s = x ^ a • v := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_cons_iff] at h
  obtain ⟨hx, hy, -⟩ := h
  have step : ∀ s u : M, y • s = x • u → ∃ v : M, s = x • v := by
    intro s u hsu
    have h0 : y • (Submodule.Quotient.mk s : M ⧸ x • (⊤ : Submodule R M)) = y • 0 := by
      rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsu]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    have h1 := hy h0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨v, -, hv⟩ := h1
    exact ⟨v, hv.symm⟩
  have P : ∀ (a : ℕ) (s u : M), y • s = x ^ a • u → ∃ v : M, s = x ^ a • v := by
    intro a
    induction a with
    | zero => intro s u _; exact ⟨s, by simp⟩
    | succ a ih =>
      intro s u hsu
      rw [pow_succ', mul_smul] at hsu
      obtain ⟨s1, rfl⟩ := step s _ hsu
      rw [smul_comm] at hsu
      obtain ⟨v, rfl⟩ := ih s1 u (hx hsu)
      exact ⟨v, by rw [pow_succ', mul_smul]⟩
  induction b generalizing s with
  | zero => exact ⟨u, by simpa using hsu⟩
  | succ b ih =>
    rw [pow_succ, mul_smul] at hsu
    obtain ⟨v, hv⟩ := ih (y • s) hsu
    exact P a s v hv

section
variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A]
  {S T : Type} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
  (π : S →ₐ[R] T) (φ : A →ₐ[R] T)

def Lifts {C : Type} [CommRing C] [Algebra R C] (σ : S →ₐ[R] C) (α : A →ₐ[R] C) : Prop :=
  ∀ a s, π s = φ a → α a - σ s ∈ (RingHom.ker π).map σ

theorem Lifts.comp {C D : Type} [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    {σ : S →ₐ[R] C} {α : A →ₐ[R] C} (h : Lifts π φ σ α) (ρ : C →ₐ[R] D) :
    Lifts π φ (ρ.comp σ) (ρ.comp α) := by
  intro a s hs
  have h1 := Ideal.mem_map_of_mem ρ (h a s hs)
  rw [map_sub] at h1
  have h2 : Ideal.map ρ (Ideal.map σ (RingHom.ker π)) = Ideal.map (ρ.comp σ) (RingHom.ker π) := by
    exact Ideal.map_map (σ : S →+* C) (ρ : C →+* D) (I := RingHom.ker π)
  rw [h2] at h1
  simpa using h1

theorem existsUnique_lifts (hπ : Function.Surjective π) (hI : RingHom.ker π ^ 2 = ⊥) (g : R)
    (hA : Algebra.FormallyEtale (Localization.Away g) (TensorProduct R (Localization.Away g) A))
    {C : Type} [CommRing C] [Algebra R C] (σ : S →ₐ[R] C) (hg : IsUnit (algebraMap R C g)) :
    ∃! α : A →ₐ[R] C, Lifts π φ σ α := by
  haveI := hA
  set J := (RingHom.ker π).map σ with hJdef
  have hJ : J ^ 2 = ⊥ := by rw [hJdef, ← Ideal.map_pow, hI, Ideal.map_bot]
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let q : S ⧸ RingHom.ker π.toRingHom →ₐ[R] C ⧸ J :=
    Ideal.quotientMapₐ J σ Ideal.le_comap_map
  let tgt : A →ₐ[R] C ⧸ J := q.comp (e.symm.toAlgHom.comp φ)
  have htgt : ∀ a s, π s = φ a → tgt a = Ideal.Quotient.mk J (σ s) := by
    intro a s hs
    have : e.symm (φ a) = Ideal.Quotient.mk _ s := by
      rw [AlgEquiv.symm_apply_eq, ← hs]; rfl
    show q (e.symm (φ a)) = _
    rw [this]; rfl
  have key : ∀ α : A →ₐ[R] C, Lifts π φ σ α ↔ (Ideal.Quotient.mkₐ R J).comp α = tgt := by
    intro α; constructor
    · intro h; ext a; obtain ⟨s, hs⟩ := hπ (φ a)
      rw [AlgHom.comp_apply, htgt a s hs, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
      exact h a s hs
    · intro h a s hs
      have := congrArg (fun f => f a) h
      simp only [AlgHom.comp_apply] at this
      rw [htgt a s hs, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at this
      exact this
  obtain ⟨α, hα, huniq⟩ := localLift R A g C hg J hJ tgt
  exact ⟨α, (key α).2 hα, fun β hβ => huniq β ((key β).1 hβ)⟩

end

end GlobalTheory.SquareZeroLift

namespace GlobalTheory.SquareZeroLift

section
variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]

noncomputable def toAway (g : R) : S →ₐ[R] Localization.Away (algebraMap R S g) :=
  IsScalarTower.toAlgHom R S _

theorem toAway_apply (g : R) (s : S) : toAway S g s = algebraMap S _ s := rfl

theorem isUnit_toAway (g : R) : IsUnit (algebraMap R (Localization.Away (algebraMap R S g)) g) := by
  rw [IsScalarTower.algebraMap_apply R S]
  exact IsLocalization.Away.algebraMap_isUnit (algebraMap R S g)

theorem isUnit_left (g h : R) :
    IsUnit (algebraMap S (Localization.Away (algebraMap R S (g * h))) (algebraMap R S g)) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap R S (g * h)))
    (algebraMap R S (g * h))
  have e : algebraMap S (Localization.Away (algebraMap R S (g * h))) (algebraMap R S (g * h)) =
      algebraMap S _ (algebraMap R S g) * algebraMap S _ (algebraMap R S h) := by
    rw [map_mul, map_mul]
  rw [e] at this
  exact isUnit_of_mul_isUnit_left this

theorem isUnit_right (g h : R) :
    IsUnit (algebraMap S (Localization.Away (algebraMap R S (g * h))) (algebraMap R S h)) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap R S (g * h)))
    (algebraMap R S (g * h))
  have e : algebraMap S (Localization.Away (algebraMap R S (g * h))) (algebraMap R S (g * h)) =
      algebraMap S _ (algebraMap R S g) * algebraMap S _ (algebraMap R S h) := by
    rw [map_mul, map_mul]
  rw [e] at this
  exact isUnit_of_mul_isUnit_right this

noncomputable def toMulLeft (g h : R) :
    Localization.Away (algebraMap R S g) →ₐ[R] Localization.Away (algebraMap R S (g * h)) :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (algebraMap R S g)) (f := toAway S (g * h))
    (fun y => by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, map_pow]
      exact (isUnit_left S g h).pow n)

noncomputable def toMulRight (g h : R) :
    Localization.Away (algebraMap R S h) →ₐ[R] Localization.Away (algebraMap R S (g * h)) :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (algebraMap R S h)) (f := toAway S (g * h))
    (fun y => by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, map_pow]
      exact (isUnit_right S g h).pow n)

theorem toMulLeft_apply (g h : R) (s : S) :
    toMulLeft S g h (algebraMap S _ s) = algebraMap S _ s := by
  simp only [toMulLeft, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]; rfl

theorem toMulRight_apply (g h : R) (s : S) :
    toMulRight S g h (algebraMap S _ s) = algebraMap S _ s := by
  simp only [toMulRight, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]; rfl

theorem toMulLeft_comp (g h : R) : (toMulLeft S g h).comp (toAway S g) = toAway S (g * h) :=
  AlgHom.ext fun s => toMulLeft_apply S g h s

theorem toMulRight_comp (g h : R) : (toMulRight S g h).comp (toAway S h) = toAway S (g * h) :=
  AlgHom.ext fun s => toMulRight_apply S g h s

end

end GlobalTheory.SquareZeroLift

namespace GlobalTheory.SquareZeroLift
open RingTheory.Sequence

theorem squareZeroLift : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A],
    (∀ g ∈ maximalIdeal R, Algebra.FormallyEtale (Localization.Away g)
      (TensorProduct R (Localization.Away g) A)) →
    ∀ (S T : Type) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T],
    ReciprocityTheory.CA.ModDepthGE R S 2 → ReciprocityTheory.CA.ModDepthGE R T 1 →
    ∀ (π : S →ₐ[R] T), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (φ : A →ₐ[R] T), ∃ ψ : A →ₐ[R] S, π.comp ψ = φ := by
  intro R _ _ A _ _ hA S T _ _ _ _ hS hT π hπ hI φ
  obtain ⟨rs, hlen, hmem, hreg⟩ := hS
  obtain ⟨x, y, rfl⟩ : ∃ x y, rs = [x, y] := by
    match rs, hlen with
    | [x, y], _ => exact ⟨x, y, rfl⟩
  have hxm : x ∈ maximalIdeal R := hmem x (by simp)
  have hym : y ∈ maximalIdeal R := hmem y (by simp)
  have hw := hreg.toIsWeaklyRegular
  have hx : IsSMulRegular S x := ((isWeaklyRegular_cons_iff S x [y]).1 hw).1
  obtain ⟨rs', hlen', hmem', hreg'⟩ := hT
  obtain ⟨z, rfl⟩ : ∃ z, rs' = [z] := by
    match rs', hlen' with
    | [z], _ => exact ⟨z, rfl⟩
  have hzm : z ∈ maximalIdeal R := hmem' z (by simp)
  have hz : IsSMulRegular T z := ((isWeaklyRegular_cons_iff T z []).1 hreg'.toIsWeaklyRegular).1
  have EU := fun (g : R) (hg : g ∈ maximalIdeal R) =>
    existsUnique_lifts π φ hπ hI g (hA g hg) (toAway S g) (isUnit_toAway S g)
  obtain ⟨αx, hαx, -⟩ := EU x hxm
  obtain ⟨αy, hαy, -⟩ := EU y hym
  obtain ⟨αz, hαz, -⟩ := EU z hzm

  have hxy : (toMulLeft S x y).comp αx = (toMulRight S x y).comp αy := by
    obtain ⟨β, -, hβ⟩ := EU (x * y) (Ideal.mul_mem_right _ _ hxm)
    have h1 := Lifts.comp π φ hαx (toMulLeft S x y)
    have h2 := Lifts.comp π φ hαy (toMulRight S x y)
    rw [toMulLeft_comp] at h1
    rw [toMulRight_comp] at h2
    rw [hβ _ h1, hβ _ h2]
  have hzx : (toMulLeft S z x).comp αz = (toMulRight S z x).comp αx := by
    obtain ⟨β, -, hβ⟩ := EU (z * x) (Ideal.mul_mem_right _ _ hzm)
    have h1 := Lifts.comp π φ hαz (toMulLeft S z x)
    have h2 := Lifts.comp π φ hαx (toMulRight S z x)
    rw [toMulLeft_comp] at h1
    rw [toMulRight_comp] at h2
    rw [hβ _ h1, hβ _ h2]

  have glue : ∀ a, ∃ v : S, αx a = toAway S x v := by
    intro a
    obtain ⟨⟨s, m⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R S x)) (αx a)
    obtain ⟨⟨s', m'⟩, hs'⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R S y)) (αy a)
    obtain ⟨n, hn⟩ := m.2
    obtain ⟨k, hk⟩ := m'.2
    have hP : toMulLeft S x y (αx a) = toMulRight S x y (αy a) := by
      have := congrArg (fun f => f a) hxy
      simpa only [AlgHom.comp_apply] using this
    have e1 := congrArg (toMulLeft S x y) hs
    have e2 := congrArg (toMulRight S x y) hs'
    rw [map_mul (toMulLeft S x y), toMulLeft_apply, toMulLeft_apply] at e1
    rw [map_mul (toMulRight S x y), toMulRight_apply, toMulRight_apply] at e2
    have e3 : algebraMap S (Localization.Away (algebraMap R S (x * y))) (s * m') =
        algebraMap S _ (s' * m) := by
      rw [map_mul (algebraMap S (Localization.Away (algebraMap R S (x * y)))),
        map_mul (algebraMap S (Localization.Away (algebraMap R S (x * y)))), ← e1, ← e2, hP]; ring
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
      (Submonoid.powers (algebraMap R S (x * y))) _).1 e3
    obtain ⟨j, hj⟩ := c.2
    simp only at hn hk hj
    rw [← hj, ← hn, ← hk] at hc
    try rw [map_mul (algebraMap R S)] at hc
    rw [mul_pow] at hc
    have hc2 : (algebraMap R S y) ^ (j + k) * s =
        (algebraMap R S x) ^ n * ((algebraMap R S y) ^ j * s') := by
      apply hx.pow j
      simp only [Algebra.smul_def, map_pow]
      linear_combination hc
    obtain ⟨v, hv⟩ := pow_dvd_of_weaklyRegular x y hw n (j + k) s ((algebraMap R S y) ^ j * s')
      (by simpa only [Algebra.smul_def, map_pow] using hc2)
    refine ⟨v, ?_⟩
    have hu : IsUnit (algebraMap S (Localization.Away (algebraMap R S x)) ((algebraMap R S x) ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (algebraMap R S x)).pow n
    rw [toAway_apply]
    apply hu.mul_right_cancel
    simp only at hs
    rw [← hn] at hs
    rw [hs, hv, Algebra.smul_def, map_mul, map_pow, mul_comm]

  have hinj : Function.Injective (toAway S x) := by
    show Function.Injective (algebraMap S (Localization.Away (algebraMap R S x)))
    apply IsLocalization.injective (M := Submonoid.powers (algebraMap R S x))
    intro c hc
    obtain ⟨n, rfl⟩ := hc
    rw [mem_nonZeroDivisors_iff]
    constructor
    · intro t ht
      apply hx.pow n
      simp only [Algebra.smul_def, map_pow, smul_zero]
      simpa [mul_comm] using ht
    · intro t ht
      apply hx.pow n
      simp only [Algebra.smul_def, map_pow, smul_zero]
      simpa [mul_comm] using ht
  let ψ : A →ₐ[R] S := ((AlgEquiv.ofInjective (toAway S x) hinj).symm : _ →ₐ[R] S).comp
    (αx.codRestrict (toAway S x).range (fun a => by
      obtain ⟨v, hv⟩ := glue a
      exact ⟨v, hv.symm⟩))
  have hψ : ∀ a, toAway S x (ψ a) = αx a := by
    intro a
    have h := congrArg Subtype.val ((AlgEquiv.ofInjective (toAway S x) hinj).apply_symm_apply
      ⟨αx a, by obtain ⟨v, hv⟩ := glue a; exact ⟨v, hv.symm⟩⟩)
    rw [AlgEquiv.ofInjective_apply] at h
    exact h

  have hαzψ : ∀ a, αz a = toAway S z (ψ a) := by
    intro a
    have h1 : toMulLeft S z x (αz a) = toMulLeft S z x (toAway S z (ψ a)) := by
      have := congrArg (fun f => f a) hzx
      simp only [AlgHom.comp_apply] at this
      rw [this, ← hψ a, toAway_apply, toAway_apply, toMulRight_apply, toMulLeft_apply]
    rw [← sub_eq_zero]
    set w := αz a - toAway S z (ψ a) with hwdef
    have hw0 : toMulLeft S z x w = 0 := by rw [hwdef, map_sub, h1, sub_self]
    obtain ⟨⟨s0, m0⟩, hs0⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R S z)) w
    simp only at hs0
    have e0 : algebraMap S (Localization.Away (algebraMap R S (z * x))) s0 =
        algebraMap S _ 0 := by
      rw [map_zero, ← toMulLeft_apply, ← hs0, map_mul (toMulLeft S z x), hw0, zero_mul]
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
      (Submonoid.powers (algebraMap R S (z * x))) _).1 e0
    obtain ⟨j, hj⟩ := c.2
    simp only at hj
    rw [← hj, mul_zero] at hc
    try rw [map_mul (algebraMap R S)] at hc
    rw [mul_pow] at hc
    have hzs : (algebraMap R S z) ^ j * s0 = 0 := by
      apply hx.pow j
      simp only [Algebra.smul_def, map_pow, mul_zero]
      linear_combination hc
    have hu : IsUnit (algebraMap S (Localization.Away (algebraMap R S z)) ((algebraMap R S z) ^ j)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (algebraMap R S z)).pow j
    have hs00 : algebraMap S (Localization.Away (algebraMap R S z)) s0 = 0 := by
      apply hu.mul_left_cancel
      rw [← map_mul, hzs, map_zero, mul_zero]
    obtain ⟨n, hn⟩ := m0.2
    simp only at hn
    have hu' : IsUnit (algebraMap S (Localization.Away (algebraMap R S z)) (m0 : S)) := by
      rw [← hn, map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (algebraMap R S z)).pow n
    apply hu'.mul_right_cancel
    rw [hs0, hs00, zero_mul]

  refine ⟨ψ, ?_⟩
  ext a
  obtain ⟨s, hs⟩ := hπ (φ a)
  have h := hαz a s hs
  rw [hαzψ a, ← map_sub] at h
  change algebraMap S (Localization.Away (algebraMap R S z)) (ψ a - s) ∈
    Ideal.map (algebraMap S (Localization.Away (algebraMap R S z))) (RingHom.ker π) at h
  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers (algebraMap R S z))] at h
  obtain ⟨⟨i, m⟩, hm⟩ := h
  simp only at hm
  rw [← map_mul] at hm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R S z)) _).1 hm
  have hker : π ((c : S) * ((ψ a - s) * m)) = 0 := by
    rw [hc, map_mul, RingHom.mem_ker.1 i.2, mul_zero]
  obtain ⟨j, hj⟩ := c.2
  obtain ⟨k, hk⟩ := m.2
  simp only at hj hk
  rw [← hj, ← hk, map_mul, map_mul, map_pow, map_pow, AlgHom.commutes, map_sub, hs] at hker
  have : π (ψ a) - φ a = 0 := by
    apply hz.pow (j + k)
    simp only [Algebra.smul_def, map_pow, smul_zero]
    linear_combination hker
  rw [AlgHom.comp_apply]
  exact sub_eq_zero.1 this

end GlobalTheory.SquareZeroLift
