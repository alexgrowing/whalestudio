import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField NumberField.InfinitePlace Module GroundTheory.Global GroundTheory.Global.Elliptic FractionalIdeal
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K]

theorem isTotallyComplex_of_primeDiscriminant [Algebra.IsQuadraticExtension ℚ K]
    (S : PrimeDiscriminant K) : IsTotallyComplex K := by
  rw [← nrRealPlaces_eq_zero_iff]
  have h2 : finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  have hr := card_add_two_mul_card_eq_rank (K := K)
  have hs := sign_discr (K := K)
  rw [S.discr_eq] at hs
  have hd : (0 : ℤ) < S.d := by exact_mod_cast S.prime.pos
  rw [Int.sign_eq_neg_one_of_neg (by omega)] at hs
  rcases Nat.even_or_odd (nrComplexPlaces K) with he | ho
  · rw [he.neg_one_pow] at hs
    norm_num at hs
  · obtain ⟨m, hm⟩ := ho
    omega

variable (σ : K →+* ℂ)

theorem image_idealLattice_spanSingleton_mul (c : ℂ) (b : K) (M : Ideal (𝓞 K)) :
    (c * ·) '' (idealLattice σ (spanSingleton (𝓞 K)⁰ b * (M : FractionalIdeal (𝓞 K)⁰ K)) : Set ℂ) =
      (fun x : 𝓞 K ↦ c * σ (b * algebraMap (𝓞 K) K x)) '' (M : Set (𝓞 K)) := by
  ext z
  simp only [Set.mem_image, SetLike.mem_coe, mem_idealLattice, mem_singleton_mul, mem_coeIdeal]
  constructor
  · rintro ⟨_, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, rfl⟩

variable (hK : finrank ℚ K = 2) [IsTotallyComplex K]
include hK

theorem le_and_relIndex (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (𝔭 : (Ideal (𝓞 K))⁰)
    (L' : PeriodPair)
    (hL' : L'.lattice = idealLattice σ ↑(FractionalIdeal.mk0 K 𝔭)⁻¹ * L.lattice) :
    L.lattice ≤ L'.lattice ∧
      L.lattice.toAddSubgroup.relIndex L'.lattice.toAddSubgroup =
        Ideal.absNorm (𝔭 : Ideal (𝓞 K)) := by
  obtain ⟨I, c, hc, hI⟩ := exists_idealLattice_of_latticeEnd_eq σ hK L hL
  have h' := idealLattice_mul_homothetic σ (I : FractionalIdeal (𝓞 K)⁰ K)
    (↑(FractionalIdeal.mk0 K 𝔭)⁻¹) hI
  rw [← hL'] at h'
  obtain ⟨a, J₀, ha, hJ⟩ := exists_eq_spanSingleton_mul
    ((↑(FractionalIdeal.mk0 K 𝔭)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K))
  have hIJ : (I : FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a)⁻¹ * ↑((𝔭 : Ideal (𝓞 K)) * J₀) := by
    rw [coeIdeal_mul, mul_left_comm, ← hJ, ← FractionalIdeal.coe_mk0 (K := K) 𝔭,
      Units.mul_inv_cancel_left]
  have ha' : (algebraMap (𝓞 K) K a)⁻¹ ≠ 0 :=
    inv_ne_zero ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 ha)
  let f : 𝓞 K →+ ℂ :=
    { toFun := fun x ↦ c * σ ((algebraMap (𝓞 K) K a)⁻¹ * algebraMap (𝓞 K) K x)
      map_zero' := by simp
      map_add' := fun x y ↦ by simp only [map_add, mul_add] }
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' : c * σ ((algebraMap (𝓞 K) K a)⁻¹ * algebraMap (𝓞 K) K x) =
        c * σ ((algebraMap (𝓞 K) K a)⁻¹ * algebraMap (𝓞 K) K y) := hxy
    exact FaithfulSMul.algebraMap_injective (𝓞 K) K
      (mul_left_cancel₀ ha' (σ.injective (mul_left_cancel₀ hc hxy')))
  have hLset : L.lattice.toAddSubgroup = ((𝔭 : Ideal (𝓞 K)) * J₀).toAddSubgroup.map f := by
    apply SetLike.coe_injective
    rw [AddSubgroup.coe_map]
    show (L.lattice : Set ℂ) = _
    rw [hI, hIJ, image_idealLattice_spanSingleton_mul]
    rfl
  have hL'set : L'.lattice.toAddSubgroup = J₀.toAddSubgroup.map f := by
    apply SetLike.coe_injective
    rw [AddSubgroup.coe_map]
    show (L'.lattice : Set ℂ) = _
    rw [h', hJ, image_idealLattice_spanSingleton_mul]
    rfl
  have hle : ((𝔭 : Ideal (𝓞 K)) * J₀).toAddSubgroup ≤ J₀.toAddSubgroup :=
    (Submodule.toAddSubgroup_le _ _).2 (Ideal.mul_le.2 fun a _ b hb ↦ J₀.mul_mem_left a hb)
  refine ⟨?_, ?_⟩
  · rw [← Submodule.toAddSubgroup_le, hLset, hL'set]
    exact AddSubgroup.map_mono hle
  · rw [hLset, hL'set, AddSubgroup.relIndex_map_map_of_injective _ _ hf]
    have hJ0 : J₀ ≠ ⊥ := by
      rintro rfl
      refine ((FractionalIdeal.mk0 K 𝔭)⁻¹ * I).ne_zero ?_
      rw [Units.val_mul, hJ, coeIdeal_bot, mul_zero]
    have key := AddSubgroup.relIndex_mul_index hle
    rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, map_mul] at key
    have hn : Ideal.absNorm J₀ ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact mul_right_cancel₀ hn key

theorem discrRatio_spanSingleton (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (π : K)
    (hπ : π ≠ 0) (U : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hU : (U : FractionalIdeal (𝓞 K)⁰ K) = spanSingleton (𝓞 K)⁰ π) :
    discrRatio σ L.lattice U = σ π ^ 12 := by
  obtain ⟨L'', hL'', -⟩ := exists_lattice_mul σ hK L hL U
  obtain ⟨I, c, hc, hI⟩ := exists_idealLattice_of_latticeEnd_eq σ hK L hL
  have h' := idealLattice_mul_homothetic σ (I : FractionalIdeal (𝓞 K)⁰ K) (↑U⁻¹) hI
  rw [← hL''] at h'
  have hσπ : σ π ≠ 0 := (map_ne_zero σ).2 hπ
  have hscale : (L''.lattice : Set ℂ) = ((σ π)⁻¹ * ·) '' L.lattice := by
    rw [h', hI, Units.val_inv_eq_inv_val, hU, spanSingleton_inv, Set.image_image]
    ext z
    simp only [Set.mem_image, SetLike.mem_coe, mem_idealLattice, mem_singleton_mul]
    constructor
    · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
      exact ⟨σ y, ⟨y, hy, rfl⟩, by rw [map_mul, map_inv₀]; ring⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, by rw [map_mul, map_inv₀]; ring⟩
  have hG : ∀ n, L''.G n = σ π ^ n * L.G n := fun n ↦ by
    rw [G_eq_of_lattice_eq_smul (inv_ne_zero hσπ) hscale n, inv_pow, inv_inv]
  have h₂ : L''.g₂ = σ π ^ 4 * L.g₂ := by
    rw [PeriodPair.g₂, PeriodPair.g₂, hG]; ring
  have h₃ : L''.g₃ = σ π ^ 6 * L.g₃ := by
    rw [PeriodPair.g₃, PeriodPair.g₃, hG]; ring
  rw [discrRatio, ← hL'', latticeDiscr_lattice, latticeDiscr_lattice, discr_of_g₂_g₃ h₂ h₃,
    mul_div_assoc, div_self (discr_ne_zero L), mul_one]

theorem isIntegral_discrRatio (hΔ : DeltaRatioIntegral.Statement)
    (hj : ∀ L : PeriodPair, latticeEnd L = cmRing σ → IsIntegral ℤ (weierstrassCurve L).j)
    (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (𝔭 : (Ideal (𝓞 K))⁰)
    (hp : (Ideal.absNorm (𝔭 : Ideal (𝓞 K))).Prime) :
    IsIntegral ℤ (discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭)) := by
  obtain ⟨L', hL', -⟩ := exists_lattice_mul σ hK L hL (FractionalIdeal.mk0 K 𝔭)
  obtain ⟨hle, hidx⟩ := le_and_relIndex σ hK L hL 𝔭 L' hL'
  have h := hΔ L L' _ hp hle hidx
  have : Algebra.IsIntegral ℤ (Algebra.adjoin ℤ {(weierstrassCurve L).j}) :=
    Algebra.IsIntegral.adjoin (by rintro x rfl; exact hj L hL)
  rw [discrRatio, ← hL']
  exact isIntegral_trans _ h

variable [Algebra.IsQuadraticExtension ℚ K] (S : PrimeDiscriminant K)

theorem exists_discrRatio_pow (hW : WCocycle.Statement S) (hΔ : DeltaRatioIntegral.Statement)
    (hj : JIntegral.Statement S) (L : PeriodPair) (hL : latticeEnd L = cmRing σ)
    (𝔭 : (Ideal (𝓞 K))⁰) (hp : (Ideal.absNorm (𝔭 : Ideal (𝓞 K))).Prime) (n : ℕ) :
    ∃ c : ℂ, IsIntegral ℤ c ∧ discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭 ^ (n + 1)) =
      discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭) * c := by
  induction n with
  | zero => exact ⟨1, isIntegral_one, by rw [zero_add, pow_one, mul_one]⟩
  | succ n ih =>
    obtain ⟨c, hc, e⟩ := ih
    obtain ⟨L', hL', hL'e⟩ := exists_lattice_mul σ hK L hL (FractionalIdeal.mk0 K 𝔭 ^ (n + 1))
    have hw := isIntegral_discrRatio σ hK hΔ (hj σ) L' hL'e 𝔭 hp
    refine ⟨c * discrRatio σ L'.lattice (FractionalIdeal.mk0 K 𝔭), hc.mul hw, ?_⟩
    rw [pow_succ, hW σ L hL, e, ← hL', mul_assoc]

omit hK [IsTotallyComplex K] in

theorem WUnitOffPrime.proof (hW : WCocycle.Statement S) (hΔ : DeltaRatioIntegral.Statement)
    (hj : JIntegral.Statement S) : WUnitOffPrime.Statement S := by
  intro σ L hL 𝔭 h𝔭 hp
  have := isTotallyComplex_of_primeDiscriminant S
  have hK : finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K

  obtain ⟨n, π, hπ0, hπ⟩ : ∃ (n : ℕ) (π : 𝓞 K), π ≠ 0 ∧
      (𝔭 : Ideal (𝓞 K)) ^ (n + 1) = Ideal.span {π} := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (orderOf_pos (ClassGroup.mk0 𝔭)).ne'
    have h1 : ClassGroup.mk0 (𝔭 ^ (n + 1)) = 1 := by
      rw [map_pow, show n + 1 = orderOf (ClassGroup.mk0 𝔭) from hn.symm, pow_orderOf_eq_one]
    have hpr := (ClassGroup.mk0_eq_one_iff (𝔭 ^ (n + 1)).2).1 h1
    rw [SubmonoidClass.coe_pow] at hpr
    refine ⟨n, Submodule.IsPrincipal.generator _, ?_, (Ideal.span_singleton_generator _).symm⟩
    intro h0
    have hb : (𝔭 : Ideal (𝓞 K)) ^ (n + 1) = ⊥ := by
      rw [← Ideal.span_singleton_generator ((𝔭 : Ideal (𝓞 K)) ^ (n + 1)), h0,
        Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.coe_ne_zero (𝔭 ^ (n + 1)) (by rw [SubmonoidClass.coe_pow, hb]; rfl)
  have hπK : algebraMap (𝓞 K) K π ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 hπ0
  have hU : ((FractionalIdeal.mk0 K 𝔭 ^ (n + 1) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K π) := by
    rw [Units.val_pow_eq_pow_val, FractionalIdeal.coe_mk0, ← coeIdeal_pow, hπ,
      coeIdeal_span_singleton]
  obtain ⟨c, hc, e⟩ := exists_discrRatio_pow σ hK S hW hΔ hj L hL 𝔭 hp n
  rw [discrRatio_spanSingleton σ hK L hL _ hπK _ hU] at e
  have hwint := isIntegral_discrRatio σ hK hΔ (hj σ) L hL 𝔭 hp
  refine ⟨(hwint.tower_top (A := ℚ)).isAlgebraic, ?_⟩
  rintro F _ _ ι τ hτ ⟨x, hx⟩
  have hcomp : ∀ z : K, τ (ι z) = σ z := fun z ↦ by rw [← hτ]; rfl
  have hσπ : σ (algebraMap (𝓞 K) K π) ≠ 0 := (map_ne_zero σ).2 hπK
  have hw0 : discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e
    exact pow_ne_zero 12 hσπ e
  have hxint : IsIntegral ℤ x := by
    rw [← isIntegral_algHom_iff τ.toIntAlgHom τ.injective]
    change IsIntegral ℤ (τ x)
    rw [hx]
    exact hwint
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [← hx, map_zero])
  set y : F := ι (algebraMap (𝓞 K) K π) ^ 12 / x with hy_def
  have hy : τ y = c := by
    rw [hy_def, map_div₀, map_pow, hcomp, hx, e, mul_div_cancel_left₀ _ hw0]
  have hyint : IsIntegral ℤ y := by
    rw [← isIntegral_algHom_iff τ.toIntAlgHom τ.injective]
    change IsIntegral ℤ (τ y)
    rw [hy]
    exact hc
  refine ⟨⟨x, hxint⟩, hx, fun Q hQ hnot hxQ ↦ hnot ?_⟩
  have hxy : (⟨x, hxint⟩ : 𝓞 F) * ⟨y, hyint⟩ = RingOfIntegers.mapRingHom ι π ^ 12 := by
    ext
    change x * y = algebraMap (𝓞 F) F (RingOfIntegers.mapRingHom ι π ^ 12)
    rw [hy_def, mul_div_cancel₀ _ hx0, map_pow]
    rfl
  have hπQ : RingOfIntegers.mapRingHom ι π ∈ Q :=
    hQ.isPrime.mem_of_pow_mem 12 (hxy ▸ Q.mul_mem_right _ hxQ)
  have hle : Ideal.map (RingOfIntegers.mapRingHom ι) ((𝔭 : Ideal (𝓞 K)) ^ (n + 1)) ≤ Q := by
    rw [hπ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    exact hπQ
  rw [Ideal.map_pow] at hle
  have := hQ.isPrime
  exact Ideal.IsPrime.le_of_pow_le hle

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
