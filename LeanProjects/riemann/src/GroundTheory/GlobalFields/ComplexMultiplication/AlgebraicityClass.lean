import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.Algebraicity

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

theorem image_mul_image_mul (c d : ℂ) (S : Set ℂ) :
    (c * ·) '' ((d * ·) '' S) = ((c * d) * ·) '' S := by
  rw [Set.image_image]
  congr 1
  funext x
  ring

theorem eq_image_mul_inv {c : ℂ} (hc : c ≠ 0) {A B : Set ℂ} (h : B = (c * ·) '' A) :
    A = (c⁻¹ * ·) '' B := by
  rw [h, image_mul_image_mul, inv_mul_cancel₀ hc]
  simp only [one_mul, Set.image_id']

theorem image_ringEquiv_image_mul (σ : ℂ ≃+* ℂ) (c : ℂ) (S : Set ℂ) :
    σ '' ((c * ·) '' S) = (σ c * ·) '' (σ '' S) := by
  rw [Set.image_image, Set.image_image]
  simp only [map_mul]

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ)

theorem image_idealLattice (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k)
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    σ '' (idealLattice σ₀ I : Set ℂ) = idealLattice σ₀ I := by
  ext z
  simp only [Set.mem_image, SetLike.mem_coe, mem_idealLattice]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (hσ x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨σ₀ x, ⟨x, hx, rfl⟩, hσ x⟩

variable (hK : finrank ℚ K = 2) [IsTotallyComplex K]
include hK

theorem latticeHom_eq_idealLattice (L L' : PeriodPair) (hL : latticeEnd L = cmRing σ₀)
    (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h : L'.lattice = idealLattice σ₀ ↑𝔟 * L.lattice) :
    (latticeHom L L' : Set ℂ) = idealLattice σ₀ ↑𝔟 := by
  obtain ⟨I, c, hc, hI⟩ := exists_idealLattice_of_latticeEnd_eq σ₀ hK L hL
  have hI' := idealLattice_mul_homothetic σ₀ (I : FractionalIdeal (𝓞 K)⁰ K) ↑𝔟 hI
  rw [← h] at hI'
  have hmem' : ∀ z, z ∈ L'.lattice ↔ ∃ x ∈ ((𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I), c * σ₀ x = z := by
    intro z
    rw [← SetLike.mem_coe, hI']
    simp only [Set.mem_image, SetLike.mem_coe, mem_idealLattice]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨σ₀ x, ⟨x, hx, rfl⟩, rfl⟩
  have hmemL : ∀ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K), c * σ₀ x ∈ L.lattice := by
    intro x hx
    rw [← SetLike.mem_coe, hI]
    exact ⟨σ₀ x, (mem_idealLattice σ₀).2 ⟨x, hx, rfl⟩, rfl⟩
  ext α
  simp only [SetLike.mem_coe, mem_latticeHom]
  constructor
  · intro hα
    have hI0 : ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≠ ⊥ := by
      rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
      exact I.ne_zero
    obtain ⟨i₀, hi₀, hi₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    obtain ⟨k₀, -, hk₀⟩ := (hmem' _).1 (hα _ (hmemL i₀ hi₀))
    have hσi₀ : σ₀ i₀ ≠ 0 := (map_ne_zero σ₀).2 hi₀0
    have hy : σ₀ (k₀ / i₀) = α := by
      rw [map_div₀, div_eq_iff hσi₀]
      exact mul_left_cancel₀ hc (by rw [hk₀]; ring)
    set y := k₀ / i₀
    have hyI : ∀ i ∈ (I : FractionalIdeal (𝓞 K)⁰ K), y * i ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I := by
      intro i hi
      obtain ⟨k, hk, hke⟩ := (hmem' _).1 (hα _ (hmemL i hi))
      have : σ₀ k = σ₀ (y * i) := by
        rw [map_mul, hy]
        exact mul_left_cancel₀ hc (by rw [hke]; ring)
      rwa [← σ₀.injective this]
    have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ y * (I : FractionalIdeal (𝓞 K)⁰ K) ≤
        (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I := by
      rw [FractionalIdeal.mul_le]
      intro a ha b hb
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton (𝓞 K)⁰).1 ha
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ r (hyI b hb)
    have hle' := mul_le_mul_left hle ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
    rw [mul_assoc, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one,
      mul_one] at hle'
    exact (mem_idealLattice σ₀).2
      ⟨y, hle' (FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ y), hy⟩
  · intro hα l hl
    rw [h]
    exact Submodule.mul_mem_mul hα hl

theorem homConstSet_of_smul {E E' : CMCurve K} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : (ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll = E'.toEll) :
    ∃ c : ℂ, c ≠ 0 ∧
      (homConstSet E.curve E'.curve : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
  obtain ⟨L, C, hL, hC, hE⟩ := E.exists_lattice σ₀ hK
  obtain ⟨L', hL'lat, hL'⟩ := exists_lattice_mul σ₀ hK L hL 𝔞
  have h1 := classGroup_smul_ellOf σ₀ hK L L' hL hL' 𝔞 hL'lat
  have h2 : E'.toEll = (CMCurve.ofLattice σ₀ L' hL').toEll := by
    rw [← h, ← hE]
    exact h1
  obtain ⟨C', hC'⟩ := (CMCurve.toEll_eq_iff _ _).1 h2
  have hC'' : C' • E'.curve = weierstrassCurve L' := hC'
  obtain ⟨d, hd, hset⟩ := homConstSet_vc C C' hC hC''
  rw [homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L L' hL 𝔞⁻¹ hL'lat] at hset
  exact ⟨d⁻¹, inv_ne_zero hd, eq_image_mul_inv hd hset⟩

theorem smul_toEll_of_homConstSet {E E' : CMCurve K} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {c : ℂ}
    (hc : c ≠ 0)
    (h : (homConstSet E.curve E'.curve : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹) :
    (ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll = E'.toEll := by
  obtain ⟨b, hb, -⟩ := existsUnique_smul_eq σ₀ hK E.toEll E'.toEll
  obtain ⟨J, rfl⟩ := classGroup_mk_surjective hK b
  obtain ⟨d, hd, h'⟩ := homConstSet_of_smul σ₀ hK hb
  have e : (idealLattice σ₀ ↑J⁻¹ : Set ℂ) = ((d⁻¹ * c) * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
    rw [eq_image_mul_inv hd h', h, image_mul_image_mul]
  have hcls := (classGroup_mk_eq_iff σ₀ hK 𝔞⁻¹ J⁻¹).2 ⟨d⁻¹ * c, mul_ne_zero (inv_ne_zero hd) hc, e⟩
  rw [map_inv, map_inv, inv_inj] at hcls
  rw [hcls]
  exact hb

theorem ELL.map_smul (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (a : ClassGroup (𝓞 K))
    (x : ELL K) :
    ELL.map σ ((ellMulAction σ₀ hK).smul a x) = (ellMulAction σ₀ hK).smul a (ELL.map σ x) := by
  obtain ⟨𝔞, rfl⟩ := classGroup_mk_surjective hK a
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  obtain ⟨E', hE'⟩ := ELL.exists_eq ((ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll)
  rw [← hE', ELL.map_toEll, ELL.map_toEll]
  obtain ⟨c, hc, h⟩ := homConstSet_of_smul σ₀ hK hE'.symm
  refine (smul_toEll_of_homConstSet σ₀ hK (c := σ c) ((map_ne_zero σ).2 hc) ?_).symm
  calc (homConstSet (E.map σ).curve (E'.map σ).curve : Set ℂ)
      = σ '' homConstSet E.curve E'.curve := homConstSet_map (E := E.curve) (E' := E'.curve) σ
    _ = σ '' ((c * ·) '' idealLattice σ₀ ↑𝔞⁻¹) := by rw [h]
    _ = (σ c * ·) '' (σ '' idealLattice σ₀ ↑𝔞⁻¹) := image_ringEquiv_image_mul σ c _
    _ = (σ c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by rw [image_idealLattice σ₀ σ hσ]

theorem ellMulAction_one_smul (x : ELL K) : (ellMulAction σ₀ hK).smul 1 x = x := by
  rw [ellMulAction_smul, one_mul, Equiv.apply_symm_apply]

theorem ellMulAction_mul_smul (a b : ClassGroup (𝓞 K)) (x : ELL K) :
    (ellMulAction σ₀ hK).smul (a * b) x =
      (ellMulAction σ₀ hK).smul a ((ellMulAction σ₀ hK).smul b x) := by
  rw [ellMulAction_smul, ellMulAction_smul, ellMulAction_smul, Equiv.symm_apply_apply, mul_assoc]

def galClass (σ : ℂ ≃+* ℂ) : ClassGroup (𝓞 K) :=
  (ellEquiv σ₀ hK).symm (ELL.map σ (ellEquiv σ₀ hK 1))

theorem ELL.map_eq_galClass_smul (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (x : ELL K) :
    ELL.map σ x = (ellMulAction σ₀ hK).smul (galClass σ₀ hK σ) x := by
  have hx : x = (ellMulAction σ₀ hK).smul ((ellEquiv σ₀ hK).symm x) (ellEquiv σ₀ hK 1) := by
    rw [ellMulAction_smul, Equiv.symm_apply_apply, mul_one, Equiv.apply_symm_apply]
  rw [hx, ELL.map_smul σ₀ hK σ hσ]
  simp only [ellMulAction_smul, Equiv.symm_apply_apply, mul_one]
  exact congrArg (ellEquiv σ₀ hK) (mul_comm _ _)

theorem apply_j_eq_j_galClass_smul (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (x : ELL K) :
    σ (ELL.j x) = ELL.j ((ellMulAction σ₀ hK).smul (galClass σ₀ hK σ) x) := by
  rw [← ELL.j_map, ELL.map_eq_galClass_smul σ₀ hK σ hσ]

theorem galClass_one : galClass σ₀ hK 1 = 1 := by
  rw [galClass, ELL.map_one, Equiv.symm_apply_apply]

theorem galClass_mul (σ τ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k)
    (hτ : ∀ k : K, τ (σ₀ k) = σ₀ k) :
    galClass σ₀ hK (σ * τ) = galClass σ₀ hK σ * galClass σ₀ hK τ := by
  rw [galClass, ELL.map_mul, ELL.map_eq_galClass_smul σ₀ hK τ hτ,
    ELL.map_eq_galClass_smul σ₀ hK σ hσ, ← ellMulAction_mul_smul]
  simp only [ellMulAction_smul, Equiv.symm_apply_apply, mul_one]

theorem galClass_eq_one_iff (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (x : ELL K) :
    galClass σ₀ hK σ = 1 ↔ σ (ELL.j x) = ELL.j x := by
  rw [apply_j_eq_j_galClass_smul σ₀ hK σ hσ]
  constructor
  · intro h
    rw [h, ellMulAction_one_smul]
  · intro h
    exact (ell_smul_eq_self_iff σ₀ hK _ x).1 (ELL.j_injective h)

end Elliptic
end GroundTheory.Global
