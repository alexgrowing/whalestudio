import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityGalois
import GroundTheory.GlobalFields.ComplexMultiplication.DualDescent

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IsDedekindDomain
open scoped nonZeroDivisors

universe u

section VC

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F]
  {E E' E₁ E₁' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E₁.IsElliptic]
  [E₁'.IsElliptic]

theorem homConstSet_vc_pair (C C' : VariableChange F) (h : C • E = E₁) (h' : C' • E' = E₁') :
    ∃ c : F, c ≠ 0 ∧ (homConstSet E₁ E₁' : Set F) = (c * ·) '' homConstSet E E' ∧
      (homConstSet E₁' E₁ : Set F) = (c⁻¹ * ·) '' homConstSet E' E := by
  set Q := vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)
  set R := vcHom C' h'
  set Q' := vcHom C h
  set R' := vcHom C'⁻¹ (inv_smul_eq_of_smul_eq C' h')
  have e1 : homConst E₁ E Q * homConst E E₁ Q' = 1 := homConst_vcHom_mul_inv C h
  have e2 : homConst E₁' E' R' * homConst E' E₁' R = 1 := homConst_vcHom_mul_inv C' h'
  set c := homConst E' E₁' R * homConst E₁ E Q
  have hc : c * (homConst E₁' E' R' * homConst E E₁ Q') = 1 := by
    linear_combination (homConst E₁' E' R' * homConst E' E₁' R) * e1 + e2
  have hcinv : c⁻¹ = homConst E E₁ Q' * homConst E₁' E' R' := by
    rw [inv_eq_of_mul_eq_one_right hc, mul_comm]
  refine ⟨c, left_ne_zero_of_mul_eq_one hc, ?_, ?_⟩
  · ext z
    simp only [SetLike.mem_coe, Set.mem_image]
    constructor
    · intro hz
      refine ⟨homConst E₁' E' R' * z * homConst E E₁ Q', homConstSet_le_mul Q' R' hz, ?_⟩
      linear_combination z * hc
    · rintro ⟨w, hw, rfl⟩
      have := homConstSet_le_mul Q R hw
      convert this using 1
      ring
  · ext z
    simp only [SetLike.mem_coe, Set.mem_image]
    constructor
    · intro hz
      refine ⟨homConst E₁ E Q * z * homConst E' E₁' R, homConstSet_le_mul R Q hz, ?_⟩
      rw [hcinv]
      linear_combination z * hc
    · rintro ⟨w, hw, rfl⟩
      have := homConstSet_le_mul R' Q' hw
      convert this using 1
      rw [hcinv]
      ring

end VC

section Invariant

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F]
  {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

theorem invConst_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    invConst (ψ.comp φ) = invConst ψ * invConst φ := by
  rw [← homConst_toHom, ← Isogeny.homComp_toHom, homConst_homComp, homConst_toHom, homConst_toHom]

theorem invConst_mem_homConstSet (φ : Isogeny E E') : invConst φ ∈ homConstSet E E' :=
  mem_homConstSet.2 ⟨φ.toHom, homConst_toHom φ⟩

theorem invConst_dualOver_mul (φ : Isogeny E E') :
    invConst (dualOver φ) * invConst φ = φ.degree := by
  rw [← invConst_comp, dualOver_comp, invConst_mulIsogeny]
  push_cast
  rfl

variable [CharZero F]

theorem invConst_ne_zero (φ : Isogeny E E') : invConst φ ≠ 0 := by
  intro h
  have := invConst_dualOver_mul φ
  rw [h, mul_zero] at this
  exact (Nat.cast_ne_zero.2 φ.degree_pos.ne') this.symm

end Invariant

section Lattice

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ)

theorem idealLattice_one_mul_lattice (L : PeriodPair) (hL : latticeEnd L = cmRing σ₀) :
    idealLattice σ₀ 1 * L.lattice = L.lattice := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro m hm l hl
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ₀).1 hm
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    have ha : σ₀ (algebraMap (𝓞 K) K a) ∈ latticeEnd L := hL ▸ (mem_cmRing σ₀).2 ⟨a, rfl⟩
    exact ha l hl
  · intro l hl
    have h1 : (1 : ℂ) ∈ idealLattice σ₀ 1 :=
      (mem_idealLattice σ₀).2 ⟨1, (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, map_one σ₀⟩
    simpa using Submodule.mul_mem_mul h1 hl

variable (hK : finrank ℚ K = 2) [IsTotallyComplex K]

theorem homConstSet_pair_of_smul {E E' : CMCurve K} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : (ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll = E'.toEll) :
    ∃ c : ℂ, c ≠ 0 ∧ (homConstSet E.curve E'.curve : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ ∧
      (homConstSet E'.curve E.curve : Set ℂ) = (c⁻¹ * ·) '' idealLattice σ₀ ↑𝔞 := by
  obtain ⟨L, C, hL, hC, hE⟩ := E.exists_lattice σ₀ hK
  obtain ⟨L', hL'lat, hL'⟩ := exists_lattice_mul σ₀ hK L hL 𝔞
  have h1 := classGroup_smul_ellOf σ₀ hK L L' hL hL' 𝔞 hL'lat
  have h2 : E'.toEll = (CMCurve.ofLattice σ₀ L' hL').toEll := by
    rw [← h, ← hE]
    exact h1
  obtain ⟨C', hC'⟩ := (CMCurve.toEll_eq_iff _ _).1 h2
  have hC'' : C' • E'.curve = weierstrassCurve L' := hC'
  obtain ⟨d, hd, hset, hset'⟩ := homConstSet_vc_pair C C' hC hC''
  rw [homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L L' hL 𝔞⁻¹ hL'lat] at hset
  have hLL : L.lattice = idealLattice σ₀ ↑𝔞 * L'.lattice := by
    rw [hL'lat, ← mul_assoc, ← idealLattice_mul, Units.mul_inv, idealLattice_one_mul_lattice σ₀ L hL]
  rw [homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L' L hL' 𝔞 hLL] at hset'
  exact ⟨d⁻¹, inv_ne_zero hd, eq_image_mul_inv hd hset, eq_image_mul_inv (inv_ne_zero hd) hset'⟩

include hK in

theorem homConstSet_symm {E E' : CMCurve K} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {b : ℂ} (hb : b ≠ 0)
    (hset : (homConstSet E.curve E'.curve : Set ℂ) = (b * ·) '' idealLattice σ₀ ↑𝔞⁻¹) :
    (homConstSet E'.curve E.curve : Set ℂ) = (b⁻¹ * ·) '' idealLattice σ₀ ↑𝔞 := by
  obtain ⟨c, hc, h1, h2⟩ :=
    homConstSet_pair_of_smul σ₀ hK (smul_toEll_of_homConstSet σ₀ hK hb hset)

  have e : (idealLattice σ₀ ↑𝔞⁻¹ : Set ℂ) = ((c⁻¹ * b) * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
    rw [← image_mul_image_mul, ← hset, h1, image_mul_image_mul, inv_mul_cancel₀ hc]
    simp

  have e' := idealLattice_mul_homothetic σ₀ (↑𝔞⁻¹) (↑𝔞 * ↑𝔞) e
  have hmul : (↑𝔞 * ↑𝔞 * ↑𝔞⁻¹ : FractionalIdeal (𝓞 K)⁰ K) = ↑𝔞 := by
    rw [mul_assoc, Units.mul_inv, mul_one]
  rw [← idealLattice_mul, hmul] at e'
  rw [h2]
  calc (c⁻¹ * ·) '' (idealLattice σ₀ ↑𝔞 : Set ℂ)
      = (c⁻¹ * ·) '' (((c⁻¹ * b)⁻¹ * ·) '' (idealLattice σ₀ ↑𝔞 : Set ℂ)) := by
        rw [← eq_image_mul_inv (mul_ne_zero (inv_ne_zero hc) hb) e']
    _ = (b⁻¹ * ·) '' (idealLattice σ₀ ↑𝔞 : Set ℂ) := by
        rw [image_mul_image_mul]
        congr 2
        field_simp

end Lattice

section Prime

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def primeUnit : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)

theorem primeUnit_val : ((primeUnit v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
    v.asIdeal :=
  rfl

theorem primeUnit_inv_val :
    (((primeUnit v)⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [Units.val_inv_eq_inv_val, primeUnit_val]

theorem classGroup_mk_primeUnit :
    ClassGroup.mk K (primeUnit v) =
      ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  rw [← ClassGroup.mk_mk0 K]
  rfl

theorem absNorm_dvd_of_natCast_mem (hv : (Ideal.absNorm v.asIdeal).Prime) {n : ℕ}
    (hn : (n : 𝓞 K) ∈ v.asIdeal) : Ideal.absNorm v.asIdeal ∣ n := by
  by_contra h
  have hcop : Nat.Coprime (Ideal.absNorm v.asIdeal) n := (Nat.Prime.coprime_iff_not_dvd hv).2 h
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hp : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ∈ v.asIdeal := Ideal.absNorm_mem _
  have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
    have e := congrArg (Int.cast : ℤ → 𝓞 K) hab
    push_cast at e
    rw [← e]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hp) (v.asIdeal.mul_mem_left _ hn)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem inv_absNorm_notMem_inv (hK : finrank ℚ K = 2) (hv : (Ideal.absNorm v.asIdeal).Prime) :
    ((Ideal.absNorm v.asIdeal : K))⁻¹ ∉ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  set p := Ideal.absNorm v.asIdeal with hpdef
  intro hmem
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hv.ne_zero
  have hle : v.asIdeal ≤ Ideal.span {(p : 𝓞 K)} := by
    intro y hy
    have h1 := (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)).1 hmem
      (algebraMap (𝓞 K) K y) (FractionalIdeal.mem_coeIdeal_of_mem _ hy)
    obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [Ideal.mem_span_singleton']
    refine ⟨z, IsFractionRing.injective (𝓞 K) K ?_⟩
    rw [map_mul, hz, map_natCast]
    field_simp
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  have hnorm : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank, hK]
    simp
  rw [hnorm] at hdvd
  have := Nat.le_of_dvd hv.pos hdvd
  have h2 := hv.two_le
  nlinarith

end Prime

section Degree

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ) (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

include hK in

theorem degree_eq_absNorm {E E' : CMCurve K} (v : HeightOneSpectrum (𝓞 K))
    (hv : (Ideal.absNorm v.asIdeal).Prime) (φ : Isogeny E.curve E'.curve)
    (hφ : (homConstSet E.curve E'.curve : Set ℂ) =
      (invConst φ * ·) '' idealLattice σ₀ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    φ.degree = Ideal.absNorm v.asIdeal := by
  classical
  set p := Ideal.absNorm v.asIdeal with hpdef
  set c := invConst φ with hcdef
  have hc : c ≠ 0 := invConst_ne_zero φ
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hv.ne_zero
  have hφu : (homConstSet E.curve E'.curve : Set ℂ) =
      (c * ·) '' idealLattice σ₀ ↑(primeUnit v)⁻¹ := by
    rw [primeUnit_inv_val]; exact hφ
  have hsym := homConstSet_symm σ₀ hK hc hφu
  rw [primeUnit_val] at hsym

  have hpmem : (p : ℂ) ∈ idealLattice σ₀ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
    have hx : ((p : K)) ∈ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
      have := FractionalIdeal.mem_coeIdeal_of_mem (S := (𝓞 K)⁰) (P := K) (Ideal.absNorm_mem v.asIdeal)
      simpa using this
    simpa using map_mem_idealLattice σ₀ hx
  have hν : c⁻¹ * p ∈ homConstSet E'.curve E.curve := by
    have h' : c⁻¹ * (p : ℂ) ∈ (homConstSet E'.curve E.curve : Set ℂ) := by
      rw [hsym]; exact ⟨p, hpmem, rfl⟩
    exact h'
  obtain ⟨Q, hQ⟩ := mem_homConstSet.1 hν
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hQ
    exact mul_ne_zero (inv_ne_zero hc) hp0 hQ.symm
  set ν := isogOfHom Q hQ0 with hνdef
  have hνc : invConst ν = c⁻¹ * p := by rw [← homConst_toHom, isogOfHom_toHom, hQ]

  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hv.ne_zero
  have hcomp : ν.comp φ = mulIsogeny E.curve p hpz := by
    have h1 : endConst E.curve (ν.comp φ).toHom = endConst E.curve (mulIsogeny E.curve p hpz).toHom := by
      rw [endConst_apply, endConst_apply, homConst_toHom, homConst_toHom, invConst_comp, hνc,
        invConst_mulIsogeny]
      field_simp
      push_cast
      ring
    have h2 := congrArg Subtype.val (endConst_injective h1)
    exact Subtype.ext h2
  have hdeg1 : ν.degree * φ.degree = p ^ 2 := by
    rw [← Isogeny.degree_comp, hcomp, degree_mulIsogeny]
    simp

  have hdvd : p ∣ φ.degree := by
    have hd : invConst (dualOver φ) ∈ (homConstSet E'.curve E.curve : Set ℂ) :=
      invConst_mem_homConstSet _
    rw [hsym] at hd
    obtain ⟨z, hz, hz'⟩ := hd
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ₀).1 hz
    have e := invConst_dualOver_mul φ
    rw [← hcdef, ← hz'] at e
    simp only at e
    have hx' : σ₀ x = σ₀ (φ.degree : K) := by
      rw [map_natCast, ← e]
      field_simp
    have hxK : x = φ.degree := σ₀.injective hx'
    rw [hxK] at hx
    obtain ⟨y, hy, hy'⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    have : y = (φ.degree : 𝓞 K) := IsFractionRing.injective (𝓞 K) K (by rw [hy', map_natCast])
    rw [this] at hy
    exact absNorm_dvd_of_natCast_mem v hv hy
  obtain ⟨k, hk, hkdeg⟩ := (Nat.dvd_prime_pow hv).1 (Dvd.intro_left _ hdeg1)
  interval_cases k
  · rw [hkdeg, pow_zero] at hdvd
    exact absurd (Nat.le_of_dvd one_pos hdvd) (by have := hv.two_le; omega)
  · rw [hkdeg, pow_one]
  · exfalso
    have hν1 : ν.degree = 1 := by
      rw [hkdeg] at hdeg1
      have hp2 : 0 < p ^ 2 := pow_pos hv.pos 2
      nlinarith
    have e := invConst_dualOver_mul ν
    rw [hν1, hνc, Nat.cast_one] at e
    have hd : invConst (dualOver ν) ∈ (homConstSet E.curve E'.curve : Set ℂ) :=
      invConst_mem_homConstSet _
    rw [hφ] at hd
    obtain ⟨z, hz, hz'⟩ := hd
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ₀).1 hz
    rw [← hz'] at e
    simp only at e
    have e2 : σ₀ x * p = 1 := by
      rw [← e]
      field_simp
    have hx' : σ₀ x = σ₀ ((p : K))⁻¹ := by
      rw [map_inv₀, map_natCast]
      exact eq_inv_of_mul_eq_one_left e2
    rw [σ₀.injective hx'] at hx
    exact inv_absNorm_notMem_inv v hK hv hx

include hK in

theorem exists_isogeny_homConstSet_eq {E E' : CMCurve K} (v : HeightOneSpectrum (𝓞 K))
    (h : (ellMulAction σ₀ hK).smul
      (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) E.toEll = E'.toEll) :
    ∃ φ : Isogeny E.curve E'.curve, (homConstSet E.curve E'.curve : Set ℂ) =
      (invConst φ * ·) '' idealLattice σ₀ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  classical
  rw [← classGroup_mk_primeUnit] at h
  obtain ⟨c, hc, hset⟩ := homConstSet_of_smul σ₀ hK h
  rw [primeUnit_inv_val] at hset
  have h1 : (1 : ℂ) ∈ idealLattice σ₀ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    simpa using map_mem_idealLattice σ₀ (FractionalIdeal.one_mem_inv_coe_ideal v.ne_bot)
  have hcmem : c ∈ homConstSet E.curve E'.curve := by
    have h' : c ∈ (homConstSet E.curve E'.curve : Set ℂ) := by
      rw [hset]; exact ⟨1, h1, mul_one c⟩
    exact h'
  obtain ⟨Q, hQ⟩ := mem_homConstSet.1 hcmem
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hQ
    exact hc hQ.symm
  refine ⟨isogOfHom Q hQ0, ?_⟩
  rw [← homConst_toHom, isogOfHom_toHom, hQ]
  exact hset

end Degree

end

end Elliptic
end GroundTheory.Global
