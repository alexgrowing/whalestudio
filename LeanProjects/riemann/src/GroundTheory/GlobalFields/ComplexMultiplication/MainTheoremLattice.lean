import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimes
import GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphismPoints
import GroundTheory.ArithmeticGeometry.AbelianVarieties.TateCharpoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IsDedekindDomain
open scoped nonZeroDivisors

section VC

variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]

theorem homPt_vcHom (C : VariableChange F) (hC : C • A = B) (R : A.toAffine.Point) :
    homPt (vcHom C hC) R = vcPoint C hC R := by
  have h0 : vcHom C hC ≠ 0 := fun h ↦ vcPt_ne_zero C hC (congrArg Subtype.val h)
  rw [homPt, dif_neg h0, Isogeny.pointHom_apply]
  exact pointMap_eq_vcPoint C hC _ (isogOfHom_val _ h0) R

variable {A' B' : WeierstrassCurve F} [A'.IsElliptic] [B'.IsElliptic]

theorem homConstSet_conj (V : VariableChange F) (hV : V • A = B) (V' : VariableChange F)
    (hV' : V' • A' = B') :
    (homConstSet A A' : Set F) =
      ((homConst B' A' (vcHom V'⁻¹ (inv_smul_eq_of_smul_eq V' hV')) *
        homConst A B (vcHom V hV)) * ·) '' homConstSet B B' := by
  set Q := vcHom V hV
  set R := vcHom V'⁻¹ (inv_smul_eq_of_smul_eq V' hV')
  set Q' := vcHom V⁻¹ (inv_smul_eq_of_smul_eq V hV)
  set R' := vcHom V' hV'
  have e1 : homConst B A Q' * homConst A B Q = 1 := homConst_vcHom_mul_inv V hV
  have e2 : homConst B' A' R * homConst A' B' R' = 1 := homConst_vcHom_mul_inv V' hV'
  ext z
  simp only [SetLike.mem_coe, Set.mem_image]
  constructor
  · intro hz
    refine ⟨homConst A' B' R' * z * homConst B A Q', homConstSet_le_mul Q' R' hz, ?_⟩
    linear_combination (homConst A B Q * homConst B A Q' * z) * e2 + z * e1
  · rintro ⟨w, hw, rfl⟩
    have := homConstSet_le_mul Q R hw
    convert this using 1
    ring

end VC

section Lattice

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ) (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

theorem latticeEnd_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    latticeEnd L = latticeEnd L' := by
  ext α
  show (∀ l ∈ L.lattice, α * l ∈ L.lattice) ↔ (∀ l ∈ L'.lattice, α * l ∈ L'.lattice)
  rw [h]

include hK in

theorem latticeEnd_eq_cmRing_of_lattice_eq {L : PeriodPair} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : L.lattice = idealLattice σ₀ 𝔞) : latticeEnd L = cmRing σ₀ := by
  rw [latticeEnd_eq_of_lattice_eq (L' := idealPeriodPair σ₀ hK 𝔞)
    (h.trans (lattice_idealPeriodPair σ₀ hK 𝔞).symm), latticeEnd_idealPeriodPair]

include hK in

theorem exists_unit_of_forall_mem_iff (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {c : ℂ}
    (hc : ∀ z, z ∈ idealLattice σ₀ J ↔ c * z ∈ idealLattice σ₀ J) :
    ∃ ε : (𝓞 K)ˣ, c = σ₀ (algebraMap (𝓞 K) K ε) := by
  have hP := lattice_idealPeriodPair σ₀ hK J
  have hPend := latticeEnd_idealPeriodPair σ₀ hK J
  have hne : ∃ z, z ∉ idealLattice σ₀ J := by
    by_contra h
    push Not at h
    have h1 : (Real.sqrt 2 : ℂ) * (idealPeriodPair σ₀ hK J).ω₁ ∉ (idealPeriodPair σ₀ hK J).lattice :=
      sqrt_two_mul_notMem _
    rw [hP] at h1
    exact h1 (h _)
  obtain ⟨z₀, hz₀⟩ := hne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hz₀ ((hc z₀).2 (by rw [zero_mul]; exact zero_mem _))
  have mult : ∀ d : ℂ, (∀ l ∈ idealLattice σ₀ J, d * l ∈ idealLattice σ₀ J) → d ∈ cmRing σ₀ := by
    intro d hd
    rw [← hPend]
    intro l hl
    rw [hP] at hl ⊢
    exact hd l hl
  obtain ⟨a, ha⟩ := (mem_cmRing σ₀).1 (mult c fun l hl ↦ (hc l).1 hl)
  obtain ⟨b, hb⟩ := (mem_cmRing σ₀).1 (mult c⁻¹ fun l hl ↦ (hc _).2 (by
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]; exact hl))
  have hinj : Function.Injective (σ₀.comp (algebraMap (𝓞 K) K)) :=
    σ₀.injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hab : a * b = 1 := hinj (by
    simp only [RingHom.comp_apply, map_mul, map_one]
    rw [ha, hb, mul_inv_cancel₀ hc0])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩

include hK in

theorem exists_unit_pointMap_vcPoint (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L L' : PeriodPair)
    (hL : L.lattice = idealLattice σ₀ 𝔞) (hL' : L'.lattice = idealLattice σ₀ ↑(𝔟 * 𝔞))
    {A A' : WeierstrassCurve ℂ} [A.IsElliptic] [A'.IsElliptic]
    (V : VariableChange ℂ) (hV : V • weierstrassCurve L = A)
    (V' : VariableChange ℂ) (hV' : V' • weierstrassCurve L' = A') (φ : Isogeny A A')
    (hφ : (homConstSet A A' : Set ℂ) = (invConst φ * ·) '' idealLattice σ₀ 𝔟) :
    ∃ u : (𝓞 K)ˣ, ∀ z : ℂ, φ.pointMap (vcPoint V hV (toPoint L z)) =
      vcPoint V' hV' (toPoint L' (σ₀ (algebraMap (𝓞 K) K u) * z)) := by
  classical
  set Q := vcHom V hV
  set R := vcHom V'⁻¹ (inv_smul_eq_of_smul_eq V' hV')
  set c := homConst A' (weierstrassCurve L') R * homConst (weierstrassCurve L) A Q
  have hset := homConstSet_conj V hV V' hV'

  set Φ := homComp R (homComp φ.toHom Q)
  have hΦ : homConst _ _ Φ = c * invConst φ := by
    rw [homConst_homComp, homConst_homComp, homConst_toHom]
    ring
  have hc0 : c ≠ 0 := by
    intro h0
    have e := homConst_vcHom_mul_inv V' hV'
    have e' := homConst_vcHom_mul_inv V hV
    simp only [c, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · rw [h0, zero_mul] at e; exact zero_ne_one e
    · rw [h0, mul_zero] at e'; exact zero_ne_one e'
  have hΦ0 : Φ ≠ 0 := by
    intro h
    have := congrArg (homConst _ _) h
    rw [hΦ, map_zero] at this
    exact mul_ne_zero hc0 (invConst_ne_zero φ) this
  set ψ := isogOfHom Φ hΦ0
  have hψc : invConst ψ = c * invConst φ := by
    rw [← homConst_toHom, isogOfHom_toHom, hΦ]
  have hLend := latticeEnd_eq_cmRing_of_lattice_eq σ₀ hK hL
  have hL'' : L'.lattice = idealLattice σ₀ ↑(𝔟⁻¹)⁻¹ * L.lattice := by
    rw [hL', inv_inv, hL, Units.val_mul, idealLattice_mul]
  have hψ : (homConstSet (weierstrassCurve L) (weierstrassCurve L') : Set ℂ) =
      (invConst ψ * ·) '' idealLattice σ₀ ↑(𝔟⁻¹)⁻¹ := by
    rw [inv_inv, hset, hφ, Set.image_image, hψc]
    congr 1
    funext x
    ring
  obtain ⟨u, -, hu⟩ := exists_unit_of_homConstSet_eq σ₀ hK L L' hLend 𝔟⁻¹ hL'' ψ hψ
  refine ⟨u, fun z ↦ ?_⟩
  have h1 := hu z
  rw [isogOfHom_toHom, TateCharpoly.homPt_homComp, TateCharpoly.homPt_homComp, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, homPt_vcHom, homPt_vcHom, homPt_toHom, Isogeny.pointHom_apply] at h1
  have h2 := congrArg (vcPoint V' hV') h1
  rwa [vcPoint_vcPoint_of_eq_inv V'⁻¹ V' (inv_inv V').symm] at h2

end Lattice

end

end Elliptic
end GroundTheory.Global
