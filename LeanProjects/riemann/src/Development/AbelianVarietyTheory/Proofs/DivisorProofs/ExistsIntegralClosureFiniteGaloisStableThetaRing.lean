import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEndOfEighthPowerOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationModelFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithBaseFiniteContainingRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.NormalClosureRing

theorem exists_integralClosure_finite : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [ArithBase o₁ Ω₁] (R₁ : Subalgebra o₁ Ω₁), R₁.FG → (∀ x : Ω₁, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b) → ∀ {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [ArithBase o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] (κ : o₁ →+* o₂), κ.Finite → (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) → ∃ (R : Subalgebra o₂ Ω₂) (h : R₁ →+* R), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a) ∧ h.Finite ∧ IsIntegrallyClosed R ∧ ∀ σ : Ω₂ ≃ₐ[Ω₁] Ω₂, ∀ x ∈ R, σ x ∈ R := by
  intro o₁ Ω₁ _ _ _ _ R₁ hR₁ hfrac o₂ Ω₂ _ _ _ _ _ _ κ hκ hcomp
  haveI : IsDedekindDomain o₁ := ArithBase.ded (Ω := Ω₁)
  haveI : CharZero Ω₁ := ArithBase.char (o := o₁)
  have hinj₁ : Function.Injective (algebraMap o₁ Ω₁) := ArithBase.inj
  haveI : CharZero o₁ := (algebraMap o₁ Ω₁).charZero
  haveI : Algebra.FiniteType o₁ R₁ := (Subalgebra.fg_iff_finiteType R₁).mp hR₁
  haveI : FaithfulSMul o₁ R₁ := (faithfulSMul_iff_algebraMap_injective _ _).mpr fun a b hab => hinj₁ (congrArg Subtype.val hab)
  haveI : FaithfulSMul R₁ Ω₁ := (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  haveI : IsFractionRing R₁ Ω₁ := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hfrac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
  haveI : IsScalarTower R₁ Ω₁ Ω₂ := inferInstance
  let C := integralClosure R₁ Ω₂
  have hmem : ∀ x : o₂, algebraMap o₂ Ω₂ x ∈ C := by
    intro x
    obtain ⟨p, hp, hpx⟩ := hκ.to_isIntegral x
    refine ⟨p.map (algebraMap o₁ R₁), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have := congrArg (algebraMap o₂ Ω₂) hpx
    rw [Polynomial.hom_eval₂, map_zero, hcomp] at this
    exact this
  let R : Subalgebra o₂ Ω₂ :=
    { toSubsemiring := C.toSubsemiring
      algebraMap_mem' := hmem }
  let h : R₁ →+* R := (algebraMap R₁ Ω₂).codRestrict R fun a => (isIntegral_algebraMap : IsIntegral R₁ (algebraMap R₁ Ω₂ a))
  have hh : ∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a := fun a => rfl
  letI : Algebra R₁ R := h.toAlgebra
  haveI : IsScalarTower R₁ R Ω₂ := .of_algebraMap_eq fun a => rfl
  haveI : IsIntegralClosure R R₁ Ω₂ :=
    { algebraMap_injective := Subtype.val_injective
      isIntegral_iff := fun {x} => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩ }
  have hfin : h.Finite := GlobalTheory.finite_of_isIntegralClosure_dedekind o₁ R₁ Ω₁ Ω₂ R
  have hic : IsIntegrallyClosed R := integralClosure.isIntegrallyClosedOfFiniteExtension (R := R₁) Ω₁ (L := Ω₂)
  haveI : Module.Finite R₁ C := GlobalTheory.finite_integralClosure_dedekind o₁ R₁ Ω₁ Ω₂
  classical
  have hfg : R.FG := by
    obtain ⟨s, hs⟩ := hR₁
    obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule R₁ C).FG)
    refine ⟨s.image (algebraMap Ω₁ Ω₂) ∪ t.image Subtype.val, le_antisymm ?_ ?_⟩
    · rw [Algebra.adjoin_le_iff]
      intro y hy
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe] at hy
      rcases hy with ⟨a, ha, rfl⟩ | ⟨z, -, rfl⟩
      · have ha' : a ∈ R₁ := hs ▸ Algebra.subset_adjoin ha
        exact (h ⟨a, ha'⟩).2
      · exact z.2
    · set A := Algebra.adjoin o₂ ((s.image (algebraMap Ω₁ Ω₂) ∪ t.image Subtype.val : Finset Ω₂) : Set Ω₂)
      have hR₁A : ∀ z ∈ Algebra.adjoin o₁ (s : Set Ω₁), algebraMap Ω₁ Ω₂ z ∈ A := by
        intro z hz
        induction hz using Algebra.adjoin_induction with
        | mem z hz => exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hz)))
        | algebraMap r =>
          have := congrArg (fun f => f r) hcomp
          simp only [RingHom.comp_apply] at this
          rw [← this]
          exact A.algebraMap_mem _
        | add x y _ _ hx hy => rw [map_add]; exact A.add_mem hx hy
        | mul x y _ _ hx hy => rw [map_mul]; exact A.mul_mem hx hy
      suffices key : ∀ y : C, y ∈ Submodule.span R₁ (t : Set C) → (y : Ω₂) ∈ A from
        fun x hx => key ⟨x, hx⟩ (ht ▸ Submodule.mem_top)
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hy)))
      | zero => exact A.zero_mem
      | add y z _ _ hy hz => exact A.add_mem hy hz
      | smul r y _ hy =>
        convert A.mul_mem (hR₁A r.1 (hs ▸ r.2)) hy using 1
        first | rfl | exact Algebra.smul_def r (y : Ω₂) | simp [Algebra.smul_def]
  refine ⟨R, h, hfg, ?_, hh, hfin, hic, ?_⟩
  · intro x
    have hxi : IsIntegral Ω₁ x := Algebra.IsIntegral.isIntegral x
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors R₁) x hxi
    have hm0 : algebraMap R₁ Ω₂ (m : R₁) ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply R₁ Ω₁ Ω₂]
      exact (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors m.2)
    refine ⟨_, hm, algebraMap R₁ Ω₂ (m : R₁), isIntegral_algebraMap, ?_⟩
    rw [Submonoid.smul_def, Algebra.smul_def, mul_div_cancel_left₀ _ hm0]
  · intro σ x hx
    exact (show IsIntegral R₁ x from hx).map (σ.toAlgHom.restrictScalars R₁)

end GlobalTheory.Poinc.NormalClosureRing
