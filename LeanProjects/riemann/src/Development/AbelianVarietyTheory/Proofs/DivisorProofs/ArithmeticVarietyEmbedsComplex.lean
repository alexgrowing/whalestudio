import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Cardinal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.FnEmb

theorem mk_le_of_isFractionRing (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] :
    #K ≤ max #A ℵ₀ := by
  have := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  exact Algebra.IsAlgebraic.cardinalMk_le_max A K

theorem nonempty_ringHom_complex (K : Type) [Field K] [CharZero K] (hK : #K ≤ 𝔠) : Nonempty (K →+* ℂ) := by
  let A := MvPolynomial ℝ K
  let F := FractionRing A
  let L := AlgebraicClosure F
  have hA : #A = 𝔠 := by
    rw [MvPolynomial.cardinalMk_eq_max, mk_real, max_eq_right hK, max_eq_left aleph0_le_continuum]
  have hinj : Function.Injective ((algebraMap F L).comp (algebraMap A F)) :=
    (algebraMap F L).injective.comp (IsFractionRing.injective A F)
  have : CharZero L := charZero_of_injective_ringHom hinj
  have hL : #L = 𝔠 := by
    apply le_antisymm
    · refine (Algebra.IsAlgebraic.cardinalMk_le_max F L).trans (max_le ?_ aleph0_le_continuum)
      exact (mk_le_of_isFractionRing A F).trans (max_le hA.le aleph0_le_continuum)
    · rw [← hA]
      exact Cardinal.mk_le_of_injective hinj
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (by rw [hL]; exact aleph0_lt_continuum) (Cardinal.eq.1 (by rw [hL, mk_complex]))
  exact ⟨(e : L →+* ℂ).comp (((algebraMap F L).comp (algebraMap A F)).comp MvPolynomial.C)⟩

theorem mk_le_aleph0_of_finiteType (A : Type) [CommRing A] [Algebra.FiniteType ℤ A] : #A ≤ ℵ₀ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType ℤ A)
  refine (Cardinal.mk_le_of_surjective hf).trans (MvPolynomial.cardinalMk_le_max.trans ?_)
  simp

theorem nonempty_functionField_ringHom_complex : ∀ (k : Type) [CommRing k] (B : Scheme.{0}) [IsIntegral B]
    (q : B ⟶ Sp k) (d : ℕ), IsArithVar q d → Nonempty (B.functionField →+* ℂ) := by
  intro k _ B _ q d hB
  have hc := hB.charZero
  have : CharZero B.functionField :=
    charZero_of_injective_ringHom (B.germToFunctionField_injective ⊤)
  obtain ⟨N, j, _, hj⟩ := hB.isProjOver
  have := isProper_str k N
  have : IsProper q := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hB.finite)
  let t := q ≫ spMap (Int.castRingHom k)
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    B.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint B)) isOpen_univ
  have hU' : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨_, hx⟩⟩
  have hft : (t.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType t inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU'⟩ le_top
  have hft' : ((t.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of ℤ)).inv.hom).FiniteType :=
    hft.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (.of ℤ)).symm.commRingCatIsoToRingEquiv.surjective)
  rw [RingHom.ext_int ((t.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of ℤ)).inv.hom) (algebraMap ℤ Γ(B, U))] at hft'
  have : Algebra.FiniteType ℤ Γ(B, U) := RingHom.finiteType_algebraMap.1 hft'
  have := functionField_isFractionRing_of_isAffineOpen B U hU'
  refine nonempty_ringHom_complex _ ((mk_le_of_isFractionRing Γ(B, U) B.functionField).trans ?_)
  exact (max_le (mk_le_aleph0_of_finiteType _) le_rfl).trans aleph0_le_continuum

end GlobalTheory.FnEmb
