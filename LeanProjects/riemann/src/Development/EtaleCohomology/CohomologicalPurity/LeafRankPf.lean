import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafRankPf

theorem finrank_tensor_surj {A B K X : Type*} [CommRing A] [CommRing B] [Field K] [Algebra A B] [Algebra A K]
    [Algebra B K] [IsScalarTower A B K] [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
    (h : Function.Surjective (algebraMap A B)) :
    Module.finrank K (K ⊗[A] X) = Module.finrank K (K ⊗[B] X) := by
  have : CompatibleSMul A B K X := CompatibleSMul.of_algebraMap_surjective K X h
  exact (LinearEquiv.finrank_eq (equivOfCompatibleSMul A B K K X)).symm

theorem finrank_tensor_cotangent {A K : Type*} [CommRing A] [Field K] [Algebra A K] (J : Ideal A)
    (hJ : ∀ a ∈ J, algebraMap A K a = 0) :
    Module.finrank K (K ⊗[A] J) = Module.finrank K (K ⊗[A] J.Cotangent) := by
  have hex := lTensor_exact K (LinearMap.exact_subtype_mkQ (J • (⊤ : Submodule A J)))
    (Submodule.mkQ_surjective _)
  have hz : ∀ (x : K) (z : J), z ∈ J • (⊤ : Submodule A J) → (x ⊗ₜ[A] z : K ⊗[A] J) = 0 := by
    intro x z hz
    refine Submodule.smul_induction_on (p := fun z => (x ⊗ₜ[A] z : K ⊗[A] J) = 0) hz ?_ ?_
    · intro a ha m _
      rw [← smul_tmul, Algebra.smul_def, hJ a ha, zero_mul, zero_tmul]
    · intro u v hu hv
      rw [tmul_add, hu, hv, add_zero]
  have h0 : LinearMap.lTensor K (J • (⊤ : Submodule A J)).subtype = 0 := by
    ext x z; exact hz x z z.2
  have hinj : Function.Injective (LinearMap.baseChange K (Ideal.toCotangent J)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have : y ∈ LinearMap.range (LinearMap.lTensor K (J • (⊤ : Submodule A J)).subtype) :=
      (hex y).mp (by rw [LinearMap.baseChange_eq_ltensor] at hy; exact hy)
    rw [h0, LinearMap.range_zero] at this
    simpa using this
  have hsurj : Function.Surjective (LinearMap.baseChange K (Ideal.toCotangent J)) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective K (Submodule.mkQ_surjective _)
  exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩)

theorem _root_.LateralTheory.CohomologicalPurity.ChartCut.LeafRank_of : LateralTheory.CohomologicalPurity.ChartCut.LeafRank := by
  intro e d R A _ _ _ I p _ hIp hA hB
  have hk : ∀ a ∈ I, algebraMap A p.ResidueField a = 0 := fun a ha =>
    Ideal.algebraMap_residueField_eq_zero.mpr (hIp ha)
  letI : Algebra (A ⧸ I) p.ResidueField := (Ideal.Quotient.lift I (algebraMap A p.ResidueField) hk).toAlgebra
  haveI : IsScalarTower A (A ⧸ I) p.ResidueField := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have hsurj : Function.Surjective (algebraMap A (A ⧸ I)) := Ideal.Quotient.mk_surjective
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top ‹_›) hIp)
  haveI : Nontrivial A := (Ideal.Quotient.mk I).domain_nontrivial
  haveI : Algebra.IsStandardSmooth R A := hA.isStandardSmooth
  haveI : Algebra.IsStandardSmooth R (A ⧸ I) := hB.isStandardSmooth
  have rA : Module.finrank A Ω[A⁄R] = e + d := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (e + d))
  have rB : Module.finrank (A ⧸ I) Ω[(A ⧸ I)⁄R] = e := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential e)
  have eqv := AlgebraTensorModule.cancelBaseChange A (A ⧸ I) p.ResidueField p.ResidueField Ω[A⁄R]
  have h1 : Module.finrank p.ResidueField (p.ResidueField ⊗[A] ((A ⧸ I) ⊗[A] Ω[A⁄R])) = e + d := by
    rw [finrank_tensor_surj hsurj, LinearEquiv.finrank_eq eqv, Module.finrank_baseChange, rA]
  have h2 : Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[(A ⧸ I)⁄R]) = e := by
    rw [finrank_tensor_surj hsurj, Module.finrank_baseChange, rB]
  have hK : RingHom.ker (algebraMap A (A ⧸ I)) = I := Ideal.mk_ker
  have h3 : Module.finrank p.ResidueField (p.ResidueField ⊗[A] I) =
      Module.finrank p.ResidueField (p.ResidueField ⊗[A] (RingHom.ker (algebraMap A (A ⧸ I))).Cotangent) := by
    rw [← finrank_tensor_cotangent _ (by rw [hK]; exact hk), hK]
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := R) (P := A) (A := A ⧸ I) hsurj).mp inferInstance
  have e0 : Function.Exact (KaehlerDifferential.kerCotangentToTensor R A (A ⧸ I))
      ((KaehlerDifferential.mapBaseChange R A (A ⧸ I)).restrictScalars A) :=
    KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A (A ⧸ I) hsurj
  have s0 : Function.Surjective ((KaehlerDifferential.mapBaseChange R A (A ⧸ I)).restrictScalars A) :=
    KaehlerDifferential.mapBaseChange_surjective R A (A ⧸ I) hsurj
  set f := (KaehlerDifferential.kerCotangentToTensor R A (A ⧸ I)).baseChange p.ResidueField
  set g := ((KaehlerDifferential.mapBaseChange R A (A ⧸ I)).restrictScalars A).baseChange p.ResidueField
  have hex : Function.Exact f g := by
    simpa only [f, g, LinearMap.baseChange_eq_ltensor] using lTensor_exact p.ResidueField e0 s0
  have hg : Function.Surjective g := by
    simpa only [g, LinearMap.baseChange_eq_ltensor] using LinearMap.lTensor_surjective p.ResidueField s0
  have hf : Function.Injective f := by
    have hc : (l.baseChange p.ResidueField).comp f = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hl, LinearMap.baseChange_id]
    exact Function.LeftInverse.injective (g := l.baseChange p.ResidueField) (fun x => by
      simpa using LinearMap.congr_fun hc x)
  have : CompatibleSMul A (A ⧸ I) p.ResidueField ((A ⧸ I) ⊗[A] Ω[A⁄R]) :=
    CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  haveI : Module.Finite p.ResidueField (p.ResidueField ⊗[A] ((A ⧸ I) ⊗[A] Ω[A⁄R])) :=
    Module.Finite.equiv ((LinearEquiv.restrictScalars p.ResidueField
      (equivOfCompatibleSMul A (A ⧸ I) p.ResidueField p.ResidueField ((A ⧸ I) ⊗[A] Ω[A⁄R])).symm).trans
      eqv).symm
  have hrk := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.mpr hg, finrank_top, hex.linearMap_ker_eq, LinearMap.finrank_range_of_inj hf,
    h1, h2] at hrk
  rw [h3]; omega

end LateralTheory.CohomologicalPurity.LeafRankPf
