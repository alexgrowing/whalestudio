import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocCpl
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HighestWeightSpaceFinite

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem max_of_fin {O D R : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing D]
    [CommRing R] [Algebra O R] [IsCO O R] (f : D →+* R) : ((maximalIdeal R).comap f).IsMaximal := by
  have hk : (maximalIdeal R).comap f = RingHom.ker ((res O R).toRingHom.comp f) := by
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, ← res_eq_zero_iff O R]
    rfl
  have hp : ((maximalIdeal R).comap f).IsPrime := Ideal.IsPrime.comap _
  rw [hk] at hp ⊢
  haveI : Finite (D ⧸ RingHom.ker ((res O R).toRingHom.comp f)) :=
    Finite.of_injective _ (RingHom.kerLift_injective _)
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

private theorem flat_dvr {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    (h : (maximalIdeal O).map (algebraMap O O') = maximalIdeal O') : Module.Flat O O' := by
  have hinj : Function.Injective (algebraMap O O') := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hne
    have hp : (RingHom.ker (algebraMap O O')).IsPrime := RingHom.ker_isPrime _
    have hm := eq_maximalIdeal (hp.isMaximal hne)
    refine IsDiscreteValuationRing.not_a_field O' ?_
    rw [← h, ← hm, Ideal.map_eq_bot_iff_le_ker]
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro z ⟨⟨a, ha⟩, hz⟩
  have h1 : algebraMap O O' a * z = 0 := by rw [← Algebra.smul_def]; exact hz
  refine (mul_eq_zero.1 h1).resolve_left fun h2 => nonZeroDivisors.ne_zero ha (hinj ?_)
  rw [h2, map_zero]

theorem UpperTheory.V.Fr.loc_flat :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (L.ι : S.A →+* L.R).Flat ∧ x.IsMaximal ∧ S.mB ≤ S.π x := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  refine ⟨?_, ?_, ?_⟩
  · have hA : IsNoetherianRing S.A := (gr_A hF hn S).2.2.2.2.2.1
    have hD : IsNoetherianRing (TensorProduct O L.O' S.A) := by
      have h1 : IsNoetherianRing (TensorProduct O S.A L.O') :=
        Algebra.FiniteType.isNoetherianRing S.A _
      exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv
    let ι' : TensorProduct O L.O' S.A →ₐ[L.O'] L.R :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) L.ι fun _ _ => Commute.all _ _
    have hι : ∀ a, ι' (1 ⊗ₜ a) = L.ι a := fun a => by simp [ι']
    have hc := loc_cpl hF hn S x L ι' hι
    haveI := max_of_fin (O := L.O') ι'.toRingHom
    have h1 : ι'.toRingHom.Flat := (@UpperTheory.V.CA.c3a _ _ _ _ _ ι'.toRingHom.toAlgebra _ _ _ hc).1
    haveI : Module.Flat O L.O' := flat_dvr L.unr
    have h2 : (Algebra.TensorProduct.includeRight (R := O) (A := L.O') (B := S.A)).toRingHom.Flat := by
      have h3 : (algebraMap S.A (TensorProduct O S.A L.O')).Flat := RingHom.flat_algebraMap_iff.2 inferInstance
      have h4 := h3.comp (RingHom.Flat.of_bijective (f := (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv.toRingHom)
        (Algebra.TensorProduct.comm O S.A L.O').bijective)
      exact h4
    have e : (L.ι : S.A →+* L.R) = ι'.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := O) (A := L.O') (B := S.A)).toRingHom :=
      RingHom.ext fun a => (hι a).symm
    rw [e]
    exact h2.comp h1
  · rw [← L.lies]
    exact max_of_fin (O := L.O') _
  · obtain ⟨h, hm⟩ := co_B hF hn S
    have h1 := max_of_fin (O := L.O') ((L.ι : S.A →+* L.R).comp (S.inc : S.B →+* S.A))
    rw [← Ideal.comap_comap, L.lies] at h1
    rw [← hm]
    exact (eq_maximalIdeal h1).ge
