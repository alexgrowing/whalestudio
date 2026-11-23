import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite

open TensorProduct
namespace GlobalTheory.FieldExtensionExists

theorem exists_field_extension {R R' K : Type} [CommRing R] [CommRing R'] [Field K]
    (ρ : R →+* R') (hinj : Function.Injective ρ) (hfin : ρ.Finite) (φ : R →+* K) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (χ : R' →+* L),
      χ.comp ρ = (algebraMap K L).comp φ := by
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Algebra.IsIntegral R R' := ⟨fun x => hfin.to_isIntegral x⟩
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨q, -, hq, hqc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker φ) (⊥ : Ideal R') (by
    intro x hx
    have : ρ x = 0 := hx
    have h0 : x = 0 := hinj (this.trans (map_zero ρ).symm)
    rw [h0]; exact Ideal.zero_mem _)
  have hqc' : q.comap ρ = RingHom.ker φ := hqc
  let j : (R ⧸ RingHom.ker φ) →+* (R' ⧸ q) := Ideal.quotientMap q ρ hqc'.ge
  have hj : Function.Injective j := Ideal.quotientMap_injective' hqc'.le
  have hjf : j.Finite := by
    apply RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk (RingHom.ker φ))
    have : j.comp (Ideal.Quotient.mk (RingHom.ker φ)) = (Ideal.Quotient.mk q).comp ρ := by
      ext x; simp [j]
    rw [this]
    exact (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective).comp hfin
  letI : Algebra (R ⧸ RingHom.ker φ) (R' ⧸ q) := j.toAlgebra
  letI : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  haveI : Module.Finite (R ⧸ RingHom.ker φ) (R' ⧸ q) := hjf
  haveI : Nontrivial (K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _
      (RingHom.kerLift_injective φ) hj
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q))
  refine ⟨(K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) ⧸ M, Ideal.Quotient.field M, inferInstance,
    (inferInstance : Module.Finite K ((K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) ⧸ M)),
    (Ideal.Quotient.mk M).comp ((Algebra.TensorProduct.includeRight (R := R ⧸ RingHom.ker φ) (A := K)
      (B := R' ⧸ q)).toRingHom.comp (Ideal.Quotient.mk q)), ?_⟩
  ext r
  change Ideal.Quotient.mk M (Algebra.TensorProduct.includeRight (R := R ⧸ RingHom.ker φ) (A := K)
      (B := R' ⧸ q) (algebraMap (R ⧸ RingHom.ker φ) (R' ⧸ q) (Ideal.Quotient.mk _ r))) =
    Ideal.Quotient.mk M ((φ r) ⊗ₜ 1)
  rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem exists_extension : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ρ : R →+* R'),
    Function.Injective ρ → ρ.Finite → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
    ∀ (ψ : R →+* V), IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V')
      (f : V →+* V') (ψ' : R' →+* V'), GlobalTheory.LN.CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ' ∧
      ψ'.comp ρ = f.comp ψ := by
  intro R R' _ _ _ _ ρ hinj hfin V _ _ _ hV ψ hψ
  obtain ⟨h1, h2, h3⟩ := hV
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  obtain ⟨L, _, _, _, χ, hχ⟩ := exists_field_extension ρ hinj hfin ((algebraMap V (FractionRing V)).comp ψ)
  obtain ⟨W, _, _, hW1, hW2, _, _, _, hc, -, hf, hl, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  have hWL : Function.Injective (algebraMap W L) := IsFractionRing.injective W L
  have hmem : ∀ x : R', ∃ w : W, algebraMap W L w = χ x := by
    intro x
    obtain ⟨P, hP, hPx⟩ := hfin.to_isIntegral x
    refine hint (χ x) ⟨P.map ψ, hP.map ψ, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.comp_assoc, ← hχ, ← Polynomial.hom_eval₂, hPx, map_zero]
  choose g hg using hmem
  let ψ' : R' →+* W :=
    { toFun := g
      map_one' := hWL (by simp [hg])
      map_mul' := fun x y => hWL (by simp [hg])
      map_zero' := hWL (by simp [hg])
      map_add' := fun x y => hWL (by simp [hg]) }
  have hcomp : ψ'.comp ρ = (algebraMap V W).comp ψ := by
    ext r
    apply hWL
    have e1 := RingHom.congr_fun hχ r
    have e2 := RingHom.congr_fun hc (ψ r)
    simp only [RingHom.comp_apply] at e1 e2 ⊢
    rw [e2, ← e1]
    exact hg _
  have hloc : IsLocalHom (ψ'.comp ρ) := by rw [hcomp]; infer_instance
  have hmax : ((IsLocalRing.maximalIdeal W).comap ψ').IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ hfin.to_isIntegral
    have e : (IsLocalRing.maximalIdeal W).comap (ψ'.comp ρ) = IsLocalRing.maximalIdeal R :=
      ((IsLocalRing.local_hom_TFAE (ψ'.comp ρ)).out 0 4).1 hloc
    rw [Ideal.comap_comap, e]
    infer_instance
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, ψ',
    ⟨hW1, hW2, charZero_of_injective_algebraMap hf⟩, hf, hl, ?_, hcomp⟩
  exact ((IsLocalRing.local_hom_TFAE ψ').out 0 4).2 (IsLocalRing.eq_maximalIdeal hmax)

end GlobalTheory.FieldExtensionExists
