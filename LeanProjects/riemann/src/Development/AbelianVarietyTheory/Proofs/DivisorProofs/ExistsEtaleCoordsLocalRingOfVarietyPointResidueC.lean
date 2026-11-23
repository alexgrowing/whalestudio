import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisOfKaehlerWedgeFreeGenerator
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleCoordLocal

open IsLocalRing KaehlerDifferential

theorem linearIndependent_one_tmul_D {k A : Type} [CommRing k] [CommRing A] [IsLocalRing A]
    [Algebra k A] [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k (ResidueField A)]
    {J : Type} (f : J → A) (hf : ∀ j, f j ∈ maximalIdeal A)
    (h : LinearIndependent (ResidueField A) (fun j =>
      ((maximalIdeal A).toCotangent ⟨f j, hf j⟩ : CotangentSpace A))) :
    LinearIndependent (ResidueField A) (fun j => (1 : ResidueField A) ⊗ₜ[A] D k A (f j)) := by
  have hs : Function.Surjective (algebraMap A (ResidueField A)) := residue_surjective
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := k) hs).mpr
    inferInstance
  have hker : maximalIdeal A = RingHom.ker (algebraMap A (ResidueField A)) := ker_residue.symm
  let c := Ideal.Cotangent.equivOfEq _ _ hker
  let e : CotangentSpace A →ₗ[A] ResidueField A ⊗[A] Ω[A⁄k] :=
    kerCotangentToTensor k A (ResidueField A) ∘ₗ c.toLinearMap
  have he : Function.Injective (e.extendScalarsOfSurjective hs) := hinj.comp c.injective
  have := h.map' (e.extendScalarsOfSurjective hs) (LinearMap.ker_eq_bot.2 he)
  have key : ⇑(e.extendScalarsOfSurjective hs) ∘ (fun j =>
      ((maximalIdeal A).toCotangent ⟨f j, hf j⟩ : CotangentSpace A)) =
      fun j => (1 : ResidueField A) ⊗ₜ[A] D k A (f j) := by
    funext j
    simp only [Function.comp_apply, LinearMap.extendScalarsOfSurjective_apply, e,
      LinearMap.comp_apply, LinearEquiv.coe_coe, c]
    rw [Ideal.Cotangent.equivOfEq_toCotangent, kerCotangentToTensor_toCotangent]
    rfl
  rw [key] at this
  exact this

theorem span_one_tmul_D {k A : Type} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hres : Function.Surjective (algebraMap k (ResidueField A))) {r : ℕ} (τ : Fin r → A)
    (hspan : maximalIdeal A = Ideal.span (Set.range τ)) :
    Submodule.span (ResidueField A)
      (Set.range fun i => (1 : ResidueField A) ⊗ₜ[A] D k A (τ i)) = ⊤ := by
  set S := Submodule.span (ResidueField A)
      (Set.range fun i => (1 : ResidueField A) ⊗ₜ[A] D k A (τ i))
  have hτ0 : ∀ i, residue A (τ i) = 0 := fun i =>
    (residue_eq_zero_iff _).2 (hspan ▸ Ideal.subset_span ⟨i, rfl⟩)

  have h1 : ∀ a : A, (1 : ResidueField A) ⊗ₜ[A] D k A a ∈ S := by
    intro a
    obtain ⟨c, hc⟩ := hres (residue A a)
    have hm : a - algebraMap k A c ∈ Ideal.span (Set.range τ) := by
      rw [← hspan, ← residue_eq_zero_iff, map_sub, ← hc]
      rw [IsScalarTower.algebraMap_apply k A (ResidueField A)]
      exact sub_self _
    obtain ⟨β, hβ⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hm
    have hD : D k A a = ∑ i, (β i • D k A (τ i) + τ i • D k A (β i)) := by
      have : D k A a = D k A (a - algebraMap k A c) := by
        rw [map_sub, Derivation.map_algebraMap, sub_zero]
      rw [this, ← hβ, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Derivation.leibniz, add_comm]
    rw [hD, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      ← algebraMap_smul (ResidueField A) (τ i), ← algebraMap_smul (ResidueField A) (β i)]
    change _ + residue A (τ i) • _ ∈ S
    rw [hτ0, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have h2 : ∀ ω : Ω[A⁄k], (1 : ResidueField A) ⊗ₜ[A] ω ∈ S := by
    intro ω
    have hω : ω ∈ Submodule.span A (Set.range (D k A)) := by
      rw [span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h1 a
    | zero => rw [TensorProduct.tmul_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact S.add_mem hx hy
    | smul a x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul (ResidueField A) a]
      exact S.smul_mem _ hx
  rw [eq_top_iff]
  intro x hx
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => exact S.zero_mem
  | tmul c ω =>
    have : c ⊗ₜ[A] ω = c • ((1 : ResidueField A) ⊗ₜ[A] ω) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact S.smul_mem _ (h2 ω)
  | add x y hx hy => exact S.add_mem hx hy

end GlobalTheory.EtaleCoordLocal

namespace GlobalTheory.EtaleCoordLocal

open IsLocalRing KaehlerDifferential

theorem exists_coords (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] [Algebra.EssFiniteType k A] [Algebra.FormallySmooth k A]
    (hres : Function.Surjective (algebraMap k (ResidueField A))) :
    ∃ (r : ℕ) (τ : Fin r → A), maximalIdeal A = Ideal.span (Set.range τ) ∧
      ∃ b : Module.Basis (Fin r) A Ω[A⁄k], ∀ i, b i = D k A (τ i) := by
  classical
  haveI : Algebra.FormallySmooth k (ResidueField A) :=
    Algebra.FormallySmooth.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId k (ResidueField A)) ⟨(algebraMap k _).injective, hres⟩)
  let b0 := Module.finBasis (ResidueField A) (CotangentSpace A)
  choose τ' hτ' using fun i => Ideal.toCotangent_surjective (maximalIdeal A) (b0 i)
  have hspan : maximalIdeal A = Ideal.span (Set.range fun i => (τ' i : A)) := by
    have h1 : Submodule.span (ResidueField A) ((maximalIdeal A).toCotangent '' Set.range τ') = ⊤ := by
      rw [← Set.range_comp, show (maximalIdeal A).toCotangent ∘ τ' = ⇑b0 from funext hτ', b0.span_eq]
    rw [CotangentSpace.span_image_eq_top_iff] at h1
    have h2 := congrArg (Submodule.map (maximalIdeal A).subtype) h1
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h2
    exact h2.symm
  refine ⟨_, fun i => (τ' i : A), hspan, ?_⟩
  have hli := linearIndependent_one_tmul_D (k := k) (fun i => (τ' i : A)) (fun i => (τ' i).2)
    (by
      have : (fun i => (maximalIdeal A).toCotangent ⟨(τ' i : A), (τ' i).2⟩) = ⇑b0 := funext hτ'
      rw [this]
      exact b0.linearIndependent)
  have hsp := span_one_tmul_D hres (fun i => (τ' i : A)) hspan
  haveI : Module.FinitePresentation A Ω[A⁄k] := Module.finitePresentation_of_finite A _
  exact Module.exists_basis_of_basis_baseChange (R := A) (fun i => D k A (τ' i : A)) hli hsp
    (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal A).subtype
      Subtype.val_injective)

theorem formallyEtale_eval₂Hom_of_basis (k A : Type) [CommRing k] [CommRing A] [Algebra k A]
    [Algebra.FormallySmooth k A] {r : ℕ} (τ : Fin r → A) (b : Module.Basis (Fin r) A Ω[A⁄k])
    (hb : ∀ i, b i = D k A (τ i)) : (MvPolynomial.eval₂Hom (algebraMap k A) τ).FormallyEtale := by
  letI := (MvPolynomial.eval₂Hom (algebraMap k A) τ).toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin r) k) A :=
    IsScalarTower.of_algebraMap_eq fun c => (MvPolynomial.eval₂Hom_C _ τ c).symm
  have hX (i : Fin r) : algebraMap (MvPolynomial (Fin r) k) A (MvPolynomial.X i) = τ i :=
    MvPolynomial.eval₂Hom_X' _ τ i
  have he : mapBaseChange k (MvPolynomial (Fin r) k) A =
      (((mvPolynomialBasis k (Fin r)).baseChange A).equiv b (Equiv.refl _)).toLinearMap := by
    refine ((mvPolynomialBasis k (Fin r)).baseChange A).ext fun i => ?_
    rw [EtaleCoordJacobian.mapBaseChange_basis, hX, ← hb]
    simp only [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
  have hbij : Function.Bijective (mapBaseChange k (MvPolynomial (Fin r) k) A) := by
    rw [he]; exact LinearEquiv.bijective _
  have h1 : Subsingleton Ω[A⁄MvPolynomial (Fin r) k] := by
    refine subsingleton_of_forall_eq 0 fun y => ?_
    obtain ⟨x, rfl⟩ := map_surjective k (MvPolynomial (Fin r) k) A y
    exact (exact_mapBaseChange_map k (MvPolynomial (Fin r) k) A x).2 (hbij.2 x)
  have h2 : Subsingleton (Algebra.H1Cotangent (MvPolynomial (Fin r) k) A) := by
    refine subsingleton_of_forall_eq 0 fun y => ?_
    have h3 : Algebra.H1Cotangent.δ k (MvPolynomial (Fin r) k) A y = 0 := by
      apply hbij.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange k (MvPolynomial (Fin r) k) A _).2 ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ k (MvPolynomial (Fin r) k) A y).1 h3
    rw [Subsingleton.elim x 0, map_zero]
  exact (⟨h1, h2⟩ : Algebra.FormallyEtale (MvPolynomial (Fin r) k) A)

end GlobalTheory.EtaleCoordLocal

namespace GlobalTheory.EtaleCoordLocal

open IsLocalRing

theorem exists_etaleCoords : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (B : Subring κ')
    (hB : IsLocModel (algebraMap ℂ κ') B),
    RatRes (algebraMap ℂ κ') B → ((algebraMap ℂ κ').codRestrict B hB.const_mem).FormallySmooth →
    ∃ (r : ℕ) (τ : Fin r → B),
      (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) ∧
      (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict B hB.const_mem) τ).FormallyEtale ∧
      TrBasis (algebraMap ℂ κ') (fun i => (τ i : κ')) := by
  intro κ' _ _ B hB hres hsm
  letI := hB.isLocalRing
  let c0 : ℂ →+* B := (algebraMap ℂ κ').codRestrict B hB.const_mem
  letI : Algebra ℂ B := c0.toAlgebra
  haveI : Algebra.EssFiniteType ℂ B := hB.essFiniteType
  haveI : Algebra.FormallySmooth ℂ B := hsm
  haveI : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing ℂ B
  have hres' : Function.Surjective (algebraMap ℂ (ResidueField B)) := by
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨a, ha⟩ := hres x x.2
    refine ⟨a, ?_⟩
    have hn : ¬ IsUnit (x - c0 a) := (nonUnit_iff (R := B) (x - c0 a)).1 ha
    have hm : x - c0 a ∈ maximalIdeal B := (mem_maximalIdeal _).2 hn
    rw [IsScalarTower.algebraMap_apply ℂ B (ResidueField B)]
    have := (residue_eq_zero_iff _).2 hm
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  obtain ⟨r, τ, hspan, b, hb⟩ := exists_coords ℂ B hres'
  refine ⟨r, τ, hspan, formallyEtale_eval₂Hom_of_basis ℂ B τ b hb, ?_⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  ·
    have hmax : maximalIdeal B = ⊥ := by
      rw [hspan, Set.range_eq_empty, Ideal.span_empty]
    have hB0 : ∀ x : B, ∃ a : ℂ, x = c0 a := by
      intro x
      obtain ⟨a, ha⟩ := hres x x.2
      have hn : ¬ IsUnit (x - c0 a) := (nonUnit_iff (R := B) (x - c0 a)).1 ha
      have hm : x - c0 a ∈ maximalIdeal B := (mem_maximalIdeal _).2 hn
      rw [hmax, Ideal.mem_bot, sub_eq_zero] at hm
      exact ⟨a, hm⟩
    have halg : Algebra.IsAlgebraic ℂ κ' := by
      refine ⟨fun f => ?_⟩
      obtain ⟨p, hp, q, hq, hq0, e⟩ := hB.frac f
      obtain ⟨a, ha⟩ := hB0 ⟨p, hp⟩
      obtain ⟨d, hd⟩ := hB0 ⟨q, hq⟩
      have ha' : p = algebraMap ℂ κ' a := congrArg Subtype.val ha
      have hd' : q = algebraMap ℂ κ' d := congrArg Subtype.val hd
      have hf : f = algebraMap ℂ κ' (a / d) := by
        rw [map_div₀, ← ha', ← hd', eq_div_iff hq0, e]
      rw [hf]
      exact isAlgebraic_algebraMap _
    have e : (algebraMap ℂ κ').toAlgebra = (inferInstance : Algebra ℂ κ') :=
      Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [e]
    exact (algebraicIndependent_empty_type : AlgebraicIndependent ℂ fun i : Fin 0 => (τ i : κ')).isTranscendenceBasis_of_trdeg_le_of_finite
      (by rw [trdeg_eq_zero]; exact zero_le)
  · exact trBasis_of_isFreeGen_dForm (algebraMap ℂ κ') B hB r τ hr
      (TopForm.isFreeGen_dForm τ b hb)

end GlobalTheory.EtaleCoordLocal
