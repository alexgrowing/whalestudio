import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfDimOfFinrankDerivatio

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CotDim

open TensorProduct KaehlerDifferential

theorem exists_basis_mod_sq {A : Type} [CommRing A] [Algebra ℂ A] (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) (d : ℕ)
    (hb : letI := e.toAlgebra; Nonempty (Module.Basis (Fin d) ℂ (ℂ ⊗[A] Ω[A⁄ℂ]))) :
    ∃ g : Fin d → A, (∀ j, e (g j) = 0) ∧
      (∀ a : A, e a = 0 → ∃ c : Fin d → ℂ, a - ∑ j, c j • g j ∈ RingHom.ker e ^ 2) ∧
      (∀ c : Fin d → ℂ, ∑ j, c j • g j ∈ RingHom.ker e ^ 2 → c = 0) := by
  letI : Algebra A ℂ := e.toAlgebra
  haveI : IsScalarTower ℂ A ℂ := IsScalarTower.of_algebraMap_eq fun c => (he c).symm
  obtain ⟨b⟩ := hb
  have hs : Function.Surjective (algebraMap A ℂ) := fun c => ⟨algebraMap ℂ A c, he c⟩
  have key : ∀ (c : ℂ) (w : Ω[A⁄ℂ]), (1 : ℂ) ⊗ₜ[A] (c • w) = c • ((1 : ℂ) ⊗ₜ[A] w) := by
    intro c w
    rw [← algebraMap_smul A c w, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
    exact he c
  let φ : A →ₗ[ℂ] ℂ ⊗[A] Ω[A⁄ℂ] :=
    { toFun := fun a => (1 : ℂ) ⊗ₜ[A] D ℂ A a
      map_add' := fun a b => by rw [map_add, TensorProduct.tmul_add]
      map_smul' := fun c a => by rw [(D ℂ A).map_smul c a, key]; rfl }
  have hφ : ∀ x : RingHom.ker (algebraMap A ℂ), φ x =
      kerCotangentToTensor ℂ A ℂ ((RingHom.ker (algebraMap A ℂ)).toCotangent x) :=
    fun x => (kerCotangentToTensor_toCotangent ℂ A ℂ x).symm
  have hinj := GlobalTheory.SmoothTangent.kerCotangentToTensor_injective ℂ A ℂ hs
  have hsurj : ∀ v, ∃ x : RingHom.ker (algebraMap A ℂ), φ x = v := by
    intro v
    obtain ⟨y, hy⟩ := (exact_kerCotangentToTensor_mapBaseChange ℂ A ℂ hs v).mp (Subsingleton.elim _ _)
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ y
    exact ⟨x, (hφ x).trans hy⟩
  have hker : ∀ x : RingHom.ker (algebraMap A ℂ), φ x = 0 → (x : A) ∈ RingHom.ker e ^ 2 := by
    intro x hx
    rw [hφ, ← map_zero (kerCotangentToTensor ℂ A ℂ), hinj.eq_iff, Ideal.toCotangent_eq_zero] at hx
    exact hx
  choose g hg using fun j => hsurj (b j)
  have hmemg : ∀ c : Fin d → ℂ, ∑ j, c j • (g j : A) ∈ RingHom.ker (algebraMap A ℂ) := fun c =>
    Ideal.sum_mem _ fun j _ => by rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (g j).2
  have hφg : ∀ c : Fin d → ℂ, φ (∑ j, c j • (g j : A)) = ∑ j, c j • b j := fun c => by
    rw [map_sum]; simp only [map_smul, hg]
  refine ⟨fun j => g j, fun j => (g j).2, ?_, ?_⟩
  · intro a ha
    refine ⟨fun j => b.repr (φ a) j, ?_⟩
    have hmem : a - ∑ j, b.repr (φ a) j • (g j : A) ∈ RingHom.ker (algebraMap A ℂ) :=
      Ideal.sub_mem _ ha (hmemg _)
    refine hker ⟨_, hmem⟩ ?_
    change φ (a - _) = 0
    rw [map_sub, hφg, b.sum_repr, sub_self]
  · intro c hc
    have h0 : φ (∑ j, c j • (g j : A)) = 0 := by
      have h1 := hφ ⟨_, hmemg c⟩
      rw [(Ideal.toCotangent_eq_zero _ _).2 hc, map_zero] at h1
      exact h1
    rw [hφg] at h0
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent c h0 i

end GlobalTheory.CotDim

namespace GlobalTheory.CotDim

open TensorProduct KaehlerDifferential

theorem nonempty_basis_fibre {A : Type} [CommRing A] [Algebra ℂ A] (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) (d : ℕ) (t : A) (ht : e t ≠ 0)
    [Algebra.IsStandardSmoothOfRelativeDimension d ℂ (Localization.Away t)] :
    letI := e.toAlgebra; Nonempty (Module.Basis (Fin d) ℂ (ℂ ⊗[A] Ω[A⁄ℂ])) := by
  letI : Algebra A ℂ := e.toAlgebra
  haveI : IsScalarTower ℂ A ℂ := IsScalarTower.of_algebraMap_eq fun c => (he c).symm
  let et : Localization.Away t →+* ℂ := IsLocalization.Away.lift t (isUnit_iff_ne_zero.2 ht)
  letI : Algebra (Localization.Away t) ℂ := et.toAlgebra
  haveI : IsScalarTower A (Localization.Away t) ℂ := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalization.Away.lift_eq t (isUnit_iff_ne_zero.2 ht) a).symm
  haveI : Nontrivial (Localization.Away t) := et.domain_nontrivial
  haveI : Algebra.FormallyEtale A (Localization.Away t) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
  haveI : Algebra.IsStandardSmooth ℂ (Localization.Away t) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := ℂ) (S := Localization.Away t) d
  haveI : Module.Finite (Localization.Away t) Ω[Localization.Away t⁄ℂ] := Module.finite_of_rank_eq_nat hr
  let b0 := Module.finBasisOfFinrankEq (Localization.Away t) Ω[Localization.Away t⁄ℂ]
    (Module.finrank_eq_of_rank_eq hr)
  let b1 : Module.Basis (Fin d) ℂ (ℂ ⊗[Localization.Away t] Ω[Localization.Away t⁄ℂ]) := b0.baseChange ℂ
  let E1 : ℂ ⊗[Localization.Away t] (Localization.Away t ⊗[A] Ω[A⁄ℂ]) ≃ₗ[ℂ]
      ℂ ⊗[Localization.Away t] Ω[Localization.Away t⁄ℂ] :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ)
      (tensorKaehlerEquivOfFormallyEtale ℂ A (Localization.Away t))
  let E2 := TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away t) ℂ ℂ Ω[A⁄ℂ]
  exact ⟨(b1.map E1.symm).map E2⟩

end GlobalTheory.CotDim

theorem GlobalTheory.CotDim.exists_cotangent_basis : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    (U : X.Opens), IsAffineOpen U → ∀ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
    let e : Sec p U →+* ℂ := CxPts.evHom hy; ∃ g : Fin d → Sec p U, (∀ j, e (g j) = 0) ∧
      (∀ a : Sec p U, e a = 0 → ∃ c : Fin d → ℂ, a - ∑ j, c j • g j ∈ RingHom.ker e ^ 2) ∧
      (∀ c : Fin d → ℂ, ∑ j, c j • g j ∈ RingHom.ker e ^ 2 → c = 0) := by
  intro X p d _ U hU y hy e
  have he : ∀ c : ℂ, e (algebraMap ℂ (Sec p U) c) = c := fun c => by
    exact (CxPts.ev_eq hy _).symm.trans (CxPts.ev_algX hy c)
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension d) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hts, ht⟩ : ∃ t : Sec p U, t ∈ s ∧ e t ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hle : Ideal.span (↑s : Set Γ(X, U)) ≤ RingHom.ker (e : Γ(X, U) →+* ℂ) :=
      Ideal.span_le.2 fun t ht => hcon t ht
    have h1 : (1 : Γ(X, U)) ∈ RingHom.ker (e : Γ(X, U) →+* ℂ) := hle (by rw [hs]; exact Submodule.mem_top)
    have h2 : e 1 = 0 := h1
    rw [map_one] at h2
    exact one_ne_zero h2
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv
    (@h t hts (Localization.Away t) _ (inferInstance : Algebra (Sec p U) (Localization.Away t))
      (by exact (inferInstance : IsLocalization (Submonoid.powers t) (Localization.Away t))))
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d ℂ (Localization.Away (t : Sec p U)) := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap,
      IsScalarTower.algebraMap_eq ℂ (Sec p U) (Localization.Away (t : Sec p U))]
    first
      | exact h₁
      | (convert h₁ using 1 <;> rfl)
  exact GlobalTheory.CotDim.exists_basis_mod_sq e he d (GlobalTheory.CotDim.nonempty_basis_fibre e he d t ht)
