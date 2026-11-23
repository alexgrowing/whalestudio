import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechFiniteAffineCoverModelsStructureSheafStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem flat_cohomology_baseChange {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R']
    {A B C H H' : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup H] [Module R H] [AddCommGroup H'] [Module R' H']
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hfg : ∀ a, g (f a) = 0)
    (θ : LinearMap.ker (g.baseChange R) →ₗ[R] H) (θ' : LinearMap.ker (g.baseChange R') →ₗ[R'] H')
    (hs : Function.Surjective θ) (hk : ∀ z, θ z = 0 ↔ z.1 ∈ LinearMap.range (f.baseChange R))
    (hs' : Function.Surjective θ') (hk' : ∀ z, θ' z = 0 ↔ z.1 ∈ LinearMap.range (f.baseChange R'))
    (p : H → H')
    (hp : ∀ z z', z'.1 = (Algebra.ofId R R').toLinearMap.rTensor B z.1 → θ' z' = p (θ z)) :
    ∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ c, e (1 ⊗ₜ c) = p c := by
  let Z := LinearMap.ker g
  let f' : A →ₗ[R] Z := f.codRestrict Z hfg
  let i : Z →ₗ[R] LinearMap.ker (g.baseChange R) :=
    ((TensorProduct.mk R R B 1) ∘ₗ Z.subtype).codRestrict _ (fun z ↦ by
      have : g z.1 = 0 := z.2
      simp [this])
  have hi : ∀ z : Z, (i z).1 = (1 : R) ⊗ₜ[R] z.1 := fun z ↦ rfl
  have his : Function.Surjective i := by
    rintro ⟨x, hx⟩
    obtain ⟨b, rfl⟩ := (TensorProduct.lid R B).symm.surjective x
    have hb : g b = 0 := by
      have h1 : (1 : R) ⊗ₜ[R] g b = 0 := by simpa using hx
      have := congrArg (TensorProduct.lid R C) h1
      simpa using this
    exact ⟨⟨b, hb⟩, Subtype.ext (by simp [hi])⟩
  let τ : Z →ₗ[R] H := θ ∘ₗ i
  have hτs : Function.Surjective τ := hs.comp his
  have hex : Function.Exact f' τ := by
    intro z
    change θ (i z) = 0 ↔ _
    rw [hk, hi]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := (TensorProduct.lid R A).symm.surjective x
      refine ⟨a, Subtype.ext ?_⟩
      have := congrArg (TensorProduct.lid R B) hx
      change f a = z.1
      simpa using this
    · rintro ⟨a, rfl⟩
      exact ⟨1 ⊗ₜ a, rfl⟩
  have hexZ : Function.Exact (Z.subtype.baseChange R') (g.baseChange R') :=
    Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map g)
  have hinj : Function.Injective (Z.subtype.baseChange R') :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := R') Z.subtype Z.subtype_injective
  let j : R' ⊗[R] Z →ₗ[R'] LinearMap.ker (g.baseChange R') :=
    (Z.subtype.baseChange R').codRestrict _ (fun x ↦ hexZ.apply_apply_eq_zero x)
  have hjs : Function.Surjective j := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := (hexZ x).1 hx
    exact ⟨y, rfl⟩
  let a : R' ⊗[R] Z →ₗ[R'] R' ⊗[R] H := τ.baseChange R'
  let b : R' ⊗[R] Z →ₗ[R'] H' := θ' ∘ₗ j
  have has : Function.Surjective a := LinearMap.lTensor_surjective R' hτs
  have hbs : Function.Surjective b := hs'.comp hjs
  have hexa : Function.Exact (f'.baseChange R') a := lTensor_exact R' hex hτs
  have hcomp : ∀ y, Z.subtype.baseChange R' (f'.baseChange R' y) = f.baseChange R' y := by
    intro y
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    rfl
  have hker : LinearMap.ker a = LinearMap.ker b := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hexa x]
    change _ ↔ θ' (j x) = 0
    rw [hk']
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (hcomp y).symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hinj ((hcomp y).trans hy)⟩
  refine ⟨(a.quotKerEquivOfSurjective has).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
    b.quotKerEquivOfSurjective hbs, fun c ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hτs c
  have h1 : (a.quotKerEquivOfSurjective has).symm ((1 : R') ⊗ₜ[R] τ z) =
      Submodule.Quotient.mk ((1 : R') ⊗ₜ[R] z) := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1]
  change θ' (j (1 ⊗ₜ z)) = p (θ (i z))
  apply hp
  rw [hi, LinearMap.rTensor_tmul]
  change (1 : R') ⊗ₜ[R] z.1 = (algebraMap R R' 1) ⊗ₜ[R] z.1
  rw [map_one]

theorem exists_fin_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [QuasiCompact s] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).1 isCompact_univ
  have := hS.fintype
  let q := (Fintype.equivFin S).symm
  refine ⟨_, fun i ↦ (q i).1.1, fun i ↦ (q i).1.2, ?_⟩
  rw [e]
  apply le_antisymm
  · exact iSup_le fun i ↦ le_iSup₂_of_le (q i).1 (q i).2 le_rfl
  · refine iSup₂_le fun U hU ↦ ?_
    obtain ⟨i, hi⟩ := q.surjective ⟨U, hU⟩
    exact le_iSup_of_le i (by simp only [hi]; exact le_rfl)

theorem flat_baseChange_HO : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → (∃ e : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s', ∀ c, e (1 ⊗ₜ c) = pullHO1 h.w c) ∧ ∃ e : R' ⊗[R] HO2 s ≃ₗ[R'] HO2 s', ∀ c, e (1 ⊗ₜ c) = pullHO2 h.w c := by
  intro R R' _ _ _ _ X X' s s' φ h hsep hqc
  obtain ⟨n, D, hD, hcov⟩ := exists_fin_affine_cover s
  obtain ⟨M⟩ := GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology R X s (Fin n) D hsep hD hcov
  generalize GlobalTheory.AbLaw.cechLB s (LB.triv X) D = K at M
  have h0 : IsPullback (𝟙 X) s s (spMap (algebraMap R R)) := by
    have e : spMap (algebraMap R R) = 𝟙 _ := spMap_id R
    rw [e]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hdd : ∀ i j k a, (K.d j k).hom ((K.d i j).hom a) = 0 := by
    intro i j k a
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.d_comp_d]
    rfl
  obtain ⟨a1, a2, a3, a4⟩ := M.exact h0
  obtain ⟨b1, b2, b3, b4⟩ := M.exact h
  obtain ⟨c1, c2⟩ := M.nat h0 h (Algebra.ofId R R') φ h.w (Category.comp_id φ)
  exact ⟨flat_cohomology_baseChange _ _ (hdd 0 1 2) (M.θ1 h0) (M.θ1 h) a1 a2 b1 b2 _ c1,
    flat_cohomology_baseChange _ _ (hdd 1 2 3) (M.θ2 h0) (M.θ2 h) a3 a4 b3 b4 _ c2⟩

end GlobalTheory.AbCoh
