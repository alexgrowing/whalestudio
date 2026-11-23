import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomCompEq
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem torsMap_injective_of_isSeparated {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    [IsSeparated G.hom] {N : ℕ} {T K : Type} [CommRing T] [_root_.IsReduced T] [Algebra R T] [CommRing K] [Algebra R K]
    (u : T →ₐ[R] K) (hu : Function.Injective u) :
    Function.Injective (torsMap u : Tors G N T → Tors G N K) := by
  intro x y h
  have hd : IsDominant (spMap (u : T →+* K)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      show RingHom.ker (u : T →+* K) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot (u : T →+* K)).1 hu]
      exact bot_le)⟩
  have h1 : spMap (u : T →+* K) ≫ x.1.left = spMap (u : T →+* K) ≫ y.1.left :=
    congrArg (fun z : Tors G N K => z.1.left) h
  have hr : AlgebraicGeometry.IsReduced (Sp T) := inferInstance
  refine Subtype.ext (Over.OverMorphism.ext ?_)
  exact ext_of_isDominant_of_isSeparated (W := Sp K) (X := Sp T) G.hom ((Over.w x.1).trans (Over.w y.1).symm)
    (spMap (u : T →+* K)) h1

theorem PreChart.range_subset_of_generic : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSeparated G.hom → ∀ (N : ℕ) (q : PrimeSpectrum R) (c : PreChart G N q) (B : Type) [CommRing B] [IsDomain B] [Algebra R B], IsUnit (algebraMap R B c.r) → ∀ (em : B →ₐ[R] K), Function.Injective em → ∀ z : Tors G N B, Set.range (torsMap em z).1.left ⊆ c.W → Set.range z.1.left ⊆ c.W := by
  intro R K _ _ _ G _ _ hsep N q c B _ _ _ hr em hem z hz
  obtain ⟨ψ, -, hψ⟩ := (c.bij K).2.2 hz
  have hψ : torsMap ψ c.j = torsMap em z := hψ
  letI : Algebra B K := (em : B →+* K).toAlgebra
  haveI : IsScalarTower R B K := IsScalarTower.of_algebraMap_eq fun a => (em.commutes a).symm
  let l : Localization.Away c.r →+* B := IsLocalization.Away.lift c.r hr
  have hl : (algebraMap B K).comp l = (ψ : c.C →+* K).comp (algebraMap (Localization.Away c.r) c.C) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers c.r) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, l, IsLocalization.Away.lift_eq]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact (ψ.commutes a).symm
  have hint : ∀ x : c.C, ψ x ∈ integralClosure B K := fun x =>
    (Algebra.IsIntegral.isIntegral (R := Localization.Away c.r) x).map_of_comp_eq l (ψ : c.C →+* K) hl
  let T := integralClosure B K
  let u : T →ₐ[R] K := T.val.restrictScalars R
  let e : B →ₐ[R] T := IsScalarTower.toAlgHom R B T
  let ψT : c.C →ₐ[R] T := ψ.codRestrict (T.restrictScalars R) hint
  have h1 : torsMap ψT c.j = torsMap e z := by
    apply torsMap_injective_of_isSeparated u Subtype.val_injective
    rw [torsMap_comp, torsMap_comp]
    exact hψ
  have h2 : Set.range (torsMap e z).1.left ⊆ c.W := h1 ▸ (c.bij T).1 (Set.mem_univ ψT)
  haveI : FaithfulSMul B T := (faithfulSMul_iff_algebraMap_injective B T).2 fun a b hab =>
    hem (congrArg Subtype.val hab)
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := Algebra.IsIntegral.comap_surjective B T x
  refine h2 ⟨y, ?_⟩
  rw [← hy]
  rfl

end GlobalTheory.GroupBplus.Aff
