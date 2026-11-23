import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

theorem isCoherent_biproduct {X : Scheme.{0}} {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → X.Modules) (hF : ∀ i, IsCoherent (F i)) : IsCoherent (⨁ F) := by
  haveI : ∀ i, SheafOfModules.IsQuasicoherent (F i) := fun i => (hF i).1
  refine ⟨isQuasicoherent_biproduct F, fun U hU => ?_⟩
  haveI : ∀ i, Module.Finite Γ(X, U) ((F i).presheaf.obj (Opposite.op U)) := fun i => (hF i).2 U hU
  let L : ∀ j, (F j).presheaf.obj (Opposite.op U) →ₗ[Γ(X, U)] (⨁ F).presheaf.obj (Opposite.op U) :=
    fun j =>
    { toFun := fun x => ConcreteCategory.hom (Scheme.Modules.Hom.app (biproduct.ι F j) U) x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        exact Scheme.Modules.Hom.app_smul _ r x }
  let f : (∀ j, (F j).presheaf.obj (Opposite.op U)) →ₗ[Γ(X, U)] (⨁ F).presheaf.obj (Opposite.op U) :=
    ∑ j, (L j).comp (LinearMap.proj j)
  refine Module.Finite.of_surjective f ?_
  intro m
  refine ⟨fun j => ConcreteCategory.hom (Scheme.Modules.Hom.app (biproduct.π F j) U) m, ?_⟩
  rw [LinearMap.sum_apply]
  exact (biproduct_app_eq_sum F U m).symm

theorem isCoherent_kerSeq : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ}, OpSeq k M T d →
    ∀ e, IsCoherent (KerSeq.kerSeq T d e) := by
  intro X _ k M T d h e
  haveI : SheafOfModules.IsQuasicoherent (M (d + e + 1)) := (h.coherent _).1
  exact isCoherent_kernel (KerSeq.sumMap T d e) (isCoherent_biproduct _ fun _ => h.coherent _)

end GlobalTheory.CompanionTheory.GE
