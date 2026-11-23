import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafCore
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.IsQuasicoherentTensorOfInvertible
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjTwist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

theorem ratio_mul_ratio {u v w : A} (hu : u ∈ 𝒜 1) (hv : v ∈ 𝒜 1) (hw : w ∈ 𝒜 1) :
    resO (inf_le_right : Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v ≤ Proj.basicOpen 𝒜 v)
        (ratio 𝒜 hv hw) *
      resO (inf_le_left : Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v ≤ Proj.basicOpen 𝒜 u)
        (ratio 𝒜 hu hv) =
    resO (inf_le_left : Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v ≤ Proj.basicOpen 𝒜 u)
        (ratio 𝒜 hu hw) :=
  ratio_mul_ratio' hu hv hw

end ProjTwist

section Iso

variable {X : Scheme.{u}}

private theorem isCoherent_unit' : IsCoherent (𝟙_ X.Modules) := by
  refine ⟨isQuasicoherent_unit X, fun U _ => ?_⟩
  let one : Γ(𝟙_ X.Modules, U) := (1 : Γ(X, U))
  refine ⟨⟨{one}, ?_⟩⟩
  rw [eq_top_iff]
  intro m _
  have hm : m = (show Γ(X, U) from m) • one := (mul_one (show Γ(X, U) from m)).symm
  rw [hm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_singleton_self _)))

private theorem isCoherent_of_iso' {M N : X.Modules} (e : M ≅ N) (hM : IsCoherent M) :
    IsCoherent N := by
  obtain ⟨hq, hf⟩ := hM
  refine ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hq, fun U hU => ?_⟩
  have := hf U hU
  let φ : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
    { toFun := e.hom.app U
      map_add' := map_add _
      map_smul' := fun r m => Scheme.Modules.Hom.app_smul e.hom r m }
  refine Module.Finite.of_surjective φ fun n => ⟨e.inv.app U n, ?_⟩
  change (e.inv ≫ e.hom).app U n = n
  rw [e.inv_hom_id]
  rfl

end Iso

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

open ProjTwist

theorem isCoherent_twistingSheaf (k : ℤ) : IsCoherent (twistingSheaf (grading A n) k) :=
  isCoherent_of_iso' (λ_ _)
    (isCoherent_tensor_of_invertible isCoherent_unit' (isInvertibleSheaf_twistingSheaf k))

instance isQuasicoherent_twistingSheaf (k : ℤ) :
    (twistingSheaf (grading A n) k).IsQuasicoherent :=
  (isCoherent_twistingSheaf k).1

def twistTwistIso (G : (projectiveSpace A n).Modules) (a b : ℤ) :
    twist (twist G a) b ≅ twist G (a + b) :=
  α_ _ _ _ ≪≫ whiskerLeftIso G (twistMulIso a b)

def twistZero (G : (projectiveSpace A n).Modules) : twist G 0 ≅ G :=
  whiskerLeftIso G twistZeroIso ≪≫ ρ_ G

instance isQuasicoherent_twist (G : (projectiveSpace A n).Modules) [G.IsQuasicoherent] (k : ℤ) :
    (twist G k).IsQuasicoherent :=
  isQuasicoherent_tensor_of_invertible G (isInvertibleSheaf_twistingSheaf k)

theorem isCoherent_twist {G : (projectiveSpace A n).Modules} (hG : IsCoherent G) (k : ℤ) :
    IsCoherent (twist G k) :=
  isCoherent_tensor_of_invertible hG (isInvertibleSheaf_twistingSheaf k)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
