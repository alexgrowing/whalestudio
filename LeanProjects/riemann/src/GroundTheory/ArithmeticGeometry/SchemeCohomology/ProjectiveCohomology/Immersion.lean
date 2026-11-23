import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafAlt
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Generation
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPullback
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPush
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionProj
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionCech
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjScheme

variable {A : Type u} [CommRing A] {n : ℕ} {X : Scheme.{u}} (i : X ⟶ projectiveSpace A n)
  [IsClosedImmersion i]

instance isQuasicoherent_pushforward (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward i).obj F).IsQuasicoherent :=
  isQuasicoherent_pushforward_of_isAffineHom i F

theorem isCoherent_pushforward {F : X.Modules} (hF : IsCoherent F) :
    IsCoherent ((Scheme.Modules.pushforward i).obj F) :=
  isCoherent_pushforward_of_isClosedImmersion i hF

omit [IsClosedImmersion i] in

theorem isInvertibleSheaf_twistingSheaf (k : ℤ) : IsInvertibleSheaf (twistingSheaf i k) := by
  intro x
  obtain ⟨j, hj⟩ : ∃ j, i.base x ∈ ProjSpace.stdOpen A n j :=
    Opens.mem_iSup.1 (by rw [ProjSpace.iSup_stdOpen]; trivial)
  exact ⟨i ⁻¹ᵁ ProjSpace.stdOpen A n j, hj, _,
    isBasisOn_pullbackUnitApp i (ProjTwist.isBasisOn_upow _ (ProjSpace.X_mem j) k)⟩

instance isQuasicoherent_twist (F : X.Modules) [F.IsQuasicoherent] (k : ℤ) :
    (twist i F k).IsQuasicoherent :=
  isQuasicoherent_tensor_of_invertible F (isInvertibleSheaf_twistingSheaf i k)

def pushforwardTwistIso (F : X.Modules) (k : ℤ) :
    ProjSpace.twist ((Scheme.Modules.pushforward i).obj F) k ≅
      (Scheme.Modules.pushforward i).obj (twist i F k) :=
  pushforwardTwistIso' i F k

theorem exists_generatingSections_of_pushforward (M : X.Modules) [M.IsQuasicoherent]
    (h : ∃ σ : ((Scheme.Modules.pushforward i).obj M).GeneratingSections, σ.IsFiniteType) :
    ∃ σ : M.GeneratingSections, σ.IsFiniteType :=
  exists_generatingSections_of_pushforward_of_isAffineHom i M h

variable [X.Over (Spec (.of A))] [i.IsOver (Spec (.of A))]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

attribute [local instance] algebraOfOver

def HLinearEquivPushforward (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) :
    Sheaf.H.{w'} (modulesAb F) p ≃ₗ[A]
      Sheaf.H.{w'} (modulesAb ((Scheme.Modules.pushforward i).obj F)) p :=
  have hUP : ⨆ j, ProjSpace.stdOpen A n j = ⊤ := ProjSpace.iSup_stdOpen
  have hUPaff : ∀ (m : ℕ) (t : Fin (m + 1) → Fin (n + 1)),
      IsAffineOpen (⨅ a, ProjSpace.stdOpen A n (t a)) := fun _ t => by
    rw [← inter_eq_iInf]
    exact ProjSpace.isAffineOpen_inter t
  have hUX : ⨆ j, i ⁻¹ᵁ ProjSpace.stdOpen A n j = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, ProjSpace.iSup_stdOpen]
    rfl
  have hUXaff : ∀ (m : ℕ) (t : Fin (m + 1) → Fin (n + 1)),
      IsAffineOpen (⨅ a, i ⁻¹ᵁ ProjSpace.stdOpen A n (t a)) := fun _ t => by
    have h := preimage_inter i (ProjSpace.stdOpen A n) t
    rw [← inter_eq_iInf (fun j => i ⁻¹ᵁ ProjSpace.stdOpen A n j) t, ← h]
    exact (ProjSpace.isAffineOpen_inter t).preimage i
  (cechHLinearEquivH (fun j => i ⁻¹ᵁ ProjSpace.stdOpen A n j) hUX hUXaff A F p).symm ≪≫ₗ
    (cechHPushforwardLinearEquiv i A F (ProjSpace.stdOpen A n) p).symm ≪≫ₗ
    cechHLinearEquivH (ProjSpace.stdOpen A n) hUP hUPaff A _ p

end ProjScheme

end

end GroundTheory.Arith.SchemeCoh
