import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl

variable {S : Scheme.{0}} (G : Over S) (L : LB G.left)

abbrev LocSec (N : S.Opens) : Type := ∀ i : L.ι, Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ N)

variable {G L}

def IsLocSec {N : S.Opens} (s : LocSec G L N) : Prop :=
  ∀ i j, resG _ (fun _ hx => ⟨hx.1.1, hx.2⟩ : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
    resG _ (fun _ hx => hx.1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U i ⊓ L.U j) (L.g i j : Γ(G.left, L.U i ⊓ L.U j)) *
      resG _ (fun _ hx => ⟨hx.1.2, hx.2⟩ : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U j ⊓ G.hom ⁻¹ᵁ N) (s j)

theorem lpow_U_le [GrpObj G] {K : Type} [Field K] {ξ : Sp K ⟶ S} {N : S.Opens} (hξ : Set.range ξ ⊆ N)
    (j : Fin 1 → L.ι) :
    (LPow G L 1 (Over.mk ξ)).U j ≤ (snd (Over.mk ξ) G).left ⁻¹ᵁ (L.U (j 0) ⊓ G.hom ⁻¹ᵁ N) := by
  intro y hy
  refine ⟨Set.mem_iInter.1 hy 0, ?_⟩
  have e : (snd (Over.mk ξ) G).left ≫ G.hom = (fst (Over.mk ξ) G).left ≫ ξ :=
    (Over.w (snd (Over.mk ξ) G)).trans (Over.w (fst (Over.mk ξ) G)).symm
  show G.hom ((snd (Over.mk ξ) G).left y) ∈ N
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact hξ ⟨_, rfl⟩

def genPull [GrpObj G] {K : Type} [Field K] {ξ : Sp K ⟶ S} {N : S.Opens} (hξ : Set.range ξ ⊆ N)
    (s : LocSec G L N) (j : Fin 1 → L.ι) : Γ((Over.mk ξ ⊗ G).left, (LPow G L 1 (Over.mk ξ)).U j) :=
  ((snd (Over.mk ξ) G).left.appLE _ _ (lpow_U_le hξ j)).hom (s (j 0))

def GenIs [GrpObj G] {K : Type} [Field K] (ξ : Sp K ⟶ S) {N : S.Opens} (s : LocSec G L N)
    (v : SecM G L 1 (Over.mk ξ)) : Prop :=
  ∃ hξ : Set.range ξ ⊆ N, genPull hξ s = v.1

def FibNz {N : S.Opens} (s : LocSec G L N) (W : S.Opens) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), Set.range x ⊆ W →
    ∃ (y : Sp K ⟶ G.left) (i : L.ι), y ≫ G.hom = x ∧ Set.range y ⊆ (L.U i ⊓ G.hom ⁻¹ᵁ N : G.left.Opens) ∧
      valF y _ (s i) ≠ 0

theorem isLocSec_zero {N : S.Opens} : IsLocSec (0 : LocSec G L N) := fun i j => by
  simp [Pi.zero_apply, map_zero, mul_zero]

end GlobalTheory.UMin.ThBdl
