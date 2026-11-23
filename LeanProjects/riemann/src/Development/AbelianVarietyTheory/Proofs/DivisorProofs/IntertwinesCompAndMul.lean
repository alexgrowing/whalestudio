import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
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

variable {p : ℕ} {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {GG : PDivGroup p R}

def torsComp {N : ℕ} {B : Type} [CommRing B] [Algebra R B] (f : A ⟶ A) [IsMonHom f] (z : Tors A N B) : Tors A N B :=
  ⟨z.1 ≫ f, by rw [← MonObj.pow_comp, z.2, MonObj.one_comp]⟩

theorem comp_add_app {B : Type} [CommRing B] [Algebra R B] (g g' : GG ⟶ GG) (n : ℕ) (φ : GG.A n →ₐ[R] B) :
    toConv (φ.comp ((g + g').app n : GG.A n →ₐ[R] GG.A n)) =
      toConv (φ.comp (g.app n : GG.A n →ₐ[R] GG.A n)) * toConv (φ.comp (g'.app n : GG.A n →ₐ[R] GG.A n)) :=
  map_mul ((PDiv.ptsPush (GG.A n) φ).comp PDiv.toPts) (g.conv n) (g'.conv n)

theorem intertwines_rules (p : ℕ) (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A]
    (GG : PDivGroup p R) (θ : TorsionMap A GG) :
    θ.Intertwines (𝟙 A) (𝟙 GG) ∧
    (∀ (f f' : A ⟶ A) [IsMonHom f] [IsMonHom f'] (g g' : GG ⟶ GG), θ.Intertwines f g → θ.Intertwines f' g' →
      θ.Intertwines (f ≫ f') (g ≫ g')) ∧
    ∀ (f f' : A ⟶ A) [IsMonHom f] [IsMonHom f'] (g g' : GG ⟶ GG), θ.Intertwines f g → θ.Intertwines f' g' →
      θ.Intertwines (f * f') (g + g') := by
  refine ⟨?_, ?_, ?_⟩
  · intro n B _ _ z z' h
    obtain rfl : z' = z := Subtype.ext (h.trans (Category.comp_id _))
    rfl
  · intro f f' _ _ g g' hf hf' n B _ _ z z'' h
    rw [hf' n B (torsComp f z) z'' (h.trans (Category.assoc _ _ _).symm), hf n B z (torsComp f z) rfl]
    rfl
  · intro f f' _ _ g g' hf hf' n B _ _ z z'' h
    have hm := θ.mul n B (torsComp f z) (torsComp f' z) z'' (h.trans (MonObj.comp_mul _ _ _))
    rw [hf n B z (torsComp f z) rfl, hf' n B z (torsComp f' z) rfl, ← comp_add_app] at hm
    exact congrArg ofConv hm

end GlobalTheory.GroupBplus.Aff
