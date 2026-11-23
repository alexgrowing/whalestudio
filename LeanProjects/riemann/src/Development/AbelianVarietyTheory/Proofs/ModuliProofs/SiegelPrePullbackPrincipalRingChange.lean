import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipalStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SiegelRingChange

variable {h k : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S : Scheme.{0}}

theorem spMap_comp' {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (a : R₁ →+* R₂) (b : R₂ →+* R₃) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_spMap {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (x : Sp R₂ ⟶ Sp R₁) :
    ∃ a : R₁ →+* R₂, spMap a = x := by
  obtain ⟨a, ha⟩ := Spec.map_surjective x
  exact ⟨a.hom, ha⟩

theorem spMap_inj {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {a b : R₁ →+* R₂} (e : spMap a = spMap b) : a = b := by
  have := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom this

def down (j : B →+* B') (hj : j ζ = ζ') {s' : S ⟶ Sp B'} (c : SiegPre h k ζ' s') : SiegPre h k ζ (s' ≫ spMap j) :=
  { A := c.A, ab := c.ab, P := c.P, isLB := c.isLB, rig₁ := c.rig₁, rig₂ := c.rig₂, symm := c.symm
    lev := c.lev, lev_add := c.lev_add, lev_tors := c.lev_tors
    geom := fun K _ _ x β z hx hz => by
      obtain ⟨β', hβ'⟩ := exists_spMap (x ≫ s')
      have e : β'.comp j = β := by
        apply spMap_inj
        rw [spMap_comp', hβ', Category.assoc, hx]
      refine c.geom K x β' z hβ'.symm ?_
      rw [hz, ← e, ← hj]; rfl }

def up (j : B →+* B') (hj : j ζ = ζ') {s' : S ⟶ Sp B'} (c : SiegPre h k ζ (s' ≫ spMap j)) : SiegPre h k ζ' s' :=
  { A := c.A, ab := c.ab, P := c.P, isLB := c.isLB, rig₁ := c.rig₁, rig₂ := c.rig₂, symm := c.symm
    lev := c.lev, lev_add := c.lev_add, lev_tors := c.lev_tors
    geom := fun K _ _ x β z hx hz => by
      refine c.geom K x (β.comp j) z ?_ ?_
      · rw [spMap_comp', ← hx, Category.assoc]
      · rw [hz, ← hj]; rfl }

theorem siegPre_pull_ringChange : ∀ (h k : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j ζ = ζ' → f ≫ s = s' ≫ spMap j → (∀ c : SiegPre h k ζ s, ∃ c' : SiegPre h k ζ' s', SiegPB c' c f) ∧ (∀ (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s'), SiegPB c' c f → c.Principal → c'.Principal) ∧ ∀ c' : SiegPre h k ζ' s', ∃ c₀ : SiegPre h k ζ (s' ≫ spMap j), SiegPB c' c₀ (𝟙 _) ∧ SiegPB c₀ c' (𝟙 _) := by
  intro h k B B' _ _ ζ ζ' j S S' s s' f hj hf
  refine ⟨fun c => ?_, fun c c' hc hp => ?_, fun c' => ?_⟩
  · obtain ⟨c₀, h₀⟩ := (GlobalTheory.T.siegelObject_pullback_exists_and_principal h k B ζ S S' s _ f c hf).1
    exact ⟨up j hj c₀, h₀⟩
  · exact (GlobalTheory.T.siegelObject_pullback_exists_and_principal h k B ζ S S' s _ f c hf).2 (down j hj c') hc hp
  · have e := (GlobalTheory.T.siegelPullback_id_comp_cancel h k B' B' B' ζ' ζ' ζ' S' S' S' s' s' s' c' c' c' (𝟙 _) (𝟙 _)).1
    exact ⟨down j hj c', e, e⟩

end GlobalTheory.SiegelRingChange
end
