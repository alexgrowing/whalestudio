import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationCrystalFormPerfectSelfAnnihila
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso

set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagPolForm

theorem exists_of_isLB (P : GlobalTheory.Published.AbelianDeRham.Free) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    {g : ℕ} (hA : IsAbelianScheme A) (gA : SmoothOfRelativeDimension g A.hom) (L : LB A.left) (hLB : L.IsLB) :
    ∃ ψ : LinearMap.BilinForm R (HdR A), IsPolForm (dp0 R) (𝟙 _) A L ψ := by
  obtain ⟨h0, -, -, -, e, he⟩ := P R A _ hA gA
  obtain ⟨z, hz, -⟩ := (isChern_existsUnique_and_iso R ⊥ (dp0 R) _ (A.hom ≫ 𝟙 _)).1 _ hLB
  obtain ⟨n, a, b, hab⟩ := PolExists.exists_sum_wedge (e.symm z)
  have hm : ∀ c : FirstDeRham (A.hom ≫ 𝟙 _), c ∈ primDR A := fun c ↦ by
    change c ∈ prim (dp0 R) (𝟙 _) A
    rw [show prim (dp0 R) (𝟙 _) A = ⊤ from h0]; trivial
  let a' : Fin n → primDR A := fun k ↦ ⟨a k, hm _⟩
  let b' : Fin n → primDR A := fun k ↦ ⟨b k, hm _⟩
  have hz' : IsChern (dp0 R) (A.hom ≫ 𝟙 _) L (∑ k, CatCoh.cup _ (a' k).1 (b' k).1) := by
    have : z = ∑ k, CatCoh.cup _ (a k) (b k) := by
      rw [← e.apply_symm_apply z, ← hab, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ he _ _
    exact this ▸ hz
  exact ⟨_, n, a', b', hz', rfl⟩

theorem diag_polForm_exists : GlobalTheory.Published.AbelianDeRham.Free → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt), ∃ ψ : LinearMap.BilinForm R (HdR X.A), IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ := by
  intro P F _ _ 𝔠 R _ X c
  exact exists_of_isLB P X.A X.ab X.dim _ (pull_isLB (X.isLB c) _)

end GlobalTheory.DiagPolForm
