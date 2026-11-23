import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjDescendLowerLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LevelSecDesc

theorem levelSections_descend : ∀ (O : Type) [Ring O] (La : Type) [AddCommGroup La] [Module O La] (N : ℕ) (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (act : OActN O A) (act₀ : OActN O A₀) (eta : La → (𝟙_ (Over X) ⟶ A)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsGrpPullback A A₀ π φ → GlobalTheory.ZM.IsGaloisCover Ga ν φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ a y, (eta y).left ≫ ν a = ρ a ≫ (eta y).left) → (∀ x y, eta (x + y) = eta x * eta y) → (∀ (c : O) x, eta (c • x) = eta x ≫ act.act c) → (∀ x, eta (N • x) = 1) → ∃ eta₀ : La → (𝟙_ (Over Y) ⟶ A₀), (∀ x y, eta₀ (x + y) = eta₀ x * eta₀ y) ∧ (∀ (c : O) x, eta₀ (c • x) = eta₀ x ≫ act₀.act c) ∧ (∀ x, eta₀ (N • x) = 1) ∧ ∀ y, (eta y).left ≫ φ = π ≫ (eta₀ y).left := by
  intro O _ La _ _ N X Y π Ga _ ρ A _ _ A₀ _ _ φ ν act act₀ eta hπ gp hφ hact heq hadd hlin htor
  have := hπ.etale
  have := hπ.onto
  have : Epi π := Flat.epi_of_flat_of_surjective π
  have desc : ∀ y, ∃ e : 𝟙_ (Over Y) ⟶ A₀, (eta y).left ≫ φ = π ≫ e.left := fun y => by
    obtain ⟨g, hg, -⟩ := (GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hπ).1 A₀.left ((eta y).left ≫ φ) fun a => by
      rw [← Category.assoc, ← heq a y, Category.assoc, hφ.inv a]
    exact GlobalTheory.ObjDesc.exists_sec gp (eta y) g hg
  choose eta₀ heta using desc
  have hse : ∀ y, GlobalTheory.ObjPull.secPull gp (eta₀ y) = eta y := fun y => GlobalTheory.ObjDesc.secPull_eq gp (heta y)
  refine ⟨eta₀, fun x y => GlobalTheory.ObjDesc.secPull_injective gp (by rw [map_mul, hse, hse, hse, hadd]),
    fun c x => ?_, fun x => GlobalTheory.ObjDesc.secPull_injective gp (by rw [map_one, hse, htor]), heta⟩
  apply Over.OverMorphism.ext
  rw [← cancel_epi π, ← heta, hlin, Over.comp_left, Over.comp_left, Category.assoc, hact c, ← Category.assoc,
    heta, Category.assoc]

end GlobalTheory.LevelSecDesc

end
