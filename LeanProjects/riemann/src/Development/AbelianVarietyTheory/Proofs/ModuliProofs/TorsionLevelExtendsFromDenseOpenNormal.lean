import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem GlobalTheory.exists_torsion_level_extend : ∀ (Λ : Type) [AddCommGroup Λ] (N : ℕ) (S W : Scheme.{0}) [IsLocallyNoetherian S] (j : W ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over W) [GrpObj G'] (φ : G'.left ⟶ G.left) (lv' : Λ → (𝟙_ (Over W) ⟶ G')), Geo.Tor.IsNormalScheme S → IsOpenImmersion j → IsDominant j → IsProper G.hom → IsUnit (N : Γ(S, ⊤)) → IsGrpPullback G' G j φ → (∀ a c, lv' (a + c) = lv' a * lv' c) → (∀ a, lv' (N • a) = 1) → ∃ lv : Λ → (𝟙_ (Over S) ⟶ G), (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv (N • a) = 1) ∧ ∀ a, (lv' a).left ≫ φ = j ≫ (lv a).left := by
  intro Λ _ N S W _ j G _ _ G' _ φ lv' hS _ _ _ hN gp hadd hker
  have hred : IsReduced S := by
    have : ∀ x : S, _root_.IsReduced (S.presheaf.stalk x) := fun x => by
      obtain ⟨_, _⟩ := hS x
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have hqc : QuasiCompact j := inferInstance
  let P : Over S := Over.mk ((𝟙_ (Over W)).hom ≫ j)
  let ρ : (𝟙_ (Over W) ⟶ G') →* (P ⟶ G) := pushHom gp _
  have hρ : ∀ x, (ρ x).left = x.left ≫ φ := fun _ => rfl
  have h0 : lv' 0 = 1 := by simpa using hker 0
  have hpow : ∀ (n : ℕ) a, lv' (n • a) = lv' a ^ n := fun n a => by
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hex : ∀ a, ∃ σ : S ⟶ G.left, σ ≫ G.hom = 𝟙 S ∧ j ≫ σ = (lv' a).left ≫ φ := fun a => by
    obtain ⟨s, h₁, h₂⟩ := GlobalTheory.exists_section_of_pow_eq_one hS j G N hN P (ρ (lv' a))
      (by rw [← map_pow, ← hpow, hker, map_one]) (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
    exact ⟨s, h₁, h₂.trans (Category.id_comp _)⟩
  choose σ hσ₁ hσ₂ using hex
  let lv : Λ → (𝟙_ (Over S) ⟶ G) := fun a => Over.homMk (σ a) (hσ₁ a)
  let u : P ⟶ 𝟙_ (Over S) := Over.homMk j ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hu : ∀ a, u ≫ lv a = ρ (lv' a) := fun a => Over.OverMorphism.ext (hσ₂ a)
  have inj : ∀ s t : 𝟙_ (Over S) ⟶ G, u ≫ s = u ≫ t → s = t := fun s t h =>
    Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := S) G.hom ((Over.w s).trans (Over.w t).symm) j
      (congrArg (fun z => z.left) h))
  refine ⟨lv, fun a c => inj _ _ ?_, fun a => inj _ _ ?_, fun a => (hσ₂ a).symm⟩
  · rw [MonObj.comp_mul, hu, hu, hu, hadd, map_mul]
  · rw [hu, hker, map_one, MonObj.comp_one]
