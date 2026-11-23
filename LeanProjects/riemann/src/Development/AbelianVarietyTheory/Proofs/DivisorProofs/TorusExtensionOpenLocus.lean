import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuasiCompactIffLocallyOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSpreadsOutStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSpecializationLocallyLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicPointLiftsFiniteTypeStatement

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.BdFib.GenRk

theorem finrank_addMonoidHom_int (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] :
    Module.finrank ℤ (Y →+ ℤ) = Module.finrank ℤ Y := by
  rw [(addMonoidHomLequivInt (B := ℤ) ℤ).finrank_eq]
  exact (Module.finrank_eq_card_basis (Module.finBasis ℤ Y).dualBasis).trans (Fintype.card_fin _)

theorem finrank_eq_of_torusExtension : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] (T₁ T₂ : TorusExtension G), @Module.finrank ℤ T₁.X _ T₁.addCommGroup.toAddCommMonoid _ = @Module.finrank ℤ T₂.X _ T₂.addCommGroup.toAddCommMonoid _ := by
  intro K _ G _ T₁ T₂
  haveI := GlobalTheory.SemiAbelianCompare.isCommMonObj_of_torusExtension T₁
  letI := T₁.addCommGroup; letI := T₂.addCommGroup
  haveI := T₁.free; haveI := T₁.finite; haveI := T₂.free; haveI := T₂.finite
  haveI := T₁.i_hom; haveI := T₂.i_hom
  have h₁ := GlobalTheory.TorusPart.ofTorus_bijective_of_torusExtension T₁
  have h₂ := GlobalTheory.TorusPart.ofTorus_bijective_of_torusExtension T₂
  let e : (T₁.X →+ ℤ) ≃+ (T₂.X →+ ℤ) := (AddEquiv.ofBijective _ h₁).trans (AddEquiv.ofBijective _ h₂).symm
  show Module.finrank ℤ T₁.X = Module.finrank ℤ T₂.X
  rw [← finrank_addMonoidHom_int T₁.X, ← finrank_addMonoidHom_int T₂.X]
  exact e.toIntLinearEquiv.finrank_eq

theorem exists_open_torRk_of_specializes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (f : Y ⟶ X), IsProper p → ∀ (k : Type) [Field k] (g : Sp k ⟶ Y) (T : TorusExtension ((Over.pullback (g ≫ f)).obj t.G)), ∃ U : Y.Opens, g (IsLocalRing.closedPoint k) ∈ U ∧ ∀ y : Sp Qb ⟶ Y, y (IsLocalRing.closedPoint Qb) ∈ U → g (IsLocalRing.closedPoint k) ⤳ y (IsLocalRing.closedPoint Qb) → TorRk t (y ≫ f) (@Module.finrank ℤ T.X _ T.addCommGroup.toAddCommMonoid _) := by
  intro E _ _ _ H X t F _ _ Y p f hp k _ g T
  haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  obtain ⟨V, π, v, rfl, hπ, hT⟩ := GlobalTheory.T.torus_extension_spreads_out E H X t Y f k g T
  obtain ⟨U, hU, hsp⟩ := GlobalTheory.T.proper_specialization_locally_lifts F Y p hp V π hπ (v (IsLocalRing.closedPoint k))
  refine ⟨U, hU, ?_⟩
  intro y hy hgy
  obtain ⟨u, hu⟩ := hsp _ hy hgy
  obtain ⟨w, rfl⟩ := GlobalTheory.T.algebraic_point_lifts_finite_type V Y π hπ Qb y u hu
  obtain ⟨T', hT'⟩ := hT Qb w
  intro T''
  rw [← hT']
  exact finrank_eq_of_torusExtension Qb _ T'' (by rw [← Category.assoc] at T'; exact T')

end GlobalTheory.BdFib.GenRk

end
