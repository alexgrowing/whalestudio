import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PartOneOfSemistableReductionPadicPolarized
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrLocalFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArcDatumRecoveringUnitaryDataCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisGenericUnitaryUniforStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointArcDataAtUniformiserCompleteDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.MumTrait.exists_unif_of_pelOK : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (G : Over (Sp R₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Sp (FractionRing R₁))), GlobalTheory.LN.CDvr R₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsSemiAbelian G ∧ Nonempty (Unif (maximalIdeal R₁) D₁ A G) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) := by
  intro R _ _ _ hR E _ _ _ H Dm D _ o hX hP
  obtain ⟨p, hp, W₀, hW, i, V₁, _, _, _, ρ₁, b₁, hV₁, hρ₁, hf₁, hl₁, hb₁⟩ := GlobalTheory.T.exists_complete_dvr_local_finite_extension R hR E H
  have hpq : 1 ≤ Dm.p + Dm.q := by have := hP.2.1; omega
  let Xo : ∀ l : Level H, Moduli Dm l := fun l => (GlobalTheory.Moduli.moduli_scheme_exists E H Dm l hpq).some
  obtain ⟨Y, hY, -⟩ := (GlobalTheory.partI_of_semistableReduction GlobalTheory.SS.semistableReductionSt).2 E H Dm hpq Xo
  have hFour := ((hY p W₀ hp hW).2 i).2.2
  obtain ⟨V, _, _, _, ρ, b, ϖ, a, hV, hρi, hρf, hϖ, hmatch⟩ := GlobalTheory.T.exists_arcDatum_recovering_unitaryData_completeDVR R hR E H Dm D o hX hP i.l i.c _ (i.c.V W₀).subtype
    Subtype.val_injective V₁ ρ₁ b₁ hV₁ hρ₁ hf₁ hl₁ hb₁
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_point_arcData_at_uniformiser_completeDVR E H Dm i.l (Xo i.l) i.c _ _ (Y p W₀ hp hW i) hFour V hV b ϖ a hϖ
  obtain ⟨t, -, P, hpull⟩ := hmatch (Xo i.l) (Y p W₀ hp hW i) y hy
  exact ⟨V, _, _, _, ρ, P.D, t.G, inferInstance, inferInstance, P.A, hV, hρi, hρf, hpull, t.semi, ⟨P.U⟩,
    GlobalTheory.T.lineBundleSymmetryHypothesis_generic_unitary_uniformised V (maximalIdeal V) E H t P⟩
