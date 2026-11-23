import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Flat.ActFam

theorem comp_mul_hom {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (a b : X ⟶ M) :
    (u ≫ a) * (u ≫ b) = u ≫ (a * b) := by
  rw [Hom.mul_def, Hom.mul_def, comp_lift_assoc]

theorem exists_action_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (ρ : ℝ) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M (Metric.ball 0 ρ) ψ), 0 < ρ → ∃ B : (Fin n → ℂ) → (𝓞 E →+* Module.End ℂ (Fin g → ℂ)), (∀ c x, DifferentiableOn ℂ (fun b => B b c x) (Metric.ball 0 ρ)) ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ c x, e.ex b (B b c x) = e.ex b x ≫ t.act.act c := by
  intro E _ _ _ H R _ t g n M ρ ψ e hρ
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.mem_ball_self hρ
  have hlift := fun c : 𝓞 E => exists_linear_lift_of_additive_family R t.G g n M (Metric.ball 0 ρ) ψ e g
    (Metric.ball 0 ρ) (fun b z => e.ex b z ≫ t.act.act c) Metric.isOpen_ball subset_rfl
    (fun b hb z w => by
      haveI := t.act.hom c
      simp only [e.add b hb z w]
      exact (IsMonHom.monoidHom (t.act.act c) _).map_mul _ _)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp e.hol (t.act.act c).left)
  choose h hd hs using hlift
  have hex : ∀ c, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ z, e.ex b (h c b z) = e.ex b z ≫ t.act.act c :=
    fun c b hb z => (hs c b hb).1 z
  have huq : ∀ c, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ l : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ z, e.ex b (l z) = e.ex b z ≫ t.act.act c) → l = h c b :=
    fun c b hb l hl => (hs c b hb).2.1 l hl
  have hring : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ f : 𝓞 E →+* Module.End ℂ (Fin g → ℂ), ∀ c, f c = h c b := by
    intro b hb
    refine ⟨RingHom.mk' ⟨⟨fun c => h c b, ?_⟩, ?_⟩ ?_, fun c => rfl⟩
    · refine (huq 1 b hb LinearMap.id fun z => ?_).symm
      rw [t.act.one]
      exact (Category.comp_id _).symm
    · intro c c'
      refine (huq (c * c') b hb (h c b * h c' b) fun z => ?_).symm
      rw [Module.End.mul_apply, hex c b hb, hex c' b hb, mul_comm c c', t.act.mul, Category.assoc]
    · intro c c'
      refine (huq (c + c') b hb (h c b + h c' b) fun z => ?_).symm
      rw [LinearMap.add_apply, e.add b hb, hex c b hb, hex c' b hb, t.act.add, comp_mul_hom]
  have hall : ∀ b, ∃ f : 𝓞 E →+* Module.End ℂ (Fin g → ℂ),
      b ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ c, f c = h c b := by
    intro b
    by_cases hb : b ∈ Metric.ball (0 : Fin n → ℂ) ρ
    · obtain ⟨f, hf⟩ := hring b hb
      exact ⟨f, fun _ => hf⟩
    · obtain ⟨f, -⟩ := hring 0 h0
      exact ⟨f, fun hb' => absurd hb' hb⟩
  choose B hB using hall
  refine ⟨B, fun c x => ?_, fun b hb c x => ?_⟩
  · refine (hd c x).congr fun b hb => ?_
    simp only [hB b hb c]
  · rw [hB b hb c]
    exact hex c b hb x

end GlobalTheory.CompanionTheory.Ar.Flat.ActFam
