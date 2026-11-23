import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFamThrough
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyPowerDegree
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.BoxFrame

open GlobalTheory.IntegralBox

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem dvd_iff (D : DegPre V) {k : ℕ} {α : D.X} (a : V) (σ τ : SecMod D k α) :
    (∀ j, LB.Sec.f σ j = constFn D.P.A.hom _ a * LB.Sec.f τ j) ↔ σ = a • τ :=
  ⟨fun h => SecOps.sec_ext h, fun h j => congrArg (fun s : SecMod D k α => LB.Sec.f s j) h⟩

theorem dvd_of_pull_eq_zero (hT : TwistBaseChangeStatement) {ϖ : V} (hϖ : Irreducible ϖ) (D : DegPre V) {k : ℕ}
    (hk : 1 ≤ k) {α : D.X} (σ : SecMod D k α) (h : pullBC (residue V) D k α σ = 0) :
    ∃ τ : SecMod D k α, σ = ϖ • τ := by
  obtain ⟨b, hb, hb'⟩ := exists_basis (residue V) D hT hk α
  obtain ⟨c, rfl⟩ := hb σ
  have h0 := hb' (fun i => residue V (c i)) (by simpa only [map_sum, map_smulₛₗ] using h)
  have hd : ∀ i, ϖ ∣ c i := fun i => by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq, ← residue_eq_zero_iff]
    exact congrFun h0 i
  choose d hd using hd
  exact ⟨∑ i, d i • b i, by simp only [hd, Finset.smul_sum, smul_smul]⟩

theorem exists_pull_ne_zero (hT : TwistBaseChangeStatement) (D : DegPre V) (α : D.X) :
    ∃ σ : SecMod D 1 α, pullBC (residue V) D 1 α σ ≠ 0 := by
  classical
  obtain ⟨b, -, hb'⟩ := exists_basis (residue V) D hT le_rfl α
  let i₀ : Fin (1 ^ D.P.g) := ⟨0, by simp⟩
  refine ⟨b i₀, fun h => ?_⟩
  have h0 := hb' (Pi.single i₀ 1) (by
    rw [Finset.sum_eq_single i₀, h, smul_zero]
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h)
  simpa using congrFun h0 i₀

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (n : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre n) (F : Type) [Field F] [Algebra (FractionRing V) F] (θ : Fam D.toPre F 1) (Θ : Fam D'.toPre F 1), ThFrame D ϖ F θ → IsBoxFam pD F 1 Θ (fun _ => θ) → ThFrame D' ϖ F Θ := by
  intro V _ _ _ _ ϖ hϖ n D D' pD F _ _ θ Θ ⟨σ, σF, hs, he, hn⟩ hB
  have hT := GlobalTheory.twistBaseChange_and_valuation_statements.1
  have hex : ∀ α : D.toPre.X, ∃ s : SecMod D.toPre 1 α, pullBC (residue V) D.toPre 1 α s ≠ 0 ∧
      (α = 0 → GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε 1) (θ.s α)
        (D.toPre.famφB α) (DegPre.famε 1) s (DegPre.prB D.toPre F).left 1) := fun α => by
    by_cases hα : α = 0
    · subst hα
      refine ⟨σ, fun h => ?_, fun _ => ?_⟩
      · obtain ⟨τ, hτ⟩ := dvd_of_pull_eq_zero hT hϖ D.toPre le_rfl σ h
        exact hn ⟨τ, (dvd_iff D.toPre ϖ σ τ).2 hτ⟩
      · rw [show θ.s 0 = σF from SecOps.sec_ext he]
        exact hs
    · obtain ⟨s, hs⟩ := exists_pull_ne_zero hT D.toPre α
      exact ⟨s, hs, fun h => absurd h hα⟩
  choose f hf hf' using hex
  refine ⟨boxFamB pD 1 (fun _ α => f α) 0, Θ.s 0,
    UnitBallBox.box_secScal pD hB (isBoxFamB_boxFamB pD 1 _) 0
      (fun i => hf' _ (by rw [map_zero]; rfl)), fun _ => rfl, ?_⟩
  rintro ⟨τ, hτ⟩
  have h1 := (dvd_iff D'.toPre ϖ _ τ).1 hτ
  have h2 : residue V ϖ = 0 := (residue_eq_zero_iff _).2 (by
    rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)
  have h3 : pullBC (residue V) D'.toPre 1 0 (boxFamB pD 1 (fun _ α => f α) 0) = 0 := by
    exact (congrArg _ h1).trans ((map_smulₛₗ (pullBC (residue V) D'.toPre 1 0) ϖ τ).trans (by rw [h2, zero_smul]))
  have h4 := box_indep (residue V) pD (m := 1) (fun α _ => f α) (fun α c hc => by
    rw [Fin.sum_univ_one, smul_eq_zero] at hc
    funext i
    rw [Subsingleton.elim i 0]
    exact hc.resolve_right (hf α)) 0 (fun _ => 1) (Finset.sum_eq_zero fun a _ => (congrArg _ h3).trans (smul_zero _))
  exact one_ne_zero (congrFun h4 fun _ => 0)

end GlobalTheory.BoxFrame
