import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LevelScalarAction

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem lev_smul {S : Finset (Pl E)} {x : XB E k} (h : Lev S x) (c : ℂ) : Lev S (c • x) := by
  intro w hw
  filter_upwards [h w hw] with u hu
  have hu' : repW k w u x = x := hu
  change repW k w u (c • x) = c • x
  rw [map_smul, hu']

end LevelScalarAction

theorem global_level_of : jumpWindows.G0 → jumpWindows.G1 → jumpWindows.AlmostEverywhereSpherical → jumpWindows.G2c → jumpWindows.G5 → K8 → K9 := by
  intro hG0 hG1 hG1b hG2c hG5 hK8 E _ _ _ k _ ψ hψ hcond π hπ
  obtain ⟨φ₀, hφ₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  obtain ⟨x₀, hx₀, -, hlev⟩ := hG1 E k π hπ φ₀ hφ₀
  have hev := hcond.and (hG1b E k π hπ φ₀ hφ₀ x₀ hx₀)
  have hfin := Filter.eventually_cofinite.1 hev
  refine ⟨hfin.toFinset, fun S hS => ?_⟩
  have hoff : ∀ w, w ∉ S → Cond ψ w ∧ ∀ B, (CG.mk π).HasSat w B → SatFn w B x₀ := by
    intro w hw
    by_contra hc
    exact hw (hS ((Set.Finite.mem_toFinset _).2 hc))
  refine ⟨fun w hw => (hoff w hw).1, fun α hα => ?_⟩
  have hgood : Good ψ (k - 1) (x₀ : GA E k → ℂ) := by
    rw [hx₀]; exact GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E k ψ φ₀ (π.cusp _ hφ₀)
  have hx0 : x₀ ≠ 0 := by
    intro h
    subst h
    exact hne (Subtype.ext (by rw [← hx₀]; rfl))
  obtain ⟨g, hg⟩ := ((hG5 E k ψ hψ).2.2.2 x₀ hgood).2.1 hx0
  have hsat : ∀ w : Off E S, SatFn w.1 (Finset.univ.val.map (α w)) x₀ := fun w => (hoff w.1 w.2).2 _ (hα w)
  obtain ⟨g₀, h1, h2, h3⟩ := (hG0 E k).2.2.2.2.2.2.2.2.2.2.1 S g
  have hne0 : Wh ψ x₀ g₀ ≠ 0 :=
    ((hK8 E k ψ hψ S (fun w hw => (hoff w hw).1) α x₀ hgood hsat).2.2 g hg).1 g₀ h1 h2 h3
  refine ⟨(Wh ψ x₀ g₀)⁻¹ • φ₀, π.V.smul_mem _ hφ₀, g₀, (Wh ψ x₀ g₀)⁻¹ • x₀, h3, ?_, ?_, LevelScalarAction.lev_smul (hlev S) _, ?_⟩
  · funext y
    change (Wh ψ x₀ g₀)⁻¹ * x₀ y = (Wh ψ x₀ g₀)⁻¹ * φ₀.1 y
    rw [hx₀]
  · intro w
    obtain ⟨Y, -, -, hY⟩ := hG2c E k w.1 (Finset.univ.val.map (α w)) (by simp)
    exact (hY _).1 (Y.smul_mem _ ((hY x₀).2 (hsat w)))
  · rw [(hG5 E k ψ hψ).2.1, one_mul]
    change whit ψ (k - 1) (fun y => (Wh ψ x₀ g₀)⁻¹ * x₀ y) g₀ = 1
    rw [GlobalTheory.CuspRep.Generic.whit_smul]
    exact inv_mul_cancel₀ hne0

end PositivityTheory.AdelicQuotientData

end
