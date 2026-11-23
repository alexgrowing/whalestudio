import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryVolumeFamily
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_unitary_volume_family : GlobalTheory.Published.TamagawaSpecialUnitary → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (p0 : Ψ → ℕ) [MeasurableSpace (GlobalTheory.SUVol.realSU Ψ G)] [BorelSpace (GlobalTheory.SUVol.realSU Ψ G)] (J : Type) (s : J → Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E)), 2 ≤ r → GlobalTheory.UCls.Unr E → GlobalTheory.UCls.SelfDualLat G Λ → (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) → GlobalTheory.SUVol.IsSReps G (Λ : Set (Fin r → E)) 1 s → ENNReal.ofReal (c ^ (ReciprocityTheory.ChartRestriction.G.FD.fdeg E * r ^ 2)) ≤ ∑' j, MeasureTheory.covolume (GlobalTheory.SUVol.inReal Ψ G (GlobalTheory.SUVol.ratStab G (Λ : Set (Fin r → E)) (s j))) (GlobalTheory.SUVol.realSU Ψ G) (GlobalTheory.SUVol.riemHaar Ψ G x) := by
  first | exact @GlobalTheory.SUVolLower.sum_covolume_ge | exact GlobalTheory.SUVolLower.sum_covolume_ge | (intros; apply GlobalTheory.SUVolLower.sum_covolume_ge <;> assumption)
