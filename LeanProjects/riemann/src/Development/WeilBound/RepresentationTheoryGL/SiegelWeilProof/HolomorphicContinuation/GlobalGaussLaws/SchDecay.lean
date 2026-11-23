import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IntegrableRho

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

def Pk (μ : Measure (Mx D m n)) (π : Mx D m n → (Fin m → Fin n → ℂ)) (B : Mx D m n → ℂ) (κ : ℂ) : Prop :=
  ∀ a : (Fin m → Fin n → ℂ) → ℂ, Measurable a → (∃ C, ∀ u, ‖a u‖ ≤ C * (1 + ‖u‖) ^ (-rr m n)) →
    ∫ z, a (π z) * B z ∂μ = κ * ∫ u, a u

def kap (μ : Measure (Mx D m n)) (π : Mx D m n → (Fin m → Fin n → ℂ)) (B : Mx D m n → ℂ) : ℂ :=
  Classical.epsilon (Pk μ π B)

set_option synthInstance.maxHeartbeats 800000 in
theorem kap_spec {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hdet : IsUnit fr.det) (μ : Measure (Mx D V.rank n)) [μ.IsAddHaarMeasure]
    {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (x : Mx D V.rank n) :
    Pk μ (piF θ τ fr) (Bw ψ V θ τ fr Ψ x) (kap μ (piF θ τ fr) (Bw ψ V θ τ fr Ψ x)) := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  apply Classical.epsilon_spec
  have hρc : Continuous fun u : Fin V.rank → Fin n → ℂ => (1 + ‖u‖) ^ (-rr V.rank n) :=
    (continuous_const.add continuous_norm).rpow_const fun u => Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg u)).ne'
  exact LocCellT.tauFact μ (piF θ τ fr) (continuous_piF hθ τ fr) (sIns τ fr)
    (fun z u => by rw [(piF θ τ fr).map_add, piF_sIns hθ τ hdet]) (Bw ψ V θ τ fr Ψ x)
    (continuous_Bw hθ hψ hΨ x).measurable (fun z u => Bw_add hθ hdet ψ hΨ x z u)
    (fun u => (1 + ‖u‖) ^ (-rr V.rank n)) hρc (fun u => Real.rpow_pos_of_pos (by positivity) _)
    (hint_int hθ hdet μ hΨ hψ x)

theorem sch_decay (f : (Fin m → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    ∃ C, ∀ u, ‖f u‖ ≤ C * (1 + ‖u‖) ^ (-rr m n) := by
  obtain ⟨S, rfl⟩ := hf
  set k : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hk
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (Fin m → Fin n → ℂ) ℂ) S, fun u => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl S u
  rw [norm_iteratedFDeriv_zero] at h
  have hpos : 0 < (1 + ‖u‖) ^ k := by positivity
  have e : (1 + ‖u‖) ^ (-rr m n) = ((1 + ‖u‖) ^ k)⁻¹ := by
    rw [rr, Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [e, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact h

end PositivityTheory.Rg.Sw.Glob.FTH
