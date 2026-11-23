import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ConjModelCast
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift

theorem overK_of_sqrt {D : D7} (σ : D.what₂.LL →+* ℂ)
    (h : σ (D.embE D.host.sqrtMinusD) = D.what₂.embLL (D.embE D.host.sqrtMinusD)) : OverK σ := by
  intro x hx
  have hx' : x ∈ IntermediateField.adjoin ℚ {D.host.sqrtMinusD} := hx
  clear hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact h
  | algebraMap q => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, map_mul, hx, hy]

theorem embLL_embE (D : D7) (x : D.host.E) : D.what₂.embLL (D.embE x) = D.host.φ₀ x :=
  RingHom.congr_fun D.embE_φ₀ x

theorem sqrtMinusD_sq (D : D7) : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) :=
  D.host.sqd_sq

theorem overK_conj {D : D7} (σ : D.what₂.LL →+* ℂ) (h : ¬ OverK σ) : OverK ((starRingEnd ℂ).comp σ) := by
  apply overK_of_sqrt
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have h1 : σ (D.embE D.host.sqrtMinusD) ^ 2 = D.what₂.embLL (D.embE D.host.sqrtMinusD) ^ 2 := by
    rw [← map_pow, ← map_pow, ← map_pow, ← map_pow, sqrtMinusD_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exact absurd (overK_of_sqrt σ h2) h
  · rw [RingHom.comp_apply, h2, embLL_embE, h0]; simp

theorem exists_psi_of_overK {D : D7} (σ : D.what₂.LL →+* ℂ) (h : OverK σ) :
    ∃ g ∈ D.R.Psi, ∀ τ, labE σ τ = D.host.emb (g * (D.eTau τ).1) := by
  obtain ⟨g0, h0⟩ := (factEmb D.R D.host).1.2 (σ.comp D.embE)
  refine ⟨g0, ((factEmb D.R D.host).2 _).1 ?_, fun τ => ?_⟩
  · have h1 := h D.host.sqrtMinusD (IntermediateField.mem_adjoin_simple_self ℚ _)
    have h2 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    rw [h0]
    exact h1.trans ((embLL_embE D _).trans h2)
  · rw [ConjReading.emb_mul, h0]; rfl

theorem labels_overK : ∀ {D : D7} (σ : D.what₂.LL →+* ℂ),
    (OverK σ → Function.Bijective (lab (D := D) σ) ∧ ∀ ρ, labE σ (lab σ ρ) = tauE D ρ) ∧
      (¬ OverK σ → OverK ((starRingEnd ℂ).comp σ)) := by
  intro D σ
  refine ⟨fun h => ?_, overK_conj σ⟩
  obtain ⟨g, hg, key⟩ := exists_psi_of_overK σ h
  have inj := (factEmb D.R D.host).1.1
  have main : ∀ ρ, labE σ (lab σ ρ) = tauE D ρ := by
    intro ρ
    have hs : labE σ (lab σ ρ) = tauE D ρ ∨ labE σ (lab σ ρ) = (starRingEnd ℂ).comp (tauE D ρ) := by
      unfold lab; rw [dif_pos (ConjReading.lab_exists σ ρ)]; exact (ConjReading.lab_exists σ ρ).choose_spec
    refine hs.resolve_right fun h' => ?_
    rw [key] at h'
    exact ConjReading.conj_not_mem D ρ _ h' (Subgroup.mul_mem _ hg (D.eTau _).2)
  refine ⟨⟨fun ρ ρ' e => ?_, fun τ => ?_⟩, main⟩
  · have e' : tauE D ρ = tauE D ρ' := by rw [← main, ← main, e]
    exact D.eTau.injective (Subtype.ext (inj e'))
  · refine ⟨D.eTau.symm ⟨g * (D.eTau τ).1, Subgroup.mul_mem _ hg (D.eTau τ).2⟩, ?_⟩
    have e := main (D.eTau.symm ⟨g * (D.eTau τ).1, Subgroup.mul_mem _ hg (D.eTau τ).2⟩)
    rw [key, tauE, Equiv.apply_symm_apply] at e
    exact D.eTau.injective (Subtype.ext (mul_left_cancel (inj e)))

end GlobalTheory.GalLift
