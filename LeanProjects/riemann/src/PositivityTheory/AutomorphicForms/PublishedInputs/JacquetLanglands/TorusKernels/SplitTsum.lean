import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

open MeasureTheory

namespace UpperTheory.Esk.CentralTermsContribution

open Classical in
theorem split_tsum {G : Type} (P : G → Prop) (f : G → ℂ) (hf : Summable fun g => ‖f g‖) :
    ∑' g, f g = (∑' g, if P g then f g else 0) + ∑' g, if P g then 0 else f g := by
  have h1 : Summable fun g => if P g then f g else 0 :=
    Summable.of_norm_bounded hf (fun g => by split_ifs <;> simp)
  have h2 : Summable fun g => if P g then 0 else f g :=
    Summable.of_norm_bounded hf (fun g => by split_ifs <;> simp)
  rw [← Summable.tsum_add h1 h2]
  congr 1; funext g; split_ifs <;> simp

end UpperTheory.Esk.CentralTermsContribution

open UpperTheory.Esk in
open Classical in
theorem UpperTheory.Esk.pf_TF : UpperTheory.Esk.E2 → UpperTheory.Esk.Ecut → UpperTheory.Esk.E6 → UpperTheory.Esk.Fell → UpperTheory.Esk.Fhyp → UpperTheory.Esk.TF := by
  intro hE2 hcut hE6 hFell hFhyp F I Gf _ _ _ D hAx ι _ a
  obtain ⟨S, hFam, hS⟩ := hFell F I Gf D hAx ι a
  refine ⟨S, hFam, fun k hH hfd h => ?_⟩
  obtain ⟨⟨b, hb⟩, -⟩ := hcut F I Gf D hAx
  obtain ⟨hi, htr⟩ := hE6 F I Gf ι D k a hH hfd h b hb
  obtain ⟨hie, hge⟩ := hS k hH b hb
  have hsplit : ∀ y, (∑' γ : PG F, D.kk k a γ y) = (∑' γ : PG F, if IsEll γ then D.kk k a γ y else 0) +
      ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y :=
    fun y => CentralTermsContribution.split_tsum _ _ ((hE2 F I Gf ι D k a hH).1 y)
  have hfun : (fun y => b y • ∑' γ : PG F, D.kk k a γ y) = fun y => b y • (∑' γ : PG F, if IsEll γ then D.kk k a γ y else 0) +
      b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y := by
    funext y; rw [hsplit y, smul_add]
  have hih : Integrable (fun y => b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) D.μY := by
    have := hi.sub hie
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    rw [hsplit y, smul_add, add_sub_cancel_left]
  have h0 := hFhyp F I Gf ι D k a hH b hb hih
  rw [htr, ← hge, hfun, integral_add hie hih, h0, add_zero]
