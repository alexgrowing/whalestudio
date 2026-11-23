import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresMono
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresDl
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PowCompPow

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

private theorem lc_mono {R : Type} [CommRing R] {l m n n' : ℕ} {f g : PowerSeries R} (h : n' ≤ n)
    (H : LC l m n f g) : LC l m n' f g := by
  unfold LC at *
  exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h) H

private theorem lc_comb {R : Type} [CommRing R] {l m n : ℕ} {f f' g g' : PowerSeries R}
    (H : LC l m n f g) (H' : LC l m n f' g') (E : LC l m n g g') : LC l m n (f - f') 0 := by
  unfold LC at *
  have := Ideal.sub_mem _ (Ideal.add_mem _ H E) H'
  rw [map_sub, map_zero, sub_zero]
  convert this using 1
  ring

private theorem cg_of_eq {l : ℕ} [Fact l.Prime] (n : ℕ) {x y : Qbar l} (h : x = y) : Cg n x y := by
  unfold Cg
  rw [h, sub_self, norm_zero]
  exact norm_nonneg _

theorem pRepUniq : SRepUniq := by
  intro l _ hl2 Ω _ _ _ A hA j Φ c β ζ hζ Z Z' D D' hD hD' hZ
  obtain ⟨c₁, m₁, h₁⟩ := hD
  obtain ⟨c₂, m₂, h₂⟩ := hD'
  funext i
  rw [← sub_eq_zero]
  refine pUniq Φ.R l Φ.σ Φ.fl (D i - D' i) (max c₁ c₂ + 1) (max m₁ m₂ + 1) (fun m hm => ?_)
  obtain ⟨P, hP, hPD⟩ := h₁ m (by omega)
  obtain ⟨P', hP', hPD'⟩ := h₂ m (by omega)
  have hPn : BPres β A ζ Z m (m - max c₁ c₂) P :=
    pPresMono l hl2 Ω A hA c β ζ hζ Z Z m (m - c₁) (m - max c₁ c₂) P (by omega)
      (fun s _ => cg_of_eq _ rfl) hP
  have hPn' : BPres β A ζ Z m (m - max c₁ c₂) P' :=
    pPresMono l hl2 Ω A hA c β ζ hζ Z' Z m (m - c₂) (m - max c₁ c₂) P' (by omega)
      (fun s hs => cg_of_eq _ (hZ m s hs).symm) hP'
  have hE := (pPresDl l hl2 Ω A hA j Φ c β ζ hζ Z m (m - max c₁ c₂) (by omega) P P' hPn hPn' i).2
  have hcomb := lc_comb (lc_mono (by omega) (hPD i)) (lc_mono (by omega) (hPD' i)) hE
  have hfin := lc_mono (n' := m - (max c₁ c₂ + 1)) (by omega) hcomb
  rwa [Fr.tw, Fr.tw, ← map_sub] at hfin

end UpperTheory.Kd.C7
