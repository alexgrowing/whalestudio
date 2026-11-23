import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSectionNef
import Development.WeilBound.CoreStatements.HodgeTatePoints.GfForms

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Bridge.GeoNum (red red_surjective ker_red comap_map_eq quotEquiv)

namespace PositivityTheory.HtPt.Gf

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem geoNum_nonneg_of_regular (p : ℕ) [Fact p.Prime] {W : Ideal (MRing J)} (hW : IsMultiProjPrime W)
    (hp : (p : MRing J) ∈ W) (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    {f g : MRing J} {bf bg : K → ℕ} {a : K → ℤ} (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg)
    (ha : ∀ k, (bf k : ℤ) - bg k = a k) (hfW : f ∉ W) (hgW : g ∉ W)
    (hreg : ∀ t : ∀ k, J k, (∀ k, (X ⟨k, t k⟩ : MRing J) ∉ W) → ∃ (n : ℕ) (c : K → ℕ) (v : MRing J),
      ¬ p ∣ n ∧ n * mon t c * f - v * g ∈ W) : 0 ≤ geoNum 1 W (fun _ => a) := by
  classical
  have hC : (MvPolynomial.C (p : ℤ) : MRing J) ∈ W := by
    simpa [map_natCast] using hp
  have hker : RingHom.ker (red (ι := J) p) ≤ W := by
    rw [ker_red]
    exact (Ideal.span_le).2 (by simpa using hC)
  set P := Ideal.map (red (ι := J) p) W with hPdef
  have hcomap : Ideal.comap (red (ι := J) p) P = W := comap_map_eq p hker
  have hWp : W.IsPrime := hW.1
  have hPprime : P.IsPrime := Ideal.map_isPrime_of_surjective (red_surjective p) hker
  have hsupp : ∀ h : MRing J, ∀ b : K → ℕ, IsMultiHomog h b →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (red (ι := J) p h) b := by
    intro h b hh
    rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff]
    intro m hm k
    exact hh m (MvPolynomial.support_map_subset _ _ hm) k
  have hPhom : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P := by
    rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, rfl⟩ := hW.2.1
    refine ⟨(red (ι := J) p) '' S, ?_, ?_⟩
    · rintro _ ⟨h, hh, rfl⟩
      obtain ⟨b, hb⟩ := hS h hh
      exact ⟨b, (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 (hsupp h b hb)⟩
    · rw [hPdef, Ideal.map_span]
  have hPrel : GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant P := by
    rw [← GroundTheory.Heights₂.Heights.Bridge.GeoNum.isRelevant_comap_iff p P, hcomap]
    exact hW.2.2
  have hPm : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime P := ⟨hPprime, hPhom, hPrel⟩
  have hdimP : ringKrullDim (GroundTheory.Heights₂.Heights.NumbersDVR.MRing J (ZMod p) ⧸ P) =
      ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← hdim, ← ringKrullDim_eq_of_ringEquiv (quotEquiv p P), hcomap]
  have hreg' : GroundTheory.Heights₂.Heights.Model.IsRegularSection P a (red (ι := J) p f) (red (ι := J) p g) := by
    refine ⟨⟨bf, bg, hsupp f bf hf, hsupp g bg hg, funext ha⟩, ?_, ?_, ?_⟩
    · intro hm
      exact hfW (by rw [← hcomap]; exact hm)
    · intro hm
      exact hgW (by rw [← hcomap]; exact hm)
    · intro W' hW' hPW'
      set W'' := Ideal.comap (red (ι := J) p) W'
      have hW'pr : W'.IsPrime := hW'.1
      have hW''pr : W''.IsPrime := Ideal.comap_isPrime _ _
      have hWW'' : W ≤ W'' := by
        rw [← hcomap]
        exact Ideal.comap_mono hPW'
      have hrel : IsRelevant W'' :=
        (GroundTheory.Heights₂.Heights.Bridge.GeoNum.isRelevant_comap_iff p W').2 hW'.relevant
      choose t ht using hrel
      obtain ⟨n, c, v, hn, hv⟩ := hreg t (fun k hk => ht k (hWW'' hk))
      refine ⟨red (ι := J) p ((n : MRing J) * mon t c), red (ι := J) p v, ?_, ?_⟩
      · intro hu
        have hu' : ((n : MRing J) * mon t c) ∈ W'' := hu
        rcases hW''pr.mem_or_mem hu' with h1 | h1
        · exact natCast_not_mem hW''pr.ne_top (hWW'' hp) hn h1
        · exact mon_not_mem hW''pr ht c h1
      · have := Ideal.mem_map_of_mem (red (ι := J) p) hv
        simpa [map_sub, map_mul] using this
  have key := GroundTheory.Heights₂.Heights.Model.SectionNef.proof K J (ZMod p) P hPm hdimP a
    (red (ι := J) p f) (red (ι := J) p g) hreg'
  rw [GroundTheory.Heights₂.Heights.Bridge.intNum_map_eq_geoNum p 1 W hW hC hdim] at key
  have hfun : (![a] : Fin 1 → K → ℤ) = fun _ => a := by
    funext i
    fin_cases i
    rfl
  rwa [hfun] at key

end PositivityTheory.HtPt.Gf
