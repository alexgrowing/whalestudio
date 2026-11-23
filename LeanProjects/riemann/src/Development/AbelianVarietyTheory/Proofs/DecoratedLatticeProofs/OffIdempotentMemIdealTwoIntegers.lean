import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPEqCP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OffIdemTwo
open GlobalTheory.IdemSupport GlobalTheory.OffIdemDen

theorem exists_split {K : Type} [Field K] [NumberField K] (c d : 𝓞 K) (hc0 : c ≠ 0) (hd : d ≠ 0) :
    ∃ x y : 𝓞 K, (x : K) / c * c + (y : K) / d * d = 1 ∧
      (∀ Q : HeightOneSpectrum (𝓞 K), ¬ (c ∈ Q.asIdeal ∧ d ∈ Q.asIdeal) →
        ∃ g t : 𝓞 K, g ≠ 0 ∧ g ∉ Q.asIdeal ∧ (x : K) / c = t * (g : K)⁻¹) ∧
      (∀ Q : HeightOneSpectrum (𝓞 K), ¬ (c ∈ Q.asIdeal ∧ d ∈ Q.asIdeal) →
        ∃ g t : 𝓞 K, g ≠ 0 ∧ g ∉ Q.asIdeal ∧ (y : K) / d = t * (g : K)⁻¹) := by
  obtain ⟨G, hG⟩ : ∃ G : Ideal (𝓞 K), G = Ideal.span {c} ⊔ Ideal.span {d} := ⟨_, rfl⟩
  obtain ⟨I', hI'⟩ : G ∣ Ideal.span {c} := Ideal.dvd_iff_le.2 (hG ▸ le_sup_left)
  obtain ⟨D', hD'⟩ : G ∣ Ideal.span {d} := Ideal.dvd_iff_le.2 (hG ▸ le_sup_right)
  have hG0 : G ≠ 0 := by
    intro h
    have : c ∈ G := hG ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    rw [h, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact hc0 this
  have hcop : I' ⊔ D' = ⊤ := by
    apply mul_left_cancel₀ hG0
    rw [Ideal.mul_sup, ← hI', ← hD', Ideal.mul_top, hG]
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hcop.symm ▸ Submodule.mem_top : (1 : 𝓞 K) ∈ I' ⊔ D')
  have coe0 : ∀ w : 𝓞 K, w ≠ 0 → (w : K) ≠ 0 := fun w hw => RingOfIntegers.coe_ne_zero_iff.2 hw
  have hint : ∀ (w z : 𝓞 K), w ≠ 0 → (∀ g ∈ G, g * z ∈ Ideal.span {w}) →
      ∀ Q : HeightOneSpectrum (𝓞 K), ¬ (c ∈ Q.asIdeal ∧ d ∈ Q.asIdeal) →
      ∃ g t : 𝓞 K, g ≠ 0 ∧ g ∉ Q.asIdeal ∧ (z : K) / w = t * (g : K)⁻¹ := by
    intro w z hw hz Q hQ
    have hGQ : ¬ G ≤ Q.asIdeal := fun h => hQ
      ⟨h (hG ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)),
       h (hG ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩
    obtain ⟨g, hg, hgQ⟩ := Set.not_subset.1 hGQ
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hz g hg)
    have hg0 : g ≠ 0 := fun h => hgQ (h ▸ Q.asIdeal.zero_mem)
    have hgE := coe0 g hg0
    have hwE := coe0 w hw
    have htE : (t : K) * w = g * z := by
      have := congrArg (algebraMap (𝓞 K) K) ht
      rwa [map_mul, map_mul] at this
    refine ⟨g, t, hg0, hgQ, ?_⟩
    field_simp
    linear_combination -htE
  refine ⟨x, y, ?_, hint c x hc0 fun g hg => hI' ▸ Ideal.mul_mem_mul hg hx,
    hint d y hd fun g hg => hD' ▸ Ideal.mul_mem_mul hg hy⟩
  rw [div_mul_cancel₀ _ (coe0 c hc0), div_mul_cancel₀ _ (coe0 d hd)]
  have := congrArg (algebraMap (𝓞 K) K) hxy
  rwa [map_add, map_one] at this

theorem off_comp {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) {e : AE D}
    {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e SS) :
    (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) → Φ (1 - e - cA D e) Q = 0) ∧
    ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Φ (1 - e - cA D e) Q ∈ Q.adicCompletionIntegers D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, horth⟩ := he
  have hdl : ∀ P ∈ SS, IsDelta Φ P (es P) := fun P hP => delta_of_isIdemAt hΦ (hes P hP)
  have hdc : ∀ P ∈ SS, IsDelta Φ (cP P) (cA D (es P)) := fun P hP => delta_conj hΦ (hdl P hP)
  have hE : ∀ Q, Φ (∑ P ∈ SS, es P) Q = ∑ P ∈ SS, Φ (es P) Q := fun Q => map_sum (evQ Φ Q) _ _
  have hC : ∀ Q, Φ (cA D (∑ P ∈ SS, es P)) Q = ∑ P ∈ SS, Φ (cA D (es P)) Q := fun Q => by
    rw [map_sum]; exact map_sum (evQ Φ Q) _ _
  have hO : ∀ Q, Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q =
      1 - Φ (∑ P ∈ SS, es P) Q - Φ (cA D (∑ P ∈ SS, es P)) Q := fun Q => by
    change evQ Φ Q _ = _
    rw [map_sub, map_sub, map_one]; rfl
  have hprod : ∀ Q, Φ (∑ P ∈ SS, es P) Q * Φ (cA D (∑ P ∈ SS, es P)) Q = 0 := fun Q => by
    rw [← ev_mul, horth, ev_zero]

  have hzero : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) →
      Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q = 0 := by
    intro Q hQQ
    rw [hO]
    rcases hQQ with hQ | hQ
    · have h1 : Φ (∑ P ∈ SS, es P) Q = 1 := by
        rw [hE, Finset.sum_eq_single Q (fun P hP hne => (hdl P hP).2.2 Q (Ne.symm hne))
          (fun h => absurd hQ h), (hdl Q hQ).2.1]
      have h2 := hprod Q
      rw [h1, one_mul] at h2
      rw [h1, h2, sub_self, sub_zero]
    · rw [conjP_eq_cP] at hQ
      have h1 : Φ (cA D (∑ P ∈ SS, es P)) Q = 1 := by
        rw [hC, Finset.sum_eq_single (cP Q) (fun P hP hne => (hdc P hP).2.2 Q (fun h => hne (by
            rw [h, cP_cP])))
          (fun h => absurd hQ h)]
        have := (hdc (cP Q) hQ).2.1
        rwa [cP_cP] at this
      have h2 := hprod Q
      rw [h1, mul_one] at h2
      rw [h1, h2, sub_zero, sub_self]

  have hoint : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q ∈ Q.adicCompletionIntegers D.host.E := by
    intro Q
    rw [hO, hE, hC]
    exact sub_mem (sub_mem (Q.adicCompletionIntegers D.host.E).one_mem
      (sum_mem fun P hP => delta_mem (hdl P hP) Q)) (sum_mem fun P hP => delta_mem (hdc P hP) Q)
  exact ⟨hzero, hoint⟩

theorem term_int {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) (o : AE D)
    (hoint : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Φ o Q ∈ Q.adicCompletionIntegers D.host.E) (u : D.host.E)
    (hu : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Φ o Q = 0 ∨ ∃ g t : 𝓞 D.host.E, g ≠ 0 ∧ g ∉ Q.asIdeal ∧
      u = t * (g : D.host.E)⁻¹) : finPart D (o * incA D u) ∈ intAE D := by
  rw [hΦ.int]
  intro Q
  rw [ev_mul, hΦ.inc]
  rcases hu Q with h0 | ⟨g, t, hg0, hgQ, heq⟩
  · rw [h0, zero_mul]
    exact (Q.adicCompletionIntegers D.host.E).zero_mem
  · refine mul_mem (hoint Q) ?_
    have : algebraMap D.host.E (Q.adicCompletion D.host.E) u ∈ Q.adicCompletionIntegers D.host.E := by
      rw [heq, map_mul]
      exact mul_mem (Q.coe_mem_adicCompletionIntegers t) ((inv_mem_iff Q hg0).2 hgQ)
    exact this

theorem off_two : ∀ (D : D7) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ c : ℕ, 0 < c → ∀ d : 𝓞 D.host.E, d ≠ 0 → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (c : 𝓞 D.host.E) ∈ Q.asIdeal → d ∈ Q.asIdeal → Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) → ∃ a₁ a₂ : AE D, finPart D a₁ ∈ intAE D ∧ finPart D a₂ ∈ intAE D ∧ 1 - e - cA D e = a₁ * incA D (c : D.host.E) + a₂ * incA D (d : D.host.E) := by
  intro D e SS he c hc d hd hcd
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨hzero, hoint⟩ := off_comp hΦ he
  generalize 1 - e - cA D e = o at hzero hoint ⊢
  have hc0 : (c : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_split (c : 𝓞 D.host.E) d hc0 hd
  have hcast : ((c : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) := map_natCast _ c
  rw [hcast] at hxy hx
  refine ⟨o * incA D ((x : D.host.E) / c), o * incA D ((y : D.host.E) / d),
    term_int hΦ o hoint _ fun Q => ?_, term_int hΦ o hoint _ fun Q => ?_, ?_⟩
  · by_cases h : (c : 𝓞 D.host.E) ∈ Q.asIdeal ∧ d ∈ Q.asIdeal
    · exact Or.inl (hzero Q (hcd Q h.1 h.2))
    · exact Or.inr (hx Q h)
  · by_cases h : (c : 𝓞 D.host.E) ∈ Q.asIdeal ∧ d ∈ Q.asIdeal
    · exact Or.inl (hzero Q (hcd Q h.1 h.2))
    · exact Or.inr (hy Q h)
  · have h1 := congrArg (incA D) hxy
    rw [map_add, map_mul, map_mul, map_one] at h1
    rw [mul_assoc, mul_assoc, ← mul_add, h1, mul_one]

end GlobalTheory.OffIdemTwo
