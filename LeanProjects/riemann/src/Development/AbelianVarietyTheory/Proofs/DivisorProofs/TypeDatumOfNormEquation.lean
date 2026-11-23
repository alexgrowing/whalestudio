import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeDatumRefactor

variable {E : Type} [Field E] [NumberField E] [StarRing E]

noncomputable def cjEquiv (E : Type) [Field E] [NumberField E] [StarRing E] : 𝓞 E ≃+* 𝓞 E :=
  RingEquiv.ofRingHom (SumWCompare.cj E) (SumWCompare.cj E) (RingHom.ext SumWCompare.cj_cj) (RingHom.ext SumWCompare.cj_cj)

theorem mul_cj {g : ℕ} {p : 𝓞 E} (hn : (p : E) * star (p : E) = (g : E)) : p * SumWCompare.cj E p = (g : 𝓞 E) :=
  RingOfIntegers.ext (by simpa [SumWCompare.cj_coe] using hn)

theorem key_of_mem {gp : Fin 2 → ℕ} {pb : Fin 2 → 𝓞 E} (h : IsTypeDatum gp pb) (i : Fin 2) (w : Pl E)
    (hw : pb i ∈ w.asIdeal) : Nat.card (kP w) = gp i ∧ ((gp i : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  refine ⟨h.deg1 i w hw, fun hg => ?_⟩
  rw [← mul_cj (h.norm i), mul_comm] at hg
  have := w.isPrime
  rcases Ideal.IsPrime.mul_mem_pow w.asIdeal hg with h1 | h1
  · exact h.split i w hw _ (SumWCompare.cj_coe _) h1
  · exact h.unram i w hw h1

theorem key {gp : Fin 2 → ℕ} {pb : Fin 2 → 𝓞 E} (h : IsTypeDatum gp pb) (i : Fin 2) (w : Pl E)
    (hw : ((gp i : ℕ) : 𝓞 E) ∈ w.asIdeal) : Nat.card (kP w) = gp i ∧ ((gp i : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  rw [← mul_cj (h.norm i)] at hw
  rcases w.isPrime.mem_or_mem hw with h1 | h1
  · exact key_of_mem h i w h1
  · have := w.isPrime
    have hmap : (w.asIdeal.comap (SumWCompare.cj E)).map (cjEquiv E : 𝓞 E →+* 𝓞 E) = w.asIdeal :=
      Ideal.map_comap_of_surjective (SumWCompare.cj E) (cjEquiv E).surjective _
    let w' : Pl E := ⟨w.asIdeal.comap (SumWCompare.cj E), Ideal.comap_isPrime _ _, fun h0 => by
      rw [h0, Ideal.map_bot] at hmap
      exact w.ne_bot hmap.symm⟩
    obtain ⟨h2, h3⟩ := key_of_mem h i w' h1
    refine ⟨?_, fun hg => h3 ?_⟩
    · rw [← h2]
      exact (Nat.card_congr (Ideal.quotientEquiv w'.asIdeal w.asIdeal (cjEquiv E) hmap.symm).toEquiv).symm
    · have h4 := Ideal.mem_map_of_mem (SumWCompare.cj E) hg
      rw [map_natCast, Ideal.map_pow] at h4
      refine Ideal.pow_right_mono ?_ 2 h4
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change SumWCompare.cj E (SumWCompare.cj E x) ∈ w.asIdeal
      rwa [SumWCompare.cj_cj]

theorem isTypeDatum_of_norm : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (gp : Fin 2 → ℕ) (pb π : Fin 2 → 𝓞 E), IsTypeDatum gp pb → (∀ i, (π i : E) * star (π i : E) = (gp i : E)) → IsTypeDatum gp π := by
  intro E _ _ _ gp pb π h hn
  have hg : ∀ i (w : Pl E), π i ∈ w.asIdeal → ((gp i : ℕ) : 𝓞 E) ∈ w.asIdeal := fun i w hw => by
    rw [← mul_cj (hn i)]; exact w.asIdeal.mul_mem_right _ hw
  refine ⟨h.prime, h.ne, hn, fun i w hw => (key h i w (hg i w hw)).1, fun i w hw h2 => ?_, fun i w hw c hc h2 => ?_⟩
  · refine (key h i w (hg i w hw)).2 ?_
    rw [← mul_cj (hn i)]; exact Ideal.mul_mem_right _ _ h2
  · refine (key h i w (hg i w hw)).2 ?_
    obtain rfl : c = SumWCompare.cj E (π i) := RingOfIntegers.ext hc
    rw [← mul_cj (hn i), sq]; exact Ideal.mul_mem_mul hw h2

end GlobalTheory.TypeDatumRefactor
