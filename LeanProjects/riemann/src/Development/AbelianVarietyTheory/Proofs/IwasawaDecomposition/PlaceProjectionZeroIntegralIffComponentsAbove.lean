import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open Formalism.UG.P
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdComp

theorem eq_zero_of_valued_le {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (x : P.adicCompletion E) (h : ∀ n : ℕ, Valued.v x ≤ WithZero.exp (-(n : ℤ))) : x = 0 := by
  by_contra hx
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log h0).symm⟩
  have h1 := h (m.natAbs + 1)
  rw [hm, WithZero.exp_le_exp] at h1
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_eps_of_under (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) = v) : adAt F w (afsplitEps E v) = 1 := by
  have hspec : ∀ (a : FiniteAdeleRing (𝓞 F) F) (k : F) (P : HeightOneSpectrum (𝓞 E)) (n : ℕ),
      Valued.v (a (P.under (𝓞 F)) - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) ≤ WithZero.exp (-(n : ℤ)) :=
    (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    simp only [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  have h0 := eq_zero_of_valued_le w (adAt F w (afsplitEps E v) - algebraMap E _ (algebraMap F E 1))
    (fun n => by
      rw [he]
      exact hspec _ 1 w n (by rw [h, afsplitI_self, map_one, sub_self, map_zero]; exact zero_le'))
  rw [sub_eq_zero, map_one, map_one] at h0
  exact h0

theorem adAt_eps_of_ne (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) ≠ v) : adAt F w (afsplitEps E v) = 0 := by
  have hspec : ∀ (a : FiniteAdeleRing (𝓞 F) F) (k : F) (P : HeightOneSpectrum (𝓞 E)) (n : ℕ),
      Valued.v (a (P.under (𝓞 F)) - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) ≤ WithZero.exp (-(n : ℤ)) :=
    (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    simp only [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  have h0 := eq_zero_of_valued_le w (adAt F w (afsplitEps E v) - algebraMap E _ (algebraMap F E 0))
    (fun n => by
      rw [he]
      exact hspec _ 0 w n (by rw [afsplitI_ne v _ h, map_zero, sub_zero, map_zero]; exact zero_le'))
  rw [sub_eq_zero, map_zero, map_zero] at h0
  exact h0

theorem adAt_eps_mul_of_under (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) = v) (z : AfE F E) : adAt F w (afsplitEps E v * z) = adAt F w z := by
  have hm : adAt F w (afsplitEps E v * z) = adAt F w (afsplitEps E v) * adAt F w z := by
    unfold adAt; exact map_mul _ _ _
  rw [hm, adAt_eps_of_under v w h, one_mul]

theorem adAt_eps_mul_of_ne (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) ≠ v) (z : AfE F E) : adAt F w (afsplitEps E v * z) = 0 := by
  have hm : adAt F w (afsplitEps E v * z) = adAt F w (afsplitEps E v) * adAt F w z := by
    unfold adAt; exact map_mul _ _ _
  rw [hm, adAt_eps_of_ne v w h, zero_mul]

theorem prV_zero_int_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (prV (E := E) v z = 0 ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → adAt F w z = 0) ∧ (prV (E := E) v z ∈ intV E v ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → Valued.v (adAt F w z) ≤ 1) := by
  intro F E _ _ _ _ _ v z
  classical
  have hinj : ∀ x y : E ⊗[F] v.adicCompletion F, afsplitIE v x = afsplitIE v y → x = y := by
    intro x y hxy
    rw [← afsplit_prV_IE v x, hxy, afsplit_prV_IE]
  have hdec : afsplitIE v (prV (E := E) v z) = afsplitEps E v * z := afsplit_decomp v z
  have hz : ∀ w : HeightOneSpectrum (𝓞 E), adAt F w (0 : AfE F E) = 0 := by
    intro w; unfold adAt; exact map_zero _
  have hcomp : ∀ w : HeightOneSpectrum (𝓞 E),
      adAt F w (afsplitEps E v * z) = if w.under (𝓞 F) = v then adAt F w z else 0 := by
    intro w
    split_ifs with hw
    · exact adAt_eps_mul_of_under v w hw z
    · exact adAt_eps_mul_of_ne v w hw z
  refine ⟨⟨fun h0 w hw => ?_, fun h => ?_⟩, ⟨fun hint w hw => ?_, fun h => ?_⟩⟩
  · rw [← adAt_eps_mul_of_under v w hw z, ← hdec, h0, map_zero, hz]
  · apply hinj
    rw [hdec, map_zero]
    apply GlobalTheory.Mem.Col2.PtExist.ad_ext
    intro w
    rw [hcomp, hz]
    split_ifs with hw
    · exact h w hw
    · rfl
  · have h1 : afsplitEps E v * z ∈ RInt F E := by
      rw [← hdec]; exact afsplit_IE_int v _ hint
    rw [← adAt_eps_mul_of_under v w hw z]
    exact (mem_rInt_iff F E _).mp h1 w
  · have h1 : afsplitEps E v * z ∈ RInt F E := by
      rw [mem_rInt_iff]
      intro w
      change Valued.v (adAt F w (afsplitEps E v * z)) ≤ 1
      rw [hcomp]
      split_ifs with hw
      · exact h w hw
      · rw [map_zero]; exact zero_le'
    have h2 := afsplit_prV_int v _ h1
    rwa [← hdec, afsplit_prV_IE] at h2

end GlobalTheory.Mem.Col2.AdComp
