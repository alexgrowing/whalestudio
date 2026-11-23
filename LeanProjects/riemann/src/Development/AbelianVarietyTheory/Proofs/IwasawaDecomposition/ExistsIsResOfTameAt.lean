import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameResidue

open Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E]

theorem locK_eq_of_congr (χ : HChar E) (P : HeightOneSpectrum (𝓞 E)) (h : χ.TameAt P)
    (a b : 𝓞 E) (k l : Eˣ) (hk : (k : E) = a) (hl : (l : E) = b) (hb : b ∉ P.asIdeal)
    (hab : a - b ∈ P.asIdeal) : χ.locK P k = χ.locK P l := by
  have ha : a ∉ P.asIdeal := fun ha => hb (by simpa using P.asIdeal.sub_mem ha hab)
  have hva : P.valuation E (k : E) = 1 := by
    rw [hk]; exact (P.valuation_eq_one_iff_notMem (K := E)).2 ha
  have hvb : P.valuation E (l : E) = 1 := by
    rw [hl]; exact (P.valuation_eq_one_iff_notMem (K := E)).2 hb
  have hvd : P.valuation E ((k : E) - l) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have e : (k : E) - l = algebraMap (𝓞 E) E (a - b) := by rw [hk, hl, map_sub]
    rw [e, HeightOneSpectrum.valuation_of_algebraMap]
    exact (P.intValuation_le_pow_iff_mem (a - b) 1).2 (by simpa using hab)
  have key : χ.locK P (k * l⁻¹) = 1 := by
    refine h (atFin P (k * l⁻¹)) ?_ ?_
    · show Valued.v ((((k * l⁻¹ : Eˣ) : E)) : P.adicCompletion E) = 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Units.val_mul, Units.val_inv_eq_inv_val, map_mul,
        map_inv₀, hva, hvb]
      simp
    · have e : ((atFin P (k * l⁻¹) : (P.adicCompletion E)ˣ) : P.adicCompletion E) - 1
          = algebraMap E (P.adicCompletion E) (((k : E) - l) * (l : E)⁻¹) := by
        have e2 : ((k : E) - l) * (l : E)⁻¹ = ((k * l⁻¹ : Eˣ) : E) - 1 := by
          rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ l.ne_zero]
        rw [e2, map_sub, map_one]
        rfl
      rw [e]
      show Valued.v (((((k : E) - l) * (l : E)⁻¹ : E)) : P.adicCompletion E) ≤ _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_mul, map_inv₀, hvb]
      simpa using hvd
  rwa [map_mul, map_inv, mul_inv_eq_one] at key

theorem exists_lift (P : HeightOneSpectrum (𝓞 E)) (u : (𝓞 E ⧸ P.asIdeal)ˣ) :
    ∃ p : 𝓞 E × Eˣ, (p.2 : E) = p.1 ∧ (u : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk _ p.1 ∧ p.1 ∉ P.asIdeal := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 E ⧸ P.asIdeal)
  haveI : Nontrivial (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have hn : a ∉ P.asIdeal := fun h => u.ne_zero (by rw [← ha]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)
  have h0 : (a : E) ≠ 0 := by
    intro h
    have : a = 0 := by exact_mod_cast h
    exact hn (this ▸ P.asIdeal.zero_mem)
  exact ⟨(a, Units.mk0 (a : E) h0), rfl, ha.symm, hn⟩

theorem exists_res (χ : HChar E) (P : HeightOneSpectrum (𝓞 E)) (h : χ.TameAt P) :
    ∃ c : (𝓞 E ⧸ P.asIdeal)ˣ →* ℂˣ, ∀ (a : 𝓞 E) (k : Eˣ) (u : (𝓞 E ⧸ P.asIdeal)ˣ), (k : E) = a →
      (u : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk _ a → c u = χ.locK P k := by
  choose f hf1 hf2 hf3 using exists_lift P
  have main : ∀ (a : 𝓞 E) (k : Eˣ) (u : (𝓞 E ⧸ P.asIdeal)ˣ), (k : E) = a →
      (u : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk _ a → χ.locK P (f u).2 = χ.locK P k := by
    intro a k u hk hu
    refine (locK_eq_of_congr χ P h a (f u).1 k (f u).2 hk (hf1 u) (hf3 u) ?_).symm
    rw [← Ideal.Quotient.eq, ← hu, ← hf2 u]
  refine ⟨MonoidHom.mk' (fun u => χ.locK P (f u).2) ?_, main⟩
  intro u v
  rw [← map_mul]
  refine main ((f u).1 * (f v).1) _ _ ?_ ?_
  · rw [Units.val_mul, hf1, hf1]; simp
  · rw [Units.val_mul, map_mul, ← hf2, ← hf2]

end GlobalTheory.TameResidue

theorem GlobalTheory.exists_isRes_of_tameAt : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (P : Pl D.host.E),
    χ.TameAt P → ∃ c, IsRes χ P c :=
  fun _ χ P h => GlobalTheory.TameResidue.exists_res χ P h
