import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open TensorProduct Formalism.UG Formalism.UG.P

namespace GlobalTheory.OpenChrRam

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inv_natCast_mem (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (hN : (N : 𝓞 F) ∉ v.asIdeal) :
    (N : v.adicCompletion F) ≠ 0 ∧ (N : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : Valued.v (N : v.adicCompletion F) = 1 := by
    have e : (N : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F) := by simp
    have e2 : v.valuation F (algebraMap (𝓞 F) F (N : 𝓞 F)) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hN
    rw [← e2, ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact congrArg _ e
  refine ⟨fun h => by rw [h] at h1; simp at h1, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem inertAt_le_congN (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (hN : (N : 𝓞 F) ∉ v.asIdeal) :
    inertAt E v ≤ congN F E N := by
  rintro x ⟨⟨hx, hx'⟩, hs⟩
  obtain ⟨hN0, hNi⟩ := inv_natCast_mem v N hN
  let u : (RInt F E)ˣ := ⟨⟨x, hx⟩, ⟨(x⁻¹ : (AfE F E)ˣ), hx'⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩
  refine ⟨u, ?_, Units.ext rfl⟩
  have hn : (1 : E) ⊗ₜ[F] afsplitI v (N : v.adicCompletion F)⁻¹ ∈ RInt F E :=
    Subring.subset_closure (Or.inr ⟨⟨_, afsplitI_mem_intAd v _ hNi⟩, rfl⟩)
  refine (mem_kerRed _ u).2 (Ideal.mem_span_singleton'.2 ⟨⟨_, hn⟩ * ((u : RInt F E) - 1), ?_⟩)
  apply Subtype.ext
  show (1 : E) ⊗ₜ[F] afsplitI v (N : v.adicCompletion F)⁻¹ * ((x : AfE F E) - 1) * ((N : RInt F E) : AfE F E)
    = (x : AfE F E) - 1
  rw [SubringClass.coe_natCast, ← sub_eq_zero]
  refine afsplit_inj _ fun w => ?_
  rw [map_sub, map_mul, map_mul, afsplit_prV_tmul, map_natCast]
  by_cases h : w = v
  · subst h
    rw [afsplitI_self, mul_right_comm]
    have : (1 : E) ⊗ₜ[F] (N : w.adicCompletion F)⁻¹ * (N : E ⊗[F] w.adicCompletion F) = 1 := by
      have e : (N : E ⊗[F] w.adicCompletion F) = (1 : E) ⊗ₜ[F] (N : w.adicCompletion F) :=
        (map_natCast (Algebra.TensorProduct.includeRight :
          w.adicCompletion F →ₐ[F] E ⊗[F] w.adicCompletion F) N).symm
      rw [e, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hN0, one_mul]
      rfl
    rw [this, one_mul, sub_self]
  · have hw : prV (E := E) w (x : AfE F E) = 1 := by
      have h1 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hs w) h
      exact congrArg Units.val (MonoidHom.mem_ker.1 h1)
    rw [map_sub, hw, map_one, sub_self, mul_zero, zero_mul, sub_self]

theorem qprime_finite (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (L : Type) [Field L] (ξ : Chr F E L) (h : ξ ∈ openChr F E L) : (Qprime ξ).Finite := by
  obtain ⟨N, hN, hk⟩ := h
  have hne : Ideal.span {(N : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  by_contra hc
  refine hv ((inertAt_le_congN v N fun hm => hc ?_).trans hk)
  exact Ideal.dvd_span_singleton.2 hm

end GlobalTheory.OpenChrRam
