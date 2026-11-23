import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLatticeOrderCoprimeIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationModuleUnitDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImaginaryGeneratorCmTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCoprimeOfTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationLatticeFgStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscriminantMulTraceDualIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeIntegerInIdealStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex

namespace GlobalTheory.PolarisationModuleProof

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gen_mul {L : Submodule (OF E) E} {l : ℕ} {ξ : E} (h : GenAt l (polMod L) ξ) :
    ∀ z ∈ polMod L * L, ∃ n : ℕ, n.Coprime l ∧ (n : E) * z ∈ mulLat ξ L := by
  intro z hz
  induction hz using Submodule.mul_induction_on' with
  | mem_mul_mem η hη x hx =>
    obtain ⟨n, hn, a, ha⟩ := h.2 η hη
    refine ⟨n, hn, Submodule.mem_map.2 ⟨a • x, L.smul_mem a hx, ?_⟩⟩
    rw [LinearMap.mulLeft_apply, Algebra.smul_def, ← mul_assoc, mul_comm ξ, ← ha]; ring
  | add z1 _ z2 _ h1 h2 =>
    obtain ⟨n1, hn1, h1⟩ := h1
    obtain ⟨n2, hn2, h2⟩ := h2
    refine ⟨n1 * n2, Nat.Coprime.mul hn1 hn2, ?_⟩
    have e : ((n1 * n2 : ℕ) : E) * (z1 + z2) = (n2 : OF E) • ((n1 : E) * z1) + (n1 : OF E) • ((n2 : E) * z2) := by
      rw [Algebra.smul_def, Algebra.smul_def]; push_cast; ring
    rw [e]
    exact add_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

theorem trInt_of_isIntegral {x : E} (hx : IsIntegral ℤ x) : TrInt x := by
  have h := Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := E) hx
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by rw [← hn]; simp⟩

theorem isIntegral_of_mem_orderC {c : Ideal (OF E)} {x : E} (hx : x ∈ orderC c) : IsIntegral ℤ x := by
  obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
  refine IsIntegral.add ?_ ?_
  · exact (algebraMap (OF E) (𝓞 E) a).2
  · exact b.2

theorem invertible_of_isUnit {M : Submodule (OF E) E} (hU : IsUnit M) : Module.Invertible (OF E) M := by
  have h : Module.Invertible (OF E) ↥(↑hU.unit : Submodule (OF E) E) := inferInstance
  rwa [hU.unit_spec] at h

theorem sandwich_latMod {c : Ideal (OF E)} (hc : c ≠ ⊥) (y : (Af E)ˣ) :
    ∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ latMod c y) ∧
      ∀ x ∈ latMod c y, IsIntegral ℤ ((N : E) * x) :=
  GlobalTheory.T.exists_denominator_of_adelic_lattice E c hc y

theorem modulePart {I : Type} (φ : I → E →+* ℂ) (hφ : IsCMType φ) (e₀ : ℤˣ) : ModulePart φ e₀ := by
  intro c hc y
  obtain ⟨N, hN, hO, hint⟩ := sandwich_latMod hc y
  obtain ⟨hU, hEq⟩ := GlobalTheory.T.polarization_module_unit_dual E (latMod c y) ⟨N, hN, hO, hint⟩
  have hanti : ∀ ξ ∈ polMod (latMod c y), IsCMField.complexConj E ξ = -ξ := fun ξ h => h.1
  have hFG : (dualLat (latMod c y)).toAddSubgroup.FG := hEq ▸ GlobalTheory.T.polarization_lattice_fg E (latMod c y) ⟨N, hN, hint⟩ hU
  refine ⟨invertible_of_isUnit hU, hEq, ?_, fun l hl => ⟨?_, fun ξ hξ hg => ?_⟩⟩
  · obtain ⟨ξ, hξ, hpos, -⟩ := GlobalTheory.T.exists_imaginary_generator_cm_type E (polMod (latMod c y)) hU hanti I φ hφ e₀ 2 Nat.prime_two
    exact ⟨ξ, hξ, hpos⟩
  · obtain ⟨ξ, hξ, hpos, hg⟩ := GlobalTheory.T.exists_imaginary_generator_cm_type E (polMod (latMod c y)) hU hanti I φ hφ e₀ l hl
    exact ⟨ξ, ⟨hξ, hpos⟩, hξ, hg⟩
  · have hle : mulLat ξ (latMod c y) ≤ dualLat (latMod c y) := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hz
      exact polMod_mul_le _ (Submodule.mul_mem_mul hg.1 hx)
    have h5 := GlobalTheory.T.relIndex_coprime_of_torsion (mulLat ξ (latMod c y)).toAddSubgroup (dualLat (latMod c y)).toAddSubgroup l hl hle hFG
      (fun z hz => by
        obtain ⟨n, hn, h⟩ := gen_mul hg z (hEq ▸ hz)
        exact ⟨n, hn, by rw [nsmul_eq_mul]; exact h⟩)
    exact ⟨hle, h5.1, h5.2⟩

theorem sizePart {I : Type} (φ : I → E →+* ℂ) (hφ : IsCMType φ) (e₀ : ℤˣ) : SizePart φ e₀ := by
  intro 𝔣 Q h𝔣 hQ l hl hQl y hy ξ hξ hg
  have hc : condQ 𝔣 Q ≠ ⊥ := by
    have : (𝔣 * ∏ q ∈ Q, q.asIdeal) ≠ 0 :=
      mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
    exact this
  obtain ⟨n, hn, hLO, hOL⟩ := GlobalTheory.T.adelic_lattice_order_coprime_index E (condQ 𝔣 Q) hc l hl y hy
  obtain ⟨N, hN, hO, hint⟩ := sandwich_latMod hc y
  obtain ⟨hU, hEq⟩ := GlobalTheory.T.polarization_module_unit_dual E (latMod (condQ 𝔣 Q) y) ⟨N, hN, hO, hint⟩
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨i, -, -⟩ := hφ σ
    have := hξ.2 i
    simp at this
  have hn1 : (n : E) ∈ dualLat (latMod (condQ 𝔣 Q) y) := by
    intro x hx
    have h1 := isIntegral_of_mem_orderC (hLO x hx)
    apply trInt_of_isIntegral
    have : (n : E) * bar x = bar ((n : E) * x) := by simp [bar]
    rw [this]
    exact map_isIntegral_int (IsCMField.complexConj E) h1
  rw [← hEq] at hn1
  obtain ⟨n', hn', hm⟩ := gen_mul hg _ hn1
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 hm
  rw [LinearMap.mulLeft_apply] at hxe
  have hxi : IsIntegral ℤ ((n : E) * x) := isIntegral_of_mem_orderC (hLO x hx)
  have key : ((n' * n * n : ℕ) : E) * ξ⁻¹ = (n : E) * x := by
    have hx' : x = ((n' : E) * n) * ξ⁻¹ := by
      rw [← hxe, mul_comm ξ, mul_assoc, mul_inv_cancel₀ hξ0, mul_one]
    rw [hx']; push_cast; ring
  have hinv : ∀ σ : E →+* ℂ, IntAt l (σ ξ)⁻¹ := fun σ => ⟨n' * n * n,
    Nat.Coprime.mul (Nat.Coprime.mul hn' hn) hn, by
      rw [← map_inv₀, ← map_natCast σ, ← map_mul, key]; exact map_isIntegral_int σ hxi⟩
  refine ⟨hξ0, hinv, fun hdisc h𝔣l σ => ?_⟩
  have hcl : ∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ condQ 𝔣 Q → (l : OF E) ∉ v.asIdeal := by
    intro v hv
    rcases v.prime.dvd_or_dvd hv with h | h
    · exact h𝔣l v h
    · obtain ⟨q, hq, hvq⟩ := (Prime.dvd_finset_prod_iff v.prime _).1 h
      have : v.asIdeal = q.asIdeal :=
        ((q.isMaximal).eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd hvq)).symm
      rw [this]; exact hQl q hq
  obtain ⟨m, hm, hmc⟩ := GlobalTheory.T.exists_coprime_integer_in_ideal (maximalRealSubfield E) (condQ 𝔣 Q) l hl hc hcl
  have hmO : ∀ b : 𝓞 E, (m : E) * algebraMap (𝓞 E) E b ∈ orderC (condQ 𝔣 Q) := by
    intro b
    refine mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) m * b,
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hmc), ?_⟩
    simp
  have hξL : ∀ b : 𝓞 E, ((n : E) * m) * algebraMap (𝓞 E) E b ∈ latMod (condQ 𝔣 Q) y := by
    intro b
    have := hOL _ (hmO b)
    rwa [← mul_assoc] at this
  have htr : ∀ b : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E ((((n : E) * m) ^ 2 * ξ) * algebraMap (𝓞 E) E b) = k := by
    intro b
    obtain ⟨k, hk⟩ := hξ.1.2 _ (hξL b) _ (by simpa using hξL 1)
    refine ⟨k, ?_⟩
    rw [← hk]
    congr 1
    simp [bar]
    ring
  have h7 := GlobalTheory.T.discriminant_mul_trace_dual_integral E _ htr
  have h7' : IsIntegral ℤ (((discr E).natAbs : E) * (((n : E) * m) ^ 2 * ξ)) := by
    have hcast : ((discr E).natAbs : E) = (((discr E).natAbs : ℤ) : E) := (Int.cast_natCast _).symm
    rw [hcast, Int.natCast_natAbs]
    rcases abs_choice (discr E) with h | h <;> rw [h]
    · exact h7
    · push_cast; rw [neg_mul]; exact h7.neg
  refine ⟨(map_ne_zero σ).2 hξ0, ⟨(discr E).natAbs * (n * m) ^ 2, ?_, ?_⟩, hinv σ⟩
  · refine Nat.Coprime.mul ?_ (Nat.Coprime.pow_left 2 (Nat.Coprime.mul hn hm))
    exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 fun h => hdisc (Int.natCast_dvd.2 h))
  · have : (((discr E).natAbs * (n * m) ^ 2 : ℕ) : ℂ) * σ ξ = σ (((discr E).natAbs : E) * (((n : E) * m) ^ 2 * ξ)) := by
      rw [map_mul, map_mul, map_pow, map_mul]; simp only [map_natCast]; push_cast; ring
    rw [this]
    exact map_isIntegral_int σ h7'

theorem polarisationModule : PolarisationModule :=
  fun _ _ _ _ _ _ φ hφ e₀ => ⟨modulePart φ hφ e₀, sizePart φ hφ e₀⟩

end GlobalTheory.PolarisationModuleProof
