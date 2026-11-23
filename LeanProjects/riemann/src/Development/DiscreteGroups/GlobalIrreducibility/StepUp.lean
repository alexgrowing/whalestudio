import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.ValUniformizerPowLt

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in
theorem step_up (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1) {n : ℕ}
    (τ : FDRep ℂ (Gn g n)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (φ : τ →ₗ[ℂ] V)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g n κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) (φ x))
    (L : Module.Dual ℂ V) (hL : IsFunctional ψ π L) (x : τ) (d : Fin n → ℤ) (a b : Fin n)
    (hb : b.val = a.val + 1) (hd : d a < d b) :
    L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) = 0 := by
  obtain ⟨x0, hx0⟩ := exists_psi_ne_one i hψ h0
  have hab : a ≠ b := fun h => by rw [h] at hb; omega
  have hlt : a < b := by rw [Fin.lt_def]; omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d b = d a + ((k + 1 : ℕ) : ℤ) := ⟨(d b - d a - 1).toNat, by omega⟩
  have hyv : valuation (w.adicCompletion E) (i (x0 : ℚ_[g])) ≤ 1 := (DzIso.valuation_le_iff i hi _).2 x0.2
  set c : w.adicCompletion E := (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ^ (k + 1) *
    i (x0 : ℚ_[g]) with hc_def
  have hcv : valuation (w.adicCompletion E) c < 1 := val_uniformizer_pow_lt k hyv
  have hmem : tv a b hab c ∈ KOne (w.adicCompletion E) (Fin n) := by
    rw [GlobalTheory.StepData.mem_KOne]
    intro p q
    show valuation (w.adicCompletion E) (((tv a b hab c : Matrix (Fin n) (Fin n) (w.adicCompletion E)) - 1) p q) < 1
    rw [Matrix.sub_apply, tv_apply, add_sub_cancel_left]
    split_ifs
    · exact hcv
    · simp
  have hconj : Iwasawa.torusPow (w.adicCompletion E) n d * tv a b hab c *
      (Iwasawa.torusPow (w.adicCompletion E) n d)⁻¹ = tv a b hab (i (x0 : ℚ_[g])) := by
    rw [Iwasawa.torusPow, conj_tv, hc_def, torus_entry d a b k hk]
  have key := hL _ (tv_mem_unipB a b hlt (i (x0 : ℚ_[g]))) (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x))
  rw [superDiag_tv a b hb] at key
  rw [← hconj, rep_conj, fix_of_mem_KOne i hi τ π φ hφ hmem] at key
  have hne : (ψ (i (x0 : ℚ_[g])) : ℂ) ≠ 1 := fun h => hx0 (Circle.ext (by simpa using h))
  have h2 : (1 - (ψ (i (x0 : ℚ_[g])) : ℂ)) * L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) = 0 := by
    rw [sub_mul, one_mul]; exact sub_eq_zero.2 key
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne.symm)

end DiscreteGroups.sglob.DzRed
