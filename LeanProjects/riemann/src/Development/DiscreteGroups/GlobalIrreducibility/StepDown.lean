import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.StepUp

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in
theorem step_down (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) {n : ℕ}
    (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (φ : τ →ₗ[ℂ] V)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g n κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) (φ x))
    (L : Module.Dual ℂ V) (hL : IsFunctional ψ π L) (x : τ) (d : Fin n → ℤ) (a b : Fin n)
    (hb : b.val = a.val + 1) (hd : d b < d a) :
    L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) = 0 := by
  classical
  have hS := DzLc.sum_unip_eq_zero τ hτ (Nat.succ_pos a.val) (by have := b.isLt; omega)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d a = d b + ((k + 1 : ℕ) : ℤ) := ⟨(d a - d b - 1).toNat, by omega⟩
  have hterm : ∀ u ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n (a.val + 1)),
      L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ (τ.ρ u x))) =
        L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) := by
    intro u hu
    obtain ⟨κ, hκ, hmem⟩ := DzLc.exists_lift i u hu
    rw [← hκ, hφ]
    have hU := unipRadical_le_unipB hmem
    rw [← rep_conj π _ _ (φ x), hL _ (by rw [Iwasawa.torusPow]; exact conj_mem_unipB _ hU)]
    rw [psi_eq_one i hi hψ, Circle.coe_one, one_mul]
    rw [Iwasawa.torusPow, superDiag_conj]
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q hq => ?_
    have hq' : q.val = p.val + 1 := (Finset.mem_filter.1 hq).2
    have hent : ∀ r s : Fin n, valuation (w.adicCompletion E)
        ((Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) r s) ≤ 1 :=
      fun r s => (DzIso.valuation_le_iff i hi _).2 (κ r s).2
    by_cases hp : p = a
    · have hqb : q = b := Fin.ext (by rw [hq', hb, hp])
      rw [hp, hqb, torus_entry' d a b k hk]
      exact val_uniformizer_pow_lt k (hent a b)
    · have hpa : p.val ≠ a.val := fun h => hp (Fin.ext h)
      have h0 : (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
          p q = 0 := by
        have := (GlobalTheory.FiniteGL.mem_unipRadical.1 hmem) p q (by
          simp only [GlobalTheory.FiniteGL.twoBlocks]; split_ifs <;> omega)
        rwa [Matrix.sub_apply, Matrix.one_apply_ne (fun h => by rw [h] at hq'; omega), sub_zero] at this
      rw [h0]; simp
  have h3 := congrArg (fun F : Module.End ℂ τ => L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ (F x)))) hS
  simp only [LinearMap.sum_apply, map_sum, LinearMap.zero_apply, map_zero] at h3
  rw [Finset.sum_congr rfl
    (fun (u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n (a.val + 1))) _ => hterm u.1 u.2), Finset.sum_const, Finset.card_univ, smul_eq_zero] at h3
  exact h3.resolve_left Fintype.card_ne_zero

end DiscreteGroups.sglob.DzRed
