import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.PairingFactorsThroughPeriods

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW

theorem lattice_reduction : LocalIsoOfLatticeIso := by
  intro hLat K E _ _ _ _ _ cj n _ I p hK hc hp hs hI hg0
  obtain ⟨g₀, hg⟩ := hg0
  set c := conjK cj hc.2.1 with hcdef
  obtain ⟨u, hu, huL⟩ := hLat K c p (Fin 4 × n) (Lset I p g₀) hK (conjK_invol cj hc) hp
    (splitK_of cj hc hs) (lset_unimod cj hc I p g₀ hI hg) (lset_spans cj hc I p g₀ hI)
  refine ⟨g₀.trans u, ?_, ?_, ?_⟩
  · intro x y
    rw [sum_conj cj hc.2.1, ← hg x y, sum_conj cj hc.2.1]
    congr 1
    exact hu (g₀ x) (g₀ y)
  · intro x hx
    have hmem : g₀ x ∈ Lset I p g₀ := ⟨1, Nat.coprime_one_left p, fun a => by
      rw [Nat.cast_one, one_mul, LinearEquiv.symm_apply_apply]; exact hx a⟩
    obtain ⟨s, hs', hsx⟩ := Rp_fintype (p := p) _ ((huL _).1 hmem)
    exact ⟨s, hs', fun w => hsx w⟩
  · intro v hv
    have hmem : u.symm v ∈ Lset I p g₀ := (huL _).2 fun i => by
      rw [LinearEquiv.apply_symm_apply]
      obtain ⟨y, hy⟩ := hv i
      exact ⟨1, Nat.coprime_one_left p, ⟨y, by rw [Nat.cast_one, one_mul]; exact hy⟩⟩
    obtain ⟨s, hs', hsv⟩ := hmem
    exact ⟨s, hs', fun a => hsv a⟩

end PI.KLW
