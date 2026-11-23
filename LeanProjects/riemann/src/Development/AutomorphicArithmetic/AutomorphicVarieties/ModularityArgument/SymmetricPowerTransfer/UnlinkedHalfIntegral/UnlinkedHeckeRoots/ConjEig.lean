import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC

open UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Unl

theorem conjEig : ConjEig := by
  intro k N χ g hg σ
  obtain ⟨f', h1, h2⟩ := hg σ
  refine ⟨⟨f', h1, ?_, ?_⟩, fun n hn => h2 n hn⟩
  · rw [h2 1 le_rfl, g.one, map_one]
  · intro p hp n hn
    have e := congrArg σ (g.eig p hp n hn)
    have hc : (cj σ χ) (p : ZMod N) = σ (χ p) := rfl
    show coef f' (p * n) + (cj σ χ) p * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then coef f' (n / p) else 0) = coef f' p * coef f' n
    rw [h2 _ (Nat.mul_pos hp.pos hn), h2 _ hp.pos, h2 _ hn, hc]
    by_cases hd : p ∣ n
    · have hm : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hd) hp.pos
      simp only [hd, if_true] at e ⊢
      rw [h2 _ hm]
      simpa [map_add, map_mul, map_pow, map_natCast] using e
    · simp only [hd, if_false] at e ⊢
      simpa [map_add, map_mul, map_pow, map_natCast] using e

end UpperTheory.V.Z.Sym.Unl
