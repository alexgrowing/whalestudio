import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.CobSwap

theorem hasSubst_swapVars {R : Type} [CommRing R] {d : ℕ} :
    HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inl i))) :=
  hasSubst_of_constantCoeff_zero fun j => by cases j <;> simp

theorem swap_map {B Q : Type} [CommRing B] [CommRing Q] (h : B →+* Q) {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) B) : swap (map h c) = map h (swap c) := by
  unfold swap at2
  rw [map_subst hasSubst_swapVars]
  congr 1
  funext j
  cases j <;> simp

theorem swap_subst {R : Type} [CommRing R] {d : ℕ} (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hν : ∀ i, constantCoeff (ν i) = 0) (f : MvPowerSeries (Fin d) R) :
    swap (subst ν f) = subst (fun i => swap (ν i)) f := by
  unfold swap at2
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hν) hasSubst_swapVars]

theorem swap_inL {R : Type} [CommRing R] {d : ℕ} (f : MvPowerSeries (Fin d) R) :
    swap (inL f) = inR f := by
  unfold swap at2 inL inR
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    hasSubst_swapVars]
  congr 1
  funext i
  rw [subst_X hasSubst_swapVars]
  rfl

theorem swap_inR {R : Type} [CommRing R] {d : ℕ} (f : MvPowerSeries (Fin d) R) :
    swap (inR f) = inL f := by
  unfold swap at2 inL inR
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    hasSubst_swapVars]
  congr 1
  funext i
  rw [subst_X hasSubst_swapVars]
  rfl

theorem swap_sub {R : Type} [CommRing R] {d : ℕ} (a b : MvPowerSeries (Fin d ⊕ Fin d) R) :
    swap (a - b) = swap a - swap b := by
  unfold swap at2
  exact subst_sub hasSubst_swapVars a b

theorem swap_cob1_eq_of_swap_eq : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) →
    (∀ i, swap (μ i) = μ i) → ∀ g : MvPowerSeries (Fin d) Q,
    swap (cob1 (up Q μ) g) = cob1 (up Q μ) g := by
  intro B Q _ _ _ d μ h0 hs g
  have h0' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, h0 i]
  have hs' : ∀ i, swap (up Q μ i) = up Q μ i := fun i => by
    simp only [up]; rw [swap_map, hs i]
  unfold cob1
  rw [swap_sub, swap_sub, swap_subst _ h0', swap_inL, swap_inR]
  simp only [hs']
  abel

end GlobalTheory.CobSwap
