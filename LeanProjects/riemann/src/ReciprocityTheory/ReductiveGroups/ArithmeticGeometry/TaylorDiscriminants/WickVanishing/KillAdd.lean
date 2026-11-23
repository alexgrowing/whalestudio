import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.KillAddQ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FoldrIterateEqTG

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

theorem exp_factor {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type} (f : MvPowerSeries σ k)
    (hf : constantCoeff f = 0) :
    ∃ Y : MvPowerSeries σ k, PowerSeries.subst f (PowerSeries.exp k) = 1 + f * Y := by
  have ha : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf

  set E : PowerSeries k := PowerSeries.mk fun n => algebraMap ℚ k (1 / ((n + 1).factorial : ℚ)) with hE
  have hexp : PowerSeries.exp k = 1 + PowerSeries.X * E := by
    ext n
    rcases n with _ | n
    · simp [PowerSeries.coeff_exp]
    · simp [PowerSeries.coeff_exp, hE, PowerSeries.coeff_succ_X_mul]
  refine ⟨PowerSeries.subst f E, ?_⟩
  rw [hexp, ← PowerSeries.coe_substAlgHom ha, map_add, map_one, map_mul,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha]

end ReciprocityTheory.ChartRestriction.G.TB.G2

namespace ReciprocityTheory.ChartRestriction.G.TB

open ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {d n : ℕ}

theorem dAdd_add (u : Fin d → k) (b : Fin n) (f g : PS k n d) : dAdd u b (f + g) = dAdd u b f + dAdd u b g := by
  simp only [dAdd, map_add, mul_add, Finset.sum_add_distrib]

theorem dAdd_C (u : Fin d → k) (b : Fin n) (a : k) : dAdd u b (C a : PS k n d) = 0 := by
  unfold dAdd
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show (C a : PS k n d) = algebraMap k (PS k n d) a from rfl, Derivation.map_algebraMap, mul_zero]

theorem dAdd_mul (u : Fin d → k) (b : Fin n) (f g : PS k n d) :
    dAdd u b (f * g) = dAdd u b f * g + f * dAdd u b g := by
  unfold dAdd
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

theorem killAdd_of (hQ : QuadColDerivSt) : KillAddSt := by
  intro k _ _ d n ι _ u β P hP m g
  obtain ⟨h0, h1, h2⟩ := hQ k d n β
  obtain ⟨Y, hY⟩ := exp_factor (m • quadCol (n := n) β) (by simp [h0])
  have key := Gen.kill_gen (D := fun p : ι × Fin n => dAdd (u p.1) p.2) (κ := (C : k →+* PS k n d))
    (fun l f g => dAdd_add (u l.1) l.2 f g) (fun l a => dAdd_C (u l.1) l.2 a)
    (fun l f g => dAdd_mul (u l.1) l.2 f g) constantCoeff (fun a => by simp)
    (fun p p' : ι × Fin n => if p.2 = p'.2 then
      dotProduct (u p.1) (β.mulVec (u p'.1)) + dotProduct (u p'.1) (β.mulVec (u p.1)) else 0)
    (quadCol (n := n) β)
    (fun l l' => by
      by_cases h : l.2 = l'.2
      · rw [if_pos h, if_pos h.symm, add_comm]
      · rw [if_neg h, if_neg (Ne.symm h)])
    h0 (fun l => h1 (u l.1) l.2) (fun l l' => h2 (u l.1) (u l'.1) l.2 l'.2) P hP g (m • Y)
  have e : FB.expS k (m • quadCol (n := n) β) * g = g * (1 + quadCol (n := n) β * (m • Y)) := by
    rw [FB.expS, hY, mul_comm, smul_mul_assoc, mul_smul_comm]
  rw [e]
  exact key

end ReciprocityTheory.ChartRestriction.G.TB
