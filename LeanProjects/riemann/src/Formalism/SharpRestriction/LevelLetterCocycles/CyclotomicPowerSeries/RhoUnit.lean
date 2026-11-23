import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

private theorem constantCoeff_algHom_C_eq_algebraMap {O S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (ρ : PowerSeries O →ₐ[O] PowerSeries S) (c : O) :
    constantCoeff (ρ (C c)) = algebraMap O S c := by
  first
  | (have e : (C c : PowerSeries O) = c • (1 : PowerSeries O) := by
       rw [PowerSeries.smul_eq_C_mul, mul_one]
     rw [e, map_smul, map_one, ← algebraMap_smul S c (1 : PowerSeries S),
       PowerSeries.smul_eq_C_mul, mul_one, PowerSeries.constantCoeff_C])
  | (have e : (C c : PowerSeries O) = algebraMap O (PowerSeries O) c := by
       first
       | rfl
       | simp [PowerSeries.algebraMap_eq]
       | exact (PowerSeries.algebraMap_apply' c).symm
     rw [e, ρ.commutes]
     first
     | simp
     | (rw [IsScalarTower.algebraMap_apply O S (PowerSeries S)]; simp)
     | simp [PowerSeries.algebraMap_apply'])

private theorem isUnit_of_isUnit_constantCoeff {S : Type} [CommRing S] {f : PowerSeries S}
    (h : IsUnit (constantCoeff f)) : IsUnit f := by
  first
  | exact PowerSeries.isUnit_iff_constantCoeff.mpr h
  | (obtain ⟨u, hu⟩ := h
     exact isUnit_of_mul_eq_one _ _ (PowerSeries.mul_invOfUnit f u hu.symm))

theorem rhoUnit : RhoUnitStatement := by
  unfold RhoUnitStatement
  intro O S _ _ _ ρ p a c hp hc hmem
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hmem
  have h2 : constantCoeff (ρ v) * constantCoeff (ρ a) = algebraMap O S c := by
    rw [← constantCoeff_algHom_C_eq_algebraMap ρ c, ← huv]
    simp only [map_add, map_mul, hp, mul_zero, zero_add]
  rw [← h2] at hc
  exact isUnit_of_isUnit_constantCoeff (IsUnit.mul_iff.mp hc).2

end LevelStatements.Lv
