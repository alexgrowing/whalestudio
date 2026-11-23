import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedAbsValueLocalFieldUnitMapHomeomorph
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalFieldIso

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem continuous_symm (i : k ≃+* k') (hi : Continuous i) : Continuous i.symm := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k')
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hi
  exact (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous

variable (k) in

theorem valuation_le_one_iff_ord (x : kˣ) : valuation k (x : k) ≤ 1 ↔ 0 ≤ GlobalTheory.SmGL.ord k x := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (x : k)) ≠ 0 := by simp
  rw [GlobalTheory.SmGL.ord, neg_nonneg, ← φ.strictMono.le_iff_le, map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  simp [φ]

variable (k) in

theorem valuation_le_one_iff_nabs (x : kˣ) : valuation k (x : k) ≤ 1 ↔ GlobalTheory.SplitWeil.nabs k x ≤ 1 := by
  rw [valuation_le_one_iff_ord, GlobalTheory.LGrp.nabs_eq_zpow,
    zpow_le_one_iff_right₀ (by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k)]
  omega

theorem nabs_map (i : k ≃+* k') (hi : Continuous i) (x : kˣ) :
    GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x :=
  GlobalTheory.SplitWeil.nabs_map_of_homeomorph i hi (continuous_symm i hi) x

theorem valuation_map_le_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := valuation_le_one_iff_nabs k' (Units.map i.toRingHom.toMonoidHom (Units.mk0 x hx))
  rw [nabs_map i hi, ← valuation_le_one_iff_nabs k] at h
  simpa using h

theorem map_integer (i : k ≃+* k') (hi : Continuous i) :
    (𝒪[k] : Subring k).map i.toRingHom = 𝒪[k'] := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Valuation.mem_integer_iff _ _).2 ((valuation_map_le_one_iff i hi x).2 ((Valuation.mem_integer_iff _ _).1 hx))
  · intro hy
    refine ⟨i.symm y, (Valuation.mem_integer_iff _ _).2 ?_, i.apply_symm_apply y⟩
    rw [← valuation_map_le_one_iff i hi, RingEquiv.apply_symm_apply]
    exact (Valuation.mem_integer_iff _ _).1 hy

theorem resCard_eq (i : k ≃+* k') (hi : Continuous i) : GlobalTheory.SplitWeil.resCard k' = GlobalTheory.SplitWeil.resCard k := by
  let e : 𝒪[k] ≃+* 𝒪[k'] := (i.subringMap (s := 𝒪[k])).trans (RingEquiv.subringCongr (map_integer i hi))
  exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv).symm

theorem ord_map (i : k ≃+* k') (hi : Continuous i) (x : kˣ) :
    GlobalTheory.SmGL.ord k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SmGL.ord k x := by
  have h := nabs_map i hi x
  rw [GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, resCard_eq i hi] at h
  have hq : (1 : ℝ) < GlobalTheory.SplitWeil.resCard k := by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k
  exact neg_inj.1 (zpow_right_injective₀ (by linarith) hq.ne' h)

theorem absPow_map (i : k ≃+* k') (hi : Continuous i) (s : ℂ) (x : kˣ) :
    GlobalTheory.SmGL.absPow k' s (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SmGL.absPow k s x := by
  ext
  rw [GlobalTheory.SmGL.val_absPow, GlobalTheory.SmGL.val_absPow, nabs_map i hi]

end GlobalTheory.LocalFieldIso

theorem GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → Continuous i.symm ∧ (∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) ∧ (∀ x : kˣ, ord k' (Units.map i.toRingHom.toMonoidHom x) = ord k x) ∧ resCard k' = resCard k ∧ ∀ (s : ℂ) (x : kˣ), absPow k' s (Units.map i.toRingHom.toMonoidHom x) = absPow k s x := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi
  exact ⟨GlobalTheory.LocalFieldIso.continuous_symm i hi, GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi,
    GlobalTheory.LocalFieldIso.ord_map i hi, GlobalTheory.LocalFieldIso.resCard_eq i hi, GlobalTheory.LocalFieldIso.absPow_map i hi⟩
