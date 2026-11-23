import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElementStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem mem_FilD_iff_xi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ ∃ y : Per.BdRp l, x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ (-a).toNat = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e) ^ a.toNat * y) := by
  intro l _ e he a x
  have h := (GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he).1
  have hg : ∀ (n : ℕ) (x : Per.BdR l), x ∈ Per.FilD l (-(n : ℤ)) ↔ ∃ y : Per.BdRp l,
      x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ n = algebraMap (Per.BdRp l) (Per.BdR l) y :=
    GlobalTheory.CrisLoc.mem_fil_neg l _ (GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he)
  generalize aDp l (xi e) = ξ at h hg ⊢
  have hn : ∀ (n : ℕ) (w : Per.BdR l), w ∈ Per.FilD l (n : ℤ) ↔
      ∃ y : Per.BdRp l, w = algebraMap (Per.BdRp l) (Per.BdR l) (ξ ^ n * y) := by
    intro n w
    constructor
    · intro hw
      obtain ⟨z, hz, ez⟩ := GlobalTheory.RingIface.exists_of_mem_FilD_nat l hw
      obtain ⟨y, rfl⟩ := (h _ _).1 hz
      exact ⟨y, ez.symm⟩
    · rintro ⟨y, rfl⟩
      exact GlobalTheory.RingIface.alg_mem_FilD_nat l ((h _ _).2 (dvd_mul_right _ _))
  rcases le_total 0 a with ha | ha
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    rw [hn, Int.toNat_neg_natCast, Int.toNat_natCast, pow_zero, mul_one]
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat ha
    rw [hg, neg_neg, Int.toNat_neg_natCast, Int.toNat_natCast]
    simp only [pow_zero, one_mul]

end GlobalTheory.MemLoc
