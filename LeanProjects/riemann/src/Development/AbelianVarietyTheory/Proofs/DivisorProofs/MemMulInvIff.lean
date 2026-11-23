import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid.StairConj

theorem mem_mul_inv_iff {E : Type} [Field E] [NumberField E] (c : E → E) (hc : ∀ x, c (c x) = x)
    (hm : ∀ x y, c (x * y) = c x * c y) {A A' B B' : FractionalIdeal (𝓞 E)⁰ E} (hB : B ≠ 0) (hB' : B' ≠ 0)
    (hA : ∀ x, x ∈ A' ↔ c x ∈ A) (hBB : ∀ x, x ∈ B' ↔ c x ∈ B) (x : E) :
    x ∈ A' * B'⁻¹ ↔ c x ∈ A * B⁻¹ := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hB,
    FractionalIdeal.mem_div_iff_of_ne_zero hB']
  constructor
  · intro h y hy
    have h1 := (hA _).1 (h (c y) ((hBB _).2 (by rwa [hc])))
    rwa [hm, hc] at h1
  · intro h y hy
    rw [hA, hm]
    exact h _ ((hBB _).1 hy)

theorem mem_coe_iff (D : D7) (I : Ideal (𝓞 D.host.E)) (x : D.host.E) :
    x ∈ (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ↔
      D.host.conj x ∈ ((D.host.conj • I : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  rw [FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨D.host.conj • z, Ideal.smul_mem_pointwise_smul _ _ _ hz, rfl⟩
  · rintro ⟨z, hz, h⟩
    refine ⟨D.host.conj⁻¹ • z, Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hz, ?_⟩
    rw [Formalism.L2.Pj.algebraMap_gal_smul, Formalism.L2.Pj.conj_inv_apply, h, Formalism.L2.Pj.conj_conj]

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero (Formalism.L2.Pj.bB_ne D).1)
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  intro h
  exact D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)

theorem conj_AA_and_stA : ∀ (D : D7), (D.host.AA ≠ 0 ∧ ∀ x, x ∈ D.host.AAbar ↔ star x ∈ D.host.AA) ∧ ∀ (T : Type) (L : LevCh D T) (P : Places L) (sc : Consts), P.stA sc ≠ 0 ∧ ∀ x, x ∈ P.stAbar sc ↔ star x ∈ P.stA sc := by
  intro D
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have hA : ∀ x, x ∈ D.host.AAbar ↔ D.host.conj x ∈ D.host.AA := fun x =>
    ⟨Formalism.L2.Pj.conj_mem_AA D, fun ha => by
      simpa only [Formalism.L2.Pj.conj_conj] using Formalism.L2.Pj.conj_mem_AAbar D ha⟩
  refine ⟨⟨AA_ne_zero D, fun x => by rw [hs]; exact hA x⟩, fun T L P sc => ?_⟩
  have h1 : ((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact P.modul_ne_bot sc
  have h2 : ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h
    apply h1
    rw [FractionalIdeal.eq_zero_iff] at h ⊢
    intro x hx
    have := h _ ((mem_coe_iff D _ x).1 hx)
    exact (map_eq_zero _).1 this
  refine ⟨mul_ne_zero (AA_ne_zero D) (inv_ne_zero h2), fun x => ?_⟩
  rw [hs]
  exact mem_mul_inv_iff D.host.conj (Formalism.L2.Pj.conj_conj D) (map_mul _) h2 h1 hA (mem_coe_iff D _) x

end GlobalTheory.ChiGrid.StairConj
