import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ConjIdeal

variable {E : Type} [Field E] [NumberField E]

theorem map_mem_mul (c : E →+* E) {A A' B B' : FractionalIdeal (𝓞 E)⁰ E}
    (hA : ∀ x ∈ A', c x ∈ A) (hB : ∀ x ∈ B', c x ∈ B) : ∀ x ∈ A' * B', c x ∈ A * B := by
  intro x hx
  refine FractionalIdeal.mul_induction_on hx (fun i hi j hj => ?_) (fun y z hy hz => ?_)
  · rw [map_mul]; exact FractionalIdeal.mul_mem_mul (hA i hi) (hB j hj)
  · rw [map_add]
    exact FractionalIdeal.mem_coe.1 (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 hy) (FractionalIdeal.mem_coe.2 hz))

theorem conj_symm (c : E →+* E) (hc : ∀ x, c (c x) = x) {I I' : FractionalIdeal (𝓞 E)⁰ E}
    (h : ∀ x, x ∈ I' ↔ c x ∈ I) : ∀ x, x ∈ I ↔ c x ∈ I' := fun x => by rw [h, hc]

theorem conj_mul (c : E →+* E) (hc : ∀ x, c (c x) = x) {A A' B B' : FractionalIdeal (𝓞 E)⁰ E}
    (hA : ∀ x, x ∈ A' ↔ c x ∈ A) (hB : ∀ x, x ∈ B' ↔ c x ∈ B) : ∀ x, x ∈ A' * B' ↔ c x ∈ A * B := by
  intro x
  refine ⟨map_mem_mul c (fun y hy => (hA y).1 hy) (fun y hy => (hB y).1 hy) x, fun h => ?_⟩
  have := map_mem_mul c (fun y hy => (conj_symm c hc hA y).1 hy) (fun y hy => (conj_symm c hc hB y).1 hy) _ h
  rwa [hc] at this

theorem conj_pow (c : E →+* E) (hc : ∀ x, c (c x) = x) (h1 : ∀ x, x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ c x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E))
    {A A' : FractionalIdeal (𝓞 E)⁰ E} (hA : ∀ x, x ∈ A' ↔ c x ∈ A) (n : ℕ) : ∀ x, x ∈ A' ^ n ↔ c x ∈ A ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact h1
  | succ n ih => simpa only [pow_succ] using conj_mul c hc ih hA

theorem conj_ne_zero (c : E →+* E) (hc : ∀ x, c (c x) = x) {B B' : FractionalIdeal (𝓞 E)⁰ E}
    (hB : ∀ x, x ∈ B' ↔ c x ∈ B) (h0 : B ≠ 0) : B' ≠ 0 := by
  intro h
  apply h0
  rw [FractionalIdeal.eq_zero_iff] at h ⊢
  intro x hx
  have := h (c x) ((hB (c x)).2 (by rwa [hc]))
  rw [← hc x, this, map_zero]

theorem conj_inv (c : E →+* E) (hc : ∀ x, c (c x) = x) (h1 : ∀ x, x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ c x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E))
    {B B' : FractionalIdeal (𝓞 E)⁰ E} (hB : ∀ x, x ∈ B' ↔ c x ∈ B) (h0 : B ≠ 0) :
    ∀ x, x ∈ B'⁻¹ ↔ c x ∈ B⁻¹ := by
  intro x
  have := GlobalTheory.ChiGrid.StairConj.mem_mul_inv_iff c hc (map_mul c) h0 (conj_ne_zero c hc hB h0) h1 hB x
  simpa only [one_mul] using this

end GlobalTheory.ConjIdeal

namespace GlobalTheory.ConjIdeal

theorem stA_modul_conj_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (a b : ℕ), ∃ I' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E, P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b * (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹) * I' = 1 ∧ ∀ x : D.host.E, x ∈ I' ↔ star x ∈ P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b * (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹) := by
  intro D T L P sc a b
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  let c : D.host.E →+* D.host.E := (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv.toRingHom
  have hcx : ∀ x, c x = D.host.conj x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Formalism.L2.Pj.conj_conj D x
  have h1 : ∀ x, x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ↔ c x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    have k : ∀ x, x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) → c x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      intro x hx
      obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 D.host.E)⁰).1 hx
      exact (FractionalIdeal.mem_one_iff (𝓞 D.host.E)⁰).2 ⟨D.host.conj • z, Formalism.L2.Pj.algebraMap_gal_smul D _ z⟩
    exact fun x => ⟨k x, fun h => by simpa only [hc] using k _ h⟩
  obtain ⟨hA0, hA⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L P sc
  have hA' : ∀ x, x ∈ P.stAbar sc ↔ c x ∈ P.stA sc := fun x => by rw [hcx, ← hs]; exact hA x
  set M : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E := ((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) with hMdef
  set Mb : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E := ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) with hMbdef
  have hM : ∀ x, x ∈ M ↔ c x ∈ Mb := fun x => GlobalTheory.ChiGrid.StairConj.mem_coe_iff D _ x
  have hM0 : M ≠ 0 := by rw [hMdef, Ne, FractionalIdeal.coeIdeal_eq_zero]; exact P.modul_ne_bot sc
  have hMb0 : Mb ≠ 0 := conj_ne_zero c hc (conj_symm c hc hM) hM0
  have hAb0 : P.stAbar sc ≠ 0 := conj_ne_zero c hc hA' hA0
  refine ⟨P.stAbar sc ^ a * (P.stA sc ^ a)⁻¹ * (Mb ^ b * (M ^ b)⁻¹), ?_, ?_⟩
  · have e1 : P.stA sc ^ a ≠ 0 := pow_ne_zero _ hA0
    have e2 : P.stAbar sc ^ a ≠ 0 := pow_ne_zero _ hAb0
    have e3 : M ^ b ≠ 0 := pow_ne_zero _ hM0
    have e4 : Mb ^ b ≠ 0 := pow_ne_zero _ hMb0
    calc P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (M ^ b * (Mb ^ b)⁻¹) *
          (P.stAbar sc ^ a * (P.stA sc ^ a)⁻¹ * (Mb ^ b * (M ^ b)⁻¹))
        = (P.stA sc ^ a * (P.stA sc ^ a)⁻¹) * (P.stAbar sc ^ a * (P.stAbar sc ^ a)⁻¹) *
          ((M ^ b * (M ^ b)⁻¹) * (Mb ^ b * (Mb ^ b)⁻¹)) := by ac_rfl
      _ = 1 := by rw [mul_inv_cancel₀ e1, mul_inv_cancel₀ e2, mul_inv_cancel₀ e3, mul_inv_cancel₀ e4]; simp
  · intro x
    rw [hs]
    exact conj_mul c hc (conj_mul c hc (conj_pow c hc h1 hA' a) (conj_inv c hc h1 (conj_pow c hc h1 (conj_symm c hc hA') a) (pow_ne_zero _ hAb0)))
      (conj_mul c hc (conj_pow c hc h1 (conj_symm c hc hM) b) (conj_inv c hc h1 (conj_pow c hc h1 hM b) (pow_ne_zero _ hMb0))) x

end GlobalTheory.ConjIdeal
