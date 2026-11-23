import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt

namespace HalfMetricWeight
section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Dblock.HalfWeight

theorem half_metWeight_eq : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (σ : F →+* ℂ) (D : ℕ) (A : FinHolAtlas D (Pts Y σ)), IsAlgAtlas A → ∀ (Δ : Y.Dv) (m : C.Met Y σ Δ) (hm : ∀ y, PosAt m y) (Q : LocPot (Pts Y σ)), IsPot id m Q → ∀ (x : Pts Y σ) (c : (toLB Δ).ι), x ∈ ptsIn Y.str σ ((toLB Δ).U c) → ∃ W : Set (Pts Y σ), IsOpen W ∧ x ∈ W ∧ ∃ G : Pts Y σ → ℂ, A.HoloOn W G ∧ ∀ z ∈ W, (metWeight Δ m hm).φ c z / 2 = Q.φ x z + (G z).re := by
  intro F _ _ C Y σ D A hA Δ m hm Q hQ x c hx
  obtain ⟨f, hf⟩ := hQ x
  have hxc : under x ∈ c.1.1 := mem_ptsIn.1 hx
  have hu : UnitAt (under x) (f * (c.1.2 : Y.Fn)) :=
    (c.2.2 _ hxc).generatesAt_iff.1 (hf x (Q.mem_U x)).1
  obtain ⟨U, hU, a, ea⟩ := hu.regAt.exists_fnOf
  have hxU : x ∈ ptsIn Y.str σ U := mem_ptsIn.2 hU
  have hv : ∀ z ∈ ptsIn Y.str σ U, ev Y.str σ U a z = ratVal (f * (c.1.2 : Y.Fn)) z := fun z hz => by
    rw [← ea, ratVal_fnOf hz]
  have hS : IsOpen (ptsIn Y.str σ U ∩ (Q.U x ∩ ptsIn Y.str σ ((toLB Δ).U c))) :=
    (isOpen_ptsIn _).inter ((Q.isOpen_U x).inter (isOpen_ptsIn _))
  have hH : hA.anRead.HoloOn (ptsIn Y.str σ U ∩ (Q.U x ∩ ptsIn Y.str σ ((toLB Δ).U c))) (ev Y.str σ U a) :=
    fun j => (hA.anRead.holoOn_ev U a j).mono fun v hv => ⟨hv.1, hv.2.1⟩
  obtain ⟨W, hW, hxW, hs, G, hG, e⟩ := AnRead.HoloOn.exists_log hH hS ⟨hxU, Q.mem_U x, hx⟩
    (by rw [hv x hxU]; exact ratVal_ne_zero hu)
  refine ⟨W, hW, hxW, G, (hA.holoOn_iff hA.anRead hW).2 hG, fun z hz => ?_⟩
  obtain ⟨hzU, hzQ, hzc⟩ := hs hz
  have hzc' : under z ∈ c.1.1 := mem_ptsIn.1 hzc
  have he := c.2.2 _ hzc'
  obtain ⟨hgen, -, hφ⟩ := hf z hzQ
  have hgen' : Δ.GeneratesAt (under z) f := hgen
  have huz : UnitAt (under z) (f * (c.1.2 : Y.Fn)) := he.generatesAt_iff.1 hgen'
  have hgi := CartierDiv.isEqn_iff_generatesAt_inv.1 he
  have hp := pn_pos_of_generatesAt (C := C) hgi (hm z)
  have hr : 0 < ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ := norm_pos_iff.2 (ratVal_ne_zero huz)
  have e1 : f = (f * (c.1.2 : Y.Fn)) * ((c.1.2 : Y.Fn))⁻¹ := by
    rw [mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), mul_one]
  have e2 : C.pn Y σ Δ m (C.cx Y σ f) z =
      ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2 * C.pn Y σ Δ m (C.cx Y σ ((c.1.2 : Y.Fn))⁻¹) z := by
    rw [← C.pn_mul Y σ Δ m _ _ z huz.regAt hgi.regularAt, ← e1]
  have e3 : Q.φ x z = -(Real.log (C.pn Y σ Δ m (C.cx Y σ f) z) / 2) := hφ
  have e4 : (G z).re = Real.log ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ := by rw [e z hz, hv z hzU]
  rw [metWeight_φ, e4, e3, e2, Real.log_mul (pow_pos hr 2).ne' hp.ne', Real.log_pow]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Dblock.HalfWeight

end
end

end HalfMetricWeight
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.half_metWeight_eq_potential_holo : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (σ : F →+* ℂ) (D : ℕ) (A : FinHolAtlas D (Pts Y σ)), IsAlgAtlas A → ∀ (Δ : Y.Dv) (m : C.Met Y σ Δ) (hm : ∀ y, PosAt m y) (Q : LocPot (Pts Y σ)), IsPot id m Q → ∀ (x : Pts Y σ) (c : (toLB Δ).ι), x ∈ ptsIn Y.str σ ((toLB Δ).U c) → ∃ W : Set (Pts Y σ), IsOpen W ∧ x ∈ W ∧ ∃ G : Pts Y σ → ℂ, A.HoloOn W G ∧ ∀ z ∈ W, (metWeight Δ m hm).φ c z / 2 = Q.φ x z + (G z).re := by
  first | exact @HalfMetricWeight.GlobalTheory.CompanionTheory.Dblock.HalfWeight.half_metWeight_eq | exact HalfMetricWeight.GlobalTheory.CompanionTheory.Dblock.HalfWeight.half_metWeight_eq | (intros; apply HalfMetricWeight.GlobalTheory.CompanionTheory.Dblock.HalfWeight.half_metWeight_eq <;> assumption)

end
