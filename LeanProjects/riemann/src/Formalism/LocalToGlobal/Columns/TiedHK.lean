import Formalism.LocalToGlobal.Columns.RecLevelLocK

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

section K1b

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} (SG : Finset (Pl E)) (H : Subgroup (GLG E n SG)) {π : 𝓞 E}
  (v : HeightOneSpectrum (𝓞 F))

local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
local notation "𝒪v" => Formalism.BasicNotions.intV E v
local notation "pE" => algebraMap (𝓞 E) E π

variable (h : BasePi ST π)
include h

theorem thk_L_le_Sh (z : Fin n → Rv) (hz : z ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹)) :
    z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)) := by
  rw [rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero)] at hz
  rw [rll_mem_loc_dLat n v _ h.star_ne_zero]
  refine ⟨hz.1, ?_⟩
  rw [← rll_p_mul_pinv v h (z (lastIdx n))]
  exact mul_mem (rll_incl_int v (cO E π)) (mul_mem (rll_incl_int v π) hz.2)

theorem thk_L_le_Ker (z : Fin n → Rv) (hz : z ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹)) :
    z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE / pE)) := by
  rw [rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero)] at hz
  rw [rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)]
  refine ⟨hz.1, ?_⟩
  rw [div_eq_mul_inv, map_mul, mul_assoc]
  exact mul_mem (rll_incl_int v (cO E π)) hz.2

theorem thk_Row {g : GL (Fin n) Rv} (hL : g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)))
    (hK : ∀ y ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)),
      (g : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹)) : rowLocalCondition n π v g := by
  refine rll_Row_of_maps n v h ?_ ?_ ?_
  · rw [← rll_baseLb_eq n h]; exact fun z hz => (hL z).1 hz
  · intro z hz
    have := add_mem (thk_L_le_Sh n v h _ (hK z hz)) hz
    rwa [sub_add_cancel] at this
  · intro z hz
    exact thk_L_le_Ker n v h _ (hK z hz)

theorem thk_inv {g : GL (Fin n) Rv} (hL : g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)))
    (hK : ∀ y ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)),
      (g : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹)) :
    ∀ y ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)),
      ((g⁻¹ : GL (Fin n) Rv) : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹) := by
  intro y hy
  have h1 := hK y hy
  rw [← rll_baseLb_eq n h] at h1 ⊢
  have h2 := ((Subgroup.inv_mem _ hL) _).1 h1
  have e : ((g⁻¹ : GL (Fin n) Rv) : Matrix (Fin n) (Fin n) Rv) *ᵥ ((g : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y) =
      y - ((g⁻¹ : GL (Fin n) Rv) : Matrix (Fin n) (Fin n) Rv) *ᵥ y := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [e] at h2
  have := neg_mem h2
  rwa [neg_sub] at this

theorem thk_K_of_Row {g : GL (Fin n) Rv} (hU : g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F))
    (h1 : rowLocalCondition n π v g) (h2 : rowLocalCondition n π v g⁻¹) :
    ∀ y ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)),
      (g : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹) := by
  intro y hy
  have hcol := rll_col hc n v hU h2
  have hgy := rll_maps_Sh n v h h1.1 hcol y hy
  rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at hy hgy
  rw [rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero)]
  refine ⟨fun i hi => sub_mem (hgy.1 i hi) (hy.1 i hi), ?_⟩
  have e : (g : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y = ((g : Matrix (Fin n) (Fin n) Rv) - 1) *ᵥ y := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e]
  show ιv pE⁻¹ * ∑ j, ((g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j - (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j) * y j ∈ 𝒪v
  rw [Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  obtain ⟨s, hs, e1⟩ := h1.2 j
  rw [e1, mul_assoc, rll_pinv_mul v h]
  by_cases hj : j = lastIdx n
  · subst hj
    obtain ⟨s2, hs2, e2⟩ := h2.2 (lastIdx n)
    have h3 := rll_inv_entry hc n v (Subgroup.inv_mem _ hU) (lastIdx n) (lastIdx n)
    rw [inv_inv] at h3
    rw [Matrix.one_apply_eq] at e1 e2
    have e3 : (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) (lastIdx n) - 1 =
        ιv (star pE) * sigR hc.sig (v.adicCompletion F) s2 := by
      rw [h3, sub_eq_iff_eq_add.1 e2, map_add, map_mul, map_one, rll_sigV_incl, add_sub_cancel_right]
    obtain ⟨a, b, hab⟩ := h.cop
    have hab' : ιv (algebraMap (𝓞 E) E a) * ιv pE + ιv (algebraMap (𝓞 E) E b) * ιv (star pE) = 1 := by
      have h4 := congrArg (fun t => ιv (algebraMap (𝓞 E) E t)) hab
      simp only [map_add, map_mul, map_one] at h4
      exact h4
    have es : s = ιv (star pE) * (ιv (algebraMap (𝓞 E) E a) * sigR hc.sig (v.adicCompletion F) s2 + ιv (algebraMap (𝓞 E) E b) * s) := by
      calc s = (ιv (algebraMap (𝓞 E) E a) * ιv pE + ιv (algebraMap (𝓞 E) E b) * ιv (star pE)) * s := by rw [hab', one_mul]
        _ = ιv (algebraMap (𝓞 E) E a) * (ιv pE * s) + ιv (algebraMap (𝓞 E) E b) * ιv (star pE) * s := by ring
        _ = ιv (algebraMap (𝓞 E) E a) * (ιv (star pE) * sigR hc.sig (v.adicCompletion F) s2) +
            ιv (algebraMap (𝓞 E) E b) * ιv (star pE) * s := by rw [← e1, e3]
        _ = _ := by ring
    rw [es]
    have e5 : ιv (star pE) * (ιv (algebraMap (𝓞 E) E a) * sigR hc.sig (v.adicCompletion F) s2 + ιv (algebraMap (𝓞 E) E b) * s) *
        y (lastIdx n) = (ιv (algebraMap (𝓞 E) E a) * sigR hc.sig (v.adicCompletion F) s2 + ιv (algebraMap (𝓞 E) E b) * s) *
        (ιv (star pE) * y (lastIdx n)) := by ring
    rw [e5]
    exact mul_mem (add_mem (mul_mem (rll_incl_int v a) (rll_sigV_mem hc v hs2)) (mul_mem (rll_incl_int v b) hs)) hy.2
  · exact mul_mem hs (hy.1 j hj)

theorem localLevel_iff_kOne (hG : v ∉ plUnder F SG) (g : GL (Fin n) Rv) :
    g ∈ levLoc hc n ST SG H v ↔
      (g ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ∧
        ∀ y ∈ Formalism.L2.Herm.locL v (Submodule.span (𝓞 E)
            (dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))),
          (g : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (baseLb E n ST)) := by
  have eD : Formalism.L2.Herm.locL v (Submodule.span (𝓞 E)
      (dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))) =
      Formalism.L2.Herm.locL v (rll_dLat n (star pE)) := rll_dualV_eq hc n v h
  constructor
  · intro hg
    have hg' := hg
    rw [levLoc_eq_stabFun hc n SG H v h hG] at hg'
    obtain ⟨hL, hF⟩ := hg'
    refine ⟨hL, fun y hy => ?_⟩
    have r1 := rll_Row_of_stabFun hc n v h hL.2 hF
    have r2 := rll_Row_of_stabFun hc n v h (Subgroup.inv_mem _ hL.2) (Subgroup.inv_mem _ hF)
    rw [rll_baseLb_eq n h]
    exact thk_K_of_Row hc n v h hL.1 r1 r2 y (eD ▸ hy)
  · rintro ⟨hL, hK⟩
    have hK' : ∀ y ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)),
        (g : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹) := by
      intro y hy
      rw [← rll_baseLb_eq n h]
      exact hK y (eD.symm ▸ hy)
    exact rll_mem_levLoc_of_Row hc n SG H v h hG hL.1 (thk_Row n v h hL.2 hK')
      (thk_Row n v h (Subgroup.inv_mem _ hL.2) (thk_inv n v h hL.2 hK'))

end K1b

end Formalism.L2.Col
