import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

noncomputable section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.JetSer

theorem valSer_germ_fnVal {A : Type} [CommRing A] {Y : Scheme.{0}} (r : Spec (CommRingCat.of A) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Spec (CommRingCat.of A)) (f : Γ(Y, U)) :
    ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (fnVal r U f)) = gs r z U f := by
  have hz : r z ∈ U := h (show z ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) from trivial)
  rw [gs_eq r z U hz, fnVal, dif_pos h]
  have e : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a) = a :=
    fun a => (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id_apply a
  rw [e]
  exact TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of A)).presheaf (homOfLE h) z trivial _

theorem valSer : ValSerSt := by
  intro A _ X L hL j z Ψ _ hΨ
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Ψ) (fun ψ => ψ.1) (fun _ => j) (fun _ _ _ => rfl)
    (fun ψ => hΨ ψ.1 ψ.2 (show z ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) from trivial))
  refine ⟨J, hJ, fun Y K _ φ ε t r hr => ?_⟩
  have hU : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun _ => j) := fun y hy => Set.mem_iInter.2 fun k => hΨ _ (hr k) hy
  rw [val_of t r z J (fun _ => j) (fun k => e ⟨_, hr k⟩)]
  exact (gs_unit r z _ (hU (show z ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) from trivial)) _).symm.trans
    (valSer_germ_fnVal r _ hU z _).symm

end GlobalTheory.JetSer
