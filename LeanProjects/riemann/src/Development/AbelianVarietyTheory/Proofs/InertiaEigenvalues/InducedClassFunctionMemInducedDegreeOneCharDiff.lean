import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndApplyOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedClassFunctionFromSubgroupTransStatement
open GlobalTheory.BI GlobalTheory.BrauerZero

noncomputable section
namespace GlobalTheory.BrauerZero

theorem ind_eq_ind_map_subgroupOf {G : Type} [Group G] [Finite G] (E : Subgroup G) (H : Subgroup E)
    (φ : H → ℂ) :
    ind H φ = ind ((H.map E.subtype).subgroupOf E)
      (fun k => φ ((Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).symm
        ⟨((k : E) : G), k.2⟩)) := by
  classical
  have hS : (H.map E.subtype).subgroupOf E = H := by
    ext y
    simp [Subgroup.mem_subgroupOf]
  have hc : Nat.card ((H.map E.subtype).subgroupOf E) = Nat.card H :=
    Nat.card_congr (MulEquiv.subgroupCongr hS).toEquiv
  funext g
  simp only [ind, hc]
  congr 1
  refine finsum_congr fun x => ?_
  simp only [ext0]
  by_cases hy : x⁻¹ * g * x ∈ H
  · have hy' : x⁻¹ * g * x ∈ (H.map E.subtype).subgroupOf E := by rw [hS]; exact hy
    rw [dif_pos hy, dif_pos hy']
    congr 1
    apply (Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  · have hy' : x⁻¹ * g * x ∉ (H.map E.subtype).subgroupOf E := by rw [hS]; exact hy
    rw [dif_neg hy, dif_neg hy']

theorem ind_mem_D0_of_mem_D0 : ∀ {G : Type} [Group G] [Finite G] (E : Subgroup G) (f : E → ℂ),
    f ∈ D0 E → ind E f ∈ D0 G := by
  intro G _ _ E f hf
  induction hf using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨H, χ, rfl⟩ := hx
    have hK : H.map E.subtype ≤ E := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    let χ' : H.map E.subtype →* ℂˣ :=
      χ.comp (Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).symm.toMonoidHom
    rw [ind_sub, ind_eq_ind_map_subgroupOf E H (fun h => (χ h : ℂ)),
      ind_eq_ind_map_subgroupOf E H (fun _ => (1 : ℂ))]
    have h1 : ind E (ind ((H.map E.subtype).subgroupOf E) (fun k =>
        ((χ ((Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).symm
          ⟨((k : E) : G), k.2⟩) : ℂˣ) : ℂ))) = ind (H.map E.subtype) (fun k => (χ' k : ℂ)) :=
      GlobalTheory.T.inducedClassFunctionFromSubgroup_trans (H.map E.subtype) E hK (fun k => (χ' k : ℂ))
    have h2 := GlobalTheory.T.inducedClassFunctionFromSubgroup_trans (H.map E.subtype) E hK (fun _ => (1 : ℂ))
    rw [h1, h2]
    exact AddSubgroup.subset_closure ⟨H.map E.subtype, χ', rfl⟩
  | zero =>
    have : ind E (0 : E → ℂ) = 0 := (indAddHomComplex E).map_zero
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : ind E (a + b) = ind E a + ind E b := (indAddHomComplex E).map_add a b
    rw [this]; exact add_mem ha hb
  | neg a _ ha =>
    have : ind E (-a) = -ind E a := (indAddHomComplex E).map_neg a
    rw [this]; exact neg_mem ha

end GlobalTheory.BrauerZero
