import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsTensorSmul

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct Pointwise

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem firstCoords_zero : crd1 X p θ Q 0 = 0 := by
  unfold crd1; rw [map_zero, Pi.zero_comp, Matrix.mulVec_zero]

theorem secondCoords_zero : crd2 X p θ Q 0 = 0 := by
  unfold crd2; rw [map_zero, Pi.zero_comp, Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem firstCoords_smul_integer (c : OvA X p) (v : Fin X.B.I.n → TpX X p) :
    crd1 X p θ Q (c • v) = c • crd1 X p θ Q v := by
  rw [smulO_eq]
  show crd1 X p θ Q ((c : FpX X p) • v) = (c : FpX X p) • crd1 X p θ Q v
  unfold crd1
  rw [LinearMap.map_smul, show ((c : FpX X p) • pr1 θ v) ∘ (idxEquiv X).symm =
    (c : FpX X p) • (pr1 θ v ∘ (idxEquiv X).symm) from rfl, Matrix.mulVec_smul]

theorem secondCoords_smul_integer (c : OvA X p) (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q (c • v) = c • crd2 X p θ Q v := by
  rw [smulO_eq]
  show crd2 X p θ Q ((c : FpX X p) • v) = (c : FpX X p) • crd2 X p θ Q v
  unfold crd2
  rw [LinearMap.map_smul, show ((c : FpX X p) • pr2 θ v) ∘ (idxEquiv X).symm =
    (c : FpX X p) • (pr2 θ v ∘ (idxEquiv X).symm) from rfl, Matrix.mulVec_smul, Matrix.mulVec_smul]

theorem splitA_of (hO1 : ∀ t ∈ OEp X p, (θ t).1 ∈ OvA X p ∧ (θ t).2 ∈ OvA X p)
    (hO2 : θ.symm (1, 0) ∈ OEp X p) (hO3 : θ.symm (0, 1) ∈ OEp X p)
    (hLat : ∀ x, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
      IntVec (OvA X p) (crd1 X p θ Q x) ∧ IntVec (OvA X p) (crd2 X p θ Q x))
    (hInj : ∀ x, crd1 X p θ Q x = 0 → crd2 X p θ Q x = 0 → x = 0)
    (hSurj : ∀ a b, ∃ x, crd1 X p θ Q x = a ∧ crd2 X p θ Q x = b) : SplitA X p θ Q := by
  intro S y
  unfold InModP
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_sup]
  constructor
  · rintro ⟨w, hw, l', hl', rfl⟩
    obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hl'
    have key : ∀ w ∈ Submodule.span (OvA X p) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s},
        crd1 X p θ Q w ∈ Submodule.span (OvA X p) (crd1 X p θ Q '' S) ∧
        crd2 X p θ Q w ∈ Submodule.span (OvA X p) (crd2 X p θ Q '' S) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨t, ht, s, hs, rfl⟩ := hx
        rw [firstCoords_tensor_smul, secondCoords_tensor_smul]
        exact ⟨Submodule.smul_mem _ (⟨_, (hO1 t ht).1⟩ : OvA X p) (Submodule.subset_span ⟨s, hs, rfl⟩),
          Submodule.smul_mem _ (⟨_, (hO1 t ht).2⟩ : OvA X p) (Submodule.subset_span ⟨s, hs, rfl⟩)⟩
      | zero => rw [firstCoords_zero, secondCoords_zero]; exact ⟨zero_mem _, zero_mem _⟩
      | add x y _ _ hx hy =>
        rw [firstCoords_add, secondCoords_add]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
      | smul c x _ hx =>
        rw [firstCoords_smul_integer, secondCoords_smul_integer]
        exact ⟨Submodule.smul_mem _ c hx.1, Submodule.smul_mem _ c hx.2⟩
    have hl2 := (hLat l).1 hl
    refine ⟨⟨crd1 X p θ Q w, (key w hw).1, crd1 X p θ Q l, hl2.1, ?_⟩,
      ⟨crd2 X p θ Q w, (key w hw).2, crd2 X p θ Q l, hl2.2, ?_⟩⟩
    · rw [firstCoords_add, firstCoords_smul_integer]; rfl
    · rw [secondCoords_add, secondCoords_smul_integer]; rfl
  · rintro ⟨⟨w1, hw1, z1, hz1, e1⟩, ⟨w2, hw2, z2, hz2, e2⟩⟩
    have lift1 : ∀ w1 ∈ Submodule.span (OvA X p) (crd1 X p θ Q '' S),
        ∃ w ∈ Submodule.span (OvA X p) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s},
          crd1 X p θ Q w = w1 ∧ crd2 X p θ Q w = 0 := by
      intro w1 hw1
      induction hw1 using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨s, hs, rfl⟩ := hx
        refine ⟨θ.symm (1, 0) • s, Submodule.subset_span ⟨_, hO2, s, hs, rfl⟩, ?_, ?_⟩
        · rw [firstCoords_tensor_smul, AlgEquiv.apply_symm_apply, one_smul]
        · rw [secondCoords_tensor_smul, AlgEquiv.apply_symm_apply, zero_smul]
      | zero => exact ⟨0, zero_mem _, firstCoords_zero X p θ Q, secondCoords_zero X p θ Q⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, ha1, ha2⟩ := hx
        obtain ⟨b, hb, hb1, hb2⟩ := hy
        exact ⟨a + b, add_mem ha hb, by rw [firstCoords_add, ha1, hb1], by rw [secondCoords_add, ha2, hb2, add_zero]⟩
      | smul c x _ hx =>
        obtain ⟨a, ha, ha1, ha2⟩ := hx
        exact ⟨c • a, Submodule.smul_mem _ c ha, by rw [firstCoords_smul_integer, ha1], by rw [secondCoords_smul_integer, ha2, smul_zero]⟩
    have lift2 : ∀ w2 ∈ Submodule.span (OvA X p) (crd2 X p θ Q '' S),
        ∃ w ∈ Submodule.span (OvA X p) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s},
          crd1 X p θ Q w = 0 ∧ crd2 X p θ Q w = w2 := by
      intro w2 hw2
      induction hw2 using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨s, hs, rfl⟩ := hx
        refine ⟨θ.symm (0, 1) • s, Submodule.subset_span ⟨_, hO3, s, hs, rfl⟩, ?_, ?_⟩
        · rw [firstCoords_tensor_smul, AlgEquiv.apply_symm_apply, zero_smul]
        · rw [secondCoords_tensor_smul, AlgEquiv.apply_symm_apply, one_smul]
      | zero => exact ⟨0, zero_mem _, firstCoords_zero X p θ Q, secondCoords_zero X p θ Q⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, ha1, ha2⟩ := hx
        obtain ⟨b, hb, hb1, hb2⟩ := hy
        exact ⟨a + b, add_mem ha hb, by rw [firstCoords_add, ha1, hb1, add_zero], by rw [secondCoords_add, ha2, hb2]⟩
      | smul c x _ hx =>
        obtain ⟨a, ha, ha1, ha2⟩ := hx
        exact ⟨c • a, Submodule.smul_mem _ c ha, by rw [firstCoords_smul_integer, ha1, smul_zero], by rw [secondCoords_smul_integer, ha2]⟩
    obtain ⟨wa, hwa, ha1, ha2⟩ := lift1 w1 hw1
    obtain ⟨wb, hwb, hb1, hb2⟩ := lift2 w2 hw2
    obtain ⟨l, hl1, hl2⟩ := hSurj z1 z2
    have hl : l ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
      (hLat l).2 ⟨hl1 ▸ hz1, hl2 ▸ hz2⟩
    have hy : y = (wa + wb) + ((gOf p : ℕ) : OvA X p) • l := by
      have h0 := hInj (y - ((wa + wb) + ((gOf p : ℕ) : OvA X p) • l)) ?_ ?_
      · exact sub_eq_zero.mp h0
      · rw [firstCoords_sub, firstCoords_add, firstCoords_add, firstCoords_smul_integer, e1, ha1, hb1, hl1, add_zero]
        show w1 + ((gA X p : OvA X p) : FpX X p) • z1 - (w1 + ((gA X p : OvA X p) : FpX X p) • z1) = 0
        exact sub_self _
      · rw [secondCoords_sub, secondCoords_add, secondCoords_add, secondCoords_smul_integer, e2, ha2, hb2, hl2, zero_add]
        show w2 + ((gA X p : OvA X p) : FpX X p) • z2 - (w2 + ((gA X p : OvA X p) : FpX X p) • z2) = 0
        exact sub_self _
    exact ⟨wa + wb, add_mem hwa hwb, _, Submodule.smul_mem_pointwise_smul _ _ _ hl, hy.symm⟩

end Loc

end MassDataIdxSteps
