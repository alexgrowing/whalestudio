import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LevelVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CentralOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrFwd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrBwd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrCochain
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ExistsCurve
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem one_kills {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))
    (hm : m ∈ Submodule.span ℂ {x | ∃ φ v, IsLevelFn U Ξ φ ∧ x = φ ⊗ₜ[ℂ] v}) : smLie Ξ (oneL E a) m = 0 := by
  obtain ⟨r, hr⟩ := oneReal E a Ξ
  have hr' : Ξ.dmat (oneL E a) = (r : ℂ) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := hr
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, v, hφ, rfl⟩ := hx
    change (lie E a (oneL E a)).rTensor _ (φ ⊗ₜ[ℂ] v) + (Matrix.toLin' (Ξ.dmat (oneL E a))).lTensor _ (φ ⊗ₜ[ℂ] v) = 0
    rw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hφ.2.2 _ hr', hr', map_smul, Matrix.toLin'_one,
      LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.smul_tmul, ← TensorProduct.tmul_add, neg_smul, neg_add_cancel,
      TensorProduct.tmul_zero]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

private theorem d_basic {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ} (α : Co Ξ q) (hα : IsLev U Ξ α)
    (X : Fin (q + 1) → Herm E a) (i : Fin (q + 1)) (hX : (X i).1 = 1) : dCo (smLie Ξ) α X = 0 := by
  rw [dCo_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : i = j
  · subst hj
    have h := one_kills U Ξ _ (hα.val (i.removeNth X))
    have e : oneL E a = toL (X i).1 := by rw [hX]
    rw [e] at h
    rw [h, smul_zero]
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
    have hz : α (j.removeNth X) = 0 := hα.basic _ k (by rw [← hX, ← hk]; rfl)
    rw [hz, map_zero, smul_zero]

theorem UpperTheory.V.Lit.Geo.levGood :
    LevGood := by
  intro E _ _ _ a ho U Ξ q
  refine ⟨fun α hα => ?_, fun w hw => ?_⟩
  · have hv : ∀ X, LeftInv (α X) ∧ RightInv U (α X) := fun X => (levelVal E a U Ξ _).1 (hα.val X)
    obtain ⟨w, hw, h0⟩ := corrFwd E a U Ξ q α hα.equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, h0 s⟩⟩
    have hw' : Corr U Ξ α w'.1 := hw
    exact ⟨w', hw', (corrInv E a ho U Ξ q _ _ hw').1 fun X => (hv X).1, (corrBasic E a U Ξ q _ _ hw').1 hα.basic,
      (corrBasic E a U Ξ (q + 1) _ _ (corrD E a ho U Ξ q _ _ hw')).1 (d_basic U Ξ α hα)⟩
  · obtain ⟨α, hα⟩ := corrBwd E a ho U Ξ q w
    have b := (corrBasic E a U Ξ q _ _ hα).2 hw.basic
    have b' := (corrBasic E a U Ξ (q + 1) _ _ (corrD E a ho U Ξ q _ _ hα)).2 hw.dbasic
    obtain ⟨c1, c2⟩ := corrCochain E a U Ξ q _ _ hα
    exact ⟨α, hα, c1, b, fun X => (levelVal E a U Ξ _).2 ((corrInv E a ho U Ξ q _ _ hα).2 hw.inv X) (c2 X)
      (centralOf E a _ (smLie Ξ) q α b b' X)⟩
