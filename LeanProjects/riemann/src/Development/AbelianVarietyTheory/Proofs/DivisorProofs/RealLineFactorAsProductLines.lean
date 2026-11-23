import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompFinEqZeroOfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixOneParameterGroupEqExpOfContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParameterSkewHermitian
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.ThK.LineDec

theorem prod_embArch_projArch {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {m : GAd σ J} (hm : m ∈ infPts σ J) :
    (((Finset.univ : Finset (InfinitePlace F)).toList).map fun w => embArch σ J w (projArch σ J w m)).prod = m := by
  classical
  have key : ∀ (l : List (InfinitePlace F)), l.Nodup → ∀ u,
      projArch σ J u (l.map fun w => embArch σ J w (projArch σ J w m)).prod = if u ∈ l then projArch σ J u m else 1 := by
    intro l hl u
    induction l with
    | nil => simp
    | cons w l ih =>
      rw [List.map_cons, List.prod_cons, map_mul, ih hl.of_cons]
      by_cases e : u = w
      · subst e
        simp [hl.notMem]
      · simp [projArch_embArch_ne σ J e, e]
  refine GAd_ext σ J (fun u => by rw [key _ (Finset.nodup_toList _), if_pos (by simp)]) fun v => ?_
  rw [mem_infPts_iff_forall.1 hm v, map_list_prod, List.map_map]
  exact List.prod_eq_one fun _ h => by
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 h
    simp

theorem isRealLine_component {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : ℝ → GAd σ J)
    (hc : Continuous g) (h0 : g 0 = 1) (hm : ∀ s t, g (s + t) = g s * g t) (w : InfinitePlace F) :
    IsRealLine σ J fun t => embArch σ J w (projArch σ J w (g t)) := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter
    (fun t => GlobalTheory.Orb.archMat σ J τ (projArch σ J w (g t)))
    ((GlobalTheory.Orb.continuous_archMat σ J τ).comp ((continuous_projArch σ J w).comp hc))
    (by simp only [h0, map_one]) (fun s t => by simp only [hm, map_mul])
  exact ⟨w, τ, Z, GlobalTheory.ThK.OneParamLie.lie_of_archMat_eq_exp F E σ hcm n J w τ Z (fun t => projArch σ J w (g t)) hZ, fun t => ⟨_, rfl, hZ t⟩⟩

theorem line_eq_prod_realLines : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x), IsCMExt F E σ → ∀ {d : ℕ} (W : Spc F E d) (c : E) (hc : c ≠ 0), ∀ γ ∈ Lines σ W,
    ∃ (k : ℕ) (δ : Fin k → ℝ → GAd σ (c • W.J.map σ)), (∀ i, IsRealLine σ (c • W.J.map σ) (δ i)) ∧
      ∀ t : ℝ, toGAd hσ W.J hc (γ (Multiplicative.ofAdd t)) = (List.ofFn fun i => δ i t).prod := by
  intro F E _ _ _ _ _ σ hσ hcm d W c hc γ hγ
  let g : ℝ → GAd σ (c • W.J.map σ) := fun t => toGAd hσ W.J hc (γ (Multiplicative.ofAdd t))
  have hT : Continuous (toGAd hσ W.J hc) := continuous_subtype_val.subtype_mk _
  have hg : Continuous g := hT.comp (hγ.1.comp continuous_ofAdd)
  let l := (Finset.univ : Finset (InfinitePlace F)).toList
  refine ⟨l.length, fun i t => embArch σ _ (l.get i) (projArch σ _ (l.get i) (g t)), fun i =>
    isRealLine_component hcm g hg (by simp [g]) (fun s t => by simp only [g, ofAdd_add, map_mul]) _, fun t => ?_⟩
  have h := prod_embArch_projArch (GlobalTheory.ThK.FiniteLevelDerivatives.toGAd_mem_infPts hσ W hc (hγ.2 (Multiplicative.ofAdd t)))
  refine h.symm.trans (congrArg List.prod ?_)
  conv_lhs => rw [← List.ofFn_get (Finset.univ : Finset (InfinitePlace F)).toList, List.map_ofFn]
  rfl

end GlobalTheory.ThK.LineDec
