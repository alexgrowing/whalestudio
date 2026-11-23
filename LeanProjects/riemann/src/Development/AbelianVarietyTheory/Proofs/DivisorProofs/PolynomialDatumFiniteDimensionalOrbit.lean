import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsDIffDOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaSpanFiniteDimensionalDualPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalArchimedeanSchwartzFockOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactArchOperatorPreservesFockVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMaximalCompactIntertwinesFockDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepIntertwinesActionStatement

noncomputable section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.FockKFin

theorem polData_kfin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.KP → GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ Φ ∈ GlobalTheory.ThK.PolData B M,
      ∃ S : Submodule ℂ (GlobalTheory.ThK.Fn F n d), FiniteDimensional ℂ S ∧ S ≤ GlobalTheory.ThK.PolData B M ∧ ∀ k ∈ KInf σ W B.emb, om (1, k) Φ ∈ S := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' _hKP hP Φ hΦ
  have hψ : IsStd B.ψ := hP.base.std
  have hfin : ∀ m, FiniteDimensional ℂ (GlobalTheory.FockKFin.polLe M B.emb m) := by
    intro m
    induction m with
    | zero => exact GlobalTheory.T.fockVacua_span_finiteDimensional_dualPair F E σ B n d X W M χX χW om r s r' s' hP
    | succ m ih =>
      rw [GlobalTheory.FockKFin.polLe_succ]
      haveI := ih
      haveI := GlobalTheory.T.finiteDimensional_archimedeanSchwartzFockOperatorSpan F _ _ ih
      infer_instance
  have hle : ∀ m, GlobalTheory.FockKFin.polLe M B.emb m ≤ M.Pol B.ψ B.emb := by
    intro m
    induction m with
    | zero => exact Submodule.span_le.2 fun g hg => GlobalTheory.ThK.EvAt0.PolEv.gauss_mem hψ M B.emb hg
    | succ m ih =>
      rw [GlobalTheory.FockKFin.polLe_succ]
      refine sup_le ih (Submodule.span_le.2 ?_)
      rintro _ ⟨a, b, f, hf, rfl⟩
      exact GlobalTheory.ThK.EvAt0.PolEv.dOp_mem hψ M B.emb a b (ih hf)
  have hdir : Directed (· ≤ ·) (GlobalTheory.FockKFin.polLe M B.emb) := (GlobalTheory.FockKFin.polLe_mono M B.emb).directed_le
  have hcov : ∀ f ∈ M.Pol B.ψ B.emb, ∃ m, f ∈ GlobalTheory.FockKFin.polLe M B.emb m := by
    intro f hf
    have hsub : M.Pol B.ψ B.emb ≤ ⨆ m, GlobalTheory.FockKFin.polLe M B.emb m := by
      rw [GlobalTheory.ThK.EvAt0.PolEv.pol_eq hψ]
      refine sInf_le ⟨fun g hg => Submodule.mem_iSup_of_mem 0 (Submodule.subset_span hg), fun a b g hg => ?_⟩
      obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hg
      refine Submodule.mem_iSup_of_mem (m + 1) ?_
      rw [GlobalTheory.FockKFin.polLe_succ]
      exact Submodule.mem_sup_right (GlobalTheory.FockKFin.dOp_mem_dStep _ a b hm)
    exact (Submodule.mem_iSup_of_directed _ hdir).1 (hsub hf)
  have hst : ∀ k ∈ KInf σ W B.emb, ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
      ∀ m, ∀ f ∈ GlobalTheory.FockKFin.polLe M B.emb m, A f ∈ GlobalTheory.FockKFin.polLe M B.emb m := by
    intro k hk A hA m
    induction m with
    | zero =>
      intro f hf
      rw [GlobalTheory.FockKFin.polLe_zero] at hf ⊢
      refine Submodule.span_induction (fun g hg => Submodule.subset_span (GlobalTheory.T.maximalCompact_archOperator_preserves_fockVacua F E σ B n d X W M χX χW om r s r' s' hP k hk A hA g hg))
        (by rw [map_zero]; exact Submodule.zero_mem _) (fun x y _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
        (fun c x _ hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) hf
    | succ m ih =>
      intro f hf
      rw [GlobalTheory.FockKFin.polLe_succ] at hf ⊢
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      rw [map_add]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (ih y hy)) (Submodule.mem_sup_right ?_)
      refine Submodule.span_induction (fun g hg => ?_)
        (by rw [map_zero]; exact Submodule.zero_mem _) (fun x y _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
        (fun c x _ hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) hz
      obtain ⟨a, b, g₀, hg₀, rfl⟩ := hg
      obtain ⟨a', b', hab⟩ := GlobalTheory.T.archimedeanMaximalCompact_intertwines_fockDerivativeOps F E σ B n d X W M χX χW om r s r' s' hP k hk A hA a b
      rw [hab]
      exact GlobalTheory.FockKFin.dOp_mem_dStep _ a' b' (ih g₀ hg₀)
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hφ, hvac, rfl⟩ := hx
    obtain ⟨m, hm⟩ := hcov f hf
    haveI := hfin m
    refine ⟨(GlobalTheory.FockKFin.polLe M B.emb m).map (GlobalTheory.FockKFin.pureL φ), inferInstance, ?_, fun k hk => ?_⟩
    · rw [Submodule.map_le_iff_le_comap]
      intro g hg
      exact Submodule.subset_span ⟨g, hle m hg, φ, hφ, hvac, rfl⟩
    · obtain ⟨A, hA⟩ := GlobalTheory.ArchLocalAct.exists_op_of_KInf F E σ B n d X W M om χX χW hP.base hP.good hP.weil k hk
      rw [GlobalTheory.T.weil_rep_intertwines_action F E σ B.ψ n d X W M om hP.good (1, k) A hA f φ hφ hvac]
      exact Submodule.mem_map_of_mem (hst k hk A hA m f hm)
  | zero =>
    exact ⟨⊥, inferInstance, bot_le, fun k _ => by rw [map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h₁, l₁, k₁⟩ := hx
    obtain ⟨S₂, h₂, l₂, k₂⟩ := hy
    exact ⟨S₁ ⊔ S₂, inferInstance, sup_le l₁ l₂, fun k hk => by
      rw [map_add]; exact Submodule.add_mem_sup (k₁ k hk) (k₂ k hk)⟩
  | smul c x _ hx =>
    obtain ⟨S, h, l, k₁⟩ := hx
    exact ⟨S, h, l, fun k hk => by rw [map_smul]; exact Submodule.smul_mem _ c (k₁ k hk)⟩

end GlobalTheory.FockKFin

end
