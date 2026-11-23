import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfIsStabSkew
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum
open GlobalTheory.DblDatum

noncomputable section
namespace GlobalTheory.DblKFinCpt

theorem map_piInf_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n) (f : UA σ X.J) (hf : f ∈ UAt σ X (sndA F))
    {w : InfinitePlace F} (τ : EmbOver E w) : (mat f).map (piInf τ) = 1 := by
  let u : AF F := (1, 0)
  have h0 := hf u rfl
  ext i j
  have h := (compInf_smul w u ((mat f - 1) i j)).symm.trans
    (congrArg (compInf F E w) (show u • (mat f - 1) i j = 0 from congrFun (congrFun h0 i) j))
  rw [show evInf F w u = 1 from rfl, one_smul, map_zero, Matrix.sub_apply, map_sub, sub_eq_zero] at h
  rw [Matrix.map_apply, piInf, RingHom.comp_apply, h, ← RingHom.comp_apply, ← piInf]
  rw [← Matrix.map_apply (f := piInf τ), Matrix.map_one _ (map_zero _) (map_one _)]

theorem finite_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    ∀ K₂ : Subgroup (UA σ W₂.J), IsStab B K₂ → ∀ N ∈ 𝓝 (1 : UA σ W₂.J),
      ∃ s : Finset (UA σ W₂.J), (∀ k ∈ s, k ∈ K₂ ∧ k ∈ UAt σ W₂ (sndA F)) ∧
        ∀ f ∈ K₂, f ∈ UAt σ W₂ (sndA F) → ∃ k ∈ s, k⁻¹ * f ∈ N ∧ k⁻¹ * f ∈ UAt σ W₂ (sndA F) := by
  intro F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ hL K₂ hK N hN
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := (GlobalTheory.UnipCT.topFacts σ W₂.J).1
  let W₃ : Spc F E (d + d) := ⟨W₂.J, W₂.L, fun w => blkMat finSumFinEquiv (W.θ w) (-W.θ w), W₂.bas⟩
  have hL₃ : W₃.L.IsLattice E := by
    show W₂.L.IsLattice E
    rw [hL]; haveI : Submodule.IsLattice E W.L := hP.skew.lat; infer_instance
  have hθ₃ : ∀ w, IsCartan (Complex.I • W₃.J.map (B.emb w).1) (W₃.θ w) := by
    intro w
    show IsCartan (Complex.I • W₂.J.map (B.emb w).1) (blkMat finSumFinEquiv (W.θ w) (-W.θ w))
    rw [hJ, dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _), GlobalTheory.DblUnfoldCont.smul_blkMat, smul_neg]
    exact GlobalTheory.DblUnfoldCont.isCartan_dbl _ _ (hP.skew.cartan w)
  have hKc : IsCompact ((GlobalTheory.StabHaar.stabK B W₃ : Subgroup (UA σ W₃.J)) : Set (UA σ W₃.J)) :=
    GlobalTheory.DblUnfoldCont.isCompact_of_isStab_skew hP.base.cm B W₃ hL₃ hθ₃ (GlobalTheory.StabHaar.isStab_stabK B W₃)
  have hC : IsCompact ((KAt (GlobalTheory.StabHaar.stabK B W₃) (sndA F) : Subgroup (UA σ W₃.J)) : Set (UA σ W₃.J)) :=
    isCompact_KAt hKc (sndA F)
  have hCeq : ∀ f : UA σ W₂.J, (f ∈ K₂ ∧ f ∈ UAt σ W₂ (sndA F)) ↔
      f ∈ ((KAt (GlobalTheory.StabHaar.stabK B W₃) (sndA F) : Subgroup (UA σ W₃.J)) : Set (UA σ W₃.J)) := by
    intro f
    have h1 : ∀ w, (mat f).map (piInf (B.emb w)) = 1 → ∀ θ : Matrix (Fin (d + d)) (Fin (d + d)) ℂ,
        Commute ((mat f).map (piInf (B.emb w))) θ := fun w hw θ => by rw [hw]; exact Commute.one_left _
    constructor
    · rintro ⟨hf1, hf2⟩
      refine ⟨⟨fun w => h1 w (map_piInf_eq_one W₂ f hf2 (B.emb w)) _, ((hK f).1 hf1).2⟩, hf2⟩
    · rintro ⟨⟨_, hf1⟩, hf2⟩
      exact ⟨(hK f).2 ⟨fun w => h1 w (map_piInf_eq_one W₂ f hf2 (B.emb w)) _, hf1⟩, hf2⟩
  obtain ⟨t, ht, hcov⟩ := hC.elim_nhds_subcover (fun k : UA σ W₂.J => (fun f => k⁻¹ * f) ⁻¹' N) (fun k _ => by
    refine (continuous_mul_left k⁻¹).continuousAt.preimage_mem_nhds ?_
    rw [inv_mul_cancel]; exact hN)
  refine ⟨t, fun k hk => (hCeq k).2 (ht k hk), fun f hf1 hf2 => ?_⟩
  obtain ⟨k, hk, hfk⟩ := Set.mem_iUnion₂.1 (hcov ((hCeq f).1 ⟨hf1, hf2⟩))
  exact ⟨k, hk, hfk, (UAtSub σ W₂ (sndA F)).mul_mem ((UAtSub σ W₂ (sndA F)).inv_mem ((hCeq k).2 (ht k hk)).2) hf2⟩

end GlobalTheory.DblKFinCpt
