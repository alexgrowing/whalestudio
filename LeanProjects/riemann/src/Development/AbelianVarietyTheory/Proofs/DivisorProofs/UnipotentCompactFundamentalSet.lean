import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedUnip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactRepresentatives
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceAdelicCmExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinateAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalCentralUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinatesInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentCoordinateSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMatrixContinuousCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCentralCoordinateDeterminedStatement

noncomputable section

namespace GlobalTheory.ThK.UnipCocompact

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.UnipDom
open GlobalTheory.Doubling (absE)

theorem exists_compact_rat_mul_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ →
    ∃ K : Set (unip σ G.W H'), IsCompact K ∧ ∀ u : unip σ G.W H', ∃ γ ∈ (ratU σ G.W.J).subgroupOf (unip σ G.W H'), γ * u ∈ K := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  have hcm := hT.base.cm
  have hW := hT.geo.hW
  have hcl := GlobalTheory.ThK.UnipClosed.isClosed_unip F E σ _ _ G.W H'
  set Γ := (ratU σ G.W.J).subgroupOf (unip σ G.W H') with hΓ
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hcA : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have halg : Continuous (algebraMap (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AE F E))
  obtain ⟨C, hC, hCa⟩ := GlobalTheory.AdeleCocompactExt.exists_compact_adele_ext F E
  obtain ⟨K0, hK0, hK0a⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  obtain ⟨Ψ, hΨ, hΨe⟩ := GlobalTheory.T.unipotent_matrix_continuous_coordinates F E σ B _ _ G.W W₁ H' _ _ i₀ i₁ hcm hW hH
  obtain ⟨g, hg, hge⟩ := GlobalTheory.T.unipotent_central_coordinate_determined F E σ B _ _ G.W W₁ H' _ _ i₀ i₁ hcm hW hH
  obtain ⟨htr2, htr⟩ := GlobalTheory.CMTrace.adele_trace F E σ hcm
  let C₁ : Set (Fin d₁ → AE F E) := Set.univ.pi fun _ => C
  have hC₁ : IsCompact C₁ := isCompact_univ_pi fun _ => hC
  let C₃ : Set (AF F) := (fun t => (2 : AF F) * t) '' K0
  have hC₃ : IsCompact C₃ := hK0.image (continuous_const.mul continuous_id)
  let f₂ : AF F × (Fin d₁ → AE F E) → AE F E := fun p => ⅟(2 : AF F) • (algebraMap (AF F) (AE F E) p.1 + g p.2)
  have hf₂ : Continuous f₂ :=
    Continuous.smul (continuous_const : Continuous fun _ : AF F × (Fin d₁ → AE F E) => ⅟(2 : AF F))
      ((halg.comp continuous_fst).add (hg.comp continuous_snd))
  let C₂ : Set (AE F E) := f₂ '' (C₃ ×ˢ C₁)
  have hC₂ : IsCompact C₂ := (hC₃.prod hC₁).image hf₂
  let Cm : Set (Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) :=
    Ψ '' (C₁ ×ˢ C₂) ∪ (fun p : (Fin d₁ → AE F E) × AE F E => Ψ (-p.1, -cA σ p.2)) '' (C₁ ×ˢ C₂)
  have hCm : IsCompact Cm := ((hC₁.prod hC₂).image hΨ).union ((hC₁.prod hC₂).image
    (hΨ.comp ((continuous_fst.neg).prodMk ((hcA.comp continuous_snd).neg))))
  let K : Set (unip σ G.W H') := Subtype.val ⁻¹' {x : UA σ G.W.J | mat x ∈ Cm ∧ mat x⁻¹ ∈ Cm}
  have hK : IsCompact K := hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (GlobalTheory.ThK.UnipDom.isCompact_setOf_mat_mem F E σ _ G.W.J Cm hCm)
  have hcov : ∀ n : unip σ G.W H', ∃ γ ∈ Γ, ∃ k ∈ K, n = γ * k := by
    intro n
    choose α hα using fun j => hCa (coA σ G.W.J H' n.1 j)
    obtain ⟨γ₁, hγ₁u, hγ₁r, hγ₁a⟩ := GlobalTheory.T.rational_unipotent_coordinate_surjective F E σ B _ _ G.W W₁ H' _ _ i₀ i₁ hcm hW hH (-α)
    have hn₁ : γ₁ * n.1 ∈ unip σ G.W H' := mul_mem hγ₁u n.2
    have ha₁ : coA σ G.W.J H' (γ₁ * n.1) ∈ C₁ := by
      intro j _
      rw [GlobalTheory.ThK.UnipDom.coA_mul_of_mem_unip F E σ B _ _ G.W W₁ H' _ _ i₀ i₁ hcm hW hH γ₁ hγ₁u n.1 n.2, hγ₁a]
      simp only [Pi.add_apply, Pi.neg_apply, map_neg]
      rw [neg_add_eq_sub]
      exact hα j
    set T := Algebra.trace (AF F) (AE F E) (coC σ G.W.J H' (γ₁ * n.1)) with hTdef
    obtain ⟨x, hx⟩ := hK0a (⅟(2 : AF F) * T)
    obtain ⟨γ₂, hγ₂u, hγ₂r, hγ₂e⟩ := GlobalTheory.ThK.UnipDom.RatCentral.exists_rat_translate_coC F E σ B _ _ G.W W₁ H' _ _ i₀ i₁ hcm hW hH (-x)
    set m := γ₂ * (γ₁ * n.1) with hm
    have hn₂ : m ∈ unip σ G.W H' := mul_mem hγ₂u hn₁
    obtain ⟨ha₂, hc₂⟩ := hγ₂e _ hn₁
    have hA₂ : coA σ G.W.J H' m ∈ C₁ := ha₂ ▸ ha₁
    have htr₂ : Algebra.trace (AF F) (AE F E) (coC σ G.W.J H' m) ∈ C₃ := by
      refine ⟨_, hx, ?_⟩
      rw [hc₂, map_add, htr2, ← hTdef]
      show (2 : AF F) * (⅟(2 : AF F) * T - algebraMap F (AdeleRing (𝓞 F) F) x) = _
      rw [mul_sub, ← mul_assoc, mul_invOf_self', one_mul, map_neg]
      ring
    have hC₂m : coC σ G.W.J H' m ∈ C₂ := by
      refine ⟨(Algebra.trace (AF F) (AE F E) (coC σ G.W.J H' m), coA σ G.W.J H' m), ⟨htr₂, hA₂⟩, ?_⟩
      show ⅟(2 : AF F) • (algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) (coC σ G.W.J H' m)) +
        g (coA σ G.W.J H' m)) = coC σ G.W.J H' m
      rw [htr, ← hge _ hn₂, add_add_sub_cancel, ← two_smul (AF F), smul_smul, invOf_mul_self', one_smul]
    refine ⟨⟨(γ₂ * γ₁)⁻¹, inv_mem (mul_mem hγ₂u hγ₁u)⟩,
      (Subgroup.mem_subgroupOf).2 (inv_mem (mul_mem hγ₂r hγ₁r)), ⟨m, hn₂⟩, ⟨?_, ?_⟩, ?_⟩
    · show mat m ∈ Cm
      exact Or.inl ⟨(coA σ G.W.J H' m, coC σ G.W.J H' m), ⟨hA₂, hC₂m⟩, (hΨe _ hn₂).symm⟩
    · show mat m⁻¹ ∈ Cm
      refine Or.inr ⟨(coA σ G.W.J H' m, coC σ G.W.J H' m), ⟨hA₂, hC₂m⟩, ?_⟩
      obtain ⟨e1, e2⟩ := GlobalTheory.T.unipotent_coordinates_inverse F E σ B _ _ G.W W₁ H' _ _ i₀ i₁ hcm hW hH _ hn₂
      show Ψ (-coA σ G.W.J H' m, -cA σ (coC σ G.W.J H' m)) = mat m⁻¹
      rw [hΨe _ (inv_mem hn₂), e1, e2]
    · exact Subtype.ext (by simp [hm, mul_assoc])
  refine ⟨K, hK, fun n => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
  refine ⟨γ⁻¹, Γ.inv_mem hγ, ?_⟩
  simpa using hk

end GlobalTheory.ThK.UnipCocompact
