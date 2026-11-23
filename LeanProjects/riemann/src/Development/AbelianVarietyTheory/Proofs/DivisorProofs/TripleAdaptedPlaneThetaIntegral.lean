import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedUnipStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryCountableDiscreteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactPreimageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceAdelicCmExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinateAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinatesInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentCoordinateSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalCentralUnipotentTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMatrixContinuousCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCentralCoordinateDeterminedStatement

noncomputable section

namespace GlobalTheory.ThK.UnipDom

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem exists_haar_fundamentalDomain_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d₁) (H' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∃ (μ : MeasureTheory.Measure (GlobalTheory.ThK.unip σ G.W H')) (𝓕 : Set (GlobalTheory.ThK.unip σ G.W H')), μ.IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ G.W.J).subgroupOf (GlobalTheory.ThK.unip σ G.W H')) 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  have hcm := hT.base.cm
  have hW := hT.geo.hW
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.T.adelic_unitary_locally_compact_hausdorff F E σ _ G.W.J
  have hcl := GlobalTheory.T.isClosed_unip' F E σ _ _ G.W H'
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unip σ G.W H') := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ G.W H') := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨dc, dd⟩ := GlobalTheory.T.rational_unitary_countable_discrete F E σ _ G.W.J
  set Γ := (ratU σ G.W.J).subgroupOf (unip σ G.W H') with hΓ
  have hinj : Function.Injective fun γ : Γ => (⟨γ.1.1, γ.2⟩ : ratU σ G.W.J) :=
    fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : ratU σ G.W.J => (t : UA σ G.W.J)) h))
  haveI : Countable Γ := hinj.countable
  haveI : DiscreteTopology Γ :=
    DiscreteTopology.of_continuous_injective ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hinj
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hcA : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have halg : Continuous (algebraMap (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AE F E))
  obtain ⟨C, hC, hCa⟩ := GlobalTheory.T.adele_quotient_compact_representatives F E
  obtain ⟨K0, hK0, hK0a⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  obtain ⟨Ψ, hΨ, hΨe⟩ := GlobalTheory.T.unipotent_matrix_continuous_coordinates F E σ B _ _ G.W W₁ H' _ _ i₀ i₁ hcm hW hH
  obtain ⟨g, hg, hge⟩ := GlobalTheory.T.unipotent_central_coordinate_determined F E σ B _ _ G.W W₁ H' _ _ i₀ i₁ hcm hW hH
  obtain ⟨htr2, htr⟩ := GlobalTheory.T.trace_adelic_cm_extension F E σ hcm
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
  have hK : IsCompact K := hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (GlobalTheory.T.unitary_compact_preimage F E σ _ G.W.J Cm hCm)
  have hcov : ∀ n : unip σ G.W H', ∃ γ ∈ Γ, ∃ k ∈ K, n = γ * k := by
    intro n
    choose α hα using fun j => hCa (coA σ G.W.J H' n.1 j)
    obtain ⟨γ₁, hγ₁u, hγ₁r, hγ₁a⟩ := GlobalTheory.T.rational_unipotent_coordinate_surjective F E σ B _ _ G.W W₁ H' _ _ i₀ i₁ hcm hW hH (-α)
    have hn₁ : γ₁ * n.1 ∈ unip σ G.W H' := mul_mem hγ₁u n.2
    have ha₁ : coA σ G.W.J H' (γ₁ * n.1) ∈ C₁ := by
      intro j _
      rw [GlobalTheory.T.unipotent_coordinate_additive F E σ B _ _ G.W W₁ H' _ _ i₀ i₁ hcm hW hH γ₁ hγ₁u n.1 n.2, hγ₁a]
      simp only [Pi.add_apply, Pi.neg_apply, map_neg]
      rw [neg_add_eq_sub]
      exact hα j
    set T := Algebra.trace (AF F) (AE F E) (coC σ G.W.J H' (γ₁ * n.1)) with hTdef
    obtain ⟨x, hx⟩ := hK0a (⅟(2 : AF F) * T)
    obtain ⟨γ₂, hγ₂u, hγ₂r, hγ₂e⟩ := GlobalTheory.T.rational_central_unipotent_translate F E σ B _ _ G.W W₁ H' _ _ i₀ i₁ hcm hW hH (-x)
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
  exact GlobalTheory.Per.UnitN.exists_unit_of_cocompact Γ hK hcov

end GlobalTheory.ThK.UnipDom
