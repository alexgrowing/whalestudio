import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedUnipStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryCountableDiscreteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactPreimageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceAdelicCmExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentCoordSurjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalCentralUnipotentExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMatrixCoordParamStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordImaginaryPartStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.UnipDom
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.UnipDomPlane

theorem exists_haar_fundamentalDomain_one_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (Y.J j i) = -Y.J i j) → IsIsoPlane σ B H Y Y₁ →
      ∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro F E _ _ _ _ _ σ B hB n n₁ Y Y₁ H hs hH
  have hcm := hB.cm
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.T.adelic_unitary_locally_compact_hausdorff F E σ _ Y.J
  have hcl := GlobalTheory.T.isClosed_unip' F E σ _ _ Y H
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unip σ Y H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ Y H) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨dc, dd⟩ := GlobalTheory.T.rational_unitary_countable_discrete F E σ _ Y.J
  set Γ := (ratU σ Y.J).subgroupOf (unip σ Y H) with hΓ
  have hinj : Function.Injective fun γ : Γ => (⟨γ.1.1, γ.2⟩ : ratU σ Y.J) :=
    fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : ratU σ Y.J => (t : UA σ Y.J)) h))
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
  obtain ⟨Ψ, hΨ, hΨe⟩ := GlobalTheory.T.unipotent_matrix_coord_param F E σ B _ _ Y Y₁ H hcm hs hH
  obtain ⟨g, hg, hge⟩ := GlobalTheory.T.unipotent_coord_imaginary_part F E σ B _ _ Y Y₁ H hcm hs hH
  obtain ⟨htr2, htr⟩ := GlobalTheory.T.trace_adelic_cm_extension F E σ hcm
  let C₁ : Set (Fin n₁ → AE F E) := Set.univ.pi fun _ => C
  have hC₁ : IsCompact C₁ := isCompact_univ_pi fun _ => hC
  let C₃ : Set (AF F) := (fun t => (2 : AF F) * t) '' K0
  have hC₃ : IsCompact C₃ := hK0.image (continuous_const.mul continuous_id)
  let f₂ : AF F × (Fin n₁ → AE F E) → AE F E := fun p => ⅟(2 : AF F) • (algebraMap (AF F) (AE F E) p.1 + g p.2)
  have hf₂ : Continuous f₂ :=
    Continuous.smul (continuous_const : Continuous fun _ : AF F × (Fin n₁ → AE F E) => ⅟(2 : AF F))
      ((halg.comp continuous_fst).add (hg.comp continuous_snd))
  let C₂ : Set (AE F E) := f₂ '' (C₃ ×ˢ C₁)
  have hC₂ : IsCompact C₂ := (hC₃.prod hC₁).image hf₂
  let Cm : Set (Matrix (Fin n) (Fin n) (AE F E)) :=
    Ψ '' (C₁ ×ˢ C₂) ∪ (fun p : (Fin n₁ → AE F E) × AE F E => Ψ (-p.1, -cA σ p.2)) '' (C₁ ×ˢ C₂)
  have hCm : IsCompact Cm := ((hC₁.prod hC₂).image hΨ).union ((hC₁.prod hC₂).image
    (hΨ.comp ((continuous_fst.neg).prodMk ((hcA.comp continuous_snd).neg))))
  let K : Set (unip σ Y H) := Subtype.val ⁻¹' {x : UA σ Y.J | mat x ∈ Cm ∧ mat x⁻¹ ∈ Cm}
  have hK : IsCompact K := hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (GlobalTheory.T.unitary_compact_preimage F E σ _ Y.J Cm hCm)
  have hcov : ∀ m₀ : unip σ Y H, ∃ γ ∈ Γ, ∃ k ∈ K, m₀ = γ * k := by
    intro m₀
    choose α hα using fun j => hCa (coA σ Y.J H m₀.1 j)
    obtain ⟨γ₁, hγ₁u, hγ₁r, hγ₁a⟩ := GlobalTheory.T.rational_unipotent_coord_surj F E σ B _ _ Y Y₁ H hcm hs hH (-α)
    have hn₁ : γ₁ * m₀.1 ∈ unip σ Y H := mul_mem hγ₁u m₀.2
    have ha₁ : coA σ Y.J H (γ₁ * m₀.1) ∈ C₁ := by
      intro j _
      rw [GlobalTheory.T.unipotent_coord_additive F E σ B _ _ Y Y₁ H hcm hs hH γ₁ hγ₁u m₀.1 m₀.2, hγ₁a]
      simp only [Pi.add_apply, Pi.neg_apply, map_neg]
      rw [neg_add_eq_sub]
      exact hα j
    set T := Algebra.trace (AF F) (AE F E) (coC σ Y.J H (γ₁ * m₀.1)) with hTdef
    obtain ⟨x, hx⟩ := hK0a (⅟(2 : AF F) * T)
    obtain ⟨γ₂, hγ₂u, hγ₂r, hγ₂e⟩ := GlobalTheory.T.rational_central_unipotent_exists F E σ B _ _ Y Y₁ H hcm hs hH (-x)
    set m := γ₂ * (γ₁ * m₀.1) with hm
    have hn₂ : m ∈ unip σ Y H := mul_mem hγ₂u hn₁
    obtain ⟨ha₂, hc₂⟩ := hγ₂e _ hn₁
    have hA₂ : coA σ Y.J H m ∈ C₁ := ha₂ ▸ ha₁
    have htr₂ : Algebra.trace (AF F) (AE F E) (coC σ Y.J H m) ∈ C₃ := by
      refine ⟨_, hx, ?_⟩
      rw [hc₂, map_add, htr2, ← hTdef]
      show (2 : AF F) * (⅟(2 : AF F) * T - algebraMap F (AdeleRing (𝓞 F) F) x) = _
      rw [mul_sub, ← mul_assoc, mul_invOf_self', one_mul, map_neg]
      ring
    have hC₂m : coC σ Y.J H m ∈ C₂ := by
      refine ⟨(Algebra.trace (AF F) (AE F E) (coC σ Y.J H m), coA σ Y.J H m), ⟨htr₂, hA₂⟩, ?_⟩
      show ⅟(2 : AF F) • (algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) (coC σ Y.J H m)) +
        g (coA σ Y.J H m)) = coC σ Y.J H m
      rw [htr, ← hge _ hn₂, add_add_sub_cancel, ← two_smul (AF F), smul_smul, invOf_mul_self', one_smul]
    refine ⟨⟨(γ₂ * γ₁)⁻¹, inv_mem (mul_mem hγ₂u hγ₁u)⟩,
      (Subgroup.mem_subgroupOf).2 (inv_mem (mul_mem hγ₂r hγ₁r)), ⟨m, hn₂⟩, ⟨?_, ?_⟩, ?_⟩
    · show mat m ∈ Cm
      exact Or.inl ⟨(coA σ Y.J H m, coC σ Y.J H m), ⟨hA₂, hC₂m⟩, (hΨe _ hn₂).symm⟩
    · show mat m⁻¹ ∈ Cm
      refine Or.inr ⟨(coA σ Y.J H m, coC σ Y.J H m), ⟨hA₂, hC₂m⟩, ?_⟩
      obtain ⟨e1, e2⟩ := GlobalTheory.T.unipotent_coord_inverse F E σ B _ _ Y Y₁ H hcm hs hH _ hn₂
      show Ψ (-coA σ Y.J H m, -cA σ (coC σ Y.J H m)) = mat m⁻¹
      rw [hΨe _ (inv_mem hn₂), e1, e2]
    · exact Subtype.ext (by simp [hm, mul_assoc])
  exact GlobalTheory.Per.UnitN.exists_unit_of_cocompact Γ hK hcov

end GlobalTheory.ThK.UnipDomPlane
