import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAutLinTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPolDataImaginaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalCompactInvariantDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumFiniteDimensionalOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpaceStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThKSpanAut

theorem polData_small_of_polMatch {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {R : RealMaps F a a'} {Rf : FinMaps F a a'} {Φ Φ'}
    (hm : PolMatch B G X R Rf Φ Φ') : Φ' ∈ PolData B G.M' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', -, hf', -, rfl, -⟩ := hm
  refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, (hf' j).1, φ' j, (hf' j).2.1, ?_, rfl⟩
  refine (T.finite_toSet.subset fun v hv => ?_)
  by_contra h
  exact hv ((hf' j).2.2 v h)

theorem isAut_small_of_le_kInf (hKP : GlobalTheory.ThK.KP) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (hT : IsTriple B G X om om') (c : E) (hc : c ≠ 0) (hcs : σ c = -c)
    (Φ : GlobalTheory.ThK.Fn F a' (a + a')) (hΦ : Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)
    (K : Subgroup (GAd σ (c • G.W.J.map σ))) (hK : ∀ x ∈ K, (toGAd hσ G.W.J hc).symm x ∈ KInf σ G.W B.emb) :
    IsAut σ (c • G.W.J.map σ) K (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) := by
  obtain ⟨K₀, -, hA⟩ := GlobalTheory.T.exists_maximal_compact_invariant_dual F E σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ
  refine ⟨hA.mod, ?_, hA.zfin⟩
  have hΦS : Φ ∈ G.M'.So B.ψ B.τ₁ := (Submodule.mem_inf.1 hΦ).2
  obtain ⟨S, hSf, -, hS⟩ := GlobalTheory.T.polynomial_datum_finite_dimensional_orbit F E σ B _ _ G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hKP
    (GlobalTheory.ThKContSmall.isPair_small hT) Φ (Submodule.mem_inf.1 hΦ).1
  let P := G.M'.So B.ψ B.τ₁
  let L : P →ₗ[ℂ] (UA σ G.W.J → ℂ) :=
    { toFun := fun Ψ => G.M'.I om' Ψ
      map_add' := fun Ψ₁ Ψ₂ => GlobalTheory.ThKAutSmallKFin.I_add_so hKP hT Ψ₁.2 Ψ₂.2
      map_smul' := fun t Ψ => GlobalTheory.ThKAutSmallKFin.I_smul G.M' om' t Ψ }
  let S' : Submodule ℂ P := S.comap P.subtype
  haveI : FiniteDimensional ℂ S := hSf
  haveI : FiniteDimensional ℂ S' :=
    FiniteDimensional.of_injective (K := ℂ) (V₂ := S) ((P.subtype.domRestrict S').codRestrict S fun x => x.2)
      fun x y e => Subtype.ext (Subtype.ext (congrArg (fun z : S => (z : GlobalTheory.ThK.Fn F a' (a + a'))) e))
  let T : P →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ) :=
    LinearMap.funLeft ℂ ℂ (toGAd hσ G.W.J hc).symm ∘ₗ L
  refine Submodule.finiteDimensional_of_le (S₂ := S'.map T) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  have hk := hS _ (hK k k.2)
  refine ⟨⟨om' (1, (toGAd hσ G.W.J hc).symm k) Φ, GlobalTheory.T.weil_representation_preserves_space hKP.base F E σ B a a' G X om om' hT _ Φ hΦS⟩, hk, ?_⟩
  funext g
  simp only [T, L, LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply, LinearMap.coe_mk, AddHom.coe_mk,
    map_mul, GlobalTheory.ThKAutSmallKFin.I_mul_right]

theorem isAut_of_mem_thetaSpan_sup : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c →
    ∀ f ∈ thetaSpanV B G X om R Rf ⊔ thetaSpanV' B G X om' R Rf,
    ∀ K : Subgroup (GAd σ (c • G.W.J.map σ)), (∀ x ∈ K, (toGAd hσ G.W.J hc).symm x ∈ KInf σ G.W B.emb) →
      IsAut σ (c • G.W.J.map σ) K (fun x => f ((toGAd hσ G.W.J hc).symm x)) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hσ c hc hσc f hf K hK
  unfold thetaSpanV thetaSpanV' at hf
  rw [← Submodule.span_union] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨Φ, Φ', hΦ', hm, rfl⟩ | ⟨Φ, Φ', hΦ', hm, rfl⟩
    · exact GlobalTheory.T.matched_pol_data_imaginary hKP F E σ B a a' G X om om' R Rf hM hσ c hc hσc Φ Φ' hΦ' hm K hK
    · exact isAut_small_of_le_kInf hKP F E σ hσ B a a' G X om om' hM.triple c hc hσc Φ'
        (Submodule.mem_inf.2 ⟨polData_small_of_polMatch hm, hΦ'⟩) K hK
  | zero => exact isAut_const σ _ K 0
  | add x y _ _ hx hy =>
    convert GlobalTheory.UAut.AutClosed.isAut_add_smul hx hy 1 1 using 1
    funext g
    simp
  | smul r x _ hx =>
    convert GlobalTheory.UAut.AutClosed.isAut_add_smul hx (isAut_const σ _ K 0) r 0 using 1
    funext g
    simp

end GlobalTheory.ThKSpanAut

end
