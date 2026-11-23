import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroRestrictionNonzeroContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictionAndProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictionPreservesAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanesDoubleRestrictionModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanesDarbouxReorderingStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.AdaptEv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isEv_restrL (B : Base F E) {n d n₁ d₁ m : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁}
    {W₁ : Spc F E d₁} (Ma : Model σ X W) (M₁ : Model σ X₁ W₁) (ι₀ : Matrix (Fin n) (Fin n₁) E)
    (ι₀' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (eq : Fin n × Fin d ≃ Fin m ⊕ (Fin n₁ × Fin d₁)) (A : ∀ v : Pl F, (Fin m → Fv F v) → ℂ)
    (h1 : ∀ z, Ma.co.e (incM F ι₀ * z * (incM F ι₀')ᵀ) = (ext0 eq (M₁.co.e z).1, ext0 eq (M₁.co.e z).2))
    (h2 : ∀ u ∈ I, (Ma.co.e u).1 = 0 ∧ ∀ j, (Ma.co.e u).2 (eq.symm (Sum.inr j)) = 0)
    (hA : ∀ v, A v ∈ SB _ ∧ A v 0 = 1) (hv : ∀ v, Ma.vac v = prodVac eq (A v) (M₁.vac v)) :
    IsEv B Ma M₁ ι₀ ι₀' I (restrL eq) := by
  obtain ⟨ei, hne, hei⟩ := GlobalTheory.T.extend_by_zero_restriction_nonzero_continuous F eq
  refine ⟨GlobalTheory.T.restriction_preserves_adelic_schwartz F eq, ?_, ?_, ⟨ei, fun _ => restrL eq, hne, fun v => ⟨?_, ?_⟩, ?_⟩⟩
  · intro z Φ _
    funext y
    simp only [restrL_apply, Darboux.rho, schr, h1 z]
    rw [dotProduct_ext0, dotProduct_ext0, ← matrixExtendByZero_add]
  · intro u hu Φ _
    funext y
    obtain ⟨hu1, hu2⟩ := h2 u hu
    simp only [restrL_apply, Darboux.rho, schr, hu1, ext0_dotProduct_of eq y _ hu2, add_zero, zero_dotProduct, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · funext y
    rw [restrL_apply, hv, prodVac_ext0, (hA v).2, one_mul]
  · refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun g hg => (GlobalTheory.T.schwartz_bruhat_restriction_and_product eq).1 g hg) fun φ hφ => ?_
    refine ⟨prodVac eq (A v) φ, (GlobalTheory.T.schwartz_bruhat_restriction_and_product eq).2 _ (hA v).1 φ hφ, ?_⟩
    funext y
    show restrL eq _ y = _
    rw [restrL_apply, prodVac_ext0, (hA v).2, one_mul]
  · intro f φ _ _
    funext y
    have hc : ∀ {S : Type} [Zero S] (g : AF F → S), g 0 = 0 →
        (fun k => g (ext0 eq y k)) = ext0 eq (fun i => g (y i)) := by
      intro S _ g hg
      funext k
      simp only [ext0]
      cases eq k <;> simp [hg]
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ (ext0 eq y) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) (fun v => restrL eq (φ v)) y
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hei, restrL_apply]
    rw [hc (evI F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))]
    congr 1
    refine finprod_congr fun v => ?_
    rw [hc (evFin F v) (map_zero _)]

end GlobalTheory.ThK.AdaptEv

namespace GlobalTheory.ThK.AdaptEv

end GlobalTheory.ThK.AdaptEv

open GlobalTheory.ThK.AdaptEv in

theorem GlobalTheory.ThK.AdaptEv.exists_isEv_isoA : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁)
    (H' : Plane E d d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∃ (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), Ma.IsGood B.ψ ∧ IsEv B Ma M₁ H.ι H'.ι (isoA H H') e := by
  intro _ F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hB hX hW hM hH hH' hM₁
  obtain ⟨co, eq, hrat, h1, h2, h2'⟩ := GlobalTheory.T.adapted_planes_double_restriction_model F E σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M₁ hB hX hW hH hH' hM₁
  obtain ⟨A, hA, hstd⟩ := GlobalTheory.T.adapted_planes_darboux_reordering F E σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M₁ co eq hB hX hW hH hH' hM₁
    hrat h1 h2 h2'
  let Ma : Model σ X W := ⟨co, fun v => prodVac eq (A v) (M₁.vac v), M.μ, M.dom⟩
  refine ⟨Ma, restrL eq, ⟨hrat, fun v => (hA v).2.2, ?_, hM.haar, hM.dom⟩,
    isEv_restrL B Ma M₁ H.ι H'.ι (isoA H H') eq A h1 h2 (fun v => ⟨(hA v).1, (hA v).2.1⟩) fun _ => rfl⟩
  filter_upwards [hstd, hM₁.std] with v hv hv₁
  show prodVac eq (A v) (M₁.vac v) = _
  rw [hv, hv₁]
  exact prodVac_indicator eq (v.adicCompletionIntegers F : Set (Fv F v))
