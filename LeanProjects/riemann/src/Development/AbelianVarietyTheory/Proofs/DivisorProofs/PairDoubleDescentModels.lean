import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneDarbouxCoordinatesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneDarbouxCoordinatesCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicEvaluationPreservesSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEvaluationSchwartzBruhatImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenIntertwinerModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerArchimedeanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductSchwartzGlue

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.EvTwoNe

open GlobalTheory.ThK.PlaneEv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_one_eq {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem ei_surjective {n d d₁ : ℕ} (hd : d = d₁ + 2) : Function.Surjective (ei (n := n) F hd) := by
  classical
  intro f
  let b : ContDiffBump (0 : Fin n × Fin 2 → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hs : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  obtain ⟨g, hg⟩ := GlobalTheory.ThK.EvAt0.SchwartzProd.exists_prod hd (hs.toSchwartzMap hc) f
  refine ⟨g, ?_⟩
  ext x
  rw [ei_apply, hg]
  have h2 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  have e1 : (fun p => ins0 hd x ((GlobalTheory.ThK.EvAt0.idx hd).symm (Sum.inr p))) = 0 := funext fun p => planeZeroInsertion_apply_inr hd x p
  have e2 : (fun q => ins0 hd x ((GlobalTheory.ThK.EvAt0.idx hd).symm (Sum.inl q))) = x := funext fun q => planeZeroInsertion_apply_inl hd x q
  rw [e1, e2]
  simp [h2]

theorem infRel_surjective (hP : GlobalTheory.FunPr.Hypotheses₂) (B : Base F E) {n d d₁ r s r' s' i₀ i₁ : ℕ} {X : Spc F E n} {W : Spc F E d}
    {W₁ : Spc F E d₁} {H' : Plane E d d₁} {M : Model σ X W} {M₁ : Model σ X W₁} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ) (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (hM₁ : M₁.IsGood B.ψ)
    (T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁)) (hT : T ≠ 0) (hR : GlobalTheory.ThK.EvUniq.InfRel B M M₁ H' T) :
    Function.Surjective T := by
  have hd : d = d₁ + 2 := hH.rank
  obtain ⟨co, hco⟩ := GlobalTheory.T.adapted_plane_darboux_coordinates_exist F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M₁ hd hB hX hW hH hM₁
  obtain ⟨vac, hvac, hstd, hres⟩ := GlobalTheory.T.exists_vacuum_family_eventually_indicator_ev_eq F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M₁ hd hB hX hW hH hM₁ co hco
  obtain ⟨hlow, hmulX, -, hrat⟩ := hco
  let Ma : Model σ X W := ⟨co, vac, M.μ, M.dom⟩
  have hMa : Ma.IsGood B.ψ := ⟨hrat, hvac, hstd, hM.haar, hM.dom⟩
  obtain ⟨e₁, h₁, ei₁, ev₁, hs₁, -, hv₁, hl₁⟩ := GlobalTheory.T.exists_eigen_intertwiner_models hP F E σ B n d r s r' s' X W M Ma hB hX hW hM hMa

  have heis₂ : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), evA F hd (Ma.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z *
      (incM F H'.ι)ᵀ) Φ) = M₁.co.rho B.ψ z (evA F hd Φ) := by
    intro z Φ _
    funext x
    simp only [evA_apply, Darboux.rho, schr, incM_one_eq, Matrix.one_mul, Ma]
    rw [hlow z, ins0_dotProduct_ins0, ins0_dotProduct_ins0, ← ins0_add]
  have hinv₂ : ∀ u ∈ iso0 (F := F) n H', ∀ Φ ∈ schA F (Fin n × Fin d), evA F hd (Ma.co.rho B.ψ u Φ) = evA F hd Φ := by
    rintro u ⟨y, rfl⟩ Φ _
    funext x
    simp only [evA_apply, Darboux.rho, schr, Ma]
    have h0 : (fun p => (co.e (Matrix.vecMulVec y (incV F H'.x))).2 ((idx hd).symm (Sum.inl p))) = 0 :=
      funext (hmulX y).2
    rw [(hmulX y).1, ins0_dotProduct, h0, dotProduct_zero, zero_dotProduct, mul_zero, add_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul]

  have heis₁ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e₁ (M.co.rho B.ψ u Φ) = Ma.co.rho B.ψ u (e₁ Φ) := by
    intro u Φ hΦ
    have := h₁.Heisenberg₂ u Φ hΦ
    rwa [incM_one_eq, incM_one_eq, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this
  let ei₀ : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁) := (ei F hd).comp ei₁
  let ev₀ : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ := fun v => (ev hd v).comp (ev₁ v)
  have hs₀ : Function.Surjective ei₀ := (ei_surjective hd).comp hs₁
  have hne₀ : ei₀ ≠ 0 := by
    intro h0
    apply ei_ne_zero (n := n) (F := F) hd
    ext1 g
    obtain ⟨g', rfl⟩ := hs₁ g
    exact congrArg (fun S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁) => S g') h0
  have hv₀ : ∀ v, ev₀ v (M.vac v) = M₁.vac v ∧ (SB _).map (ev₀ v) = SB _ := fun v => by
    refine ⟨?_, ?_⟩
    · show ev hd v (ev₁ v (M.vac v)) = M₁.vac v
      rw [(hv₁ v).1]; exact hres v
    · show (SB _).map ((ev hd v).comp (ev₁ v)) = SB _
      rw [Submodule.map_comp, (hv₁ v).2, GlobalTheory.T.local_evaluation_schwartz_bruhat_image F n d d₁ hd v]
  have hl₀ : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      (evA F hd ∘ₗ e₁) (pure f φ) = pure (ei₀ f) fun v => ev₀ v (φ v) := by
    intro f φ hφ hc
    simp only [LinearMap.comp_apply]
    rw [hl₁ f φ hφ hc, evA_pure]
    rfl
  have hE : IsEv B M M₁ 1 H'.ι (iso0 n H') (evA F hd ∘ₗ e₁) := by
    refine ⟨fun Φ hΦ => GlobalTheory.T.adelic_evaluation_preserves_schwartz F n d d₁ hd _ (h₁.maps Φ hΦ), fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_,
      ⟨ei₀, ev₀, hne₀, hv₀, hl₀⟩⟩
    · simp only [LinearMap.comp_apply]
      rw [heis₁ _ Φ hΦ, heis₂ z _ (h₁.maps Φ hΦ)]
    · simp only [LinearMap.comp_apply]
      rw [heis₁ _ Φ hΦ, hinv₂ u hu _ (h₁.maps Φ hΦ)]
  have hR₀ := GlobalTheory.ThK.EvUniq.infRel_of_isEv F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ _ hE
    ei₀ ev₀ hne₀ hv₀ hl₀
  obtain ⟨c, hc⟩ := GlobalTheory.T.eigen_intertwiner_archimedean hP F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ T ei₀ hT hR hR₀
  intro g
  obtain ⟨f, hf⟩ := hs₀ g
  refine ⟨c • f, ?_⟩
  rw [map_smul, ← ContinuousLinearMap.smul_apply, ← hc, hf]

theorem comp_ne_zero : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ : ℕ) (Ma : Model σ X W₁) (oma : Rep σ X W₁) (r₁ s₁ : ℕ)
    (M₁ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B Ma χX χW oma r s r₁ s₁ → M₁.IsGood B.ψ →
    ∀ e₁ e₂, IsEv B M Ma 1 H'.ι (iso0 n H') e₁ → IsEv B Ma M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₂ →
    ∃ Φ ∈ schA F (Fin n × Fin d), e₂ (e₁ Φ) ≠ 0 := by
  intro hP F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M χX χW om r s r' s' hPr H H' j₀ j₁ i₀ i₁ Ma oma r₁ s₁ M₁ hH hH' hPa hM₁
    e₁ e₂ he₁ he₂
  obtain ⟨ei₁, ev₁, hei₁, hv₁, hl₁⟩ := he₁.loc
  obtain ⟨ei₂, ev₂, hei₂, hv₂, hl₂⟩ := he₂.loc
  have hR := GlobalTheory.ThK.EvUniq.infRel_of_isEv F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M Ma hPr.base hPr.herm hPr.skew
    hPr.good hH' hPa.good e₁ he₁ ei₁ ev₁ hei₁ hv₁ hl₁
  have hsurj := infRel_surjective hP B hPr.base hPr.herm hPr.skew hPr.good hH' hPa.good ei₁ hei₁ hR
  obtain ⟨g, hg⟩ : ∃ g, ei₂ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei₂ (ContinuousLinearMap.ext h)
  obtain ⟨f, rfl⟩ := hsurj g
  have hvacM : ∀ v, M.vac v ∈ SB _ := fun v => (hPr.good.vac v).1
  refine ⟨pure f M.vac, GlobalTheory.TensUniq.pure_mem_schA f M.vac hvacM hPr.good.std, ?_⟩
  rw [hl₁ f M.vac hvacM (Filter.Eventually.of_forall fun _ => rfl)]
  have e1 : (fun v => ev₁ v (M.vac v)) = Ma.vac := funext fun v => (hv₁ v).1
  rw [e1, hl₂ (ei₁ f) Ma.vac (fun v => (hPa.good.vac v).1) (Filter.Eventually.of_forall fun _ => rfl)]
  have e2 : (fun v => ev₂ v (Ma.vac v)) = M₁.vac := funext fun v => (hv₂ v).1
  rw [e2]
  exact GlobalTheory.ThK.EvNeZero.pure_ne_zero (ei₂ (ei₁ f)) hg M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std

end GlobalTheory.ThK.EvTwoNe
