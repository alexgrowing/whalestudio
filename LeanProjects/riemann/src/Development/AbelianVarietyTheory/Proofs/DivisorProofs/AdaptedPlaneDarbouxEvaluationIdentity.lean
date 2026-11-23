import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesInsertZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxDerivativeExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativeExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneEvaluationClosureDerivativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfPlaneDerivativeVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxAdaptedPlaneEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroGaussianVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianRestrictedAdaptedPlaneStatement

noncomputable section
namespace GlobalTheory.ThK.PlaneEv
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem pol_map_ei : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M₁ : Model σ X W₁)
    (hd : d = d₁ + 2), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d), ((∀ z : Matrix (Fin n) (Fin d₁) (AE F E), co.e (z * (incM F H'.ι)ᵀ) = (ins0 hd (M₁.co.e z).1, ins0 hd (M₁.co.e z).2)) ∧
      (∀ a : Fin n → AE F E, (co.e (Matrix.vecMulVec a (incV F H'.x))).1 = 0 ∧
        ∀ p, (co.e (Matrix.vecMulVec a (incV F H'.x))).2 ((idx hd).symm (Sum.inl p)) = 0) ∧
      (∀ b : Fin n → AE F E, (co.e (Matrix.vecMulVec b (incV F H'.y))).2 = 0 ∧
        ∀ p, (co.e (Matrix.vecMulVec b (incV F H'.y))).1 ((idx hd).symm (Sum.inl p)) = 0) ∧
      ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ((Model.mk co (fun _ _ => 0) 0 ∅ : Model σ X W).Pol B.ψ B.emb).map ((ei (n := n) F hd : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁)) : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d₁)) =
      M₁.Pol B.ψ B.emb := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M₁ hd hB hX hW hH hM₁ co ⟨h1, h2, h3, hrat⟩
  classical
  set M : Model σ X W := Model.mk co (fun _ _ => 0) 0 ∅ with hMdef
  have hstd := hB.std
  obtain ⟨hS, act, real⟩ := GlobalTheory.T.darboux_derivative_existence F E σ (Fin n) (Fin d) (Fin n × Fin d) B.ψ _ _ co hstd GlobalTheory.T.archHeisenbergDerivatives_exist GlobalTheory.T.archActionReadings_compatible
  obtain ⟨hS₁, act₁, real₁⟩ := GlobalTheory.T.darboux_derivative_existence F E σ (Fin n) (Fin d₁) (Fin n × Fin d₁) B.ψ _ _ M₁.co hstd GlobalTheory.T.archHeisenbergDerivatives_exist GlobalTheory.T.archActionReadings_compatible
  have cwz : ∀ z, cw co (z * (incM F H'.ι)ᵀ) = (ins0 hd (cw M₁.co z).1, ins0 hd (cw M₁.co z).2) := by
    intro z
    simp only [cw, h1 z]
    rw [ins0_map hd (evI F) evI_zero_eq, ins0_map hd (evI F) evI_zero_eq]
  have key1 : ∀ w (z : Matrix (Fin n) (Fin d₁) (AE F E)), (z * (incM F H'.ι)ᵀ).map (piInf (B.emb w)) =
      z.map (piInf (B.emb w)) * (H'.ι.map (B.emb w).1)ᵀ := by
    intro w z
    rw [Matrix.map_mul, Matrix.transpose_map, incM_map_piInf_emb]
  have gco : ∀ f₀, M.IsGauss B.ψ B.emb f₀ → ∃ ε : InfinitePlace F → ℤˣ, ∀ u u', At (evI F) u → At (evI F) u' →
      (∀ w, u'.map (piInf (B.emb w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) →
      ∀ x, dH (cw co u').1 (cw co u').2 ⇑f₀ x = Complex.I * dH (cw co u).1 (cw co u).2 ⇑f₀ x := by
    rintro f₀ ⟨ε, hε⟩
    refine ⟨ε, fun u u' hu hu' hr x => ?_⟩
    obtain ⟨g, hg⟩ := hS (cw co u).1 (cw co u).2 f₀
    obtain ⟨g', hg'⟩ := hS (cw co u').1 (cw co u').2 f₀
    have e := hε u u' hu hu' hr g g' ((act u hu f₀ g).2 hg) ((act u' hu' f₀ g').2 hg')
    rw [← hg, ← hg', e]
    rfl
  have gtr : ∀ f₀, M.IsGauss B.ψ B.emb f₀ → M₁.IsGauss B.ψ B.emb (ei F hd f₀) := by
    intro f₀ hf₀
    obtain ⟨ε, hε⟩ := gco f₀ hf₀
    refine ⟨ε, fun z z' hz hz' hr g g' hg hg' => ?_⟩
    have hu := at_mul_right_of hz (incM F H'.ι)ᵀ
    have hu' := at_mul_right_of hz' (incM F H'.ι)ᵀ
    have hr' : ∀ w, (z' * (incM F H'.ι)ᵀ).map (piInf (B.emb w)) = (((ε w : ℤ) : ℂ) * Complex.I) •
        (X.θ w * (z * (incM F H'.ι)ᵀ).map (piInf (B.emb w)) * (W.θ w)ᵀ) := by
      intro w
      have e : (W₁.θ w)ᵀ * (H'.ι.map (B.emb w).1)ᵀ = (H'.ι.map (B.emb w).1)ᵀ * (W.θ w)ᵀ := by
        rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, (hH.cartan w).1]
      rw [key1, key1, hr w, Matrix.smul_mul]
      congr 1
      simp only [Matrix.mul_assoc, e]
    obtain ⟨h, hh⟩ := hS (ins0 hd (cw M₁.co z).1) (ins0 hd (cw M₁.co z).2) f₀
    obtain ⟨h', hh'⟩ := hS (ins0 hd (cw M₁.co z').1) (ins0 hd (cw M₁.co z').2) f₀
    have e1 : ei F hd h = g := DFunLike.coe_injective ((GlobalTheory.T.heisenberg_derivative_extension F n d d₁ hd _ _ f₀ h hh).trans ((act₁ z hz _ _).1 hg).symm)
    have e1' : ei F hd h' = g' :=
      DFunLike.coe_injective ((GlobalTheory.T.heisenberg_derivative_extension F n d d₁ hd _ _ f₀ h' hh').trans ((act₁ z' hz' _ _).1 hg').symm)
    have e3 : h' = Complex.I • h := SchwartzMap.ext fun x => by
      have := hε _ _ hu hu' hr' x
      rw [cwz, cwz] at this
      rw [SchwartzMap.smul_apply, smul_eq_mul, hh', hh]
      exact this
    rw [← e1', e3, map_smul, e1]
  have plane : ∀ f₀, M.IsGauss B.ψ B.emb f₀ → ∀ γ : Fin n × Fin d → mixedEmbedding.mixedSpace F, IsPl hd γ →
      ∃ β : Fin n × Fin d → mixedEmbedding.mixedSpace F, IsPl hd β ∧ ∃ c : ℂ, ∀ x, dH γ 0 ⇑f₀ x = c * dH 0 β ⇑f₀ x := by
    intro f₀ hf₀ γ hγ
    obtain ⟨ε, hε⟩ := gco f₀ hf₀
    obtain ⟨u, u', hu, hu', hr, hcu, hcu1, hcu2⟩ := GlobalTheory.T.darboux_adapted_plane_evaluation F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M₁ hd hB hX hW hH co h1 h2 h3 ε γ hγ
    refine ⟨(cw co u').2, hcu2, -Complex.I, fun x => ?_⟩
    have e := hε u u' hu hu' hr x
    rw [hcu, hcu1] at e
    dsimp only at e
    linear_combination Complex.I * e + dH γ 0 ⇑f₀ x * Complex.I_sq
  have P1cl : ∀ (a b : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F), ∀ g ∈ M₁.Pol B.ψ B.emb,
      ∀ g₁ : SInf F (Fin n × Fin d₁), ⇑g₁ = dH a b ⇑g → g₁ ∈ M₁.Pol B.ψ B.emb := by
    intro a b g hg g₁ hg₁
    obtain ⟨z, hz, hzab⟩ := real₁ a b
    exact Submodule.mem_sInf.2 fun N hN => hN.2 z hz g (Submodule.mem_sInf.1 hg N hN) g₁
      ((act₁ z hz g g₁).2 (by rw [hzab]; exact hg₁))
  obtain ⟨Q, hGQ, hQcl, hQei⟩ := GlobalTheory.T.plane_evaluation_closure_derivatives F n d d₁ hd (M₁.Pol B.ψ B.emb) {f₀ | M.IsGauss B.ψ B.emb f₀} hS P1cl
    (fun f₀ hf₀ => ⟨Submodule.mem_sInf.2 fun N hN => hN.1 _ (gtr f₀ hf₀), plane f₀ hf₀⟩)
  have hPQ : M.Pol B.ψ B.emb ≤ Q :=
    sInf_le ⟨fun f₀ hf₀ => hGQ hf₀, fun u hu f hf f₁ hf₁ => hQcl _ _ f hf f₁ ((act u hu f f₁).1 hf₁)⟩
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    exact hQei f (hPQ hf)
  · refine sInf_le ⟨fun g₀ hg₀ => ?_, fun z hz g hg g₁ hg₁ => ?_⟩
    · obtain ⟨f₀, hf₀ne, hf₀⟩ := GlobalTheory.T.exists_nonzero_gaussian_vector F E σ B n d r s r' s' X W M hB hX hW GlobalTheory.T.archHeisenbergDerivatives_exist GlobalTheory.T.archActionReadings_compatible
      obtain ⟨g, hgU⟩ := GlobalTheory.T.gaussian_restricted_adapted_plane F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M₁ hB hX hW hH GlobalTheory.T.archHeisenbergDerivatives_exist GlobalTheory.T.archActionReadings_compatible
      have hne : ei F hd f₀ ≠ 0 := fun h0 => hf₀ne (GlobalTheory.T.eq_zero_of_plane_derivative_vanishing F n d d₁ hd f₀ (plane f₀ hf₀) fun x₁ => by
        simpa using congrArg (fun k : SInf F (Fin n × Fin d₁) => k x₁) h0)
      obtain ⟨z, hz⟩ := hgU _ hg₀
      obtain ⟨z₀, hz₀⟩ := hgU _ (gtr f₀ hf₀)
      have hz₀ne : z₀ ≠ 0 := by
        rintro rfl
        exact hne (by rw [hz₀, zero_smul])
      refine ⟨(z / z₀) • f₀, Submodule.mem_sInf.2 fun N hN => N.smul_mem _ (hN.1 _ hf₀), ?_⟩
      show ei F hd ((z / z₀) • f₀) = g₀
      rw [map_smul, hz₀, hz, smul_smul, div_mul_cancel₀ _ hz₀ne]
    · obtain ⟨f, hf, rfl⟩ := hg
      obtain ⟨h, hh⟩ := hS (ins0 hd (cw M₁.co z).1) (ins0 hd (cw M₁.co z).2) f
      have hu := at_mul_right_of hz (incM F H'.ι)ᵀ
      refine ⟨h, Submodule.mem_sInf.2 fun N hN => hN.2 _ hu f (Submodule.mem_sInf.1 hf N hN) h
        ((act _ hu f h).2 (by rw [cwz]; exact hh)), ?_⟩
      exact DFunLike.coe_injective ((GlobalTheory.T.heisenberg_derivative_extension F n d d₁ hd _ _ f h hh).trans ((act₁ z hz _ _).1 hg₁).symm)

end GlobalTheory.ThK.PlaneEv

end
