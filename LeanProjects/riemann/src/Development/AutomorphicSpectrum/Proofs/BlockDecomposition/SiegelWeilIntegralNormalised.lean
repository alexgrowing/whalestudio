import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem fubini_starN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (fouH σ ψ db τ) db → (∀ z, ∫ y, fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∫ y, fouH σ ψ db τ y * (starN σ J ψ dx Φ y * chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) ∂dx := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ ψ hψ dx hdx db hdb Φ hΦ τ hτ hinv T hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, hTr, -, hB, hCl, hG⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  have := hB n M
  have : BorelSpace (AF F) := ⟨rfl⟩
  have : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AF F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AF F ⊗[F] E))
  have : LocallyCompactSpace (HermR (AF F) σ n) := (hCl n).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (HermR (AF F) σ n) :=
    (hCl n).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have := hdx.1
  have := hdb.1
  have : SFinite dx := inferInstance
  have : SFinite db := inferInstance
  set Th := fouH σ ψ db τ with hTh
  set S : HermR (AF F) σ n := hermOf (AF F) σ T hT with hS
  obtain ⟨hψc, hψn, -⟩ := hψ

  have hstar : ∀ (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E),
      algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x)) =
      pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x) := by
    intro y x
    simp only [pairHerm, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rfl
  have hchi : ∀ y : HermR (AF F) σ n, chiT σ ψ T y = ψ (-pairHerm (AF F) σ n y S) := by
    intro y
    have e : Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) =
        ∑ a, ∑ b, (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b *
          (S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) b a := by
      rw [Matrix.trace_mul_comm]
      rfl
    rw [chiT, e]
    rfl
  have hsub : ∀ y z w : HermR (AF F) σ n,
      pairHerm (AF F) σ n y z + -pairHerm (AF F) σ n y w = pairHerm (AF F) σ n y (z - w) := by
    intro y z w
    simp only [pairHerm, AddSubgroup.coe_sub, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, map_sub]
    ring
  have hpc : Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
      pairHerm (AF F) σ n z.1 (gramH hCM hJ (AF F) z.2 - S) := by
    have hg : Continuous (gramR (AF F) σ J : (Fin n → Fin M → AF F ⊗[F] E) → _) := hG n M J
    show Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
      algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (∑ a, ∑ b, (z.1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b *
          (gramR (AF F) σ J z.2 b a - (S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) b a))
    refine continuous_const.mul (hTr.comp (continuous_finset_sum _ fun a _ =>
      continuous_finset_sum _ fun b _ => ?_))
    exact ((continuous_subtype_val.comp continuous_fst).matrix_elem a b).mul
      (((hg.comp continuous_snd).matrix_elem b a).sub continuous_const)
  have hint : Integrable (Function.uncurry fun (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E) =>
      Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S)))) (db.prod dx) := by
    have h0 : Integrable (fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) => Th z.1 * Φ z.2)
        (db.prod dx) := hτ.mul_prod hΦ
    have hc : Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
        ψ (pairHerm (AF F) σ n z.1 (gramH hCM hJ (AF F) z.2 - S)) := hψc.comp hpc
    refine h0.mono ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have := h0.aestronglyMeasurable.mul hc.aestronglyMeasurable
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.uncurry, Pi.mul_apply, mul_assoc]
    · simp only [Function.uncurry, norm_mul, hψn, mul_one, le_refl]
  have hL : ∀ y, Th y * (starN σ J ψ dx Φ y * chiT σ ψ T y) =
      ∫ x, Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S))) ∂dx := by
    intro y
    rw [integral_const_mul, starN, ← integral_mul_const, hchi]
    congr 2
    funext x
    rw [hstar, mul_assoc, ← AddChar.map_add_eq_mul, hsub]
  have hR : ∀ x, ∫ y, Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S))) ∂db =
      Φ x * τ (S - gramH hCM hJ (AF F) x) := by
    intro x
    have := hinv (gramH hCM hJ (AF F) x - S)
    rw [neg_sub] at this
    rw [← this, ← integral_const_mul]
    congr 1
    funext y
    ring
  simp_rw [hL]
  rw [integral_integral_swap hint]
  simp_rw [hR]

end GlobalTheory.CompanionTheory.SiegelND.Coef
