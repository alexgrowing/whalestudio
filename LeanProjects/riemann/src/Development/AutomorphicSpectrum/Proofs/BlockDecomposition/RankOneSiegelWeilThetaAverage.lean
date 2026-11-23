import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem actW_rat_one {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix (Fin 1) (Fin 1) E) (g : HA (AF F) σ J) (X : Fin 1 → Fin 1 → E) (a i : Fin 1) :
    actW (AF F) σ J g (ratTup (AF F) X) a i = (ue (AF F) σ J g : AF F ⊗[F] E) * inclR (AF F) (X a i) := by
  have e : ((ue (AF F) σ J g : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (HA.mat (AF F) σ J g).val 0 0 := by
    simp [ue, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  rw [e]
  simp only [actW, actTup, Matrix.mulVec, dotProduct, ratTup, Fin.sum_univ_one, Subsingleton.elim i 0,
    Subsingleton.elim a 0]

theorem mean_eq_lint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ 1 J μ → IsFDH F E σ 1 J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ x : (AF F ⊗[F] E)ˣ, mean σ J μ 𝓕 φ A x = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, Th φ A (x * ue (AF F) σ J h⁻¹) ∂μ ∧ Measurable fun h : HA (AF F) σ J => Th φ A (x * ue (AF F) σ J h⁻¹) := by
  intro F E _ _ _ _ _ σ hcm J hJ μ 𝓕 hμ h𝓕 d b S φ A hT x
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 1
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm 1 J hJ (AF F)
  obtain ⟨ac, -, -, -⟩ := hact 1
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨k1, -, -, -, -, -, -, k8, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)
  have := k8 1 1
  obtain ⟨t1, t2, t3, t4, t5, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1
  obtain ⟨hφc, -, hφ0, -, hAS, hAoff⟩ := hT
  have hs : ∀ v, Continuous fun X : Fin 1 → Fin 1 → AF F ⊗[F] E => projV v (projFin X) := fun v => (t3 v).comp t2
  have hP : IsOpen {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := by
    have e : {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} =
        (⋂ v ∈ S, (fun X => projV v (projFin X)) ⁻¹' A v) ∩ intOff b S := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, intOff]
      refine ⟨fun h => ⟨fun v _ => h v, fun v hv => hAoff v hv ▸ h v⟩, fun h v => ?_⟩
      by_cases hv : v ∈ S
      · exact h.1 v hv
      · rw [hAoff v hv]; exact h.2 v hv
    rw [e]
    exact (isOpen_biInter_finset fun v hv => (hAS v hv).2.1.preimage (hs v)).inter (t5 S)
  have hPsi : Measurable (Psi φ A) :=
    (ENNReal.measurable_ofReal.comp (hφc.comp t1).measurable).indicator hP.measurableSet
  have hmul : Continuous fun (Y : Fin 1 → Fin 1 → AF F ⊗[F] E) (a i : Fin 1) => (x : AF F ⊗[F] E) * Y a i :=
    continuous_pi fun a => continuous_pi fun i => continuous_const.mul (continuous_apply_apply a i)
  set Φ : (Fin 1 → Fin 1 → AF F ⊗[F] E) → ℝ≥0∞ := fun Y => Psi φ A fun a i => (x : AF F ⊗[F] E) * Y a i with hΦd
  have hΦ : Measurable Φ := hPsi.comp hmul.measurable
  have hQ : MeasurableSet {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin fun a i => (x : AF F ⊗[F] E) * X a i) ∈ A v} :=
    (hP.preimage hmul).measurableSet
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  have hterm : ∀ (h : HA (AF F) σ J), Th φ A (x * ue (AF F) σ J h⁻¹) =
      ∑' X : ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _), Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) := fun h => by
    refine tsum_congr fun X => ?_
    simp only [hΦd]
    congr 1
    funext a i
    rw [actW_rat_one, Units.val_mul, mul_assoc]
  refine ⟨?_, ?_⟩
  · simp only [hterm]
    rw [← PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm 1 J hJ μ 𝓕 hμ h𝓕 1 _ Φ hΦ, mean, ← lintegral_indicator hQ]
    refine lintegral_congr fun X => ?_
    simp only [hΦd, Psi, Set.indicator, Set.mem_setOf_eq]
  · simp only [hterm]
    exact Measurable.ennreal_tsum fun X => hΦ.comp (ac.comp (continuous_inv.prodMk continuous_const)).measurable

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
