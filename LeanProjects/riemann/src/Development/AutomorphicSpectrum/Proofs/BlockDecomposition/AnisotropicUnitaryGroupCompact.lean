import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.CompactField

section Shell

variable {K W : Type} [NontriviallyNormedField K] [NormedAddCommGroup W] [NormedSpace K W] [ProperSpace W]

theorem exists_lower_bound (P : W → ℝ) (hc : Continuous P) (hpos : ∀ w, w ≠ 0 → 0 < P w)
    (hom : ∀ (t : K) w, P (t • w) = ‖t‖ ^ 2 * P w) : ∃ m : ℝ, 0 < m ∧ ∀ w, m * ‖w‖ ^ 2 ≤ P w := by
  obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm K
  have hk0 : 0 < ‖k‖ := by linarith
  set S : Set W := Metric.closedBall 0 1 \ Metric.ball 0 (1 / ‖k‖) with hS
  have hSc : IsCompact S := (isCompact_closedBall (0 : W) 1).diff Metric.isOpen_ball
  have hP0 : P 0 = 0 := by
    have := hom 0 0
    simpa using this
  have key : ∃ m : ℝ, 0 < m ∧ ∀ w ∈ S, m ≤ P w := by
    rcases S.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨x, hx, hmin⟩ := hSc.exists_isMinOn h hc.continuousOn
      have hx0 : x ≠ 0 := by
        rintro rfl
        apply hx.2
        simp only [Metric.mem_ball, dist_self]
        positivity
      exact ⟨P x, hpos x hx0, fun w hw => hmin hw⟩
  obtain ⟨m, hm, hmS⟩ := key
  refine ⟨m, hm, fun w => ?_⟩
  by_cases hw : w = 0
  · simp [hw, hP0]
  obtain ⟨d, hd0, hd1, hd2, -⟩ := rescale_to_shell hk one_pos hw
  have hmem : d • w ∈ S := ⟨by simpa using hd1.le, by simpa using hd2⟩
  have h1 := hmS _ hmem
  rw [hom] at h1
  have hd' : 0 < ‖d‖ := norm_pos_iff.2 hd0
  have hnorm : ‖d‖ * ‖w‖ < 1 := by simpa [norm_smul] using hd1
  have hPw := hpos w hw
  have hnn : 0 ≤ ‖d‖ * ‖w‖ := mul_nonneg hd'.le (norm_nonneg w)
  have h2 : (‖d‖ * ‖w‖) ^ 2 ≤ 1 := by nlinarith
  have h3 : ‖d‖ ^ 2 * (m * ‖w‖ ^ 2) ≤ ‖d‖ ^ 2 * P w := by nlinarith
  exact le_of_mul_le_mul_left h3 (by positivity)

end Shell

section Bound

variable {K R : Type} [NontriviallyNormedField K] [ProperSpace K] [CommRing R] [Algebra K R] [Module.Finite K R]
  [TopologicalSpace R] [IsModuleTopology K R]

theorem continuous_of_fix (c : R →+* R) (hc : ∀ t : K, c (algebraMap K R t) = algebraMap K R t) : Continuous c := by
  haveI : IsTopologicalRing R := IsModuleTopology.isTopologicalRing K R
  let cl : R →ₗ[K] R :=
    { toFun := c
      map_add' := map_add c
      map_smul' := fun t x => by simp [Algebra.smul_def, hc] }
  exact IsModuleTopology.continuous_of_linearMap cl

theorem hform_smul {M : ℕ} (c : R →+* R) (hc : ∀ t : K, c (algebraMap K R t) = algebraMap K R t)
    (J : Matrix (Fin M) (Fin M) R) (t : K) (u : Fin M → R) :
    Formalism.UG.hform c J (t • u) (t • u) = (t ^ 2) • Formalism.UG.hform c J u u := by
  unfold Formalism.UG.hform
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hc, map_pow]
  ring

theorem hform_col {M : ℕ} (c : R →+* R) (J g : Matrix (Fin M) (Fin M) R) (j : Fin M) :
    Formalism.UG.hform c J (fun i => g i j) (fun i => g i j) = (Formalism.UG.cT c g * J * g) j j := by
  unfold Formalism.UG.hform Formalism.UG.cT
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem exists_compact_entries {M : ℕ} (c : R →+* R) (hc : ∀ t : K, c (algebraMap K R t) = algebraMap K R t)
    (J : Matrix (Fin M) (Fin M) R) (hne : ∀ u : Fin M → R, u ≠ 0 → Formalism.UG.hform c J u u ≠ 0) :
    ∃ C : Set R, IsCompact C ∧
      ∀ g : Matrix (Fin M) (Fin M) R, Formalism.UG.cT c g * J * g = J → ∀ i j, g i j ∈ C := by
  haveI : IsTopologicalRing R := IsModuleTopology.isTopologicalRing K R
  let e : R ≃ₗ[K] (Fin (Module.finrank K R) → K) := (Module.finBasis K R).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hes : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  have hcc : Continuous c := continuous_of_fix c hc
  let U : (Fin M → Fin (Module.finrank K R) → K) → (Fin M → R) := fun w i => e.symm (w i)
  have hU : Continuous U := continuous_pi fun i => hes.comp (continuous_apply i)
  let Q : (Fin M → R) → R := fun u => Formalism.UG.hform c J u u
  have hQ : Continuous Q := by
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact ((hcc.comp (continuous_apply i)).mul continuous_const).mul (continuous_apply j)
  let P : (Fin M → Fin (Module.finrank K R) → K) → ℝ := fun w => ‖e (Q (U w))‖
  have hP : Continuous P := (he.comp (hQ.comp hU)).norm
  have hUinj : ∀ w, w ≠ 0 → U w ≠ 0 := by
    intro w hw h
    apply hw
    funext i
    have := congrFun h i
    simpa [U] using this
  have hpos : ∀ w, w ≠ 0 → 0 < P w := by
    intro w hw
    refine norm_pos_iff.2 fun h => ?_
    exact hne _ (hUinj w hw) (e.map_eq_zero_iff.1 h)
  have hom : ∀ (t : K) w, P (t • w) = ‖t‖ ^ 2 * P w := by
    intro t w
    have h1 : U (t • w) = t • U w := by
      funext i
      simp [U]
    simp only [P, Q]
    rw [h1, hform_smul c hc, map_smul, norm_smul, norm_pow]
  obtain ⟨m, hm, hmP⟩ := exists_lower_bound (K := K) P hP hpos hom
  let A : ℝ := ∑ j, ‖e (J j j)‖
  have hA : ∀ j, ‖e (J j j)‖ ≤ A := fun j =>
    Finset.single_le_sum (f := fun j => ‖e (J j j)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  refine ⟨e.symm '' Metric.closedBall 0 (Real.sqrt (A / m)),
    (isCompact_closedBall _ _).image hes, fun g hg i j => ?_⟩
  refine ⟨e (g i j), ?_, e.symm_apply_apply _⟩
  let w : Fin M → Fin (Module.finrank K R) → K := fun i => e (g i j)
  have hw : P w = ‖e (J j j)‖ := by
    have h1 : U w = fun i => g i j := by
      funext i
      simp [U, w]
    simp only [P, Q]
    rw [h1, hform_col, hg]
  have h2 := hmP w
  rw [hw] at h2
  have h3 : ‖w‖ ^ 2 ≤ A / m := by
    rw [le_div_iff₀ hm]
    linarith [hA j]
  have h4 : ‖w‖ ≤ Real.sqrt (A / m) := Real.le_sqrt_of_sq_le h3
  have h5 : ‖e (g i j)‖ ≤ ‖w‖ := norm_le_pi_norm w i
  simpa using h5.trans h4

end Bound

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

section Main

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_algebraMap_left (K : Type) [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) (t : K) :
    sigR K σ (algebraMap K (K ⊗[F] E) t) = algebraMap K (K ⊗[F] E) t := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem sigR_sigR (K : Type) [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (z : K ⊗[F] E) :
    sigR K σ (sigR K σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, hσ]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem hform_ne_zero (K : Type) [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) (hf : IsField (K ⊗[F] E)) (hiso : ¬ IsoAt K σ J)
    (u : Fin M → K ⊗[F] E) (hu : u ≠ 0) : Formalism.UG.hform (sigR K σ) (JR (F := F) K J) u u ≠ 0 := by
  intro h0
  have hdet : IsUnit (JR (F := F) K J).det := by
    unfold JR
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ).map _
  set c := sigR K σ with hc
  let y : Fin M → K ⊗[F] E := Matrix.vecMul (fun i => c (u i)) (JR (F := F) K J)
  have hy : y ≠ 0 := by
    intro hy0
    have h1 : (fun i => c (u i)) = 0 := by
      have h2 := congrArg (fun v => Matrix.vecMul v (JR (F := F) K J)⁻¹) hy0
      simp only [y, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one, Matrix.zero_vecMul] at h2
      exact h2
    apply hu
    funext i
    have h3 := congrArg c (congrFun h1 i)
    simpa [hc, sigR_sigR K σ hσ] using h3
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel hj
  refine hiso ⟨u, Pi.single j b, h0, ?_⟩
  have h4 : Formalism.UG.hform c (JR (F := F) K J) u (Pi.single j b) = y j * b := by
    unfold Formalism.UG.hform
    simp only [y, Matrix.vecMul, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp
  exact h4.trans hb

end Main

theorem isCompact_univ_HA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ {K : Type} [NontriviallyNormedField K] [ProperSpace K] [Algebra F K], IsField (K ⊗[F] E) → ¬ IsoAt K σ J →
      IsCompact (Set.univ : Set (HA K σ J)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ K _ _ _ hfield hiso
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (K ⊗[F] E) := IsModuleTopology.isTopologicalRing K _
  let e : (K ⊗[F] E) ≃ₗ[K] (Fin (Module.finrank K (K ⊗[F] E)) → K) := (Module.finBasis K (K ⊗[F] E)).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  haveI : T2Space (K ⊗[F] E) := T2Space.of_injective_continuous e.injective he
  have hc := sigR_algebraMap_left (F := F) (E := E) K σ
  obtain ⟨C, hC, hCg⟩ := exists_compact_entries (K := K) (sigR K σ) hc (JR (F := F) K J)
    (hform_ne_zero K σ (GlobalTheory.CompanionTheory.SaGen.CompactField.sigma_sigma hσ) J hJ.2 hfield hiso)
  have hcs : Continuous (sigR (F := F) (E := E) K σ) := continuous_of_fix (K := K) _ hc
  have hcl : IsClosed (HR K σ J : Set (GL (Fin M) (K ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin M) (K ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (K ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map hcs).matrix_transpose.matrix_mul continuous_const).matrix_mul hv)
      continuous_const
  have hemb : Topology.IsClosedEmbedding fun g : HR K σ J => Units.embedProduct _ g.1 :=
    Units.isClosedEmbedding_embedProduct.comp hcl.isClosedEmbedding_subtypeVal
  let S : Set (Matrix (Fin M) (Fin M) (K ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have hK := hemb.isCompact_preimage (hS.prod (hS.image MulOpposite.continuous_op))
  have huniv : (fun g : HR K σ J => Units.embedProduct _ g.1) ⁻¹'
      (S ×ˢ (MulOpposite.op '' S)) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    exact ⟨fun i _ j _ => hCg _ g.2 i j, (g⁻¹).1.1, fun i _ j _ => hCg _ (g⁻¹).2 i j, rfl⟩
  rw [huniv] at hK
  exact hK

end GlobalTheory.CompanionTheory.SaGen.CompactField
