import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConverges

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero

theorem mass_dilated_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ (a e : ℕ), 0 < a → Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ e → ¬ Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ (e + 1) → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (e * (2 * M - 2))) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₀ d b v lam hlam m hm a e ha h1 h2
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hloc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have hnorm := GlobalTheory.CompanionTheory.SW.Dil.norm_natCast v a e ha h1 h2
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have ht : (a : Fv F v) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact (pow_ne_zero e (inv_ne_zero hq)) hnorm.symm
  have ht2 : (a : Fv F v) ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hnorm2 : ‖(a : Fv F v) ^ 2‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ (2 * e) := by
    rw [norm_pow, hnorm, ← pow_mul, mul_comm]
  have hs1 := GlobalTheory.CompanionTheory.SW.Dil.scale_fv v lam _ ht e hnorm
  have hs2 := GlobalTheory.CompanionTheory.SW.Dil.scale_fv v lam _ ht2 (2 * e) hnorm2
  set q : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) with hqdef
  set f : Fv F v ⊗[F] E → Fv F v ⊗[F] E :=
    fun y => algebraMap (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v) * y with hf
  have hcast : algebraMap (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v) = (a : Fv F v ⊗[F] E) := map_natCast _ _
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk := GlobalTheory.CompanionTheory.SW.Dil.coordK_map (Fv F v) σ hσ b lam _ ht _ hs1
  have hk1 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin M) (coordK (Fv F v) b lam) f hfm _ hk
  have hk2 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => coordK (Fv F v) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one] at hk2
  let g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E) := Matrix.of fun _ _ => (a : Fv F v ⊗[F] E)
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    change IsUnit (a : Fv F v ⊗[F] E)
    rw [← hcast]
    exact ht.isUnit.map _
  have hrm : (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g) =
      fun X p i => f (X p i) := by
    funext X p i
    simp only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, hf, hcast]
    rw [Subsingleton.elim p 0, mul_comm]
  let τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1 := fun S => (a ^ 2) • S
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) ((a : Fv F v) ^ 2) *
        (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j := by
    intro S i j
    change (a ^ 2) • (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j = _
    rw [nsmul_eq_mul, map_pow, hcast]
    push_cast
    rfl
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
    exact (continuous_nsmul (a ^ 2)).measurable
  have hc := GlobalTheory.CompanionTheory.SW.Dil.coordHerm_map (Fv F v) σ hσ b lam _ ht2 _ hs2 τ hτm hτe
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g := by
    intro S
    ext i j
    have hsig : sigR (Fv F v) σ (a : Fv F v ⊗[F] E) = a := map_natCast _ _
    rw [hτe, map_pow, hcast, GlobalTheory.CompanionTheory.SW.Dil.cT_scalar _ _ hsig]
  have hrmap : Measurable fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g := by
    rw [hrm]
    exact measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun i =>
      hfm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))
  have hfree : IsOpen {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} :=
    GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.isOpen_free b (Fv F v) hloc (PI.VolStabSW.TensAllW.lip_field _)
  have key := GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.free_rmul σ hσ J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm hfree g hg τ hτ _ _
    (by rw [hrm]; exact hk2) hc (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)
  have hτs : τ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) =
      hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ := by
    have h0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ = 0 := by
      apply Subtype.ext
      funext i j
      simp [hermOf]
    rw [h0]
    exact smul_zero _
  rw [hτs] at key
  have hA : MeasurableSet (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) :=
    GlobalTheory.CompanionTheory.SW.Growth.measurable_latV b v
  have key2 := congrArg (fun μ' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) => μ' (latV b v)) key
  simp only [Measure.smul_apply, Measure.map_apply hrmap hA] at key2
  have e1 : ((q ^ e) ^ 2) ^ M = q ^ (2 * e) * q ^ (e * (2 * M - 2)) := by
    rw [← pow_add, ← pow_mul, ← pow_mul]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have : 2 * (k + 1) - 2 = 2 * k := by omega
    rw [this]
    ring
  rw [e1, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.coe_mul, mul_assoc] at key2
  have hq0 : ((q ^ (2 * e) : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    refine pow_ne_zero _ ?_
    rw [hqdef]
    exact_mod_cast hq
  have key3 := (ENNReal.mul_right_inj hq0 ENNReal.coe_ne_top).1 key2
  have hset : {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} =
      (fun X => rmul (Fv F v) X g) ⁻¹' (latV b v) := by
    rw [hrm]
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hf, hcast]
  have hof : ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (e * (2 * M - 2))) =
      ((q ^ (e * (2 * M - 2)) : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
  rw [hset, ← key3, hof]

end GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero
