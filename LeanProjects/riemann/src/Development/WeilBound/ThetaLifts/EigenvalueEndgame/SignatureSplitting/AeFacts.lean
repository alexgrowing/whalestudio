import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.NonarchFiniteAdeleRing
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.StabClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinity
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

noncomputable section

namespace PositivityTheory.ThKEnd.Two

open scoped TensorProduct NNReal Matrix MatrixGroups Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEnd.Grp
open GlobalTheory.Eis.Conv (halfE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}

theorem ae_facts (h : IsCMExt F E σ) : LocallyCompactSpace (AE F E) ∧ SecondCountableTopology (AE F E) ∧
    Cusp (Matrix.SpecialLinearGroup.map (n := Fin 2) (inclR (F := F) (E := E) (AF F))).range uni (dia (halfE F E)⁻¹) ∧
    Lat ((inclR (F := F) (E := E) (AF F)).toAddMonoidHom.toMultiplicative).range := by
  obtain ⟨Φ, j, h1, h2, h3, h4⟩ := GlobalTheory.HeckeBridge.exists_tensor_adele_equiv F E σ h
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  let e : AE F E ≃ₜ AdeleRing (𝓞 E) E := ⟨Φ.toEquiv, h1, h2⟩
  have hi : ∀ x, Φ (inclR (F := F) (AF F) x) = algebraMap E _ x := fun x => (h4 _).trans (Prod.ext (h3 x) (by
    change GlobalTheory.AdeleBaseChange.adMap F E 1 * algebraMap E _ x = algebraMap E _ x
    rw [map_one, one_mul]))
  refine ⟨e.isClosedEmbedding.locallyCompactSpace, e.secondCountableTopology, cusp_of Φ h1 h2 hi ?_ ?_, lat_of Φ h1 h2 hi⟩
  · rw [inv_inv, h4]
    change (2 : InfiniteAdeleRing E) * j (algebraMap F (Ainf F ⊗[F] E) 2⁻¹) = 1
    rw [← map_ofNat j, ← map_mul, ← map_ofNat (algebraMap F (Ainf F ⊗[F] E)), ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one, map_one]
  · rw [inv_inv, h4]
    exact map_one (finAdEquiv F E)

theorem sl_facts {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] : LocallyCompactSpace SL(2, R) ∧ SecondCountableTopology SL(2, R) ∧ T2Space SL(2, R) :=
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) R) := inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → R))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R) := inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → R))
  ⟨closedEmb.locallyCompactSpace, closedEmb.isEmbedding.secondCountableTopology, closedEmb.isEmbedding.t2Space⟩

variable {J : Matrix (Fin d) (Fin d) E}

theorem ht_mul (g h : UA σ J) : (ht (g * h) : ℝ) ≤ ht g * ht h := by exact_mod_cast heightGL_mul_le F g.1 h.1

theorem ht_cont : Continuous fun g : UA σ J => (ht g : ℝ) :=
  NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)

def Mod (f : UA σ J → ℂ) : Prop := ∃ (C : ℝ) (k : ℕ), ∀ x, ‖f x‖ ≤ C * (ht x : ℝ) ^ k

theorem Mod.gr {G : Type} [Group G] [TopologicalSpace G] {f : UA σ J → ℂ} (hf : Mod f) {m : G →* UA σ J} (hm : Continuous m)
    (a : G) (x : UA σ J) : ∃ k, Gr a k fun g => f (m g * x) := by
  obtain ⟨C, k, hf⟩ := hf
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (ht (m a) : ℝ) one_lt_two
  refine ⟨n * k, fun Ω hΩ => ?_⟩
  obtain ⟨M, hM⟩ := hΩ.exists_bound_of_continuousOn (f := fun κ => (ht (m κ * x) : ℝ))
    (ht_cont.comp (hm.mul continuous_const)).continuousOn
  refine ⟨max C 0 * M ^ k, fun i κ hκ => (hf _).trans ?_⟩
  have e : (ht (m (a ^ i * κ) * x) : ℝ) ≤ M * (2 ^ i) ^ n := by
    induction i with
    | zero => simpa using hM κ hκ
    | succ i ih =>
      rw [pow_succ' a, mul_assoc, map_mul, mul_assoc, pow_succ' 2, mul_pow, mul_left_comm]
      exact (ht_mul _ _).trans (mul_le_mul hn.le ih (by positivity) (by positivity))
  rw [pow_mul, mul_assoc, ← mul_pow]
  exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity) e _) (by positivity) (le_max_right _ _)

theorem Mod.av {N : Subgroup (UA σ J)} (hN : UnipGood N) {f c : UA σ J → ℂ} (hf : Mod f) (hi : ∀ γ ∈ ratU σ J, ∀ x, f (γ * x) = f x)
    (h : IsAv ((ratU σ J).subgroupOf N) Subtype.val f c) : Mod c := by
  obtain ⟨C, k, hf⟩ := hf
  obtain ⟨K, hK, hc⟩ := hN.cov
  obtain ⟨μ, 𝓕, h1, h2, h3⟩ := hN.ex
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun u => (ht u.1 : ℝ)) (ht_cont.comp continuous_subtype_val).continuousOn
  refine ⟨max C 0 * M ^ k, k, fun x => ?_⟩
  rw [h μ 𝓕 h1 h2 h3]
  refine (norm_setIntegral_le_of_norm_le_const (by simp [h3]) fun u _ => ?_).trans_eq (by rw [Measure.real, h3, ENNReal.toReal_one, mul_one])
  obtain ⟨γ, a, b⟩ := hc u
  rw [← hi _ a, ← mul_assoc, mul_assoc (max C 0), ← mul_pow]
  refine (hf _).trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity) ((ht_mul _ _).trans
    (mul_le_mul_of_nonneg_right ?_ (by positivity))) _) (by positivity) (le_max_right _ _))
  simpa using hM _ b

end PositivityTheory.ThKEnd.Two

end
