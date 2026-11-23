import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsRealFlowAdelicUnitsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaustStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FlowLatticeCountBoundedStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SmallQ

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem gramR_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : R)
    (X : Fin n → Fin M → R ⊗[F] E) (a c : Fin n) :
    gramR R σ J ((s ⊗ₜ[F] (1 : E)) • X) a c =
      ((s ⊗ₜ[F] (1 : E)) * (s ⊗ₜ[F] (1 : E))) * gramR R σ J X a c := by
  have hs : sigR R σ (s ⊗ₜ[F] (1 : E)) = s ⊗ₜ[F] (1 : E) := by simp [sigR]
  simp only [gramR, hR, hform, Pi.smul_apply, smul_eq_mul, map_mul, hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem small_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), 0 < N → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (t : F) (Y : Fin 1 → Fin M → AF F ⊗[F] E), Y ∈ box b N r₀ → (gramR (AF F) σ J Y = fun _ _ => inclR (AF F) (algebraMap F E t)) → t = 0 := by
  intro F E _ _ _ _ _ σ hcm M J hJ d b N hN
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hcont : Continuous (gramR (AF F) σ J : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
    (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).2.2.2.2.2.2.2.2.2 1 M J
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_real_flow_adelic_units F E σ hcm
  have hbox := GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hcm d b 1 M
  have hΩ : IsCompact (box b N 1 : Set (Fin 1 → Fin M → AF F ⊗[F] E)) := hbox.1 N 1 hN
  let φ : (Fin 1 → Fin M → AF F ⊗[F] E) → Fin 1 → Fin 1 → AF F ⊗[F] E :=
    fun Y a c => gramR (AF F) σ J Y a c
  have hφ : Continuous φ :=
    continuous_pi fun a => continuous_pi fun c => hcont.matrix_elem a c
  obtain ⟨x₀, C, hcount⟩ := GlobalTheory.T.flow_lattice_count_bounded F E σ hcm τ hτ 1 (φ '' box b N 1) (hΩ.image hφ)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, -(2 * x) < x₀ :=
    ⟨|x₀| + 1, by linarith [neg_abs_le x₀, abs_nonneg x₀]⟩
  refine ⟨Real.exp (-x), Real.exp_pos _, ?_⟩
  intro t Y hY hg
  by_contra ht
  have hY' : ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y ∈ box b N 1 := by
    have h := (hbox.2.2 τ hτ N (Real.exp (-x)) x Y).2 hY
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  obtain ⟨-, θ, -, hθ⟩ := hτ
  have hc := hθ x
  have hsq : ((τ (Multiplicative.ofAdd (-(-(2 * x)))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) *
        ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) := by
    rw [← Units.val_mul, ← map_mul, ← ofAdd_add]
    congr 3
    ring
  let X₀ : {X : Fin 1 → Fin 1 → E // X ≠ 0} :=
    ⟨fun _ _ => algebraMap F E t, fun h0 =>
      ht ((algebraMap F E).injective (by simpa using congrFun (congrFun h0 0) 0))⟩
  have hmem : ((τ (Multiplicative.ofAdd (-(-(2 * x)))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) •
      ratTup (AF F) X₀.1 ∈ φ '' box b N 1 := by
    refine ⟨_, hY', ?_⟩
    funext a c
    have h1 : gramR (AF F) σ J Y a c = inclR (AF F) (algebraMap F E t) := by rw [hg]
    simp only [φ]
    rw [hc, gramR_smul, h1, hsq, hc]
    rfl
  have hle := hcount (-(2 * x))
  rw [if_pos hx] at hle
  have h1 := (ENNReal.le_tsum X₀).trans hle
  rw [Set.indicator_of_mem hmem] at h1
  simp at h1

end GlobalTheory.CompanionTheory.SW.SmallQ
