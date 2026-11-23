import Formalism.HermitianCurvature.StatementD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceLastLevel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialMapProper
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SectionDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P.Dx3

section weight

variable {k r : ℕ}

def Om (μR : Measure (Mt k r)) (M : ℝ) (n : Mt k r) : ℝ :=
  ∫ x, B.gN (Matrix.of x * Matrix.of n) ^ (-M) ∂μR

def cut (μR : Measure (Mt k r)) (M : ℝ) (p : B.SS k r) : ℝ :=
  B.gN (Matrix.of p.1.2) ^ (-M) / Om μR M p.1.2

end weight

private theorem rpa_lemma {a b z : ℝ} (ha : 0 < a) (hab : a ≤ b) (hz : 0 ≤ z) : b ^ (-z) ≤ a ^ (-z) := by
  rw [Real.rpow_neg ha.le, Real.rpow_neg (ha.le.trans hab)]
  gcongr

theorem key_real {N N' X Y Gg S θv Fv cR cF CP K1 Kγ A bN M : ℝ} {c : ℕ}
    (hN : 1 ≤ N) (hS : 1 ≤ S) (hSX : S ≤ X) (hY : 1 ≤ Y) (hGg : 0 < Gg)
    (hc : 1 ≤ c) (hXY : X ≤ CP * Y ^ c) (hN'le : N' ≤ Kγ * N * X ^ 2) (hN' : 1 ≤ N') (hYG : Y ≤ K1 * Gg)
    (hθ : θv ≤ N ^ (-M) * S ^ M / cR) (hθ0 : 0 ≤ θv) (hF : Fv ≤ cF * Gg ^ (-A)) (hF0 : 0 ≤ Fv)
    (hcR : 0 < cR) (hcF : 0 ≤ cF) (hCP : 0 < CP) (hK1 : 0 < K1) (hKγ : 0 < Kγ)
    (hM : M = A / c - 2 * bN) (hbN : 0 ≤ bN) (hA : 4 * bN ≤ A / c) :
    θv * Fv ≤ (cF * K1 ^ A * CP ^ (A / c) * Kγ ^ bN / cR) * (N ^ (-(A / c - 3 * bN)) * N' ^ (-bN)) := by
  have hc0 : (0:ℝ) < c := Nat.cast_pos.mpr (by omega)
  have ha0 : 0 ≤ A / c := le_trans (by positivity) hA
  have hA0 : 0 ≤ A := by
    have h := mul_nonneg ha0 hc0.le
    rwa [div_mul_cancel₀ A hc0.ne'] at h
  have hM0 : 0 ≤ M := by rw [hM]; linarith
  have hS0 : 0 ≤ S := by linarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hN0 : 0 < N := by linarith
  have hN'0 : 0 < N' := by linarith
  have hGgY : Y / K1 ≤ Gg := by rw [div_le_iff₀ hK1]; linarith
  have s1 : θv * Fv ≤ (N ^ (-M) * S ^ M / cR) * (cF * Gg ^ (-A)) :=
    mul_le_mul hθ hF hF0 (le_trans hθ0 hθ)
  have s2 : S ^ M ≤ X ^ M := Real.rpow_le_rpow hS0 hSX hM0
  have s3 : Gg ^ (-A) ≤ K1 ^ A * Y ^ (-A) := by
    calc Gg ^ (-A) ≤ (Y / K1) ^ (-A) := rpa_lemma (div_pos hY0 hK1) hGgY hA0
      _ = K1 ^ A * Y ^ (-A) := by
        rw [Real.div_rpow hY0.le hK1.le, Real.rpow_neg hK1.le, div_inv_eq_mul, mul_comm]
  have s4 : Y ^ (-A) ≤ CP ^ (A / c) * X ^ (-(A / c)) := by
    have hYc : (Y ^ c) ^ (A / c) = Y ^ A := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le, mul_comm, div_mul_cancel₀ A hc0.ne']
    have hXa : X ^ (A / c) ≤ CP ^ (A / c) * Y ^ A := by
      rw [← hYc, ← Real.mul_rpow hCP.le (pow_nonneg hY0.le c)]
      exact Real.rpow_le_rpow hX0.le hXY ha0
    have hXa0 : 0 < X ^ (A / c) := by positivity
    have hYA0 : 0 < Y ^ A := by positivity
    rw [Real.rpow_neg hY0.le, Real.rpow_neg hX0.le, ← div_eq_mul_inv, le_div_iff₀ hXa0,
      ← div_eq_inv_mul, div_le_iff₀ hYA0]
    exact hXa
  have s5 : X ^ (-(2 * bN)) ≤ Kγ ^ bN * N ^ bN * N' ^ (-bN) := by
    have hX2 : X ^ (2 * bN) = (X ^ 2) ^ bN := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
    have hN'b : N' ^ bN ≤ Kγ ^ bN * N ^ bN * X ^ (2 * bN) := by
      rw [hX2, ← Real.mul_rpow hKγ.le hN0.le, ← Real.mul_rpow (mul_nonneg hKγ.le hN0.le) (sq_nonneg X)]
      exact Real.rpow_le_rpow hN'0.le hN'le hbN
    have hNb : 0 < N' ^ bN := by positivity
    have hXb : 0 < X ^ (2 * bN) := by positivity
    rw [Real.rpow_neg hX0.le, Real.rpow_neg hN'0.le, ← div_eq_mul_inv, le_div_iff₀ hNb,
      ← div_eq_inv_mul, div_le_iff₀ hXb]
    exact hN'b
  have e2 : Gg ^ (-A) ≤ K1 ^ A * CP ^ (A / c) * X ^ (-(A / c)) := by
    rw [mul_assoc]; exact s3.trans (mul_le_mul_of_nonneg_left s4 (by positivity))
  have e3 : X ^ M * X ^ (-(A / c)) = X ^ (-(2 * bN)) := by
    rw [← Real.rpow_add hX0]; congr 1; rw [hM]; ring
  have e4 : N ^ (-M) * N ^ bN = N ^ (-(A / c - 3 * bN)) := by
    rw [← Real.rpow_add hN0]; congr 1; rw [hM]; ring
  calc θv * Fv ≤ (N ^ (-M) * S ^ M / cR) * (cF * Gg ^ (-A)) := s1
    _ ≤ (N ^ (-M) * X ^ M / cR) * (cF * (K1 ^ A * CP ^ (A / c) * X ^ (-(A / c)))) := by
        refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · gcongr
        · gcongr
    _ = (cF * K1 ^ A * CP ^ (A / c) / cR) * N ^ (-M) * X ^ (-(2 * bN)) := by rw [← e3]; ring
    _ ≤ (cF * K1 ^ A * CP ^ (A / c) / cR) * N ^ (-M) * (Kγ ^ bN * N ^ bN * N' ^ (-bN)) := by
        gcongr
    _ = (cF * K1 ^ A * CP ^ (A / c) * Kγ ^ bN / cR) * (N ^ (-(A / c - 3 * bN)) * N' ^ (-bN)) := by
        rw [← e4]; ring

section norms

variable {k r : ℕ}

private theorem gN_nonneg_lemma_2 (g : B.Mat k r) : 0 ≤ B.gN g := Real.sqrt_nonneg _

theorem entry_le_gN (g : B.Mat k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  have h1 : Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
    Finset.single_le_sum (f := fun j' => Complex.normSq (g i j')) (fun j' _ => Complex.normSq_nonneg _)
      (Finset.mem_univ j)
  have h2 : ∑ j', Complex.normSq (g i j') ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
    Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
      (fun i' _ => Finset.sum_nonneg fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have h3 : ‖g i j‖ ^ 2 ≤ ∑ i', ∑ j', Complex.normSq (g i' j') := by
    rw [← Complex.normSq_eq_norm_sq]; exact h1.trans h2
  unfold B.gN
  rw [← abs_of_nonneg (norm_nonneg (g i j))]
  exact Real.abs_le_sqrt h3

theorem a_mv_le {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → ℂ) (i : Fin m) :
    ‖(M *ᵥ u) i‖ ≤ ∑ j, ‖M i j‖ * ‖u j‖ := by
  calc ‖(M *ᵥ u) i‖ = ‖∑ j, M i j * u j‖ := rfl
    _ ≤ ∑ j, ‖M i j * u j‖ := norm_sum_le _ _
    _ = ∑ j, ‖M i j‖ * ‖u j‖ := by simp only [norm_mul]

theorem a_gmv_le (g : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) :
    ‖(g *ᵥ v) j‖ ≤ B.gN g * ∑ l, ‖v l‖ := by
  calc ‖(g *ᵥ v) j‖ ≤ ∑ l, ‖g j l‖ * ‖v l‖ := a_mv_le g v j
    _ ≤ ∑ l, B.gN g * ‖v l‖ :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (entry_le_gN g j l) (norm_nonneg _)
    _ = B.gN g * ∑ l, ‖v l‖ := by rw [Finset.mul_sum]

theorem a_herm_le (H g : B.Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    ‖herm H (g *ᵥ v) w‖ ≤ B.gN g * (∑ i, ‖w i‖ * ∑ j, ‖H i j‖ * ∑ l, ‖v l‖) := by
  have hv : ∀ j, ‖(g *ᵥ v) j‖ ≤ B.gN g * ∑ l, ‖v l‖ := a_gmv_le g v
  have key : ‖herm H (g *ᵥ v) w‖ ≤ ∑ i, ‖w i‖ * ∑ j, ‖H i j‖ * (B.gN g * ∑ l, ‖v l‖) := by
    calc ‖herm H (g *ᵥ v) w‖ = ‖∑ i, star (w i) * (H *ᵥ (g *ᵥ v)) i‖ := rfl
      _ ≤ ∑ i, ‖star (w i) * (H *ᵥ (g *ᵥ v)) i‖ := norm_sum_le _ _
      _ = ∑ i, ‖w i‖ * ‖(H *ᵥ (g *ᵥ v)) i‖ := by simp only [norm_mul, norm_star]
      _ ≤ ∑ i, ‖w i‖ * ∑ j, ‖H i j‖ * (B.gN g * ∑ l, ‖v l‖) := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine (a_mv_le H (g *ᵥ v) i).trans ?_
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv j) (norm_nonneg _)
  refine key.trans (le_of_eq ?_)
  generalize B.gN g = G
  generalize (∑ l, ‖v l‖) = S
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem uMap_entry_le_matrix_norm (z : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : B.Mat k r, ‖C2.uMap k r z g a b‖ ≤ C * B.gN g := by
  by_cases h : a.val < r
  · refine ⟨∑ i, ‖bvec (esI k r ⟨a.val, h⟩) i‖ * ∑ j, ‖Hpk k r i j‖ * ∑ l, ‖fvec k r z b l‖,
      by positivity, fun g => ?_⟩
    simp only [C2.uMap, dif_pos h]
    rw [mul_comm _ (B.gN g)]
    exact a_herm_le _ g _ _
  · refine ⟨(∑ i, ‖z i‖ * ∑ j, ‖Hpk k r i j‖ * ∑ l, ‖fvec k r z b l‖) / ‖herm (Hpk k r) z z‖,
      by positivity, fun g => ?_⟩
    simp only [C2.uMap, dif_neg h]
    rw [norm_div, div_mul_eq_mul_div, mul_comm _ (B.gN g)]
    gcongr
    exact a_herm_le _ g _ _

theorem uMap_le (z : Fin (2 * r + k + 1) → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : B.Mat k r) (a b : Fin (r + 1)), ‖C2.uMap k r z g a b‖ ≤ C * B.gN g := by
  choose C hC hb using fun a b => uMap_entry_le_matrix_norm (k := k) (r := r) z a b
  refine ⟨∑ a, ∑ b, C a b, Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hC a b,
    fun g a b => (hb a b g).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (gN_nonneg_lemma_2 g)
  exact (Finset.single_le_sum (f := fun b => C a b) (fun b _ => hC a b) (Finset.mem_univ b)).trans
    (Finset.single_le_sum (f := fun a => ∑ b, C a b)
      (fun a _ => Finset.sum_nonneg fun b _ => hC a b) (Finset.mem_univ a))

theorem UW_bound (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ h ∈ UWset k r z, B.gN h ≤ K := by
  obtain ⟨C, hC⟩ := (P.weyl_subgroup_compact k r z hz hT).exists_bound_of_continuousOn
    (P.B6.gN_continuous (k := k) (r := r)).continuousOn
  refine ⟨max C 1, le_max_right _ _, fun h hh => ?_⟩
  have := hC h hh
  rw [Real.norm_of_nonneg (P.B6.gN_nonneg h)] at this
  exact this.trans (le_max_left _ _)

end norms

section intN

variable {k r : ℕ}

theorem b_fin {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) (hU : IsCompact U) :
    IsFiniteMeasure μ := by
  have hc : μ (@id (Set (Mt k r)) U)ᶜ = 0 := h.conc
  have hf : μ (@id (Set (Mt k r)) U) < ⊤ := h.finite_compact _ hU
  exact ⟨lt_of_le_of_lt (measure_univ_le_add_compl (@id (Set (Mt k r)) U))
    (ENNReal.add_lt_top.mpr ⟨hf, by rw [hc]; exact ENNReal.zero_lt_top⟩)⟩

theorem integrable_unipotent_norm_rpow_neg {μN : Measure (Mt k r)} (hN : B.IsHaarOn (Nset k r) μN) (a : ℝ)
    (ha : 4 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ a) :
    Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (-a)) μN := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hsub : (Nset k 0 : Set (B.Mat k 0)) ⊆ {(1 : B.Mat k 0)} := by
      intro x hx
      exact P.SliceLastLevel.sz_N_zero hx
    have hfin : IsFiniteMeasure μN := by
      refine ⟨?_⟩
      calc μN Set.univ ≤ μN (Nset k 0) + μN (Nset k 0)ᶜ := measure_univ_le_add_compl _
        _ = μN (Nset k 0) := by rw [hN.conc, add_zero]
        _ ≤ μN {(1 : B.Mat k 0)} := measure_mono hsub
        _ < ∞ := hN.finite_compact _ isCompact_singleton
    have ha0 : 0 ≤ a := by
      have : (4 : ℝ) * ((0 : ℕ) * (((2 * 0 + k + 1 : ℕ)) : ℝ) + 1) = 4 := by simp
      linarith
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (((P.HaarUniquenessConjugation.gN_meas k 0).pow_const _).aestronglyMeasurable) ?_
    filter_upwards [P.Dx2.OrbJ.ae_mem hN] with x hx
    have h1 : 1 ≤ B.gN (Matrix.of x : B.Mat k 0) := P.BetaSesquilinearity.gN_ge_one hx.1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
  · refine P.SliceLastLevel.intN k r μN hN a (le_trans ?_ ha)
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    unfold B.AB
    push_cast
    nlinarith [mul_nonneg hk0 (show (0 : ℝ) ≤ r - 1 by linarith)]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem maj_int (D : B.RealPlaceData k r Wp Wq) (a b : ℝ)
    (ha : 4 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ a)
    (hb : 4 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ b) :
    Integrable (fun p : B.SS k r => B.gN (Matrix.of p.1.2) ^ (-a) * B.gN (Matrix.of p.2.2) ^ (-b)) D.μSS := by
  have := P.Dx2.OrbJ.sigmaF D.haarW
  have := P.Dx2.OrbJ.sigmaF D.haarN
  have := P.Dx2.OrbJ.sigmaF D.haarW'
  have : IsFiniteMeasure D.μW := b_fin D.haarW (P.weyl_subgroup_compact k r D.z D.z_mem D.T_pos)
  have : IsFiniteMeasure D.μW' := b_fin D.haarW' (P.weyl_subgroup_compact k r D.z' D.z'_mem D.T'_pos)
  have i1 : Integrable (fun q : Mt k r × Mt k r => (1 : ℝ) * B.gN (Matrix.of q.2) ^ (-a)) (D.μW.prod D.μN) :=
    (integrable_const (1 : ℝ)).mul_prod (integrable_unipotent_norm_rpow_neg D.haarN a ha)
  have i2 : Integrable (fun q : Mt k r × Mt k r => (1 : ℝ) * B.gN (Matrix.of q.2) ^ (-b)) (D.μW'.prod D.μN) :=
    (integrable_const (1 : ℝ)).mul_prod (integrable_unipotent_norm_rpow_neg D.haarN b hb)
  have i3 := i1.mul_prod i2
  unfold B.RealPlaceData.μSS
  simpa only [one_mul] using i3

theorem integrand_aesm (D : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (B.GV k r)) :
    AEStronglyMeasurable (Formalism.FourierDecayAlt.D.orbIntegrand D γ F) D.μSS := by
  set S : Set (B.SS k r) := {p | D.inSS p} with hS
  have hWc := (P.weyl_subgroup_closed k r D.z).closed
  have hWc' := (P.weyl_subgroup_closed k r D.z').closed
  have hNc := (P.unipotent_radical_closed k r).closed
  have hSc : IsClosed S := by
    have e : S = (fun p : B.SS k r => (p.1.1 : B.Mat k r)) ⁻¹' (UWset k r D.z) ∩
        ((fun p : B.SS k r => (p.1.2 : B.Mat k r)) ⁻¹' (Nset k r) ∩
          ((fun p : B.SS k r => (p.2.1 : B.Mat k r)) ⁻¹' (UWset k r D.z') ∩
            (fun p : B.SS k r => (p.2.2 : B.Mat k r)) ⁻¹' (Nset k r))) := by
      ext p; rfl
    rw [e]
    exact (hWc.preimage continuous_fst.fst).inter ((hNc.preimage continuous_fst.snd).inter
      ((hWc'.preimage continuous_snd.fst).inter (hNc.preimage continuous_snd.snd)))
  have hxi : Continuous fun p : B.SS k r => B.xiTau D (1, 1) p :=
    (P.B7.continuous_xi D).comp (by fun_prop : Continuous fun p : B.SS k r => (((1 : ℝ), (1 : ℝ)), p))
  have hπ : ContinuousOn (fun p : B.SS k r => D.π (Matrix.of p.1.1)) S :=
    D.π_cont.comp (continuous_fst.fst).continuousOn (fun p hp => hp.1)
  have hinv1 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.fst).continuousOn (fun p hp => hp.1.1)
  have hinv2 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.snd).continuousOn (fun p hp => hp.2.1.1)
  have hinv3 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_snd.fst).continuousOn (fun p hp => hp.2.2.1.1)
  have hπ' : ContinuousOn (fun p : B.SS k r => D.π' (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    D.π'_cont.comp hinv3 (fun p hp => Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.2.2.1)
  have hc4 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r)) S :=
    (continuous_snd.snd).continuousOn
  have hc5 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)) S :=
    (continuous_snd.fst).continuousOn
  have hsgs : ContinuousOn (fun p : B.SS k r => B.sgs p γ) S :=
    ((((hinv1.mul hinv2).mul continuousOn_const).mul hc4).mul hc5)
  have hFs : ContinuousOn (fun p : B.SS k r => F (B.sgs p γ)) S :=
    hF.comp hsgs (fun p hp => P.B7.sgs_mem D hp hγ)
  have hcont : ContinuousOn (Formalism.FourierDecayAlt.D.orbIntegrand D γ F) S := by
    unfold Formalism.FourierDecayAlt.D.orbIntegrand B.rho
    exact hxi.continuousOn.smul (hπ.clm_comp (hFs.clm_comp hπ'))
  have h1 := hcont.aestronglyMeasurable (μ := D.μSS) hSc.measurableSet
  have hae : ∀ᵐ p ∂D.μSS, p ∈ S := P.Dx2.OrbJ.ae_inSS D
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h1

end intN

section omega

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem intR (D : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0) (hG : P.Dx2.Rad.Good D γ w d)
    {M : ℝ} (hM : 2 * ((r : ℝ) + 1) ^ 2 < M) :
    Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (-M)) (Formalism.FourierDecayAlt.D.muR D γ w) := by
  have hmu : Formalism.FourierDecayAlt.D.muR D γ w = (volume : Measure (C2.Lstidx w → ℂ)).map
      (fun x => (Matrix.of.symm (P.Dx2.Rad.rhoF D γ w x) : Mt k r)) := rfl
  have hm := P.Dx2.Rad.rhoF_meas D hγ hd hG
  have hgm : Measurable fun x : Mt k r => B.gN (Matrix.of x) ^ (-M) := (P.HaarUniquenessConjugation.gN_meas k r).pow_const _
  rw [hmu, integrable_map_measure hgm.aestronglyMeasurable hm.aemeasurable]
  obtain ⟨C, hC0, hC⟩ := uMap_le (k := k) (r := r) D.z
  have hM0 : 0 ≤ M := by nlinarith [sq_nonneg ((r : ℝ) + 1)]
  have hfin : (Module.finrank ℝ (C2.Lstidx w → ℂ) : ℝ) < M := by
    have h1 : Module.finrank ℝ (C2.Lstidx w → ℂ) = Fintype.card (C2.Lstidx w) * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex]
    have h2 : Fintype.card (C2.Lstidx w) ≤ (r + 1) ^ 2 := by
      calc Fintype.card (C2.Lstidx w) ≤ Fintype.card (Fin (r + 1) × Fin (r + 1)) := Fintype.card_subtype_le _
        _ = (r + 1) ^ 2 := by simp [sq]
    rw [h1]
    have h3 : ((Fintype.card (C2.Lstidx w) * 2 : ℕ) : ℝ) ≤ 2 * ((r : ℝ) + 1) ^ 2 := by
      have : (Fintype.card (C2.Lstidx w) : ℝ) ≤ ((r : ℝ) + 1) ^ 2 := by exact_mod_cast h2
      push_cast; linarith
    linarith
  have hint := (integrable_one_add_norm (μ := (volume : Measure (C2.Lstidx w → ℂ))) hfin).const_mul ((1 + C) ^ M)
  refine Integrable.mono' hint (hgm.comp hm).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  obtain ⟨hρR, hρu⟩ := P.Dx2.Rad.rhoF_spec D hγ hd hG y
  set ρ := P.Dx2.Rad.rhoF D γ w y with hρ
  have hρ1 : 1 ≤ B.gN ρ := P.BetaSesquilinearity.gN_ge_one hρR.1.1
  have hy : ‖y‖ ≤ C * B.gN ρ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun q => ?_
    have e : C2.uMap k r D.z ρ q.1.2 q.1.1 = star (y q) := by
      rw [hρu, Matrix.conjTranspose_apply, P.Dx2.Rad.low_coord]
    calc ‖y q‖ = ‖C2.uMap k r D.z ρ q.1.2 q.1.1‖ := by rw [e, norm_star]
      _ ≤ C * B.gN ρ := hC ρ _ _
  have hle : 1 + ‖y‖ ≤ (1 + C) * B.gN ρ := by nlinarith
  have hpos : 0 < (1 + ‖y‖) / (1 + C) := by positivity
  have hle' : (1 + ‖y‖) / (1 + C) ≤ B.gN ρ := by rw [div_le_iff₀ (by positivity)]; linarith
  simp only [Function.comp, Equiv.apply_symm_apply]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (P.B6.gN_nonneg _) _)]
  calc B.gN ρ ^ (-M) ≤ ((1 + ‖y‖) / (1 + C)) ^ (-M) := Real.rpow_le_rpow_of_nonpos hpos hle' (by linarith)
    _ = (1 + C) ^ M * (1 + ‖y‖) ^ (-M) := by
      rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + C)]
      field_simp

variable {γ : B.Mat k r} {μR : Measure (Mt k r)}

private theorem ae_R_lemma_6 (hR : B.IsHaarOn (C6.Rset γ) μR) : ∀ᵐ x ∂μR, Matrix.of x ∈ C6.Rset γ := by
  have h0 : μR (@id (Set (Mt k r)) (C6.Rset γ))ᶜ = 0 := hR.conc
  filter_upwards [mem_ae_iff.mpr h0] with x hx
  exact hx

theorem om_bound (hR : B.IsHaarOn (C6.Rset γ) μR) {M : ℝ} (hM : 0 ≤ M) {n : Mt k r}
    (hn : Matrix.of n ∈ B.GV k r) :
    ∀ᵐ x ∂μR, B.gN (Matrix.of x * Matrix.of n) ^ (-M) ≤ B.gN (Matrix.of n)⁻¹ ^ M * B.gN (Matrix.of x) ^ (-M) := by
  filter_upwards [ae_R_lemma_6 hR] with x hx
  have hxG : Matrix.of x ∈ B.GV k r := hx.1.1
  have hc := PI.PolynomialProperness.GN.gN_pos hxG
  have hb : 0 < B.gN (Matrix.of n)⁻¹ := by
    rw [PI.PolynomialProperness.GN.gN_inv hn]; exact PI.PolynomialProperness.GN.gN_pos hn
  have hle : B.gN (Matrix.of x) ≤ B.gN (Matrix.of x * Matrix.of n) * B.gN (Matrix.of n)⁻¹ := by
    calc B.gN (Matrix.of x) = B.gN (Matrix.of x * Matrix.of n * (Matrix.of n)⁻¹) := by
          rw [Matrix.mul_assoc, PI.PolynomialProperness.GN.mul_inv hn, Matrix.mul_one]
      _ ≤ _ := PI.PolynomialProperness.GN.gN_mul_le _ _
  have hle' : B.gN (Matrix.of x) / B.gN (Matrix.of n)⁻¹ ≤ B.gN (Matrix.of x * Matrix.of n) := by
    rw [div_le_iff₀ hb]; exact hle
  calc B.gN (Matrix.of x * Matrix.of n) ^ (-M)
      ≤ (B.gN (Matrix.of x) / B.gN (Matrix.of n)⁻¹) ^ (-M) := rpa_lemma (div_pos hc hb) hle' hM
    _ = B.gN (Matrix.of n)⁻¹ ^ M * B.gN (Matrix.of x) ^ (-M) := by
        rw [Real.div_rpow hc.le hb.le, Real.rpow_neg hb.le, div_inv_eq_mul, mul_comm]

private theorem gNc_lemma_3 {X : Type*} [TopologicalSpace X] {f g : X → Mt k r} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun q => B.gN (Matrix.of (f q) * Matrix.of (g q)) := by
  unfold B.gN
  refine Continuous.sqrt ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact Complex.continuous_normSq.comp (continuous_finset_sum _ fun l _ =>
    ((continuous_apply l).comp ((continuous_apply i).comp hf)).mul
      ((continuous_apply j).comp ((continuous_apply l).comp hg)))

theorem om_meas_int (M : ℝ) (n : Mt k r) :
    Measurable fun x : Mt k r => B.gN (Matrix.of x * Matrix.of n) ^ (-M) := by
  exact ((gNc_lemma_3 (k := k) (r := r) (f := id) (g := fun _ => n) continuous_id
    continuous_const).measurable).pow_const _

theorem om_int (hR : B.IsHaarOn (C6.Rset γ) μR) {M : ℝ} (hM : 0 ≤ M)
    (hI : Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (-M)) μR) {n : Mt k r}
    (hn : Matrix.of n ∈ B.GV k r) :
    Integrable (fun x : Mt k r => B.gN (Matrix.of x * Matrix.of n) ^ (-M)) μR := by
  refine (hI.const_mul (B.gN (Matrix.of n)⁻¹ ^ M)).mono' (om_meas_int M n).aestronglyMeasurable ?_
  filter_upwards [om_bound hR hM hn] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (gN_nonneg_lemma_2 _) _)]
  exact hx

private theorem gv_mul_lemma_5 {a b : B.Mat k r} (ha : a ∈ B.GV k r) (hb : b ∈ B.GV k r) :
    a * b ∈ B.GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

theorem om_pos (hR : B.IsHaarOn (C6.Rset γ) μR) {M : ℝ} (hM : 0 ≤ M)
    (hI : Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (-M)) μR) {n : Mt k r}
    (hn : Matrix.of n ∈ B.GV k r) : 0 < Om μR M n := by
  unfold Om
  have hint := om_int hR hM hI hn
  have hnn : ∀ x, 0 ≤ B.gN (Matrix.of x * Matrix.of n) ^ (-M) := fun x => Real.rpow_nonneg (gN_nonneg_lemma_2 _) _
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hsub : @id (Set (Mt k r)) (C6.Rset γ) ⊆
      Function.support (fun x : Mt k r => B.gN (Matrix.of x * Matrix.of n) ^ (-M)) := by
    intro x hx
    have hxG : Matrix.of x ∈ B.GV k r := (hx : Matrix.of x ∈ C6.Rset γ).1.1
    exact (Real.rpow_pos_of_pos (PI.PolynomialProperness.GN.gN_pos (gv_mul_lemma_5 hxG hn)) _).ne'
  have hpos : 0 < μR (@id (Set (Mt k r)) (C6.Rset γ)) := by
    rw [pos_iff_ne_zero]
    intro h0
    apply hR.ne_zero
    rw [← Measure.measure_univ_eq_zero]
    have hc : μR (@id (Set (Mt k r)) (C6.Rset γ))ᶜ = 0 := hR.conc
    exact le_antisymm ((measure_univ_le_add_compl (@id (Set (Mt k r)) (C6.Rset γ))).trans
      (le_of_eq (by rw [h0, hc, add_zero]))) (by simp)
  exact hpos.trans_le (measure_mono hsub)

theorem om_shift (hR : B.IsHaarOn (C6.Rset γ) μR) (M : ℝ) {ρ : B.Mat k r} (hρ : ρ ∈ C6.Rset γ)
    (n : Mt k r) : Om μR M (Matrix.of.symm (ρ * Matrix.of n)) = Om μR M n := by
  have hmeas : Measurable (B.rmulF ρ) := by
    refine Continuous.measurable (continuous_pi fun i => continuous_pi fun j => ?_)
    simp only [B.rmulF, Matrix.mul_apply, Matrix.of_apply]
    exact continuous_finset_sum _ fun l _ => by fun_prop
  unfold Om
  calc ∫ x, B.gN (Matrix.of x * Matrix.of (Matrix.of.symm (ρ * Matrix.of n))) ^ (-M) ∂μR
      = ∫ x, (fun y : Mt k r => B.gN (Matrix.of y * Matrix.of n) ^ (-M)) (B.rmulF ρ x) ∂μR := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show B.gN (Matrix.of x * (ρ * Matrix.of n)) ^ (-M) = B.gN (Matrix.of x * ρ * Matrix.of n) ^ (-M)
        rw [mul_assoc]
    _ = ∫ y, B.gN (Matrix.of y * Matrix.of n) ^ (-M) ∂(μR.map (B.rmulF ρ)) :=
        (integral_map hmeas.aemeasurable (om_meas_int M n).aestronglyMeasurable).symm
    _ = ∫ y, B.gN (Matrix.of y * Matrix.of n) ^ (-M) ∂μR := by rw [hR.right ρ hρ]

theorem om_lower (hR : B.IsHaarOn (C6.Rset γ) μR) {M : ℝ} (hM : 0 ≤ M)
    (hI : Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (-M)) μR) {ρ σ : B.Mat k r}
    (hρ : ρ ∈ C6.Rset γ) (hσ : σ ∈ B.GV k r) :
    (∫ x, B.gN (Matrix.of x) ^ (-M) ∂μR) * B.gN σ ^ (-M) ≤ Om μR M (Matrix.of.symm (ρ * σ)) := by
  have hshift := om_shift hR M hρ (Matrix.of.symm σ)
  rw [Equiv.apply_symm_apply] at hshift
  rw [hshift]
  unfold Om
  rw [← integral_mul_const]
  refine integral_mono_ae (hI.mul_const _) (om_int hR hM hI (n := Matrix.of.symm σ) hσ) ?_
  filter_upwards [ae_R_lemma_6 hR] with x hx
  have hxG : Matrix.of x ∈ B.GV k r := hx.1.1
  have hc := PI.PolynomialProperness.GN.gN_pos hxG
  have hs := PI.PolynomialProperness.GN.gN_pos hσ
  have ha := PI.PolynomialProperness.GN.gN_pos (gv_mul_lemma_5 hxG hσ)
  have hle := PI.PolynomialProperness.GN.gN_mul_le (Matrix.of x) σ
  show B.gN (Matrix.of x) ^ (-M) * B.gN σ ^ (-M) ≤ B.gN (Matrix.of x * σ) ^ (-M)
  rw [← Real.mul_rpow hc.le hs.le]
  exact rpa_lemma ha hle hM

private theorem gNc1_lemma_4 : Continuous fun x : Mt k r => B.gN (Matrix.of x) := by
  unfold B.gN
  refine Continuous.sqrt ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  simp only [Matrix.of_apply]
  exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))

theorem cut_meas [SFinite μR] (M : ℝ) : Measurable (cut μR M) := by
  have hf : StronglyMeasurable fun q : Mt k r × Mt k r => B.gN (Matrix.of q.2 * Matrix.of q.1) ^ (-M) :=
    ((gNc_lemma_3 (f := fun q : Mt k r × Mt k r => q.2) (g := fun q => q.1) continuous_snd
      continuous_fst).measurable.pow_const _).stronglyMeasurable
  have hOm : Measurable fun n : Mt k r => Om μR M n :=
    (StronglyMeasurable.integral_prod_right' (ν := μR) hf).measurable
  have hg : Measurable fun n : Mt k r => B.gN (Matrix.of n) ^ (-M) := (gNc1_lemma_4.measurable).pow_const _
  exact (hg.comp measurable_fst.snd).div (hOm.comp measurable_fst.snd)

theorem cut_nonneg (μR : Measure (Mt k r)) (M : ℝ) (p : B.SS k r) : 0 ≤ cut μR M p := by
  unfold cut Om
  exact div_nonneg (Real.rpow_nonneg (gN_nonneg_lemma_2 _) _)
    (integral_nonneg fun x => Real.rpow_nonneg (gN_nonneg_lemma_2 _) _)

theorem cut_norm (hR : B.IsHaarOn (C6.Rset γ) μR) {M : ℝ} (hM : 0 ≤ M)
    (hI : Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (-M)) μR) (p : B.SS k r)
    (hn : Matrix.of p.1.2 ∈ Nset k r) :
    ∫ x, cut μR M (C6.actR γ (Matrix.of x) p) ∂μR = 1 := by
  have hn' : Matrix.of p.1.2 ∈ B.GV k r := hn.1
  have hpos := om_pos hR hM hI hn'
  have hae : ∀ᵐ x ∂μR, cut μR M (C6.actR γ (Matrix.of x) p) =
      B.gN (Matrix.of x * Matrix.of p.1.2) ^ (-M) / Om μR M p.1.2 := by
    filter_upwards [ae_R_lemma_6 hR] with x hx
    show B.gN (Matrix.of x * Matrix.of p.1.2) ^ (-M) /
      Om μR M (Matrix.of.symm (Matrix.of x * Matrix.of p.1.2)) = _
    rw [om_shift hR M hx p.1.2]
  rw [integral_congr_ae hae, integral_div]
  exact div_self hpos.ne'

end omega

section geom

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem geom (D : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) (hpos : 0 < Gf k r D.z D.z' γ)
    {e : ℕ} {CP : ℝ}
    (hCP : ∀ σ ∈ C2.Sg k r D.z D.z' γ, ∀ s' ∈ Sset k r D.z', B.gN σ + B.gN s' ≤ CP * B.gN (σ⁻¹ * γ * s') ^ e)
    (hmono : C2.IsMonomial (Zhat k r D.z D.z' γ))
    {n n' : B.Mat k r} (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) :
    ∃ ρ σ : B.Mat k r, ∃ X : ℝ, ρ ∈ C6.Rset γ ∧ σ ∈ B.GV k r ∧ n = ρ * σ ∧ B.gN σ ≤ X ∧
      X ≤ CP * B.gN (n⁻¹ * γ * n') ^ e ∧ B.gN n' ≤ (B.gN γ⁻¹ * B.gN γ) * B.gN n * X ^ 2 := by
  obtain ⟨⟨ρ, σ⟩, ⟨hρ, hσSg, hnρσ⟩, -⟩ := P.c2_section_decomp k r D.z D.z' γ (P.Dx2.Rad.std D) ⟨hγ, hpos⟩ hmono n
    (P.Dx2.Rad.N_sub_S D.z hn)
  simp only at hρ hσSg hnρσ
  rw [← P.Dx2.Rad.rset_eq D hγ hpos] at hρ
  have hγu : IsUnit γ.det := (P.unitary_group_closed k r).unit γ hγ
  have hRg := P.Dx2.OrbJ.closedR hγu
  have hNg := P.unipotent_radical_closed k r
  have hρu : IsUnit ρ.det := hRg.unit ρ hρ
  have hρi : ρ⁻¹ ∈ C6.Rset γ := hRg.inv_mem ρ hρ
  have hσe : σ = ρ⁻¹ * n := by rw [hnρσ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hρu, Matrix.one_mul]
  have hσN : σ ∈ Nset k r := by rw [hσe]; exact hNg.mul_mem _ hρi.1 _ hn
  have hσG : σ ∈ B.GV k r := hσN.1
  set s'' := γ⁻¹ * ρ⁻¹ * γ * n' with hs''
  have hs''N : s'' ∈ Nset k r := hNg.mul_mem _ hρi.2 _ hn'
  have hσu : IsUnit σ.det := hNg.unit σ hσN
  have hkey : σ⁻¹ * γ * s'' = n⁻¹ * γ * n' := by
    rw [hσe, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hρu, hs'']
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hγu, Matrix.mul_nonsing_inv_cancel_left _ _ hρu]
  refine ⟨ρ, σ, B.gN σ + B.gN s'', hρ, hσG, hnρσ, ?_, ?_, ?_⟩
  · linarith [P.B6.gN_nonneg s'']
  · have := hCP σ hσSg s'' (P.Dx2.Rad.N_sub_S D.z' hs''N)
    rwa [hkey] at this
  · have hn'e : n' = γ⁻¹ * ρ * γ * s'' := by
      rw [hs'']
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hγu, Matrix.mul_nonsing_inv_cancel_left _ _ hρu,
        Matrix.nonsing_inv_mul_cancel_left _ _ hγu]
    have hρe : ρ = n * σ⁻¹ := by rw [hnρσ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hσu, Matrix.mul_one]
    have hgρ : B.gN ρ ≤ B.gN n * B.gN σ := by
      rw [hρe]
      calc B.gN (n * σ⁻¹) ≤ B.gN n * B.gN σ⁻¹ := P.B6.gN_mul_le _ _
        _ = B.gN n * B.gN σ := by rw [(P.norm_of_inverse k r σ hσG).1]
    have h0 := P.B6.gN_nonneg (γ⁻¹ : B.Mat k r)
    have h0' := P.B6.gN_nonneg γ
    have h0n := P.B6.gN_nonneg n
    have h0s := P.B6.gN_nonneg σ
    have h0s'' := P.B6.gN_nonneg s''
    have h0ρ := P.B6.gN_nonneg ρ
    calc B.gN n' = B.gN (γ⁻¹ * ρ * γ * s'') := by rw [← hn'e]
      _ ≤ B.gN γ⁻¹ * B.gN ρ * B.gN γ * B.gN s'' := by
        refine (P.B6.gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ h0s'')
        refine (P.B6.gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ h0')
        exact P.B6.gN_mul_le _ _
      _ ≤ B.gN γ⁻¹ * (B.gN n * B.gN σ) * B.gN γ * B.gN s'' := by
        have := mul_le_mul_of_nonneg_left hgρ h0
        have := mul_le_mul_of_nonneg_right this h0'
        exact mul_le_mul_of_nonneg_right this h0s''
      _ ≤ (B.gN γ⁻¹ * B.gN γ) * B.gN n * (B.gN σ + B.gN s'') ^ 2 := by
        have hX : B.gN σ * B.gN s'' ≤ (B.gN σ + B.gN s'') ^ 2 := by nlinarith
        have hc : 0 ≤ B.gN γ⁻¹ * B.gN γ * B.gN n := by positivity
        calc B.gN γ⁻¹ * (B.gN n * B.gN σ) * B.gN γ * B.gN s''
            = (B.gN γ⁻¹ * B.gN γ * B.gN n) * (B.gN σ * B.gN s'') := by ring
          _ ≤ (B.gN γ⁻¹ * B.gN γ * B.gN n) * (B.gN σ + B.gN s'') ^ 2 := mul_le_mul_of_nonneg_left hX hc

end geom

theorem d_orbJConv : Formalism.FourierDecayAlt.D.OrbJConv := by
  obtain ⟨c₁, hPP⟩ := Formalism.FourierDecayAlt.P.polynomial_map_proper
  refine ⟨16 * ((c₁ : ℝ) + 1), ?_⟩
  intro k r Wp Wq _ _ _ _ D γ w d A F hγ _hrel hd hZ hpos hA hF
  set nn : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hnn
  set bN : ℝ := 4 * ((r : ℝ) * nn + 1) with hbN
  set c : ℕ := (c₁ + 1) * (r + 1) ^ 2 with hc
  set M : ℝ := A / c - 2 * bN with hM
  have hmono : C2.IsMonomial (Zhat k r D.z D.z' γ) := ⟨w, d, hd, hZ⟩
  obtain ⟨CP, hCP, -⟩ := hPP k r D.z D.z' γ (P.Dx2.Rad.std D) ⟨hγ, hpos⟩ hmono

  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc1
  have hnn0 : 0 ≤ nn := by positivity
  have hrn : 0 ≤ (r : ℝ) * nn := by positivity
  have hbN0 : 0 ≤ bN := by positivity
  have hccast : (c : ℝ) = ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 := by rw [hc]; push_cast; ring
  have hAc : 16 * ((r : ℝ) * nn + 1) ≤ A / c := by
    rw [le_div_iff₀ hcpos, hccast]
    calc 16 * ((r : ℝ) * nn + 1) * (((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2)
        = 16 * ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * nn + 1) := by ring
      _ ≤ A := hA
  have hA4 : 4 * bN ≤ A / c := by rw [hbN]; linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast D.k_pos
  have hr2 : ((r : ℝ) + 1) ^ 2 ≤ (r : ℝ) * nn + 1 := by
    rw [hnn]; push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
      (show (0 : ℝ) ≤ r + k - 1 by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])]
  have hMR : 2 * ((r : ℝ) + 1) ^ 2 < M := by
    rw [hM, hbN]; nlinarith [sq_nonneg ((r : ℝ) + 1)]
  have hM0 : 0 ≤ M := by nlinarith [sq_nonneg ((r : ℝ) + 1)]
  have hA0 : 0 ≤ A := by
    have := div_nonneg_iff.mp (show 0 ≤ A / c by linarith)
    rcases this with h | h
    · exact h.1
    · linarith [h.2]

  have hG : P.Dx2.Rad.Good D γ w d := ⟨P.Dx2.Rad.exists_rho D hγ hpos hd hZ, P.Dx2.Rad.u_inj D hγ hpos hd hZ,
    fun ρ hρ => P.Dx2.Rad.u_lstg D hγ hpos hd hZ hρ⟩
  have hR := P.Dx2.Rad.haar_good D hγ hd hG
  have := P.Dx2.OrbJ.sigmaF hR
  have hI := intR D hγ hd hG hMR
  set μR := Formalism.FourierDecayAlt.D.muR D γ w with hμR
  set cR : ℝ := ∫ x, B.gN (Matrix.of x) ^ (-M) ∂μR with hcRdef
  have hone : Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ B.GV k r := by
    simpa using (P.unitary_group_closed k r).one_mem
  have hcR : 0 < cR := by
    have := om_pos hR hM0 hI hone
    simpa [Om] using this

  obtain ⟨sharpFunctionalExponent, hCC⟩ := hF
  set cF := max sharpFunctionalExponent 0 with hcF
  have hFb : ∀ g ∈ B.GV k r, ‖F g‖ ≤ cF * B.gN g ^ (-A) := by
    intro g hg
    have h0 := hCC.2 [] [] (by simp) (by simp) (by simp) g hg
    have e : B.dLR [] [] F g = F g := rfl
    rw [e] at h0
    have hg1 : 1 ≤ B.gN g := P.BetaSesquilinearity.gN_ge_one hg
    have hpw : 0 < B.gN g ^ A := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hpw]
    calc ‖F g‖ * B.gN g ^ A = B.gN g ^ A * ‖F g‖ := by ring
      _ ≤ sharpFunctionalExponent := h0
      _ ≤ cF := le_max_left _ _
  have hFc : ContinuousOn F (B.GV k r) := P.B5.ckOn_continuousOn hCC.1

  obtain ⟨KW, hKW1, hKW⟩ := UW_bound D.z D.z_mem D.T_pos
  obtain ⟨KW', hKW1', hKW'⟩ := UW_bound D.z' D.z'_mem D.T'_pos
  set K1 := KW * KW' with hK1
  set Kγ := B.gN γ⁻¹ * B.gN γ with hKγ
  have hγ1 : 1 ≤ B.gN γ := P.BetaSesquilinearity.gN_ge_one hγ
  have hγi : B.gN γ⁻¹ = B.gN γ := (P.norm_of_inverse k r γ hγ).1
  have hKγ0 : 0 < Kγ := by rw [hKγ, hγi]; nlinarith
  set Kf := cF * K1 ^ A * CP ^ (A / c) * Kγ ^ bN / cR with hKf
  refine ⟨cut μR M, ⟨cut_meas M, cut_nonneg μR M, fun p hp => cut_norm hR hM0 hI p hp.2.1⟩, ?_⟩
  have hmaj := (maj_int D (A / c - 3 * bN) bN (by linarith) le_rfl).const_mul Kf
  refine Integrable.mono' hmaj ((cut_meas M).aestronglyMeasurable.smul (integrand_aesm D hγ hFc)) ?_
  filter_upwards [P.Dx2.OrbJ.ae_inSS D] with p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  obtain ⟨ρ, σ, X, hρ, hσ, hnρσ, hσX, hXY, hn'le⟩ := geom D hγ hpos hCP hmono h2 h4
  have hN1 : 1 ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one h2.1
  have hN1' : 1 ≤ B.gN (Matrix.of p.2.2 : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one h4.1
  have hS1 : 1 ≤ B.gN σ := P.BetaSesquilinearity.gN_ge_one hσ
  have hg0 : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 ∈ B.GV k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1) hγ) h4.1
  have hY1 : 1 ≤ B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) := P.BetaSesquilinearity.gN_ge_one hg0
  have hsgs := P.B7.sgs_mem D ⟨h1, h2, h3, h4⟩ hγ
  have hGg : 0 < B.gN (B.sgs p γ) := by linarith [P.BetaSesquilinearity.gN_ge_one hsgs]
  have hYG : B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) ≤ K1 * B.gN (B.sgs p γ) := by
    have hhu : IsUnit (Matrix.of p.1.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h1.1
    have hh'u : IsUnit (Matrix.of p.2.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h3.1
    have e : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 =
        (Matrix.of p.1.1 : B.Mat k r) * B.sgs p γ * (Matrix.of p.2.1 : B.Mat k r)⁻¹ := by
      simp only [B.sgs, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hhu, Matrix.mul_nonsing_inv _ hh'u, Matrix.mul_one]
    rw [e]
    calc B.gN ((Matrix.of p.1.1 : B.Mat k r) * B.sgs p γ * (Matrix.of p.2.1 : B.Mat k r)⁻¹)
        ≤ B.gN (Matrix.of p.1.1 : B.Mat k r) * B.gN (B.sgs p γ) * B.gN (Matrix.of p.2.1 : B.Mat k r)⁻¹ :=
          (P.B6.gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right (P.B6.gN_mul_le _ _) (P.B6.gN_nonneg _))
      _ ≤ KW * B.gN (B.sgs p γ) * KW' := by
          have a1 := hKW _ h1
          have a2 := hKW' _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv h3)
          have s0 := P.B6.gN_nonneg (B.sgs p γ)
          exact mul_le_mul (mul_le_mul_of_nonneg_right a1 s0) a2 (P.B6.gN_nonneg _)
            (mul_nonneg (by linarith) s0)
      _ = K1 * B.gN (B.sgs p γ) := by rw [hK1]; ring
  have hθ : cut μR M p ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR := by
    have hlow := om_lower hR hM0 hI hρ hσ
    have e : Matrix.of.symm (ρ * σ) = p.1.2 := by rw [← hnρσ]; exact Equiv.symm_apply_apply _ _
    rw [e] at hlow
    have hσp : 0 < B.gN σ ^ (-M) := Real.rpow_pos_of_pos (by linarith) _
    have hpos' : 0 < cR * B.gN σ ^ (-M) := mul_pos hcR hσp
    unfold cut
    calc B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) / Om μR M p.1.2
        ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) / (cR * B.gN σ ^ (-M)) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg (P.B6.gN_nonneg _) _) hpos' hlow
      _ = B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR := by
          rw [Real.rpow_neg (P.B6.gN_nonneg σ)]
          have : 0 < B.gN σ ^ M := Real.rpow_pos_of_pos (by linarith) _
          field_simp
  have hθ0 := cut_nonneg μR M p
  have hFv : ‖B.rho D p F γ‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A) :=
    (P.B7.norm_rho_le D ⟨h1, h2, h3, h4⟩ F γ).trans (hFb _ hsgs)
  have hCP0 : 0 < CP := by
    by_contra hle'
    have hle := not_lt.mp hle'
    have := mul_nonpos_of_nonpos_of_nonneg hle
      (pow_nonneg (P.B6.gN_nonneg ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2)) (c₁ * (r + 1) ^ 2))
    linarith
  have hec : c₁ * (r + 1) ^ 2 ≤ c := Nat.mul_le_mul_right _ (Nat.le_succ _)
  have hXY' : X ≤ CP * B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) ^ c :=
    hXY.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 hec) hCP0.le)
  have hK10 : 0 < K1 := by rw [hK1]; positivity
  have hkey := key_real hN1 hS1 hσX hY1 hGg hc1 hXY' hn'le hN1' hYG hθ hθ0 hFv (norm_nonneg _) hcR
    (le_max_right _ _) hCP0 hK10 hKγ0 hM hbN0 hA4
  rw [norm_smul, Real.norm_of_nonneg hθ0]
  unfold Formalism.FourierDecayAlt.D.orbIntegrand
  rw [norm_smul, P.B7.norm_xi, one_mul]
  exact hkey

end Formalism.FourierDecayAlt.P.Dx3

theorem Formalism.FourierDecayAlt.P.orbital_integral_converges : Formalism.FourierDecayAlt.D.OrbJConv := Formalism.FourierDecayAlt.P.Dx3.d_orbJConv
