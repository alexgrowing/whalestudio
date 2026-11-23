import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumNormLePolynomialScale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameDarbouxCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusActionModelCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzThetaPolynomialGrowthStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.TorusTheta

theorem min_pow_le_of_mem_cone {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ}
    (ht : t ∈ GlobalTheory.SiegelSet.cone r c) (i : Fin r) : min 1 c ^ r ≤ t i := by
  obtain ⟨hpos, hstep, hlast⟩ := ht
  have hm0 : 0 < min 1 c := lt_min one_pos hc
  have hm1 : min 1 c ≤ 1 := min_le_left _ _
  have key : ∀ k : ℕ, ∀ i : Fin r, i.val + k + 1 = r → min 1 c ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simp only [zero_add, pow_one]
      exact (min_le_right _ _).trans (hlast i (by omega))
    | succ k ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have h1 := ih ⟨i.val + 1, hj⟩ (by simp; omega)
      have h2 := hstep i ⟨i.val + 1, hj⟩ rfl
      have h3 : 0 < t ⟨i.val + 1, hj⟩ := hpos _
      calc min 1 c ^ (k + 1 + 1) = min 1 c * min 1 c ^ (k + 1) := by ring
        _ ≤ min 1 c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 hm0.le
        _ ≤ c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_right (min_le_right _ _) h3.le
        _ ≤ t i := h2
  have := key (r - i.val - 1) i (by omega)
  refine le_trans ?_ this
  exact pow_le_pow_of_le_one hm0.le hm1 (by omega)

theorem mul_norm_le_norm_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V] {c' : ℝ} (hc' : 0 < c')
    (s : ι → ℝ) (hs : ∀ i, c' ≤ s i) (v : ι → V) : c' * ‖v‖ ≤ ‖fun i => s i • v i‖ := by
  rw [← le_div_iff₀' hc']
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [le_div_iff₀' hc']
  have hsi : 0 < s i := hc'.trans_le (hs i)
  calc c' * ‖v i‖ ≤ s i * ‖v i‖ := mul_le_mul_of_nonneg_right (hs i) (norm_nonneg _)
    _ = ‖s i • v i‖ := by rw [norm_smul, Real.norm_of_nonneg hsi.le]
    _ ≤ ‖fun i => s i • v i‖ := norm_le_pi_norm (fun i => s i • v i) i

theorem prod_elim_pow {κ : Type} [Fintype κ] {r : ℕ} (blk : κ → Option (Fin r)) (t : Fin r → ℝ) (f d : ℕ)
    (hcard : ∀ i : Fin r, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) :
    ∏ j, (blk j).elim 1 t ^ f = (∏ i, t i ^ (f * d)) ^ 2 := by
  rw [← Finset.prod_fiberwise (Finset.univ : Finset κ) blk (fun j => ((blk j).elim 1 t : ℝ) ^ f)]
  have h1 : ∀ o : Option (Fin r), ∏ j ∈ Finset.univ.filter (fun j => blk j = o), (blk j).elim 1 t ^ f =
      (o.elim 1 t ^ f) ^ (Finset.univ.filter (fun j => blk j = o)).card := by
    intro o
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]
  rw [Finset.prod_congr rfl (fun o _ => h1 o), Fintype.prod_option]
  simp only [Option.elim_none, Option.elim_some, one_pow, one_mul, hcard]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

end GlobalTheory.TorusTheta

namespace GlobalTheory.TorusTheta

theorem theta_torus_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf → ∀ c : ℝ, 0 < c →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ a' : UA σ X.J,
      (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a → ∀ (y : UA σ X.J) (h : UA σ W.J),
      ‖theta om Φ (a' * y) h‖ ≤ C * ((ht y : ℝ) * ht h) ^ k * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt c hc Φ hΦ
  obtain ⟨co, blk, hrat, hcard, hact⟩ := GlobalTheory.T.witt_frame_darboux_coordinates F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt
  obtain ⟨M₁, om₁, e, c₀, hco, hP₁, hc₀, he⟩ := GlobalTheory.T.darboux_coords_rational_points F E σ B n d X W M χX χW om r s r' s' hP co hrat
  obtain ⟨N₀, k₃, C₃, hlat⟩ := GlobalTheory.LatScaleSum.thetaSum_norm_le_pow F (Fin n × Fin d)
  have heΦ := (he Φ hΦ).1
  obtain ⟨C₁, k₁, hdec⟩ := GlobalTheory.T.weilRepresentation_pointwise_archimedeanDecay_bound F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ (e Φ) heΦ N₀
  obtain ⟨C₂, k₂, hden⟩ := GlobalTheory.T.schwartz_theta_polynomial_growth F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ (e Φ) heΦ
  set c' : ℝ := min 1 c ^ r₀ with hc'def
  have hc'0 : 0 < c' := pow_pos (lt_min one_pos hc) _
  have hc'1 : c' ≤ 1 := pow_le_one₀ (lt_min one_pos hc).le (min_le_left _ _)
  refine ⟨‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃, k₁ + k₂ * k₃, ?_⟩
  intro t htc a hta a' ha' y h
  have tlow : ∀ i, c' ≤ t i := min_pow_le_of_mem_cone hc htc
  have tpos : ∀ i, 0 < t i := fun i => hc'0.trans_le (tlow i)
  set u : Fin n × Fin d → ℝ := fun j => (blk j).elim 1 t with hudef
  have hulow : ∀ j, c' ≤ u j := by
    intro j
    simp only [hudef]
    cases blk j with
    | none => exact hc'1
    | some i => exact tlow i
  have hupos : ∀ j, 0 < u j := fun j => hc'0.trans_le (hulow j)
  obtain ⟨κ, hκ, hom⟩ := GlobalTheory.T.torus_action_model_coordinates F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ a' u hupos
    (by rw [hco]; exact hact t tpos a hta a' ha')

  have hΨ0 : om (y, h) Φ ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΦ
  have hT : om (a', 1) (om (y, h) Φ) ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΨ0
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ, Ψ = om₁ (y, h) (e Φ) := ⟨_, rfl⟩
  have hΨ : Ψ ∈ schA F (Fin n × Fin d) := hΨdef ▸ (IsUWeilPair.isUSplitting hP₁.weil).pres _ _ heΦ
  have hmul : ((a' * y, h) : UA σ X.J × UA σ W.J) = (a', 1) * (y, h) := by
    ext <;> simp
  have hsplit : om (a' * y, h) Φ = om (a', 1) (om (y, h) Φ) := by
    rw [hmul, map_mul, Module.End.mul_apply]
  have heT : e (om (a', 1) (om (y, h) Φ)) = om₁ (a', 1) Ψ := by
    rw [(he _ hΨ0).2.2, (he Φ hΦ).2.2, hΨdef]
  have hthT : thetaSum F (om (a', 1) (om (y, h) Φ)) = c₀⁻¹ * thetaSum F (om₁ (a', 1) Ψ) := by
    rw [← heT, (he _ hT).2.1, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]
  have hfun : om₁ (a', 1) Ψ = fun x => κ * Ψ (fun j => infScale F (u j) * x j) := funext (hom Ψ hΨ)
  have hkey : theta om Φ (a' * y) h =
      c₀⁻¹ * (κ * thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))) := by
    show thetaSum F (om (a' * y, h) Φ) = _
    rw [hsplit, hthT, hfun]
    unfold thetaSum
    rw [tsum_mul_left]

  have hκ' : ‖κ‖ = ∏ i, t i ^ (Module.finrank ℚ F * d) := by
    have h2 : ‖κ‖ ^ 2 = (∏ i, t i ^ (Module.finrank ℚ F * d)) ^ 2 := by
      rw [hκ]
      exact prod_elim_pow blk t _ d hcard
    have hnn : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
      Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
    exact (pow_left_inj₀ (norm_nonneg _) hnn two_ne_zero).1 h2

  set P : ℝ := (ht y : ℝ) * ht h with hPdef
  have hP0 : 0 ≤ P := mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  obtain ⟨m, hm1, hmC, hmint⟩ := hden y h
  have hdecay : ∀ ξ : Fin n × Fin d → F,
      ‖Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j)‖ *
        (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ (c'⁻¹) ^ N₀ * (C₁ * P ^ k₁) := by
    intro ξ
    beta_reduce
    have h1 := hdec y h (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))
    rw [← hΨdef] at h1
    have hnorm : c' * ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
        ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ := by
      simp only [evI_infScale_mul]
      exact mul_norm_le_norm_smul hc'0 u hulow _
    have hle : 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
        c'⁻¹ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) := by
      have hi : 1 ≤ c'⁻¹ := one_le_inv₀ hc'0 |>.2 hc'1
      have h3 : ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
          c'⁻¹ * ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ := by
        rw [le_inv_mul_iff₀ hc'0]; exact hnorm
      nlinarith [norm_nonneg (fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i)))]
    have hpow : (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤
        (c'⁻¹) ^ N₀ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀ := by
      have h0 : 0 ≤ 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ :=
        add_nonneg zero_le_one (norm_nonneg _)
      have h4 := pow_le_pow_left₀ h0 hle N₀
      rw [mul_pow] at h4
      exact h4
    calc ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀
        ≤ ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          ((c'⁻¹) ^ N₀ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (c'⁻¹) ^ N₀ * (‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀) := by ring
      _ ≤ (c'⁻¹) ^ N₀ * (C₁ * P ^ k₁) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hint : ∀ ξ : Fin n × Fin d → F,
      Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j) ≠ 0 →
        ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
    intro ξ hne
    rw [hΨdef] at hne
    exact hmint _ ξ (fun i => infScale_mul_snd F (u i) _) hne
  have hS := hlat ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) m (fun x => Ψ (fun j => infScale F (u j) * x j)) hm1 hdecay hint

  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmk : (m : ℝ) ^ k₃ ≤ |C₂| ^ k₃ * P ^ (k₂ * k₃) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hm0 (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hP0 _))) k₃
  have hS' : ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖ ≤
      |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃) := by
    refine hS.trans ?_
    calc C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) * (m : ℝ) ^ k₃
        ≤ |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) * (m : ℝ) ^ k₃ := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hm0 _)
          calc C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) ≤ |C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁))| := le_abs_self _
            _ = |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (c'⁻¹) ^ N₀),
                abs_of_nonneg (pow_nonneg hP0 _)]
      _ ≤ |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) * (|C₂| ^ k₃ * P ^ (k₂ * k₃)) :=
          mul_le_mul_of_nonneg_left hmk (by positivity)
      _ = |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃) := by ring
  rw [hkey, norm_mul, norm_mul, norm_inv, hκ']
  have hT0 : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
  calc ‖c₀‖⁻¹ * ((∏ i, t i ^ (Module.finrank ℚ F * d)) * ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖)
      ≤ ‖c₀‖⁻¹ * ((∏ i, t i ^ (Module.finrank ℚ F * d)) *
          (|C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃))) := by gcongr
    _ = _ := by ring

end GlobalTheory.TorusTheta
