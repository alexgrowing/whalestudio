import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBaseEqOfClosedDiscExtendsNormLeOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiContractionDiscStepStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_root_radii (l : ℕ) (hl : 2 ≤ l) (ρ₀ : ℝ≥0) (h0 : 0 < ρ₀) (h1 : ρ₀ < 1) :
    ∃ r : ℕ → ℝ≥0, r 0 = ρ₀ ∧ (∀ n, r (n + 1) ^ l = r n) ∧ (∀ n, ρ₀ ≤ r n) ∧ (∀ n, r n < 1) ∧
      ∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ n, ρ₁ ≤ r n := by
  have hl0 : l ≠ 0 := by omega
  let r : ℕ → ℝ≥0 := fun n => ρ₀ ^ (((l ^ n : ℕ) : ℝ)⁻¹)
  have hp : ∀ n, r n ^ (l ^ n) = ρ₀ := fun n => NNReal.rpow_inv_natCast_pow _ (pow_ne_zero _ hl0)
  have hlt : ∀ n, r n < 1 := fun n => by
    by_contra h
    have := one_le_pow₀ (not_lt.1 h) (n := l ^ n)
    rw [hp] at this
    exact absurd h1 (not_lt.2 this)
  refine ⟨r, by simpa using hp 0, fun n => ?_, fun n => ?_, hlt, fun ρ₁ h => ?_⟩
  · refine (pow_left_inj₀ zero_le zero_le (pow_ne_zero n hl0)).1 ?_
    rw [← pow_mul, ← pow_succ', hp, hp]
  · rw [← hp n]
    exact pow_le_of_le_one zero_le (hlt n).le (pow_ne_zero _ hl0)
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h0 h
    refine ⟨n, le_of_lt (lt_of_pow_lt_pow_left₀ (l ^ n) zero_le ?_)⟩
    rw [hp]
    exact (pow_le_pow_of_le_one zero_le h.le (Nat.lt_pow_self (by omega)).le).trans_lt hn

theorem norm_l_pow_mul_disc (l : ℕ) [Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (k : ℕ)
    (y : Disc l u ρ) : ‖((l : ℕ) : Disc l u ρ) ^ k * y‖ = ‖y‖ / (l : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A u ρ).2.1, ih, div_div, pow_succ]

theorem exists_bounded_of_phi_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), Filter.Tendsto V Filter.cofinite (nhds 0) → (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∃ (k : ℕ) (v : κ → A), (∀ j, toDisc l (s X) bk.ρ₀ (v j) = (l : Disc l (s X) bk.ρ₀) ^ k * V j) ∧ ∀ n : ℕ, {j | v j ∉ (bk.J ^ n).map s}.Finite := by
  intro l hl K bk A _ s ι tb φ hφ Φ hΦ κ c hc h V hV hs
  obtain ⟨-, -, ⟨h0, h1, -⟩, -⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have hl2 := hl.out.two_le
  obtain ⟨r, r0, rs, rle, rlt, rlim⟩ := exists_root_radii l hl2 bk.ρ₀ h0 h1
  have rpos : ∀ n, 0 < r n := fun n => h0.trans_le (rle n)
  have hR : ∀ n, ∃ R : Disc l (s X) (r n) →+* Disc l (s X) bk.ρ₀, IsDiscMap (RingHom.id A) R := fun n =>
    GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l A A (RingHom.id A) (s X) (s X) (r n) bk.ρ₀ 1 h0 (by simp) (by simpa using rle n)
  choose R hR using hR
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ j, ‖V j‖ ≤ C := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto_cofinite hV)
    exact ⟨max C 0, le_max_right _ _, fun j => (hC _ ⟨j, rfl⟩).trans (le_max_left _ _)⟩
  set m := bk.Ep.natDegree * h with hm
  have h0' : (0 : ℝ) < bk.ρ₀ := h0
  have key : ∀ n, ∃ U : κ → Disc l (s X) (r n), Filter.Tendsto U Filter.cofinite (nhds 0) ∧
      (∀ j, R n (U j) = V j) ∧ ∀ j, ‖U j‖ ≤ C * ((r n : ℝ) / bk.ρ₀) ^ m := by
    intro n
    induction n with
    | zero =>
      have gen : ∀ (ρ : ℝ≥0) (R₀ : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀), ρ = bk.ρ₀ →
          IsDiscMap (RingHom.id A) R₀ → ∃ U : κ → Disc l (s X) ρ, Filter.Tendsto U Filter.cofinite (nhds 0) ∧
          (∀ j, R₀ (U j) = V j) ∧ ∀ j, ‖U j‖ ≤ C * ((ρ : ℝ) / bk.ρ₀) ^ m := by
        rintro ρ R₀ rfl hR₀
        refine ⟨V, hV, fun j => ?_, fun j => ?_⟩
        · rw [hR₀.unique (isDiscMap_id l (s X) bk.ρ₀)]; rfl
        · rw [div_self h0'.ne', one_pow, mul_one]; exact hC j
      exact gen _ _ r0 (hR 0)
    | succ n ih =>
      obtain ⟨U, hU, hRU, hn⟩ := ih
      obtain ⟨U', hU', hRU', hn'⟩ := GlobalTheory.T.exists_phiContraction_disc_step l K bk A s ι tb φ hφ Φ hΦ κ c hc h V hs (r n) (r (n + 1))
        (rle n) (rlt n) (rs n) (R n) (R (n + 1)) (hR n) (hR (n + 1)) U _ (by positivity) hU hRU hn
      refine ⟨U', hU', hRU', fun j => ?_⟩
      have hp : (0 : ℝ) < r (n + 1) := rpos _
      have hle : (r n : ℝ) ≤ r (n + 1) * r (n + 1) := by
        have : r n ≤ r (n + 1) ^ 2 := by
          rw [← rs n]; exact pow_le_pow_of_le_one zero_le (rlt _).le hl2
        rw [← sq]; exact_mod_cast this
      refine le_of_mul_le_mul_left ((hn' j).trans ?_) (pow_pos hp m)
      rw [mul_left_comm, ← mul_pow, ← mul_div_assoc]
      gcongr
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C * (1 / (bk.ρ₀ : ℝ)) ^ m)
    (show (1 : ℝ) < l by exact_mod_cast hl.out.one_lt)
  have hlk : (0 : ℝ) < (l : ℝ) ^ k := pow_pos (Nat.cast_pos.2 hl.out.pos) k
  have hv : ∀ j, ∃ a, toDisc l (s X) bk.ρ₀ a = (l : Disc l (s X) bk.ρ₀) ^ k * V j := fun j =>
    GlobalTheory.T.exists_base_eq_of_closedDisc_extends_norm_le_one l K bk A s ι tb bk.ρ₀ h0 h1 _ fun ρ₁ hρ₁ => by
      obtain ⟨n, hn⟩ := rlim ρ₁ hρ₁
      obtain ⟨U, -, hRU, hU⟩ := key n
      refine ⟨r n, R n, (l : Disc l (s X) (r n)) ^ k * U j, hn, rle n, rlt n, hR n, ?_, ?_⟩
      · rw [map_mul, map_pow, map_natCast, hRU]
      · rw [norm_l_pow_mul_disc, div_le_one hlk]
        refine (hU j).trans (le_trans ?_ hk.le)
        have : (r n : ℝ) ≤ 1 := (rlt n).le
        gcongr
  choose v hv using hv
  refine ⟨k, v, hv, fun n => ?_⟩
  obtain ⟨ε, hε, hJ⟩ := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk A s ι tb bk.ρ₀ h0 h1).2.1 n
  have ht : Filter.Tendsto (fun j => (l : Disc l (s X) bk.ρ₀) ^ k * V j) Filter.cofinite (nhds 0) := by
    simpa using hV.const_mul ((l : Disc l (s X) bk.ρ₀) ^ k)
  have he := Filter.eventually_cofinite.1 (ht.eventually (Metric.closedBall_mem_nhds 0 hε))
  refine he.subset fun j hj hj' => hj (hJ _ ?_)
  rw [hv]
  simpa using hj'

end GlobalTheory.BSP
