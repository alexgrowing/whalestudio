import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBaseRingToClosedDiscJPowSmallStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDivClosedDiscOfTopBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem norm_pow_mul_eq_of_norm_mul_eq {R : Type*} [NormedRing R] (E : R) (q : ℝ)
    (hE : ∀ y, ‖E * y‖ = q * ‖y‖) (h : ℕ) (y : R) : ‖E ^ h * y‖ = q ^ h * ‖y‖ := by
  induction h generalizing y with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_assoc, ih, hE, pow_succ]; ring

theorem exists_discStep : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∀ (ρ ρ' : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ρ' ^ l = ρ → ∀ (R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀) (R' : Disc l (s X) ρ' →+* Disc l (s X) bk.ρ₀), IsDiscMap (RingHom.id A) R → IsDiscMap (RingHom.id A) R' → ∀ (U : κ → Disc l (s X) ρ) (C : ℝ), 0 ≤ C → Filter.Tendsto U Filter.cofinite (nhds 0) → (∀ j, R (U j) = V j) → (∀ j, ‖U j‖ ≤ C) → ∃ U' : κ → Disc l (s X) ρ', Filter.Tendsto U' Filter.cofinite (nhds 0) ∧ (∀ j, R' (U' j) = V j) ∧ ∀ j, (ρ' : ℝ) ^ (bk.Ep.natDegree * h) * ‖U' j‖ ≤ C := by
  intro l _ K bk A _ s ι tb φ hφ Φ hΦ κ c hc h V hV ρ ρ' hρ₀ hρ1 hρ' R R' hR hR' U C hC hU hRU hUC
  obtain ⟨-, -, ⟨hρ₀pos, hρ₀1, -⟩, -⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have hρpos : 0 < ρ := hρ₀pos.trans_le hρ₀
  have hρ'pos : 0 < ρ' := by
    rcases (show (0 : ℝ≥0) ≤ ρ' from zero_le).eq_or_lt with h0 | h0
    · rw [← h0, zero_pow (by omega)] at hρ'
      exact absurd hρ' hρpos.ne
    · exact h0
  have hρ'1 : ρ' < 1 := by
    by_contra hh
    push_neg at hh
    have h2 := one_le_pow₀ hh (n := l)
    rw [hρ'] at h2
    exact absurd hρ1 (not_lt.2 h2)
  have hρρ' : ρ ≤ ρ' := by rw [← hρ']; exact pow_le_of_le_one zero_le hρ'1.le (by omega)

  obtain ⟨Φ', hΦ'⟩ := GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l A A φ (s X) (s X) ρ ρ' l hρ'pos (by rw [hφ]) hρ'.le
  have hc1 := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).2.2.2 A A (s X) (s X) ρ' bk.ρ₀ φ (RingHom.id A) Φ' R' hΦ' hR'
  have hc2 := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).2.2.2 A A (s X) (s X) bk.ρ₀ bk.ρ₀ (RingHom.id A) φ R Φ hR hΦ
  rw [RingHom.id_comp] at hc1
  rw [RingHom.comp_id] at hc2
  have hcomm : ∀ x, R' (Φ' x) = Φ (R x) := fun x => RingHom.congr_fun (hc1.unique hc2) x
  haveI : IsUltrametricDist (Disc l (s X) ρ') := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ').1
  haveI : NonarchimedeanAddGroup (Disc l (s X) ρ') := IsUltrametricDist.nonarchimedeanAddGroup

  have hUn : Filter.Tendsto (fun i => ‖U i‖) Filter.cofinite (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.1 hU
  have hTle : ∀ i j, ‖Φ' (U i) * toDisc l (s X) ρ' (c i j)‖ ≤ ‖U i‖ * ‖toDisc l (s X) ρ' (c i j)‖ := fun i j =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hΦ'.norm_le _) (norm_nonneg _))
  have hTle' : ∀ i j, ‖Φ' (U i) * toDisc l (s X) ρ' (c i j)‖ ≤ ‖U i‖ := fun i j =>
    (hTle i j).trans (mul_le_of_le_one_right (norm_nonneg _) (norm_toDisc_le _))
  have hsum : ∀ j, Summable fun i => Φ' (U i) * toDisc l (s X) ρ' (c i j) := fun j =>
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (squeeze_zero_norm (fun i => hTle' i j) hUn)
  set Z : κ → Disc l (s X) ρ' := fun j => ∑' i, Φ' (U i) * toDisc l (s X) ρ' (c i j) with hZdef
  have hZC : ∀ j, ‖Z j‖ ≤ C := fun j =>
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun i => (hTle' i j).trans (hUC i)
  have hR'c : Continuous R' :=
    AddMonoidHomClass.continuous_of_bound R' 1 fun y => (hR'.norm_le y).trans (one_mul _).ge
  have hRZ : ∀ j, R' (Z j) = toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j := fun j => by
    have h1 := (hsum j).hasSum.map R' hR'c
    have h2 : (R' ∘ fun i => Φ' (U i) * toDisc l (s X) ρ' (c i j)) =
        fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j) := by
      funext i
      simp only [Function.comp_apply, map_mul, hcomm, hRU, hR'.ext, RingHom.id_apply]
    rw [h2] at h1
    exact h1.unique (hV j)

  have hsmall : ∀ r : ℝ, 0 < r → {j | r < ‖Z j‖}.Finite := by
    intro r hr
    have hF : {i | r < ‖U i‖}.Finite := by
      have := Filter.eventually_cofinite.1 (hUn.eventually (ge_mem_nhds hr))
      simpa only [not_le] using this
    obtain ⟨n, hn⟩ := GlobalTheory.T.norm_baseRingToClosedDisc_J_pow_small l K bk A s ρ' hρ'pos hρ'1 (r / (C + 1)) (by positivity)
    refine (hF.biUnion fun i _ => hc i n).subset ?_
    intro j hj
    by_contra hj'
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hj'
    refine (not_le.2 (show r < ‖Z j‖ from hj)) ?_
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr.le fun i => ?_
    by_cases hi : r < ‖U i‖
    · refine (hTle i j).trans ((mul_le_mul (hUC i) (hn _ (hj' i hi)) (norm_nonneg _) hC).trans ?_)
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    · exact (hTle' i j).trans (not_lt.1 hi)
  have hZ : Filter.Tendsto Z Filter.cofinite (nhds 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => Filter.eventually_cofinite.2 ((hsmall (ε / 2) (by linarith)).subset ?_)
    intro j hj
    simp only [Set.mem_setOf_eq, dist_zero_right, not_lt] at hj ⊢
    linarith

  obtain ⟨hnorm', hdiv'⟩ := GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι tb ρ' (hρ₀.trans hρρ') hρ'1
  obtain ⟨hnorm₀, -⟩ := GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι tb bk.ρ₀ le_rfl hρ₀1
  choose U' hU' using fun j => hdiv' R' hR' h (Z j) ⟨V j, hRZ j⟩
  have hq : (0 : ℝ) < (ρ' : ℝ) ^ (bk.Ep.natDegree * h) := by positivity
  have hnZ : ∀ j, ‖Z j‖ = (ρ' : ℝ) ^ (bk.Ep.natDegree * h) * ‖U' j‖ := fun j => by
    rw [hU' j, norm_pow_mul_eq_of_norm_mul_eq _ _ hnorm' h, pow_mul]
  refine ⟨U', ?_, ?_, fun j => (hnZ j).symm.trans_le (hZC j)⟩
  · have he : ∀ j, ‖U' j‖ = ((ρ' : ℝ) ^ (bk.Ep.natDegree * h))⁻¹ * ‖Z j‖ := fun j => by
      rw [hnZ j, inv_mul_cancel_left₀ hq.ne']
    refine squeeze_zero_norm (fun j => (he j).le) ?_
    simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hZ).const_mul ((ρ' : ℝ) ^ (bk.Ep.natDegree * h))⁻¹
  · intro j
    have h1 : toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * (R' (U' j) - V j) = 0 := by
      have h2 := hRZ j
      rw [hU' j, map_mul, map_pow, hR'.ext, RingHom.id_apply] at h2
      rw [mul_sub, h2, sub_self]
    have h3 := congrArg norm h1
    rw [norm_pow_mul_eq_of_norm_mul_eq _ _ hnorm₀ h, norm_zero] at h3
    have h4 : (0 : ℝ) < ((bk.ρ₀ : ℝ) ^ bk.Ep.natDegree) ^ h := by positivity
    exact sub_eq_zero.1 (norm_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left h4.ne'))

end GlobalTheory.BSP
