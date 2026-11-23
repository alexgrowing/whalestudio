import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatIffMemAdelicMatrixSchwartzSpaceStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SchwartzMaj

variable {D : D7}

theorem finPart_section (D : D7) : Continuous (finPart D) ∧
    ∃ s : (Af D.host.F ⊗[D.host.F] D.host.E) → AE D, Continuous s ∧ ∀ z, finPart D (s z) = z := by
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, hes⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨?_, fun z => e.symm (0, z), hes.comp (continuous_const.prodMk continuous_id), fun z => ?_⟩
  · have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
    rw [this]
    exact continuous_snd.comp hec
  · rw [← (he _).2, RingEquiv.apply_symm_apply]

theorem maj_mono (θ : InfFam D) {m n : ℕ} {K K' : Set (Mx D m n)} (h : K ⊆ K') (N : ℕ) (x : Mx D m n) :
    GlobalTheory.Unf.maj θ K N x ≤ GlobalTheory.Unf.maj θ K' N x := by
  by_cases hx : GlobalTheory.Unf.InBox K x
  · have hx' : GlobalTheory.Unf.InBox K' x := let ⟨k, hk, h0⟩ := hx; ⟨k, h hk, h0⟩
    unfold GlobalTheory.Unf.maj
    rw [if_pos hx, if_pos hx']
  · have h0 : GlobalTheory.Unf.maj θ K N x = 0 := by unfold GlobalTheory.Unf.maj; rw [if_neg hx]
    rw [h0]
    exact GlobalTheory.Unf.maj_nonneg θ K' N x

theorem realSize_le (θ : InfFam D) (m n : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Mx D m n,
    1 + GlobalTheory.Unf.realSize θ x ≤
      c * (1 + ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖) := by
  set a : ℝ := ∑ _τ : D.what₂.Tau, ∑ _i : Fin m, ∑ _j : Fin n, (1 : ℝ) with ha
  have ha0 : 0 ≤ a :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => zero_le_one
  refine ⟨1 + a, by linarith, fun x => ?_⟩
  set y : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ x i j with hy
  have h1 : GlobalTheory.Unf.realSize θ x ≤ a * ‖y‖ := by
    rw [ha]
    simp only [Finset.sum_mul, one_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    exact (norm_le_pi_norm (y τ i) j).trans ((norm_le_pi_norm (y τ) i).trans (norm_le_pi_norm y τ))
  have h2 := norm_nonneg y
  nlinarith

def HasMaj (θ : InfFam D) {m n : ℕ} (φ : Mx D m n → ℂ) : Prop :=
  Continuous φ ∧ ∃ K : Set (Mx D m n), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C * GlobalTheory.Unf.maj θ K N x

theorem HasMaj.zero (θ : InfFam D) (m n : ℕ) : HasMaj θ (0 : Mx D m n → ℂ) :=
  ⟨continuous_const, ∅, isCompact_empty, fun _ => ⟨0, fun _ => by simp⟩⟩

theorem HasMaj.add {θ : InfFam D} {m n : ℕ} {φ φ' : Mx D m n → ℂ} (h : HasMaj θ φ) (h' : HasMaj θ φ') :
    HasMaj θ (φ + φ') := by
  obtain ⟨hc, K, hK, hb⟩ := h
  obtain ⟨hc', K', hK', hb'⟩ := h'
  refine ⟨hc.add hc', K ∪ K', hK.union hK', fun N => ?_⟩
  obtain ⟨C, hC⟩ := hb N
  obtain ⟨C', hC'⟩ := hb' N
  refine ⟨|C| + |C'|, fun x => ?_⟩
  have h1 : ‖φ x‖ ≤ |C| * GlobalTheory.Unf.maj θ (K ∪ K') N x :=
    (hC x).trans (mul_le_mul (le_abs_self C) (maj_mono θ Set.subset_union_left N x) (GlobalTheory.Unf.maj_nonneg θ K N x)
      (abs_nonneg C))
  have h2 : ‖φ' x‖ ≤ |C'| * GlobalTheory.Unf.maj θ (K ∪ K') N x :=
    (hC' x).trans (mul_le_mul (le_abs_self C') (maj_mono θ Set.subset_union_right N x) (GlobalTheory.Unf.maj_nonneg θ K' N x)
      (abs_nonneg C'))
  rw [add_mul]
  exact (norm_add_le (φ x) (φ' x)).trans (add_le_add h1 h2)

theorem HasMaj.smul {θ : InfFam D} {m n : ℕ} {φ : Mx D m n → ℂ} (a : ℂ) (h : HasMaj θ φ) : HasMaj θ (a • φ) := by
  obtain ⟨hc, K, hK, hb⟩ := h
  refine ⟨hc.const_smul a, K, hK, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hb N
  refine ⟨‖a‖ * C, fun x => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg a)

theorem hasMaj_pure {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    HasMaj θ fun x : Mx D m n => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j)) := by
  obtain ⟨hfc, s, hs, hsec⟩ := finPart_section D
  have hgc : Continuous g := hg.1.continuous
  have hgs : HasCompactSupport g := hg.2
  have hy : Continuous fun x : Mx D m n => (fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ) :=
    continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.RealWeil.continuous_compAt hθ τ m n).matrix_elem i j
  have hz : Continuous fun x : Mx D m n =>
      (fun i j => finPart D (x i j) : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    continuous_pi fun i => continuous_pi fun j => hfc.comp (continuous_id.matrix_elem i j)
  let t : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → Mx D m n := fun z => Matrix.of fun i j => s (z i j)
  have ht : Continuous t :=
    continuous_matrix fun i j => hs.comp ((continuous_apply j).comp (continuous_apply i))
  refine ⟨(f.continuous.comp hy).mul (hgc.comp hz), t '' tsupport g, hgs.isCompact.image ht, fun N => ?_⟩
  obtain ⟨G, hG⟩ := hgs.exists_bound_of_continuous hgc
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  obtain ⟨c, hc0, hc⟩ := realSize_le θ m n
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ y, (1 + ‖y‖) ^ N * ‖f y‖ ≤ S := by
    have h := fun y =>
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl f y
    simp only [norm_iteratedFDeriv_zero] at h
    exact ⟨_, h⟩
  have hS0 : 0 ≤ S := le_trans (by positivity) (hS 0)
  refine ⟨c ^ N * S * G, fun x => ?_⟩
  by_cases h0 : g (fun i j => finPart D (x i j)) = 0
  · simp only [h0, mul_zero, norm_zero]
    exact mul_nonneg (by positivity) (GlobalTheory.Unf.maj_nonneg θ _ N x)
  · have hin : GlobalTheory.Unf.InBox (t '' tsupport g) x := by
      refine ⟨t fun i j => finPart D (x i j), ⟨_, subset_tsupport g h0, rfl⟩, ?_⟩
      refine Matrix.ext fun i j => ?_
      change finPart D (x i j - s (finPart D (x i j))) = 0
      rw [(finPart D).map_sub, hsec, sub_self]
    have hr := GlobalTheory.Unf.realSize_nonneg θ x
    unfold GlobalTheory.Unf.maj
    rw [if_pos hin, le_mul_inv_iff₀ (by positivity), norm_mul]
    have h1 := hc x
    have h2 := hS (fun τ i j => compAt θ τ x i j)
    have h3 := hG (fun i j => finPart D (x i j))
    generalize (fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ) = y at h1 h2 ⊢
    generalize g (fun i j => finPart D (x i j)) = b at h3 ⊢
    have h4 : (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ c ^ N * (1 + ‖y‖) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) h1 N
    calc ‖f y‖ * ‖b‖ * (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ ‖f y‖ * G * (c ^ N * (1 + ‖y‖) ^ N) := by gcongr
      _ = c ^ N * ((1 + ‖y‖) ^ N * ‖f y‖) * G := by ring
      _ ≤ c ^ N * S * G := by gcongr

theorem hasMaj_of_mem {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} {φ : Mx D m n → ℂ}
    (hφ : φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n) : HasMaj θ φ := by
  refine Submodule.span_induction (p := fun φ _ => HasMaj θ φ) ?_ (HasMaj.zero θ m n)
    (fun _ _ _ _ h h' => h.add h') (fun a _ _ h => h.smul a) hφ
  rintro _ ⟨f, g, hg, rfl⟩
  exact hasMaj_pure hθ f g hg

theorem continuous_and_le_maj : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → Continuous φ ∧ ∃ K : Set (Mx D m n), IsCompact K ∧
      ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C * GlobalTheory.Unf.maj θ K N x :=
  fun D θ hθ m n φ hφ => hasMaj_of_mem hθ ((GlobalTheory.T.isSchwartzBruhat_iff_mem_adelicMatrixSchwartzSpace D θ hθ m n φ).1 hφ)

end GlobalTheory.SchwartzMaj

end
