import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAndEventuallySubMemLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDeRhamFiltrationOfForallAinfLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage Filter Topology

namespace GlobalTheory.FundCont

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem l_ne : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero

theorem small_mul_mem (T : LocTied l P AI) {M n k : ℕ} {c : ℚ_[l]} {b : P.R.BdR}
    (hc : ‖c‖ ≤ (l : ℝ) ^ (-(k : ℤ))) (hb : (l : P.R.BdR) ^ k * b ∈ Lat AI M n) :
    qB P c * b ∈ Lat AI M n := by
  have h0 : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) := by
    have := (Fact.out : l.Prime).pos
    positivity
  have hz : ‖c / (l : ℚ_[l]) ^ k‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p_pow, div_le_one h0]
    exact hc
  have := qB_mul_mem_Lat AI T ⟨_, hz⟩ hb
  convert this using 1
  rw [← mul_assoc, ← map_natCast (qB P), ← map_pow, ← map_mul]
  congr 2
  exact (div_mul_cancel₀ _ (pow_ne_zero _ l_ne)).symm

theorem large_mul_mem (T : LocTied l P AI) {M n k : ℕ} {c : ℚ_[l]} {b : P.R.BdR}
    (hc : ‖(l : ℚ_[l]) ^ k * c‖ ≤ 1) (hb : b ∈ Lat AI M (k + n)) :
    qB P c * b ∈ Lat AI M n := by
  rw [← pow_mul_mem_Lat_iff AI (k := k)]
  have := qB_mul_mem_Lat AI T ⟨_, hc⟩ hb
  convert this using 1
  simp only [map_mul, map_pow, map_natCast, mul_assoc]

theorem exists_pow_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, (l : ℝ) ^ (-(k : ℤ)) < ε :=
  PadicInt.exists_pow_neg_lt l hε

theorem exists_mul_le_one (c : ℚ_[l]) : ∃ k : ℕ, ‖(l : ℚ_[l]) ^ k * c‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_pow_lt (l := l) (ε := (‖c‖ + 1)⁻¹) (by positivity)
  refine ⟨k, ?_⟩
  rw [norm_mul, Padic.norm_p_pow]
  calc _ ≤ (‖c‖ + 1)⁻¹ * (‖c‖ + 1) := by gcongr; linarith
    _ = 1 := inv_mul_cancel₀ (by positivity)

variable {X : Type} [TopologicalSpace X]

theorem eventually_orbit (T : LocTied l P AI) {b : P.R.BdR} (hb : b ∈ FilB P 0) (M n : ℕ)
    {c : X → ℚ_[l]} (hc : Continuous c) {γ : X → GQ l} (hγ : Continuous γ) (x₀ : X) :
    ∀ᶠ x in 𝓝 x₀, qB P (c x) * P.actQdR (γ x) b - qB P (c x₀) * P.actQdR (γ x₀) b ∈ Lat AI M n := by
  obtain ⟨⟨k, hk⟩, -⟩ := bounded_and_eventually_sub_mem_Lat l P AI T b hb M n
  obtain ⟨j, hj⟩ := exists_mul_le_one (c x₀)
  obtain ⟨-, he⟩ := bounded_and_eventually_sub_mem_Lat l P AI T b hb M (j + n)
  have h0 : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) := by
    have := (Fact.out : l.Prime).pos
    positivity
  have t1 : Tendsto (fun x => (γ x₀)⁻¹ * γ x) (𝓝 x₀) (𝓝 1) := by
    have : Continuous fun x => (γ x₀)⁻¹ * γ x := continuous_const.mul hγ
    simpa using this.tendsto x₀
  filter_upwards [t1.eventually he, Metric.tendsto_nhds.1 (hc.tendsto x₀) _ h0] with x h1 h2
  rw [dist_eq_norm] at h2
  have h3 := act_mem_Lat AI (γ x) hk
  rw [map_mul, map_pow, map_natCast] at h3
  have h4 := small_mul_mem AI T h2.le h3
  have h5 := act_mem_Lat AI (γ x₀) h1
  rw [map_sub, ← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel_left] at h5
  have h6 := large_mul_mem AI T hj h5
  convert add_mem h4 h6 using 1
  rw [map_sub]
  ring

def LatCont (h : X → P.R.BdR) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (n : ℕ) (x₀ : X), ∀ᶠ x in 𝓝 x₀, tD P ^ N * (h x - h x₀) ∈ Lat AI (N + 1) n

theorem latCont_const (b : P.R.BdR) : LatCont AI (fun _ : X => b) :=
  ⟨0, fun N _ n x₀ => Eventually.of_forall fun x => by simp⟩

theorem LatCont.add {h h' : X → P.R.BdR} (H : LatCont AI h) (H' : LatCont AI h') :
    LatCont AI (fun x => h x + h' x) := by
  obtain ⟨N₀, H⟩ := H
  obtain ⟨N₁, H'⟩ := H'
  refine ⟨max N₀ N₁, fun N hN n x₀ => ?_⟩
  filter_upwards [H N (le_of_max_le_left hN) n x₀, H' N (le_of_max_le_right hN) n x₀] with x a b
  convert add_mem a b using 1
  ring

theorem LatCont.sum {ι : Type} (s : Finset ι) (h : ι → X → P.R.BdR) (H : ∀ i, LatCont AI (h i)) :
    LatCont AI (fun x => ∑ i ∈ s, h i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using latCont_const AI 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (H i).add AI ih

theorem continuous_chi : Continuous fun g : GQ l => (P.χQ g : ℚ_[l]) := by
  obtain ⟨χ, h1, h2, -⟩ := exists_integral_cyclotomicChar l P
  simp only [← h1]
  have h3 : Continuous fun g => (χ g : ℤ_[l]) := Units.continuous_val.comp h2
  exact continuous_subtype_val.comp h3

theorem latCont_orbit (T : LocTied l P AI) (b : P.R.BdR)
    {c : X → ℚ_[l]} (hc : Continuous c) {γ : X → GQ l} (hγ : Continuous γ) :
    LatCont AI (fun x => qB P (c x) * P.actQdR (γ x) b) := by
  obtain ⟨a, ha⟩ := (P.PD (botExt l)).Fil_exh b
  refine ⟨(-a).toNat, fun N hN n x₀ => ?_⟩
  have hb : tD P ^ N * b ∈ FilB P 0 :=
    FilB_anti (by omega) (FilB_mul (FilB_pow tD_mem N) ha)
  have hc' : Continuous fun x => c x * ((P.χQ (γ x) : ℚ_[l]) ^ N)⁻¹ :=
    hc.mul (((continuous_chi.comp hγ).pow N).inv₀ fun x => pow_ne_zero _ (Units.ne_zero _))
  have e : ∀ x, qB P (c x * ((P.χQ (γ x) : ℚ_[l]) ^ N)⁻¹) * P.actQdR (γ x) (tD P ^ N * b) =
      tD P ^ N * (qB P (c x) * P.actQdR (γ x) b) := by
    intro x
    have h1 : qB P ((P.χQ (γ x) : ℚ_[l]) ^ N)⁻¹ * qB P (P.χQ (γ x) : ℚ_[l]) ^ N = 1 := by
      rw [← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), map_one]
    rw [map_mul, map_mul, map_pow, act_tD, mul_pow]
    linear_combination (tD P ^ N * (qB P (c x) * P.actQdR (γ x) b)) * h1
  filter_upwards [eventually_orbit AI T hb (N + 1) n hc' hγ x₀] with x hx
  rwa [e, e, ← mul_sub] at hx

theorem tD_pow_not_mem (T : LocTied l P AI) (N : ℕ) : tD P ^ N ∉ FilB P ((N : ℤ) + 1) := by
  have hu : IsUnit (tD P) := by
    have := (P.PD (botExt l)).t_unit
    rw [P.period_datum_t_eq] at this
    exact this.map P.ιB
  induction N with
  | zero =>
    intro h
    apply (P.PD (botExt l)).not_mem_filtration_two
    rw [P.PD_ι, P.period_datum_t_eq]
    simpa using FilB_mul (tD_mem (P := P)) h
  | succ N ih =>
    intro h
    obtain ⟨y, hy, e⟩ := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 (botExt l) _ _).1 h
    rw [pow_succ'] at e
    apply ih
    rw [hu.mul_left_cancel e]
    exact_mod_cast hy

theorem continuous_of_latCont (T : LocTied l P AI) {c : X → ℚ_[l]}
    (H : LatCont AI (fun x => qB P (c x))) : Continuous c := by
  obtain ⟨N, H⟩ := H
  obtain ⟨n, hn⟩ : ∃ n, tD P ^ N ∉ Lat AI (N + 1) n := by
    by_contra h
    push Not at h
    exact tD_pow_not_mem AI T N (by exact_mod_cast mem_FilB_of_forall_Lat l P AI T (N + 1) _ h)
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt (l := l) hε
  filter_upwards [H N le_rfl (k + n) x₀] with x hx
  rw [dist_eq_norm]
  by_contra hlt
  push Not at hlt
  have h0 : 0 < ‖c x - c x₀‖ := hε.trans_le hlt
  apply hn
  have := large_mul_mem AI T (c := (c x - c x₀)⁻¹) (by
    rw [norm_mul, Padic.norm_p_pow, norm_inv, ← div_eq_mul_inv, div_le_one h0]
    exact hk.le.trans hlt) hx
  rwa [← map_sub, mul_left_comm, ← map_mul, inv_mul_cancel₀ (norm_pos_iff.1 h0), map_one,
    mul_one] at this

theorem contCore_of_tied (T : LocTied l P AI) (K : FinExt l) : contCore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A k x β hβ x' f hf
  obtain ⟨-, hfd, hmt, htr, -⟩ := hO
  have hLL : ∀ (φ : A.V →ₗ[ℚ_[l]] ℚ_[l]) (v : A.V), Continuous fun c : LL => φ (c • v) := fun φ v =>
    IsModuleTopology.continuous_of_linearMap
      (φ ∘ₗ (LinearMap.toSpanSingleton LL A.V v).restrictScalars ℚ_[l])
  have hV : ∀ φ : A.V →ₗ[ℚ_[l]] ℚ_[l], Continuous φ := by
    intro φ
    let b := Module.finBasis LL A.V
    have : (φ : A.V → ℚ_[l]) = fun v => ∑ j, φ (b.coord j v • b j) := by
      funext v
      rw [← map_sum]
      simp [b.sum_repr]
    rw [this]
    exact continuous_finset_sum _ fun j _ =>
      (hLL φ (b j)).comp (IsModuleTopology.continuous_of_linearMap (b.coord j))
  have key : ∀ φ : A.V →ₗ[ℚ_[l]] ℚ_[l], Continuous fun g => φ (f g) := by
    intro φ
    let Φ : A.V ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] P.R.BdR :=
      (TensorProduct.lid ℚ_[l] P.R.BdR).toLinearMap ∘ₗ TensorProduct.map φ P.ιB.toLinearMap
    have hΦ : ∀ v b, Φ (v ⊗ₜ b) = qB P (φ v) * P.ιB b := by
      intro v b
      simp [Φ, Algebra.smul_def]
    have h1 : ∀ (y : A.V ⊗[ℚ_[l]] P.R.B) (i : Fin k), LatCont AI fun g => Φ (β i g • y) := by
      intro y i
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        simp only [TensorProduct.smul_tmul', hΦ]
        simpa using latCont_orbit AI T (P.ιB b) ((hLL φ v).comp (hβ i))
          (γ := fun _ => 1) continuous_const
      | add y y' ih ih' =>
        simp only [smul_add, map_add]
        exact ih.add AI ih'
    have h2 : ∀ y : A.V ⊗[ℚ_[l]] P.R.B, LatCont AI fun g => Φ (actVB (P.PD K) A.ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        have e : ∀ g : ↥(GK K), Φ (actVB (P.PD K) A.ρ g (v ⊗ₜ b)) =
            qB P (φ (A.ρ g v)) * P.actQdR (g : GQ l) (P.ιB b) := by
          intro g
          rw [← ιB_act, ← hΦ, ← P.PD_actB]
          rfl
        simp only [e]
        exact latCont_orbit AI T (P.ιB b) ((hV φ).comp (A.cont v)) continuous_subtype_val
      | add y y' ih ih' =>
        simp only [map_add]
        exact ih.add AI ih'
    apply continuous_of_latCont AI T
    have e : ∀ g, qB P (φ (f g)) =
        ∑ i, Φ (β i g • x i) + (Φ (actVB (P.PD K) A.ρ g x') + -Φ x') := by
      intro g
      have := congrArg Φ (hf g)
      rwa [hΦ, map_one, mul_one, map_add, map_sum, map_sub, sub_eq_add_neg] at this
    simp only [e]
    exact (LatCont.sum AI _ _ fun i => h1 (x i) i).add AI ((h2 x').add AI (latCont_const AI _))
  haveI : Module.Finite ℚ_[l] A.V := Module.Finite.trans LL A.V
  let b := Module.finBasis ℚ_[l] A.V
  have : f = fun g => ∑ j, algebraMap ℚ_[l] LL (b.coord j (f g)) • b j := by
    funext g
    simp [b.sum_repr]
  rw [this]
  haveI : ContinuousSMul LL A.V := IsModuleTopology.toContinuousSMul LL A.V
  haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  exact continuous_finset_sum _ fun j _ =>
    ((continuous_algebraMap ℚ_[l] LL).comp (key (b.coord j))).smul continuous_const

theorem fundamentalExactSequence_continuity_all_theories : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm6 D := fun D l _ K =>
  contCore_of_tied (D.locA l) (D.locT l) K

end GlobalTheory.FundCont
