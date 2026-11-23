import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

private theorem integral_indicator_mul_char_of_trivial {K : Type} [CommRing K] [MeasurableSpace K]
    (μ : Measure K) (p : K → ℂ) (S : AddSubgroup K) (hSm : MeasurableSet (S : Set K)) (y : K)
    (h : ∀ s ∈ S, p (s * y) = 1) :
    ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ = ((μ (S : Set K)).toReal : ℂ) := by
  have hfun : (fun x => (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y)) =
      (S : Set K).indicator (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ (S : Set K)
    · rw [Set.indicator_of_mem hx, one_mul, h x hx]
    · rw [Set.indicator_of_notMem hx, zero_mul]
  rw [hfun, integral_indicator_const _ hSm, measureReal_def, Complex.real_smul, mul_one]

private theorem integral_indicator_mul_char_eq_zero {K : Type} [CommRing K] [MeasurableSpace K] [MeasurableAdd K]
    (μ : Measure K) [μ.IsAddLeftInvariant] (p : K → ℂ) (hadd : ∀ x y, p (x + y) = p x * p y)
    (S : AddSubgroup K) (y : K) (h : ∃ s ∈ S, p (s * y) ≠ 1) :
    ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ = 0 := by
  obtain ⟨s, hs, hps⟩ := h
  have hI : ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ =
      p (s * y) * ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ := by
    rw [← integral_const_mul, ← integral_add_left_eq_self
      (fun x => (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y)) s]
    congr 1
    funext x
    beta_reduce
    by_cases hx : x ∈ (S : Set K)
    · have hsx : s + x ∈ (S : Set K) := (S.add_mem_cancel_left hs).mpr hx
      rw [Set.indicator_of_mem hsx, Set.indicator_of_mem hx, add_mul, hadd]
      ring
    · have hsx : s + x ∉ (S : Set K) := fun h' => hx ((S.add_mem_cancel_left hs).mp h')
      rw [Set.indicator_of_notMem hsx, Set.indicator_of_notMem hx]
      ring
  have h1 : (1 - p (s * y)) * ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ = 0 := by
    rw [sub_mul, one_mul, ← hI, sub_self]
  rcases mul_eq_zero.mp h1 with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hps
  · exact h0

theorem ann_core {K : Type} [CommRing K] [TopologicalSpace K] [T2Space K] [MeasurableSpace K] [MeasurableAdd K]
    (μ : Measure K) (p : K → ℂ) (hadd : ∀ x y, p (x + y) = p x * p y)
    (hSD : SelfDual μ (fun s t => p (s * t)))
    (U A B : AddSubgroup K) (hUc : IsCompact (U : Set K)) (hUo : IsOpen (U : Set K))
    (hUm : MeasurableSet (U : Set K)) (hAm : MeasurableSet (A : Set K)) (hAf : μ (A : Set K) ≠ ⊤)
    (hA : ∀ y, y ∈ A ↔ ∀ s ∈ U, p (s * y) = 1)
    (hB : ∀ z, z ∈ B ↔ ∀ s ∈ A, p (s * z) = 1) :
    B = U ∧ (μ (U : Set K)).toReal * (μ (A : Set K)).toReal = 1 := by
  obtain ⟨hHaar, hinv⟩ := hSD
  have hp0 : p 0 = 1 := by simpa using (hA 0).mp A.zero_mem 0 U.zero_mem
  have hΦc : Continuous ((U : Set K).indicator (fun _ => (1 : ℂ))) :=
    IsClopen.continuous_indicator ⟨hUc.isClosed, hUo⟩ continuous_const
  have hΦs : HasCompactSupport ((U : Set K).indicator (fun _ => (1 : ℂ))) :=
    HasCompactSupport.intro hUc (fun x hx => Set.indicator_of_notMem hx _)
  have hFT : ∀ y, ∫ x, (U : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ =
      (A : Set K).indicator (fun _ => ((μ (U : Set K)).toReal : ℂ)) y := by
    intro y
    by_cases h : ∀ s ∈ U, p (s * y) = 1
    · rw [integral_indicator_mul_char_of_trivial μ p U hUm y h,
        Set.indicator_of_mem (show y ∈ (A : Set K) from (hA y).mpr h)]
    · push_neg at h
      rw [integral_indicator_mul_char_eq_zero μ p hadd U y h,
        Set.indicator_of_notMem (show y ∉ (A : Set K) from fun h' => by
          obtain ⟨s, hs, hps⟩ := h
          exact hps ((hA y).mp h' s hs))]
  have hint : Integrable (fun y => ∫ x, (U : Set K).indicator (fun _ => (1 : ℂ)) x *
      (fun s t => p (s * t)) x y ∂μ) μ := by
    simp only [hFT]
    exact (integrable_indicator_iff hAm).mpr (integrableOn_const hAf)
  have key : ∀ z, ((μ (U : Set K)).toReal : ℂ) *
      ∫ y, (A : Set K).indicator (fun _ => (1 : ℂ)) y * p (y * z) ∂μ =
      (U : Set K).indicator (fun _ => (1 : ℂ)) (-z) := by
    intro z
    rw [← integral_const_mul, ← hinv _ hΦc hΦs hint z]
    congr 1
    funext y
    beta_reduce
    rw [hFT y]
    by_cases hy : y ∈ (A : Set K)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      ring
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      ring
  have h0 := key 0
  have hc0 : ∀ s ∈ A, p (s * 0) = 1 := fun s _ => by rw [mul_zero, hp0]
  rw [integral_indicator_mul_char_of_trivial μ p A hAm 0 hc0, neg_zero,
    Set.indicator_of_mem (show (0 : K) ∈ (U : Set K) from U.zero_mem)] at h0
  have hprod : (μ (U : Set K)).toReal * (μ (A : Set K)).toReal = 1 := by exact_mod_cast h0
  refine ⟨?_, hprod⟩
  ext z
  rw [hB z]
  have hz := key z
  constructor
  · intro h
    rw [integral_indicator_mul_char_of_trivial μ p A hAm z h, h0] at hz
    by_contra hzU
    rw [Set.indicator_of_notMem (show -z ∉ (U : Set K) from fun h' => hzU (by simpa using U.neg_mem h'))] at hz
    exact one_ne_zero hz
  · intro hzU
    by_contra h
    push_neg at h
    rw [integral_indicator_mul_char_eq_zero μ p hadd A z h, mul_zero,
      Set.indicator_of_mem (show -z ∈ (U : Set K) from U.neg_mem hzU)] at hz
    exact zero_ne_one hz

theorem localDual : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (c : ℝ≥0), GlobalTheory.CompanionTheory.SW.IsStdV v lam → SelfDual (c • lam) (fun s t => psiV F ψ v (s * t)) → ∀ U : AddSubgroup (Fv F v), IsCompact (U : Set (Fv F v)) → IsOpen (U : Set (Fv F v)) → annV ψ v (annV ψ v U) = U ∧ IsCompact (annV ψ v U) ∧ IsOpen (annV ψ v U) ∧ (c : ℝ) ^ 2 * (lam U).toReal * (lam (annV ψ v U)).toReal = 1 := by
  intro F _ _ ψ hψ v lam c _ hSD U hUc hUo
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hc, y, hy⟩ := (GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ).1 v
  have ha := psiV_add ψ v
  have h0 := psiV_zero ψ v
  have hinv := hSD.1
  have hcomp : IsCompact (annV ψ v U) := GlobalTheory.CompanionTheory.SW.PiV.ann_isCompact hc h0 hy U hUo
  have hnear : {x | ‖psiV F ψ v x - 1‖ < 1 / 2} ∈ nhds (0 : Fv F v) :=
    (isOpen_lt (hc.sub continuous_const).norm continuous_const).mem_nhds (by
      change ‖psiV F ψ v 0 - 1‖ < 1 / 2
      rw [h0]
      norm_num)
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.SW.PiV.exists_ball_subset _ hnear
  obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.SW.PiV.exists_ball_of_isCompact _ hUc
  have htriv : ∀ x ∈ GlobalTheory.CompanionTheory.SW.PiV.ball v m, psiV F ψ v x = 1 := fun x hx =>
    char_eq_one_of_near (GlobalTheory.CompanionTheory.SW.PiV.ball v m) _ h0 ha (fun x hx => hm hx) hx
  have hsub : (GlobalTheory.CompanionTheory.SW.PiV.ball v (m - n) : Set (Fv F v)) ⊆ annV ψ v U := by
    intro t ht s hs
    refine htriv _ ?_
    rw [GlobalTheory.CompanionTheory.SW.PiV.mem_ball, map_mul]
    calc Valued.v s * Valued.v t ≤ WithZero.exp n * WithZero.exp (m - n) :=
          mul_le_mul' (hn hs) ht
      _ = WithZero.exp m := by rw [← WithZero.exp_add, add_sub_cancel]
  have hopen : IsOpen (annV ψ v U) :=
    AddSubgroup.isOpen_of_mem_nhds (annS ψ v U) (g := 0)
      (Filter.mem_of_superset ((GlobalTheory.CompanionTheory.SW.PiV.ball_isOpen (m - n)).mem_nhds
        (GlobalTheory.CompanionTheory.SW.PiV.ball v (m - n)).zero_mem) hsub)
  have hcore := ann_core (c • lam) (psiV F ψ v) ha hSD U (annS ψ v U) (annS ψ v (annV ψ v U))
    hUc hUo hUo.measurableSet hopen.measurableSet hcomp.measure_lt_top.ne
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  refine ⟨?_, hcomp, hopen, ?_⟩
  · rw [← coe_annS, hcore.1]
  · have h5 := hcore.2
    rw [coe_annS] at h5
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal] at h5
    rw [← h5]
    ring

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
