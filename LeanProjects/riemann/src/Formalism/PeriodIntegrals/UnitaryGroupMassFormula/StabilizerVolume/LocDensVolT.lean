import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolA

noncomputable section

namespace PI.VolStabS

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW

theorem eq_one_of_pow (z : ℂ) (hz : ‖z‖ = 1) (h : ∀ k : ℕ, 1 / 2 < (z ^ (2 ^ k)).re) : z = 1 := by
  have hsq : ∀ w : ℂ, ‖w‖ = 1 → w.re ^ 2 + w.im ^ 2 = 1 := by
    intro w hw
    have h1 := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at h1
    nlinarith
  have hre : ∀ w : ℂ, ‖w‖ = 1 → (w ^ 2).re = 2 * w.re ^ 2 - 1 := by
    intro w hw
    have := hsq w hw
    rw [sq, Complex.mul_re]
    nlinarith
  have hn : ∀ k : ℕ, ‖z ^ (2 ^ k)‖ = 1 := fun k => by rw [norm_pow, hz, one_pow]
  have hle : ∀ k : ℕ, (z ^ (2 ^ k)).re ≤ 1 := fun k => (Complex.re_le_norm _).trans (hn k).le
  have key : ∀ k : ℕ, (3 : ℝ) ^ k * (1 - z.re) ≤ 1 - (z ^ (2 ^ k)).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e, hre _ (hn k)]
      have h1 := h k
      have h2 := hle k
      rw [pow_succ]
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℝ) ≤ 2 * (z ^ 2 ^ k).re - 1)]
  have hz1 : z.re ≤ 1 := by simpa using hle 0
  have hre1 : z.re = 1 := by
    by_contra hne
    have hε : 0 < 1 - z.re := by
      rcases lt_or_eq_of_le hz1 with h' | h'
      · linarith
      · exact absurd h' hne
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (1 - z.re)) (by norm_num : (1 : ℝ) < 3)
    have h1 := key k
    have h2 := h k
    have h3 : 1 < (3 : ℝ) ^ k * (1 - z.re) := by
      rw [div_lt_iff₀ hε] at hk
      linarith
    linarith
  have him : z.im = 0 := by
    have := hsq z hz
    rw [hre1] at this
    nlinarith
  exact Complex.ext (by simp [hre1]) (by simp [him])

variable {F : Type} [Field F] [NumberField F]

theorem psiV_nsmul (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (y : Fv F v) :
    psiV F ψ v (n • y) = psiV F ψ v y ^ n := by
  induction n with
  | zero =>
    simp only [zero_smul, pow_zero, psiV]
    have : pairA F 0 (singleV F v 0) = 0 := by
      have h := singleV_add (F := F) v 0 0
      rw [add_zero] at h
      have h0 : singleV F v 0 = 0 := by
        have := congrArg (fun x => x - singleV F v 0) h
        exact (by simpa using this : (0 : Af F) = singleV F v 0).symm
      rw [h0]
      rfl
    rw [this, AddChar.map_zero_eq_one]
  | succ n ih => rw [succ_nsmul, psiV_add, ih, pow_succ]

theorem ev_triv (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∀ᶠ v in cofinite, ∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v y = 1 := by
  classical
  set U : Set (AF F) := {x | 1 / 2 < (ψ x).re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp hψ.1)
  let Φ : (∀ v : HeightOneSpectrum (𝓞 F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) → AF F :=
    fun x => pairA F 0 (RestrictedProduct.structureMap _ _ Filter.cofinite x)
  have hΦ : Continuous Φ :=
    continuous_const.prodMk RestrictedProduct.isEmbedding_structureMap.continuous
  let x0 : ∀ v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨0, zero_mem _⟩
  have hx0 : Φ x0 = 0 := by
    show pairA F 0 _ = 0
    have : (RestrictedProduct.structureMap _ _ Filter.cofinite x0 : Af F) = 0 := by
      apply RestrictedProduct.ext
      intro j
      rfl
    rw [this]
    rfl
  have hx0U : x0 ∈ Φ ⁻¹' U := by
    simp only [Set.mem_preimage, hx0, hUdef, Set.mem_setOf_eq, AddChar.map_zero_eq_one,
      Complex.one_re]
    norm_num
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 (hU.preimage hΦ) x0 hx0U
  filter_upwards [(I.finite_toSet).eventually_cofinite_notMem] with v hv
  have hbig : ∀ y ∈ v.adicCompletionIntegers F, 1 / 2 < (psiV F ψ v y).re := by
    intro y hy
    have hmem : Function.update x0 v ⟨y, hy⟩ ∈ (I : Set _).pi u := by
      intro w hw
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      rw [Function.update_of_ne hwv]
      exact (hu w hw).2
    have e : Φ (Function.update x0 v ⟨y, hy⟩) = pairA F 0 (singleV F v y) := by
      show pairA F 0 _ = _
      congr 1
      apply RestrictedProduct.ext
      intro j
      show ((Function.update x0 v ⟨y, hy⟩ j : _) : Fv F j) =
        (Pi.single v y : ∀ w : HeightOneSpectrum (𝓞 F), Fv F w) j
      by_cases hj : j = v
      · subst hj
        simp
      · rw [Function.update_of_ne hj, Pi.single_eq_of_ne hj]
    have := hsub hmem
    simp only [Set.mem_preimage, e, hUdef, Set.mem_setOf_eq] at this
    exact this
  intro y hy
  refine eq_one_of_pow (psiV F ψ v y) (hψ.2.1 _) ?_
  intro k
  rw [← psiV_nsmul]
  apply hbig
  rw [nsmul_eq_mul]
  exact mul_mem (by exact_mod_cast (natCast_mem (v.adicCompletionIntegers F) (2 ^ k))) hy

def CondExact : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v in cofinite, ∀ t : Fv F v,
      (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) → t ∈ v.adicCompletionIntegers F

theorem condAA_of (hE : CondExact) : CondAA := by
  intro F _ _ ψ hψ
  filter_upwards [hE F ψ hψ, ev_triv ψ hψ] with v h1 h2
  intro t
  refine ⟨h1 t, fun ht s hs => h2 _ (mul_mem hs ht)⟩

end VolAAW

end PI.VolStabS
