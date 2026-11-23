import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PairingRankOneMemInverseDifferent
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct Pointwise

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.PDA

open Formalism.IndefR.Fin Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem xi_AA_AAbar : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA *
    D.host.AAbar = FractionalIdeal.dual ℤ ℚ 1 := by
  have hfp := factPrincipalDatum D.R D.host
  have hdd := coeIdeal_differentIdeal ℤ ℚ D.host.E (𝓞 D.host.E)
  have := eq_inv_of_mul_eq_one_left hfp
  rw [this]
  show (((differentIdeal ℤ (𝓞 D.host.E)) : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ = _
  rw [hdd, inv_inv]

theorem one_ne_zero' : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
  rw [← FractionalIdeal.coeIdeal_top]; exact FractionalIdeal.coeIdeal_ne_zero.2 top_ne_bot

theorem dual_ne_zero' : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
  FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero'

theorem AA_ne_zero : D.host.AA ≠ 0 := by
  intro h0
  have h := xi_AA_AAbar (D := D)
  rw [h0, mul_zero, zero_mul] at h
  exact dual_ne_zero' h.symm

set_option maxHeartbeats 800000 in

theorem mem_AA_of_trace {z : D.host.E}
    (h : ∀ c ∈ D.host.AA, Algebra.trace D.host.F D.host.E (D.host.xi0 * (star c * z)) ∈ invDiff D.host.F) :
    z ∈ D.host.AA := by
  have hX := xi_AA_AAbar (D := D)
  have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := one_ne_zero'
  have hmem : ∀ j ∈ D.host.AAbar, D.host.xi0 * z * j ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro j hj
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    have hc : D.host.conj j ∈ D.host.AA := Formalism.L2.Pj.conj_mem_AA D hj
    have hco : D.host.conj j * star (algebraMap (𝓞 D.host.E) D.host.E o) ∈ D.host.AA := by
      have e : D.host.conj j * star (algebraMap (𝓞 D.host.E) D.host.E o) = starO o • D.host.conj j := by
        rw [Algebra.smul_def, mul_comm]; rfl
      rw [e]; exact Submodule.smul_mem _ _ hc
    obtain ⟨k, hk⟩ := h _ hco 1
    rw [show ((1 : 𝓞 D.host.F) : D.host.F) = 1 from rfl, mul_one] at hk
    have hs : star (D.host.conj j) = j := by
      rw [Formalism.BasicNotions.Examples₂.star_eq_conj, Formalism.MainNotions.UnusedSlot33.HK.conj_conj]
    have he : D.host.xi0 * (star (D.host.conj j * star (algebraMap (𝓞 D.host.E) D.host.E o)) * z) =
        D.host.xi0 * z * j * algebraMap (𝓞 D.host.E) D.host.E o := by
      rw [star_mul', star_star, hs]; ring
    rw [he] at hk
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, ← Algebra.trace_trace (S := D.host.F), hk, eq_intCast]
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (D.host.xi0 * z) * D.host.AAbar ≤
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r (hmem j hj)
  set Y := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AAbar with hYdef
  have hAY : D.host.AA * Y = FractionalIdeal.dual ℤ ℚ 1 := by rw [← hX, hYdef]; ring
  have hY : Y ≠ 0 := by
    have h0 : D.host.AA * Y ≠ 0 := by rw [hAY]; exact dual_ne_zero'
    exact right_ne_zero_of_mul h0
  have hzY : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z * Y ≤ D.host.AA * Y := by
    rw [hAY, hYdef, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_comm z]
    exact hle
  have hsp : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z ≤ D.host.AA :=
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z * Y * Y⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hY, mul_one]
      _ ≤ D.host.AA * Y * Y⁻¹ := by gcongr
      _ = D.host.AA := by rw [mul_assoc, mul_inv_cancel₀ hY, mul_one]
  exact hsp (FractionalIdeal.mem_spanSingleton_self _ _)

theorem hF_smul_right (T : HSp D) (x v : Fin T.rank → D.host.E) (j : D.host.E) :
    hF T x (j • v) = j * hF T x v := by
  unfold hF
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem ind_of_hF {T : HSp D} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hT : IsSelfDualC T ΛT)
    {v : Fin T.rank → D.host.E} (hv : ∀ t ∈ ΛT, hF T t v ∈ D.host.AA) (P : (Fin T.rank → D.host.E) → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hgen : ∀ a ∈ D.host.AA, ∀ t ∈ ΛT, P (a • t)) : P v := by
  have hA := AA_ne_zero (D := D)
  have key : ∀ x ∈ D.host.AA * D.host.AA⁻¹, P (x • v) := by
    intro x hx
    refine FractionalIdeal.mul_induction_on hx ?_ ?_
    · intro i hi j hj
      have hjv : j • v ∈ ΛT := by
        refine (hT.2 (j • v)).2 fun t ht => ?_
        have hm : j * hF T t v ∈ D.host.AA⁻¹ * D.host.AA := FractionalIdeal.mul_mem_mul hj (hv t ht)
        rw [inv_mul_cancel₀ hA] at hm
        obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 hm
        refine ⟨b, ?_⟩
        rw [show (b : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b from rfl, hb, ← hF_smul_right]
        rfl
      rw [mul_smul]
      exact hgen i hi _ hjv
    · intro x y hx hy
      rw [add_smul]
      exact hadd _ _ hx hy
  have h1 : (1 : D.host.E) ∈ D.host.AA * D.host.AA⁻¹ := by
    rw [mul_inv_cancel₀ hA]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  simpa using key 1 h1

abbrev rkSpan (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Submodule ℤ (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
  Submodule.span ℤ {M | ∃ c ∈ D.host.AA, ∃ s ∈ ΛS, ∃ t ∈ ΛT, M = rk1 S T c s t}

theorem hF_mulVec (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    ∑ cc, ∑ d, star (t cc) * T.gram cc d * ∑ a, γ d a * s a = hF T t (γ.mulVec s) := by
  unfold hF
  simp only [Matrix.mulVec, dotProduct]

theorem globalDual_of_basis (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hT : IsSelfDualC T ΛT)
    (hB : ∃ (N : ℕ) (g s' : Fin N → Fin S.rank → D.host.E), (∀ i, g i ∈ ΛS) ∧ (∀ i, s' i ∈ ΛS) ∧
      ∀ v : Fin S.rank → D.host.E, ∑ i, hF S (s' i) v • g i = v)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (h : ∀ c ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, betaO S T γ (rk1 S T c s t) ∈ invDiff D.host.F) :
    γ ∈ Submodule.span ℤ {M | ∃ c ∈ D.host.AA, ∃ s ∈ ΛS, ∃ t ∈ ΛT, M = rk1 S T c s t} := by
  obtain ⟨N, g, s', hg, hs', hid⟩ := hB
  have h1 : ∀ s ∈ ΛS, ∀ t ∈ ΛT, hF T t (γ.mulVec s) ∈ D.host.AA := by
    intro s hs t ht
    apply mem_AA_of_trace
    intro c hc
    have := h c hc s hs t ht
    unfold betaO at this
    rwa [hermitian_rank_one_right, hF_mulVec] at this
  have h2 : ∀ s ∈ ΛS, ∀ v : Fin T.rank → D.host.E, (∀ t ∈ ΛT, hF T t v ∈ D.host.AA) →
      rk1 S T 1 s v ∈ rkSpan S T ΛS ΛT := by
    intro s hs v hv
    refine ind_of_hF hT hv (fun w => rk1 S T 1 s w ∈ rkSpan S T ΛS ΛT) ?_ ?_ ?_
    · have : rk1 S T 1 s 0 = 0 := by ext i j; simp [rk1]
      simp only [this]; exact zero_mem _
    · intro x y hx hy
      have : rk1 S T 1 s (x + y) = rk1 S T 1 s x + rk1 S T 1 s y := by
        ext i j; simp only [rk1, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; ring
      simp only [this]; exact add_mem hx hy
    · intro a ha t ht
      have : rk1 S T 1 s (a • t) = rk1 S T a s t := by
        ext i j; simp only [rk1, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]; ring
      simp only [this]
      exact Submodule.subset_span ⟨a, ha, s, hs, t, ht, rfl⟩
  have h3 : γ = ∑ i, rk1 S T 1 (s' i) (γ.mulVec (g i)) := by
    refine Matrix.ext fun a j => ?_
    have hj : γ.mulVec (∑ i, hF S (s' i) (Pi.single j 1) • g i) a = γ.mulVec (Pi.single j 1) a :=
      congrArg (fun w => γ.mulVec w a) (hid (Pi.single j 1))
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at hj
    rw [← hj]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.sum_apply, rk1, Matrix.of_apply, one_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : hF S (s' i) (Pi.single j 1) = ∑ k, star (s' i k) * S.gram k j := by
      unfold hF
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [Pi.single_apply]
    rw [e]; ring
  rw [h3]
  exact Submodule.sum_mem _ fun i _ => h2 (s' i) (hs' i) _ fun t ht => h1 (g i) (hg i) t ht

end Formalism.IndefR.Fin.PDA

end
