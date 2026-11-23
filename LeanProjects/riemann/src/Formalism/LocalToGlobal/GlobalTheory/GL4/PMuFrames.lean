import Mathlib
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.BasicNotions.SkeletonIndexLemmas
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

section Frames

variable {K : Type} [Field K] [NumberField K]

def toH (p : FinPl K) : HeightOneSpectrum (𝓞 K) := ⟨p.1, p.2.isPrime, Formalism.LFunctionChainParameters.slopeLatticeData.finPl_ne_bot p⟩

def ellP (p : FinPl K) : ℝ := Real.log (Ideal.absNorm p.1 : ℝ) / (finrank ℚ K : ℝ)

def finPart (d : FinPl K → K) : ℝ := 2 * ∑ᶠ p : FinPl K, ellP p * (vAdd (toH p) (d p) : ℝ)

def infPart (G : InfinitePlace K → ℝ) : ℝ := (1 / (nPl K : ℝ)) * ∑ v, Real.log (G v)

variable [StarRing K]

def gramJ (A : HLat K) {J : Type} (e : J → A.V) (v : InfinitePlace K) : Matrix J J ℂ :=
  Matrix.of fun a c => majAt A.b A.X v (e a) (e c)

structure FrameData (A : HLat K) (J : Type) [Fintype J] [DecidableEq J] where
  e : Basis J K A.V
  Γ : FinPl K → Matrix J J K
  det_ne : ∀ p, (Γ p).det ≠ 0
  loc : ∀ p, localization₂ (toH p).asIdeal A.L = localization₂ (toH p).asIdeal (latOf (K := K) (famOf e (Γ p)))

variable [IsTotallyComplex K]

theorem mu_of_frames (A : HLat K) (hA : A.Good) {J : Type} [Fintype J] [DecidableEq J] [Nonempty J] (F : FrameData A J) :
    (∀ v, 0 < (gramJ A F.e v).det.re) ∧ (Function.support fun p => vAdd (toH p) (F.Γ p).det).Finite ∧
    (Fintype.card J : ℝ) * A.mu = -(infPart (fun v => (gramJ A F.e v).det.re) + finPart fun p => (F.Γ p).det) := by
  classical
  set j := Fintype.card J with hj
  set eq := Fintype.equivFin J
  set e' : Fin j → A.V := fun a => F.e (eq.symm a) with he'
  have hli : LinearIndependent K e' := F.e.linearIndependent.comp _ eq.symm.injective
  have hrange : Set.range e' = Set.range F.e := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨eq a, by simp [he']⟩
  have hne : A.L ≠ ⊥ := by
    intro h
    have h2 := hA.2.2
    rw [h] at h2
    simp only [Submodule.bot_coe, Submodule.span_zero_singleton] at h2
    obtain ⟨i⟩ := (inferInstance : Nonempty J)
    have : F.e i ∈ (⊥ : Submodule K A.V) := h2 ▸ Submodule.mem_top
    exact F.e.ne_zero i ((Submodule.mem_bot K).1 this)
  have hsp : Submodule.span K (A.L : Set A.V) = Submodule.span K (Set.range e') := by
    rw [hA.2.2, hrange, F.e.span_eq]
  obtain ⟨hrk, -, hG, hsupp, hmu⟩ := Formalism.LFunctionChainParameters.LLcv.log_covolume_slope_mu K A.V A.ι A.b A.X hA.1 j e' A.L hli hA.2.1 hne hsp
  have hgram : ∀ v, (gramPl A.b A.X v e').det = (gramJ A F.e v).det := by
    intro v
    have : gramPl A.b A.X v e' = (gramJ A F.e v).submatrix eq.symm eq.symm := rfl
    rw [this, Matrix.det_submatrix_equiv_self]
  have hidx : ∀ p : FinPl K, (haveI := p.2.isPrime; lidx p.1 (Submodule.span (𝓞 K) (Set.range e')) A.L) =
      vAdd (toH p) (F.Γ p).det := by
    intro p
    rw [hrange]
    have h1 := lidx_congr (toH p) (A := latOf (K := K) F.e) (A' := latOf (K := K) F.e) rfl (F.loc p)
    have h2 := lidx_latOf (toH p) F.e F.e.linearIndependent (F.Γ p) (F.det_ne p)
    exact h1.trans h2
  refine ⟨fun v => by rw [← hgram]; exact (hG v).1, ?_, ?_⟩
  · refine hsupp.subset fun p hp => ?_
    simp only [Function.mem_support] at hp ⊢
    rw [hidx p]; exact hp
  · have hj0 : (j : ℝ) ≠ 0 := by
      have : 0 < j := Fintype.card_pos
      exact_mod_cast this.ne'
    show (j : ℝ) * muDef A.b A.X A.L = _
    rw [hmu, hrk]
    unfold Formalism.LFunctionChainParameters.LLcv.lcv Formalism.LFunctionChainParameters.LLcv.lcvInf Formalism.LFunctionChainParameters.LLcv.lcvFin infPart finPart ellP
    simp only [hgram, hidx]
    field_simp

end Frames

section Functor

variable {K : Type} [Field K] [NumberField K]

theorem vAdd_pow' (w : HeightOneSpectrum (𝓞 K)) (x : K) (m : ℕ) : vAdd w (x ^ m) = m * vAdd w x := by
  simp only [vAdd, map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

theorem vAdd_zpow' (w : HeightOneSpectrum (𝓞 K)) (x : K) (m : ℤ) : vAdd w (x ^ m) = m * vAdd w x := by
  simp only [vAdd, map_zpow₀, WithZero.log_zpow, zsmul_eq_mul, Int.cast_id]
  ring

theorem vAdd_prod_zpow (w : HeightOneSpectrum (𝓞 K)) {S : Type} (T : Finset S) (x : S → K) (hx : ∀ s, x s ≠ 0) (a : S → ℤ) :
    vAdd w (∏ s ∈ T, x s ^ a s) = ∑ s ∈ T, a s * vAdd w (x s) := by
  have hm : ∀ y z : K, y ≠ 0 → z ≠ 0 → vAdd w (y * z) = vAdd w y + vAdd w z := by
    intro y z hy hz
    simp only [vAdd, map_mul]
    rw [WithZero.log_mul ((map_ne_zero _).2 hy) ((map_ne_zero _).2 hz)]
    ring
  induction T using Finset.cons_induction with
  | empty => simp [vAdd]
  | cons s T hs ih =>
    have h1 : x s ^ a s ≠ 0 := zpow_ne_zero _ (hx s)
    have h2 : ∏ i ∈ T, x i ^ a i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hx i)
    rw [Finset.prod_cons, Finset.sum_cons, hm _ _ h1 h2, ih, vAdd_zpow']

theorem log_prod_zpow {S : Type} (T : Finset S) (x : S → ℝ) (hx : ∀ s, 0 < x s) (a : S → ℤ) :
    Real.log (∏ s ∈ T, x s ^ a s) = ∑ s ∈ T, (a s : ℝ) * Real.log (x s) := by
  rw [Real.log_prod (fun s _ => (zpow_pos (hx s) _).ne')]
  exact Finset.sum_congr rfl fun s _ => by rw [Real.log_zpow]

variable [StarRing K] [IsTotallyComplex K]

theorem mu_functor (A : HLat K) (hA : A.Good) {J : Type} [Fintype J] [DecidableEq J] [Nonempty J] (F : FrameData A J)
    {S : Type} [Fintype S] (Q : S → HLat K) (hQ : ∀ s, (Q s).Good) (k : ℕ) (hk : 0 < k)
    (hcard : ∀ s, Fintype.card (Q s).ι = k) (FQ : ∀ s, FrameData (Q s) (Q s).ι) (a : S → ℤ) (g0 : ℝ) (hg0 : 0 < g0)
    (hfin : ∀ p, (F.Γ p).det ^ k = ∏ s, ((FQ s).Γ p).det ^ a s)
    (hinf : ∀ v, (gramJ A F.e v).det.re ^ k = g0 ^ k * ∏ s, (gramJ (Q s) (FQ s).e v).det.re ^ a s) :
    (Fintype.card J : ℝ) * A.mu = -Real.log g0 + ∑ s, (a s : ℝ) * (Q s).mu := by
  haveI : ∀ s, Nonempty (Q s).ι := fun s => Fintype.card_pos_iff.1 (by rw [hcard s]; exact hk)
  obtain ⟨-, hAf, hAmu⟩ := mu_of_frames A hA F
  have hQm : ∀ s, (k : ℝ) * (Q s).mu = -(infPart (fun v => (gramJ (Q s) (FQ s).e v).det.re) +
      finPart fun p => ((FQ s).Γ p).det) := by
    intro s
    have h1 := (mu_of_frames (Q s) (hQ s) (FQ s)).2.2
    rwa [hcard s] at h1
  have hQp : ∀ s v, 0 < (gramJ (Q s) (FQ s).e v).det.re := fun s => (mu_of_frames (Q s) (hQ s) (FQ s)).1
  have hQf : ∀ s, (Function.support fun p => vAdd (toH p) ((FQ s).Γ p).det).Finite :=
    fun s => (mu_of_frames (Q s) (hQ s) (FQ s)).2.1
  have hn : (nPl K : ℝ) ≠ 0 := by
    have h1 : 0 < nPl K := Fintype.card_pos
    exact_mod_cast h1.ne'
  have hnpl : (nPl K : ℝ) = (Fintype.card (InfinitePlace K) : ℝ) := rfl

  have hv : ∀ v, (k : ℝ) * Real.log (gramJ A F.e v).det.re =
      (k : ℝ) * Real.log g0 + ∑ s, (a s : ℝ) * Real.log (gramJ (Q s) (FQ s).e v).det.re := by
    intro v
    rw [← Real.log_pow, hinf v, Real.log_mul (pow_pos hg0 k).ne'
      (Finset.prod_ne_zero_iff.2 fun s _ => (zpow_pos (hQp s v) _).ne'), Real.log_pow,
      log_prod_zpow _ _ (fun s => hQp s v)]
  have hsum : ∑ v, (k : ℝ) * Real.log (gramJ A F.e v).det.re =
      (Fintype.card (InfinitePlace K) : ℝ) * ((k : ℝ) * Real.log g0) +
        ∑ s, (a s : ℝ) * ∑ v, Real.log (gramJ (Q s) (FQ s).e v).det.re := by
    rw [Finset.sum_congr rfl (fun v _ => hv v), Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.sum_comm]
    simp only [Finset.mul_sum]
  have hinfk : (k : ℝ) * infPart (fun v => (gramJ A F.e v).det.re) =
      (k : ℝ) * Real.log g0 + ∑ s, (a s : ℝ) * infPart (fun v => (gramJ (Q s) (FQ s).e v).det.re) := by
    simp only [infPart]
    rw [mul_left_comm, Finset.mul_sum, hsum, ← hnpl, mul_add, ← mul_assoc, one_div_mul_cancel hn, one_mul,
      Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring

  have hd0 : ∀ s p, ((FQ s).Γ p).det ≠ 0 := fun s p => (FQ s).det_ne p
  have hpv : ∀ p, (k : ℤ) * vAdd (toH p) (F.Γ p).det = ∑ s, a s * vAdd (toH p) ((FQ s).Γ p).det := by
    intro p
    rw [← vAdd_pow', hfin p, vAdd_prod_zpow _ _ _ (fun s => hd0 s p) _]
  have h1 : ∀ p, (k : ℝ) * (ellP p * (vAdd (toH p) (F.Γ p).det : ℝ)) =
      ∑ s, (a s : ℝ) * (ellP p * (vAdd (toH p) ((FQ s).Γ p).det : ℝ)) := by
    intro p
    have h2 := congrArg (Int.cast : ℤ → ℝ) (hpv p)
    push_cast at h2
    calc (k : ℝ) * (ellP p * (vAdd (toH p) (F.Γ p).det : ℝ))
        = ellP p * ((k : ℝ) * (vAdd (toH p) (F.Γ p).det : ℝ)) := by ring
      _ = ellP p * ∑ s, (a s : ℝ) * (vAdd (toH p) ((FQ s).Γ p).det : ℝ) := by rw [h2]
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
  have finA : (Function.support fun p => ellP p * (vAdd (toH p) (F.Γ p).det : ℝ)).Finite :=
    hAf.subset fun p hp h => hp (by simp [h])
  have finQ : ∀ s, (Function.support fun p => ellP p * (vAdd (toH p) ((FQ s).Γ p).det : ℝ)).Finite :=
    fun s => (hQf s).subset fun p hp h => hp (by simp [h])
  have hfink : (k : ℝ) * finPart (fun p => (F.Γ p).det) =
      ∑ s, (a s : ℝ) * finPart (fun p => ((FQ s).Γ p).det) := by
    simp only [finPart]
    calc (k : ℝ) * (2 * ∑ᶠ p, ellP p * (vAdd (toH p) (F.Γ p).det : ℝ))
        = 2 * ∑ᶠ p, (k : ℝ) * (ellP p * (vAdd (toH p) (F.Γ p).det : ℝ)) := by
          rw [mul_left_comm, mul_finsum]
      _ = 2 * ∑ᶠ p, ∑ s, (a s : ℝ) * (ellP p * (vAdd (toH p) ((FQ s).Γ p).det : ℝ)) := by
          rw [finsum_congr h1]
      _ = 2 * ∑ s, ∑ᶠ p, (a s : ℝ) * (ellP p * (vAdd (toH p) ((FQ s).Γ p).det : ℝ)) := by
          rw [finsum_sum_comm _ _ (fun s _ => (finQ s).subset fun p hp h => hp (by simp [h]))]
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← mul_finsum]
          ring
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  apply mul_left_cancel₀ hk'
  have h3 : (k : ℝ) * ∑ s, (a s : ℝ) * (Q s).mu = ∑ s, (a s : ℝ) * ((k : ℝ) * (Q s).mu) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hAmu, mul_add, h3]
  simp only [hQm]
  rw [mul_neg, mul_add, hinfk, hfink]
  simp only [mul_neg, mul_add, Finset.sum_neg_distrib, Finset.sum_add_distrib]
  ring

end Functor

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
