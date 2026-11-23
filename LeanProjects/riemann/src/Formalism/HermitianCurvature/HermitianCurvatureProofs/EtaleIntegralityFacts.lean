import Formalism.HermitianCurvature.StatementG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionCriticalPoints
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AffineChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RemainderNormLeStrictUpper
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardCharacterExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FourierUniquenessMirabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeakApproximationGL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WhittakerVanishingImpliesZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CuspidalIrreducibleSubrep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionDerivatives

namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts

open Filter Topology

section Calc

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

def DB (q : ℕ) (f : E → F) (u : E) (S P : ℝ) : Prop :=
  ContDiffAt ℝ q f u ∧ ∀ j ≤ q, ‖iteratedFDeriv ℝ j f u‖ ≤ S * P ^ j

theorem exists_open_contDiffOn {q : ℕ} {f : E → F} {u : E} (h : ContDiffAt ℝ q f u) :
    ∃ U : Set E, IsOpen U ∧ u ∈ U ∧ ContDiffOn ℝ q f U := by
  obtain ⟨U, hU, hu, hc⟩ := h.contDiffOn' le_rfl (by simp)
  exact ⟨U, hU, hu, by simpa using hc⟩

theorem bilin_le (B : F →L[ℝ] G →L[ℝ] H) (hB : ‖B‖ ≤ 1) {q : ℕ} {f : E → F} {g : E → G} {u : E}
    (hf : ContDiffAt ℝ q f u) (hg : ContDiffAt ℝ q g u) {n : ℕ} (hn : n ≤ q) :
    ‖iteratedFDeriv ℝ n (fun y => B (f y) (g y)) u‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f u‖ * ‖iteratedFDeriv ℝ (n - i) g u‖ := by
  obtain ⟨U₁, hU₁, hu₁, hc₁⟩ := exists_open_contDiffOn hf
  obtain ⟨U₂, hU₂, hu₂, hc₂⟩ := exists_open_contDiffOn hg
  have hU : IsOpen (U₁ ∩ U₂) := hU₁.inter hU₂
  have hu : u ∈ U₁ ∩ U₂ := ⟨hu₁, hu₂⟩
  have key := B.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one (hc₁.mono Set.inter_subset_left)
    (hc₂.mono Set.inter_subset_right) hU.uniqueDiffOn hu (n := n) (by exact_mod_cast hn) hB
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hu] using key

theorem comp_le {q n : ℕ} {g : F → G} {f : E → F} {u : E} (hg : ContDiffAt ℝ q g (f u))
    (hf : ContDiffAt ℝ q f u) (hn : n ≤ q) {C D : ℝ} (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g (f u)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f u‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) u‖ ≤ n.factorial * C * D ^ n := by
  obtain ⟨T, hT, hfu, hcT⟩ := exists_open_contDiffOn hg
  obtain ⟨U₁, hU₁, hu₁, hc₁⟩ := exists_open_contDiffOn hf
  have hU : IsOpen (U₁ ∩ f ⁻¹' T) := hc₁.continuousOn.isOpen_inter_preimage hU₁ hT
  have hu : u ∈ U₁ ∩ f ⁻¹' T := ⟨hu₁, hfu⟩
  have key := norm_iteratedFDerivWithin_comp_le (n := n) (x := u) (C := C) (D := D) hcT
    (hc₁.mono Set.inter_subset_left) (by exact_mod_cast hn) hT.uniqueDiffOn hU.uniqueDiffOn
    (fun v hv => hv.2) hu
    (fun i hi => by rw [iteratedFDerivWithin_of_isOpen _ hT hfu]; exact hC i hi)
    (fun i h1 hi => by rw [iteratedFDerivWithin_of_isOpen _ hU hu]; exact hD i h1 hi)
  rwa [iteratedFDerivWithin_of_isOpen _ hU hu] at key

theorem DB.nonneg {q : ℕ} {f : E → F} {u : E} {S P : ℝ} (h : DB q f u S P) : 0 ≤ S := by
  have := h.2 0 (Nat.zero_le _)
  simp only [pow_zero, mul_one] at this
  exact (norm_nonneg _).trans this

theorem DB.norm_le {q : ℕ} {f : E → F} {u : E} {S P : ℝ} (h : DB q f u S P) : ‖f u‖ ≤ S := by
  have := h.2 0 (Nat.zero_le _)
  simpa using this

theorem DB.mono {q : ℕ} {f : E → F} {u : E} {S P S' P' : ℝ} (h : DB q f u S P) (hS : S ≤ S') (hP0 : 0 ≤ P)
    (hP : P ≤ P') : DB q f u S' P' := by
  refine ⟨h.1, fun j hj => (h.2 j hj).trans ?_⟩
  have h0 := h.nonneg
  have h1 : 0 ≤ S' := h0.trans hS
  gcongr

theorem DB.of_le {q q' : ℕ} {f : E → F} {u : E} {S P : ℝ} (h : DB q f u S P) (hq : q' ≤ q) : DB q' f u S P :=
  ⟨h.1.of_le (by exact_mod_cast hq), fun j hj => h.2 j (hj.trans hq)⟩

theorem DB.congr {q : ℕ} {f g : E → F} {u : E} {S P : ℝ} (h : DB q f u S P) (he : g =ᶠ[𝓝 u] f) :
    DB q g u S P := by
  refine ⟨h.1.congr_of_eventuallyEq he, fun j hj => ?_⟩
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  exact h.2 j hj

theorem DB.const (q : ℕ) (c : F) (u : E) {S P : ℝ} (hc : ‖c‖ ≤ S) (hP : 0 ≤ P) :
    DB q (fun _ : E => c) u S P := by
  refine ⟨contDiffAt_const, fun j _ => ?_⟩
  have hS : 0 ≤ S := (norm_nonneg _).trans hc
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simpa using hc
  · rw [iteratedFDeriv_const_of_ne hj.ne']
    simp only [Pi.zero_apply, norm_zero]
    positivity

theorem DB.of_eventually_zero {q : ℕ} {f : E → F} {u : E} {S P : ℝ} (he : f =ᶠ[𝓝 u] fun _ => 0) (hS : 0 ≤ S)
    (hP : 0 ≤ P) : DB q f u S P :=
  (DB.const q (0 : F) u (by simpa using hS) hP).congr he

theorem DB.add {q : ℕ} {f g : E → F} {u : E} {S₁ S₂ P : ℝ} (hf : DB q f u S₁ P) (hg : DB q g u S₂ P) :
    DB q (fun v => f v + g v) u (S₁ + S₂) P := by
  refine ⟨hf.1.add hg.1, fun j hj => ?_⟩
  have hj' : (j : WithTop ℕ∞) ≤ q := by exact_mod_cast hj
  have e : iteratedFDeriv ℝ j (fun v => f v + g v) u = iteratedFDeriv ℝ j f u + iteratedFDeriv ℝ j g u :=
    iteratedFDeriv_add_apply (hf.1.of_le hj') (hg.1.of_le hj')
  rw [e, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hf.2 j hj) (hg.2 j hj))

theorem DB.neg {q : ℕ} {f : E → F} {u : E} {S P : ℝ} (hf : DB q f u S P) : DB q (fun v => -f v) u S P := by
  refine ⟨hf.1.neg, fun j hj => ?_⟩
  have e : iteratedFDeriv ℝ j (fun v => -f v) u = -iteratedFDeriv ℝ j f u := iteratedFDeriv_neg_apply
  rw [e, norm_neg]
  exact hf.2 j hj

theorem DB.sub {q : ℕ} {f g : E → F} {u : E} {S₁ S₂ P : ℝ} (hf : DB q f u S₁ P) (hg : DB q g u S₂ P) :
    DB q (fun v => f v - g v) u (S₁ + S₂) P := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem DB.sum {ι : Type*} {q : ℕ} {f : ι → E → F} {u : E} {S : ι → ℝ} {P : ℝ} (s : Finset ι) (hP : 0 ≤ P)
    (h : ∀ i ∈ s, DB q (f i) u (S i) P) : DB q (fun v => ∑ i ∈ s, f i v) u (∑ i ∈ s, S i) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using DB.const q (0 : F) u (S := 0) (by simp) hP
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem DB.clm {q : ℕ} {f : E → F} {u : E} {S P : ℝ} (L : F →L[ℝ] G) (hf : DB q f u S P) :
    DB q (fun v => L (f v)) u (‖L‖ * S) P := by
  refine ⟨L.contDiff.contDiffAt.comp u hf.1, fun j hj => ?_⟩
  have h1 := L.norm_iteratedFDeriv_comp_left hf.1 (n := j) (by exact_mod_cast hj)
  refine h1.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf.2 j hj) (norm_nonneg _)

theorem DB.clm_one {q : ℕ} {f : E → F} {u : E} {S P : ℝ} (L : F →L[ℝ] G) (hL : ‖L‖ ≤ 1) (hf : DB q f u S P) :
    DB q (fun v => L (f v)) u S P := by
  refine ⟨(hf.clm L).1, fun j hj => ?_⟩
  have h1 := L.norm_iteratedFDeriv_comp_left hf.1 (n := j) (by exact_mod_cast hj)
  refine h1.trans ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (hf.2 j hj))

theorem DB.affine (q : ℕ) (L : E →L[ℝ] F) (c : F) (u : E) {S : ℝ} (h0 : ‖L u + c‖ ≤ S) (h1 : ‖L‖ ≤ S) :
    DB q (fun v => L v + c) u S 1 := by
  refine ⟨(L.contDiff.add contDiff_const).contDiffAt, fun j _ => ?_⟩
  have hS : 0 ≤ S := (norm_nonneg _).trans h1
  have hfd : fderiv ℝ (fun v => L v + c) = fun _ => L := by
    funext v
    rw [fderiv_add_const]
    exact L.fderiv
  simp only [one_pow, mul_one]
  match j with
  | 0 => simpa using h0
  | 1 => rw [norm_iteratedFDeriv_one, hfd]; exact h1
  | (j + 2) =>
    rw [← norm_iteratedFDeriv_fderiv, hfd, iteratedFDeriv_succ_const]
    simpa using hS

theorem DB.bilin (B : F →L[ℝ] G →L[ℝ] H) (hB : ‖B‖ ≤ 1) {q : ℕ} {f : E → F} {g : E → G} {u : E} {S₁ S₂ P : ℝ}
    (hf : DB q f u S₁ P) (hg : DB q g u S₂ P) (hP : 0 ≤ P) :
    DB q (fun v => B (f v) (g v)) u (2 ^ q * S₁ * S₂) P := by
  refine ⟨(B.contDiff.contDiffAt.comp u hf.1).clm_apply hg.1, fun n hn => ?_⟩
  have hS₁ := hf.nonneg
  have hS₂ := hg.nonneg
  refine (bilin_le B hB hf.1 hg.1 hn).trans ?_
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f u‖ * ‖iteratedFDeriv ℝ (n - i) g u‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (S₁ * P ^ i) * (S₂ * P ^ (n - i)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Finset.mem_range_succ_iff.mp hi
        have h1 := hf.2 i (hi'.trans hn)
        have h2 := hg.2 (n - i) ((Nat.sub_le _ _).trans hn)
        gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (S₁ * S₂ * P ^ n) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i ≤ n := Finset.mem_range_succ_iff.mp hi
        rw [show P ^ n = P ^ i * P ^ (n - i) by rw [← pow_add, Nat.add_sub_cancel' hi']]
        ring
    _ = 2 ^ n * (S₁ * S₂ * P ^ n) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
    _ ≤ 2 ^ q * (S₁ * S₂ * P ^ n) := by
        have : (2 : ℝ) ^ n ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hn
        gcongr
    _ = 2 ^ q * S₁ * S₂ * P ^ n := by ring

theorem DB.mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {q : ℕ} {f g : E → A} {u : E} {S₁ S₂ P : ℝ}
    (hf : DB q f u S₁ P) (hg : DB q g u S₂ P) (hP : 0 ≤ P) :
    DB q (fun v => f v * g v) u (2 ^ q * S₁ * S₂) P :=
  DB.bilin (ContinuousLinearMap.mul ℝ A) (ContinuousLinearMap.opNorm_mul_le _ _) hf hg hP

theorem DB.smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {q : ℕ} {f : E → ℂ} {g : E → V} {u : E}
    {S₁ S₂ P : ℝ} (hf : DB q f u S₁ P) (hg : DB q g u S₂ P) (hP : 0 ≤ P) :
    DB q (fun v => f v • g v) u (2 ^ q * S₁ * S₂) P :=
  DB.bilin (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] V →L[ℝ] V) ContinuousLinearMap.opNorm_lsmul_le hf hg hP

theorem DB.comp {q : ℕ} {g : F → G} {f : E → F} {u : E} {So Po S P : ℝ} (hg : DB q g (f u) So Po)
    (hf : DB q f u S P) (hS : 1 ≤ S) (hPo : 1 ≤ Po) (hP : 0 ≤ P) :
    DB q (fun v => g (f v)) u (q.factorial * So) (Po * S * P) := by
  refine ⟨hg.1.comp u hf.1, fun n hn => ?_⟩
  have hSo := hg.nonneg
  have h := comp_le (n := n) (C := So * Po ^ n) (D := S * P) hg.1 hf.1 hn
    (fun i hi => (hg.2 i (hi.trans hn)).trans (by
      have : Po ^ i ≤ Po ^ n := pow_le_pow_right₀ hPo hi
      gcongr))
    (fun i h1 hi => (hf.2 i (hi.trans hn)).trans (by
      rw [mul_pow]
      have : S ≤ S ^ i := le_self_pow₀ hS (by omega)
      gcongr))
  refine h.trans ?_
  have hfac : (n.factorial : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_le hn
  calc (n.factorial : ℝ) * (So * Po ^ n) * (S * P) ^ n ≤ (q.factorial : ℝ) * (So * Po ^ n) * (S * P) ^ n := by
        gcongr
    _ = q.factorial * So * (Po * S * P) ^ n := by
        rw [mul_assoc Po S P, mul_pow Po (S * P) n]
        ring

theorem DB_inv (q : ℕ) (c : ℂ) (hc : c ≠ 0) :
    DB q (fun z : ℂ => z⁻¹) c (q.factorial * ‖c‖⁻¹) ‖c‖⁻¹ := by
  refine ⟨contDiffAt_inv ℝ hc, fun j hj => ?_⟩
  have h : ContDiffAt ℂ j (Inv.inv : ℂ → ℂ) c := contDiffAt_inv ℂ hc
  have e := h.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
  have e' : iteratedFDeriv ℝ j (fun z : ℂ => z⁻¹) c = iteratedFDeriv ℝ j (Inv.inv : ℂ → ℂ) c := rfl
  rw [e', ← e, Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]
  have hfac : (j.factorial : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_le hj
  have hn : ‖c ^ (-1 - (j : ℤ))‖ = ‖c‖⁻¹ * ‖c‖⁻¹ ^ j := by
    rw [norm_zpow, sub_eq_add_neg, zpow_add₀ (norm_ne_zero_iff.mpr hc), zpow_neg_one, zpow_neg, zpow_natCast,
      inv_pow]
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hn, Complex.norm_natCast, mul_assoc]
  gcongr

theorem DB.inv {q : ℕ} {f : E → ℂ} {u : E} {S P W : ℝ} (hf : DB q f u S P) (hc : f u ≠ 0) (hW : ‖f u‖⁻¹ ≤ W)
    (hS : 1 ≤ S) (hW1 : 1 ≤ W) (hP : 0 ≤ P) :
    DB q (fun v => (f v)⁻¹) u (q.factorial * (q.factorial * W)) (W * S * P) := by
  have h0 : DB q (fun z : ℂ => z⁻¹) (f u) (q.factorial * W) W :=
    (DB_inv q (f u) hc).mono (by gcongr) (by positivity) hW
  exact h0.comp hf hS hW1 hP

theorem iteratedDeriv_expI (n : ℕ) :
    iteratedDeriv n (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ))) =
      fun r : ℝ => Complex.I ^ n * Complex.exp (Complex.I * (r : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext r
    have h1 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ)))
        (Complex.exp (Complex.I * (r : ℂ)) * (Complex.I * 1)) r := (h1.const_mul Complex.I).cexp
    rw [(h2.const_mul (Complex.I ^ n)).deriv]
    ring

theorem DB_expI (q : ℕ) (r : ℝ) : DB q (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ))) r 1 1 := by
  refine ⟨?_, fun j _ => ?_⟩
  · have : ContDiff ℝ q (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ))) :=
      (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
    exact this.contDiffAt
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expI]
    simp only [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, mul_one]
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

end Calc

end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts

namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts

open Formalism.FourierDecayAlt.G Matrix

noncomputable section

def Xm (m : ℕ) (p : XY m) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := strictUpper (redOf m p).2.2.1

def Bm (m : ℕ) (p : XY m) : Fin (m + 1) → ℂ := (redOf m p).2.2.2

def rm (m : ℕ) (p : XY m) : Fin m → ℂ := (redOf m p).2.1

def sm (m : ℕ) (p : XY m) : ℂ := (redOf m p).1

def cof1XY (m : ℕ) (t : ℂ) (p : XY m) : ℂ :=
  ∑ j ∈ Finset.range m, ((-Xm m p) ^ j *ᵥ Bm m p) 0 * t ^ (m - 1 - j)

def r1XY (m : ℕ) (t : ℂ) (p : XY m) : ℂ :=
  ∑ j ∈ Finset.range m, (∑ k : Fin m, rm m p k * ((-Xm m p) ^ j *ᵥ Bm m p) k.succ) * t ^ (m - 1 - j)

def cof0XY (m : ℕ) (p : XY m) : ℂ := (-1) ^ m * ∏ k, p.1 k

def gExt (m : ℕ) (D t : ℂ) (p : XY m) : ℂ :=
  ((t ^ m * sm m p - r1XY m t p) * cof0XY m p + D * cof1XY m t p) * (cofXY m t p)⁻¹ * (cof0XY m p)⁻¹

theorem Xm_apply (m : ℕ) (p : XY m) (i j : Fin (m + 1)) :
    Xm m p i j = if i < j then triXY p.1 p.2 i.succ j.castSucc else 0 := by
  by_cases h : i < j <;> simp [Xm, strictUpper, redOf, h]

theorem Xm_strict (m : ℕ) (p : XY m) : IsStrictUpper (Xm m p) :=
  G6.isStrictUpper_strictUpper _

theorem Bm_apply (m : ℕ) (p : XY m) (i : Fin (m + 1)) : Bm m p i = triXY p.1 p.2 i.succ (Fin.last (m + 1)) :=
  rfl

theorem rm_apply (m : ℕ) (p : XY m) (k : Fin m) : rm m p k = triXY p.1 p.2 0 k.succ.castSucc :=
  rfl

theorem sm_apply (m : ℕ) (p : XY m) : sm m p = triXY p.1 p.2 0 (Fin.last (m + 1)) :=
  rfl

theorem tri_cases (m : ℕ) (a b : Fin (m + 2)) :
    (∀ (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ), triXY x y a b = 0) ∨
    (∃ k, ∀ (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ), triXY x y a b = x k) ∨
    (∃ e, ∀ (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ), triXY x y a b = y e) := by
  rcases lt_trichotomy a b with h | h | h
  · exact Or.inr (Or.inr ⟨⟨(a, b), h⟩, fun x y => WeakApproximationGL.tri_lt x y h⟩)
  · subst h
    induction a using Fin.cases with
    | zero => exact Or.inl fun x y => by simp [triXY, strictUpper]
    | succ k => exact Or.inr (Or.inl ⟨k, fun x y => WeakApproximationGL.tri_diag x y k⟩)
  · exact Or.inl fun x y => WeakApproximationGL.tri_gt x y h

theorem cofXY_def (m : ℕ) (t : ℂ) (p : XY m) :
    cofXY m t p = ∑ j ∈ Finset.range (m + 1), ((-Xm m p) ^ j *ᵥ Bm m p) 0 * t ^ (m - j) :=
  rfl

theorem top_eq (m : ℕ) (p : XY m) : ((-Xm m p) ^ m *ᵥ Bm m p) 0 = cof0XY m p := by
  have h := (leading_cofactor m (Xm m p) (Bm m p) (rm m p) (Xm_strict m p)).1
  rw [Cof, G6.sum_mul_zero_pow m (fun j => ((-Xm m p) ^ j *ᵥ Bm m p) 0)] at h
  rw [h, cof0XY]
  congr 1
  exact Finset.prod_congr rfl fun k _ => WeakApproximationGL.xOf_redOf m p k

theorem sum_shift (m : ℕ) (t : ℂ) (a : ℕ → ℂ) :
    ∑ j ∈ Finset.range m, a j * t ^ (m - j) = t * ∑ j ∈ Finset.range m, a j * t ^ (m - 1 - j) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have e : m - j = (m - 1 - j) + 1 := by omega
  rw [e, pow_succ]
  ring

theorem cofXY_eq (m : ℕ) (t : ℂ) (p : XY m) : cofXY m t p = cof0XY m p + t * cof1XY m t p := by
  rw [cofXY_def, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, top_eq,
    sum_shift m t (fun j => ((-Xm m p) ^ j *ᵥ Bm m p) 0), cof1XY, add_comm]

theorem remainder_eq_mul_first (m : ℕ) (t : ℂ) (p : XY m) : R0 (Xm m p) (Bm m p) (rm m p) t = t * r1XY m t p := by
  rw [R0, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one,
    sum_shift m t (fun j => ∑ k : Fin m, rm m p k * ((-Xm m p) ^ j *ᵥ Bm m p) k.succ), r1XY]
  rw [Finset.sum_eq_zero (s := Finset.univ), add_zero]
  intro k _
  rw [G6.pow_mulVec_succ (G6.isStrictUpper_neg (Xm_strict m p)), mul_zero]

theorem rhoXY_def (m : ℕ) (D t : ℂ) (p : XY m) :
    rhoXY m D t p = (t ^ (m + 1) * sm m p - D - R0 (Xm m p) (Bm m p) (rm m p) t) / cofXY m t p :=
  rfl

theorem rhoXY_eq (m : ℕ) (D t : ℂ) (p : XY m) :
    rhoXY m D t p = (t ^ (m + 1) * sm m p - D - t * r1XY m t p) * (cofXY m t p)⁻¹ := by
  rw [rhoXY_def, remainder_eq_mul_first, div_eq_mul_inv]

theorem rhoXY_ext (m : ℕ) (D t : ℂ) (p : XY m) (hc : cofXY m t p ≠ 0) (hp : ∏ k, p.1 k ≠ 0) :
    rhoXY m D t p = (-1) ^ (m + 3) * D / ∏ k, p.1 k + t * gExt m D t p := by
  have he : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; simp
  have he0 : ((-1 : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h0 : cof0XY m p ≠ 0 := mul_ne_zero he0 hp
  have hP : ∏ k, p.1 k = (-1) ^ m * cof0XY m p := by
    rw [cof0XY, ← mul_assoc, he, one_mul]
  have e3 : (-1 : ℂ) ^ (m + 3) = -(-1) ^ m := by rw [pow_add]; norm_num
  rw [rhoXY_eq, gExt, hP, e3]
  rw [cofXY_eq] at hc ⊢
  clear hP he e3
  generalize cof0XY m p = c0 at *
  generalize cof1XY m t p = c1 at *
  generalize r1XY m t p = r1 at *
  generalize sm m p = σ at *
  generalize ((-1 : ℂ) ^ m) = e at *
  field_simp
  ring

theorem gRem_eq (m : ℕ) (D t : ℂ) (p : XY m) (ht : t ≠ 0) (hc : cofXY m t p ≠ 0) (hp : ∏ k, p.1 k ≠ 0) :
    gRem m D t p = gExt m D t p := by
  rw [gRem, rhoXY_ext m D t p hc hp, add_sub_cancel_left, mul_div_cancel_left₀ _ ht]

theorem corner_XY (m : ℕ) (D t : ℂ) (p : XY m) (hc : cofXY m t p ≠ 0) :
    t ^ (m + 1) * sm m p = D + Cof (Xm m p) (Bm m p) t * rhoXY m D t p + R0 (Xm m p) (Bm m p) (rm m p) t := by
  have h : Cof (Xm m p) (Bm m p) t = cofXY m t p := rfl
  rw [h, rhoXY_def, mul_div_cancel₀ _ hc]
  ring

theorem MXY_eq (m : ℕ) (D t : ℂ) (p : XY m) :
    (MXY m D t p : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) =
      wMat (m + 2) * (t • subShift (m + 2) + Matrix.diagonal (Fin.cons (rhoXY m D t p) p.1 : Fin (m + 2) → ℂ) +
        strictUpper p.2) := by
  rw [← (split_xy_matrix m t (rhoXY m D t p) p).2, ← Matrix.mul_assoc, G3.wMat_mul_self, Matrix.one_mul]
  rfl

theorem MXY_apply (m : ℕ) (D t : ℂ) (p : XY m) (i j : Fin (m + 2)) :
    MXY m D t p i j =
      (t • subShift (m + 2) + Matrix.diagonal (Fin.cons (rhoXY m D t p) p.1 : Fin (m + 2) → ℂ) +
        strictUpper p.2) i.rev j := by
  have h := congrFun (congrFun (MXY_eq m D t p) i) j
  rw [G2.wMat_mul_apply] at h
  exact h

theorem H_zero_zero (m : ℕ) (t ρ₁ : ℂ) (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) :
    (t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ x : Fin (m + 2) → ℂ) + strictUpper y) 0 0 = ρ₁ := by
  simp [subShift, strictUpper]

theorem MXY_cases (m : ℕ) (i j : Fin (m + 2)) :
    (∀ (D t : ℂ) (p : XY m), MXY m D t p i j = 0) ∨ (∀ (D t : ℂ) (p : XY m), MXY m D t p i j = t) ∨
    (∀ (D t : ℂ) (p : XY m), MXY m D t p i j = rhoXY m D t p) ∨
    (∃ k, ∀ (D t : ℂ) (p : XY m), MXY m D t p i j = p.1 k) ∨
    (∃ e, ∀ (D t : ℂ) (p : XY m), MXY m D t p i j = p.2 e) := by
  simp only [MXY_apply]
  generalize i.rev = a
  induction a using Fin.cases with
  | zero =>
    by_cases hj : j = 0
    · subst hj
      exact Or.inr (Or.inr (Or.inl fun D t p => H_zero_zero m t _ p.1 p.2))
    · have hj' : 0 < j := Fin.pos_of_ne_zero hj
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨(0, j), hj'⟩, fun D t p => ?_⟩)))
      rw [WeakApproximationGL.rhs_zero t _ p.1 p.2 hj', WeakApproximationGL.tri_lt p.1 p.2 hj']
  | succ a =>
    simp only [WeakApproximationGL.rhs_succ]
    by_cases hj : (j : ℕ) = a
    · refine Or.inr (Or.inl fun D t p => ?_)
      have h : j < a.succ := by rw [Fin.lt_def, Fin.val_succ]; omega
      rw [if_pos hj, WeakApproximationGL.tri_gt p.1 p.2 h, add_zero]
    · simp only [if_neg hj, zero_add]
      rcases tri_cases m a.succ j with h | ⟨k, h⟩ | ⟨e, h⟩
      · exact Or.inl fun D t p => h p.1 p.2
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, fun D t p => h p.1 p.2⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e, fun D t p => h p.1 p.2⟩)))

theorem x_le_MXY (m : ℕ) (D t : ℂ) (p : XY m) (k : Fin (m + 1)) : ‖p.1 k‖ ≤ ‖MXY m D t p‖ := by
  have h : MXY m D t p k.succ.rev k.succ = p.1 k := by
    rw [MXY_apply, Fin.rev_rev, WeakApproximationGL.rhs_succ, WeakApproximationGL.tri_diag, if_neg (by simp), zero_add]
  rw [← h]
  exact G7.norm_entry_le _ _ _

theorem y_le_MXY (m : ℕ) (D t : ℂ) (p : XY m) : ‖p.2‖ ≤ ‖MXY m D t p‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun e => ?_
  obtain ⟨⟨a, b⟩, hab⟩ := e
  have hab' : a < b := hab
  have h : MXY m D t p a.rev b = p.2 ⟨(a, b), hab⟩ := by
    rw [MXY_apply, Fin.rev_rev]
    have h1 : ¬ ((b : ℕ) + 1 = a) := by rw [Fin.lt_def] at hab'; omega
    simp [subShift, strictUpper, hab', hab'.ne, h1]
  rw [← h]
  exact G7.norm_entry_le _ _ _

theorem rho_le_MXY (m : ℕ) (D t : ℂ) (p : XY m) : ‖rhoXY m D t p‖ ≤ ‖MXY m D t p‖ := by
  have h : MXY m D t p (Fin.rev 0) 0 = rhoXY m D t p := by
    rw [MXY_apply, Fin.rev_rev, H_zero_zero]
  rw [← h]
  exact G7.norm_entry_le _ _ _

theorem MXY_le (m : ℕ) (D t : ℂ) (p : XY m) {R : ℝ} (hR : 0 ≤ R) (ht : ‖t‖ ≤ R) (hρ : ‖rhoXY m D t p‖ ≤ R)
    (hx : ∀ k, ‖p.1 k‖ ≤ R) (hy : ‖p.2‖ ≤ R) : ‖MXY m D t p‖ ≤ R := by
  refine (pi_norm_le_iff_of_nonneg hR).2 fun i => (pi_norm_le_iff_of_nonneg hR).2 fun j => ?_
  rcases MXY_cases m i j with h | h | h | ⟨k, h⟩ | ⟨e, h⟩
  · rw [h]; simpa using hR
  · rw [h]; exact ht
  · rw [h]; exact hρ
  · rw [h]; exact hx k
  · rw [h]; exact (norm_le_pi_norm p.2 e).trans hy

theorem tri_le (m : ℕ) (p : XY m) {R : ℝ} (hR : 0 ≤ R) (hx : ∀ k, ‖p.1 k‖ ≤ R) (hy : ‖p.2‖ ≤ R)
    (a b : Fin (m + 2)) : ‖triXY p.1 p.2 a b‖ ≤ R := by
  rcases tri_cases m a b with h | ⟨k, h⟩ | ⟨e, h⟩
  · rw [h]; simpa using hR
  · rw [h]; exact hx k
  · rw [h]; exact (norm_le_pi_norm p.2 e).trans hy

theorem Xm_le (m : ℕ) (p : XY m) {R : ℝ} (hR : 0 ≤ R) (hx : ∀ k, ‖p.1 k‖ ≤ R) (hy : ‖p.2‖ ≤ R)
    (i j : Fin (m + 1)) : ‖Xm m p i j‖ ≤ R := by
  rw [Xm_apply]
  split_ifs
  · exact tri_le m p hR hx hy _ _
  · simpa using hR

theorem Bm_le (m : ℕ) (p : XY m) {R : ℝ} (hR : 0 ≤ R) (hx : ∀ k, ‖p.1 k‖ ≤ R) (hy : ‖p.2‖ ≤ R)
    (i : Fin (m + 1)) : ‖Bm m p i‖ ≤ R :=
  tri_le m p hR hx hy _ _

theorem rm_le (m : ℕ) (p : XY m) {R : ℝ} (hR : 0 ≤ R) (hx : ∀ k, ‖p.1 k‖ ≤ R) (hy : ‖p.2‖ ≤ R)
    (k : Fin m) : ‖rm m p k‖ ≤ R :=
  tri_le m p hR hx hy _ _

theorem sm_le (m : ℕ) (p : XY m) {R : ℝ} (hR : 0 ≤ R) (hx : ∀ k, ‖p.1 k‖ ≤ R) (hy : ‖p.2‖ ≤ R) :
    ‖sm m p‖ ≤ R :=
  tri_le m p hR hx hy _ _

theorem first_cofactor_norm_le (m : ℕ) (t : ℂ) (p : XY m) {R : ℝ} (hR : 1 ≤ R) (ht : ‖t‖ ≤ 1) (hx : ∀ k, ‖p.1 k‖ ≤ R)
    (hy : ‖p.2‖ ≤ R) : ‖cof1XY m t p‖ ≤ ((m : ℝ) + 1) ^ (m + 1) * R ^ m := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have term : ∀ j ∈ Finset.range m, ‖((-Xm m p) ^ j *ᵥ Bm m p) 0 * t ^ (m - 1 - j)‖ ≤
      ((m : ℝ) + 1) ^ m * R ^ m := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [norm_mul, norm_pow]
    calc ‖((-Xm m p) ^ j *ᵥ Bm m p) 0‖ * ‖t‖ ^ (m - 1 - j)
        ≤ (((m : ℝ) + 1) ^ j * R ^ (j + 1)) * 1 :=
          mul_le_mul (G6.norm_pow_mulVec_le hR0 (Xm_le m p hR0 hx hy) (Bm_le m p hR0 hx hy) j 0)
            (pow_le_one₀ (norm_nonneg _) ht) (by positivity) (by positivity)
      _ ≤ ((m : ℝ) + 1) ^ m * R ^ m := by
          rw [mul_one]
          exact mul_le_mul (pow_le_pow_right₀ hm1 hj'.le) (pow_le_pow_right₀ hR (by omega)) (by positivity)
            (by positivity)
  calc ‖cof1XY m t p‖ ≤ ∑ j ∈ Finset.range m, ‖((-Xm m p) ^ j *ᵥ Bm m p) 0 * t ^ (m - 1 - j)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range m, ((m : ℝ) + 1) ^ m * R ^ m := Finset.sum_le_sum term
    _ = (m : ℝ) * (((m : ℝ) + 1) ^ m * R ^ m) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((m : ℝ) + 1) * (((m : ℝ) + 1) ^ m * R ^ m) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

theorem remainder_norm_le (m : ℕ) (t : ℂ) (p : XY m) {R : ℝ} (hR : 1 ≤ R) (ht : ‖t‖ ≤ 1) (hx : ∀ k, ‖p.1 k‖ ≤ R)
    (hy : ‖p.2‖ ≤ R) : ‖r1XY m t p‖ ≤ ((m : ℝ) + 1) ^ (m + 2) * R ^ (m + 1) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have term : ∀ j ∈ Finset.range m,
      ‖(∑ k : Fin m, rm m p k * ((-Xm m p) ^ j *ᵥ Bm m p) k.succ) * t ^ (m - 1 - j)‖ ≤
      ((m : ℝ) + 1) ^ (m + 1) * R ^ (m + 1) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [norm_mul, norm_pow]
    have h1 : ‖∑ k : Fin m, rm m p k * ((-Xm m p) ^ j *ᵥ Bm m p) k.succ‖ ≤
        (m : ℝ) * (R * (((m : ℝ) + 1) ^ j * R ^ (j + 1))) := by
      calc ‖∑ k : Fin m, rm m p k * ((-Xm m p) ^ j *ᵥ Bm m p) k.succ‖
          ≤ ∑ k : Fin m, ‖rm m p k * ((-Xm m p) ^ j *ᵥ Bm m p) k.succ‖ := norm_sum_le _ _
        _ ≤ ∑ _k : Fin m, R * (((m : ℝ) + 1) ^ j * R ^ (j + 1)) := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [norm_mul]
            exact mul_le_mul (rm_le m p hR0 hx hy k)
              (G6.norm_pow_mulVec_le hR0 (Xm_le m p hR0 hx hy) (Bm_le m p hR0 hx hy) j k.succ)
              (norm_nonneg _) hR0
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ‖∑ k : Fin m, rm m p k * ((-Xm m p) ^ j *ᵥ Bm m p) k.succ‖ * ‖t‖ ^ (m - 1 - j)
        ≤ ((m : ℝ) * (R * (((m : ℝ) + 1) ^ j * R ^ (j + 1)))) * 1 :=
          mul_le_mul h1 (pow_le_one₀ (norm_nonneg _) ht) (by positivity) (by positivity)
      _ = (m : ℝ) * (((m : ℝ) + 1) ^ j * R ^ (j + 2)) := by ring
      _ ≤ ((m : ℝ) + 1) * (((m : ℝ) + 1) ^ m * R ^ (m + 1)) :=
          mul_le_mul (by linarith)
            (mul_le_mul (pow_le_pow_right₀ hm1 hj'.le) (pow_le_pow_right₀ hR (by omega)) (by positivity)
              (by positivity)) (by positivity) (by positivity)
      _ = _ := by ring
  calc ‖r1XY m t p‖ ≤ ∑ j ∈ Finset.range m,
        ‖(∑ k : Fin m, rm m p k * ((-Xm m p) ^ j *ᵥ Bm m p) k.succ) * t ^ (m - 1 - j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range m, ((m : ℝ) + 1) ^ (m + 1) * R ^ (m + 1) := Finset.sum_le_sum term
    _ = (m : ℝ) * (((m : ℝ) + 1) ^ (m + 1) * R ^ (m + 1)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((m : ℝ) + 1) * (((m : ℝ) + 1) ^ (m + 1) * R ^ (m + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

theorem rhoXY_zero (m : ℕ) (D z : ℂ) (y : UT (m + 2) → ℂ) (hz : z ≠ 0) (hzD : z ^ (m + 2) = (-1) ^ (m + 3) * D) :
    rhoXY m D 0 (fun _ => z, y) = z :=
  (reduced_phase_critical_points m z D (sm m (fun _ => z, y)) (rm m (fun _ => z, y)) (Xm m (fun _ => z, y))
    (Bm m (fun _ => z, y)) hz hzD (Xm_strict m _) (fun k => WeakApproximationGL.xOf_redOf m (fun _ => z, y) k)).1

theorem MXY_zero (m : ℕ) (D z : ℂ) (y : UT (m + 2) → ℂ) (hz : z ≠ 0) (hzD : z ^ (m + 2) = (-1) ^ (m + 3) * D) :
    MXY m D 0 (fun _ => z, y) =
      wMat (m + 2) * (z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y) := by
  have h := MXY_eq m D 0 (fun _ => z, y)
  rw [rhoXY_zero m D z y hz hzD, zero_smul, zero_add, WeakApproximationGL.diag_const] at h
  exact h

theorem differentiable_cofXY (m : ℕ) (p : XY m) : Differentiable ℂ fun t => cofXY m t p := by
  simp only [cofXY_def]
  fun_prop

theorem leading_cofactor_ne_zero (m : ℕ) (p : XY m) (hp : ∏ k, p.1 k ≠ 0) : cof0XY m p ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) hp

theorem cofXY_at_zero (m : ℕ) (p : XY m) : cofXY m 0 p = cof0XY m p := by
  rw [cofXY_eq, zero_mul, add_zero]

theorem gExt_zero (m : ℕ) (D z : ℂ) (y : UT (m + 2) → ℂ) (hz : z ≠ 0) (hzD : z ^ (m + 2) = (-1) ^ (m + 3) * D) :
    gExt m D 0 (fun _ => z, y) = superSum (strictUpper y) / z := by
  set p : XY m := (fun _ => z, y) with hp
  have hprod : ∏ k, p.1 k ≠ 0 := by simp [hp, hz]
  have hc0 : cofXY m 0 p ≠ 0 := by rw [cofXY_at_zero]; exact leading_cofactor_ne_zero m p hprod
  have h1 := (reduced_phase_critical_points m z D (sm m p) (rm m p) (Xm m p) (Bm m p) hz hzD (Xm_strict m _)
    (fun k => WeakApproximationGL.xOf_redOf m p k)).2
  have hL : wMat (m + 2) * Mcoord 0 (Xm m p) (Bm m p) (Fin.cons z (rm m p)) (sm m p) =
      z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y := limit_coordinates_xy m z y
  have hS : superSum (z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y) =
      superSum (strictUpper y) := by
    unfold superSum
    refine Finset.sum_congr rfl fun i _ => ?_
    have : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
    simp [this]
  rw [hL, hS] at h1
  have hg : DifferentiableAt ℂ (fun t => gExt m D t p) 0 := by
    unfold gExt r1XY cof1XY
    refine DifferentiableAt.mul (DifferentiableAt.mul (by fun_prop) ?_) (by fun_prop)
    exact (differentiable_cofXY m p 0).inv hc0
  have h2 : HasDerivAt (fun t => (-1) ^ (m + 3) * D / ∏ k, p.1 k + t * gExt m D t p) (gExt m D 0 p) 0 := by
    have := ((hasDerivAt_id (0 : ℂ)).mul hg.hasDerivAt).const_add ((-1) ^ (m + 3) * D / ∏ k, p.1 k)
    simpa using this
  have h3 : HasDerivAt (fun t => rhoXY m D t p) (gExt m D 0 p) 0 := by
    refine h2.congr_of_eventuallyEq ?_
    have hev : ∀ᶠ t in nhds (0 : ℂ), cofXY m t p ≠ 0 :=
      (differentiable_cofXY m p).continuous.continuousAt.eventually_ne hc0
    filter_upwards [hev] with t ht
    exact rhoXY_ext m D t p ht hprod
  exact h3.unique h1

theorem cofXY_zero (m : ℕ) (z : ℂ) (y : UT (m + 2) → ℂ) : ‖cofXY m 0 (fun _ => z, y)‖ = ‖z‖ ^ (m + 1) := by
  rw [cofXY_at_zero, cof0XY]
  simp

end

end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts

namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts

open Formalism.FourierDecayAlt.G Matrix Filter Topology

noncomputable section

def ampE {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ) (Φ : Mat (m + 1 + 1) → V)
    (D t : ℂ) (p : XY m) : V :=
  (psi β (gExt m D t p) * (((‖cofXY m t p‖ ^ 2)⁻¹ : ℝ) : ℂ)) • Φ (MXY m D t p)

theorem amp_eq_ampE {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ) (Φ : Mat (m + 1 + 1) → V)
    (D t : ℂ) (p : XY m) (ht : t ≠ 0) (hp : ∏ k, p.1 k ≠ 0) : amp β m Φ D t p = ampE β m Φ D t p := by
  by_cases hc : cofXY m t p = 0
  · simp [amp, ampE, hc]
  · rw [amp, ampE, gRem_eq m D t p ht hc hp]

theorem DB_of_DerivBound {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {s k q : ℕ} {Kd : Set ℂ}
    {bd : Mat s → ℝ} {Φ : Mat s → V} (h : DerivBound k Kd bd Φ) (hq : q ≤ k) {Z : Mat s} (hZ : detM Z ∈ Kd) :
    DB q Φ Z (bd Z) 1 := by
  have h1 : DB k Φ Z (bd Z) 1 := ⟨(h Z hZ).1, fun j hj => by simpa using (h Z hZ).2 j hj⟩
  exact h1.of_le hq

section Gen

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem DB.powle {q : ℕ} {f : E → F} {u : E} {Q P : ℝ} {a b : ℕ} (h : DB q f u (Q ^ a) P) (hQ : 1 ≤ Q)
    (hab : a ≤ b) (hP : 0 ≤ P) : DB q f u (Q ^ b) P :=
  h.mono (pow_le_pow_right₀ hQ hab) hP le_rfl

theorem DB.mulQ {q : ℕ} {f g : E → ℂ} {u : E} {Q P : ℝ} {a b : ℕ} (hf : DB q f u (Q ^ a) P)
    (hg : DB q g u (Q ^ b) P) (hP : 0 ≤ P) (h2 : (2 : ℝ) ^ q ≤ Q) :
    DB q (fun v => f v * g v) u (Q ^ (a + b + 1)) P := by
  have hQ0 : 0 ≤ Q := le_trans (by positivity) h2
  refine (hf.mul hg hP).mono ?_ hP le_rfl
  calc (2 : ℝ) ^ q * Q ^ a * Q ^ b ≤ Q * Q ^ a * Q ^ b := by gcongr
    _ = Q ^ (a + b + 1) := by ring

theorem DB.addQ {q : ℕ} {f g : E → F} {u : E} {Q P : ℝ} {a : ℕ} (hf : DB q f u (Q ^ a) P)
    (hg : DB q g u (Q ^ a) P) (hP : 0 ≤ P) (h2 : (2 : ℝ) ≤ Q) :
    DB q (fun v => f v + g v) u (Q ^ (a + 1)) P := by
  have hQ0 : 0 ≤ Q := le_trans (by positivity) h2
  refine (hf.add hg).mono ?_ hP le_rfl
  calc Q ^ a + Q ^ a = 2 * Q ^ a := by ring
    _ ≤ Q * Q ^ a := by gcongr
    _ = Q ^ (a + 1) := by ring

theorem DB.subQ {q : ℕ} {f g : E → F} {u : E} {Q P : ℝ} {a : ℕ} (hf : DB q f u (Q ^ a) P)
    (hg : DB q g u (Q ^ a) P) (hP : 0 ≤ P) (h2 : (2 : ℝ) ≤ Q) :
    DB q (fun v => f v - g v) u (Q ^ (a + 1)) P := by
  have hQ0 : 0 ≤ Q := le_trans (by positivity) h2
  refine (hf.sub hg).mono ?_ hP le_rfl
  calc Q ^ a + Q ^ a = 2 * Q ^ a := by ring
    _ ≤ Q * Q ^ a := by gcongr
    _ = Q ^ (a + 1) := by ring

theorem DB.sumQ {ι : Type*} {q : ℕ} {f : ι → E → F} {u : E} {Q P : ℝ} {a : ℕ} (s : Finset ι)
    (h : ∀ i ∈ s, DB q (f i) u (Q ^ a) P) (hP : 0 ≤ P) (hQ0 : 0 ≤ Q) (hc : (s.card : ℝ) ≤ Q) :
    DB q (fun v => ∑ i ∈ s, f i v) u (Q ^ (a + 1)) P := by
  refine (DB.sum s hP h).mono ?_ hP le_rfl
  rw [Finset.sum_const, nsmul_eq_mul]
  calc (s.card : ℝ) * Q ^ a ≤ Q * Q ^ a := by gcongr
    _ = Q ^ (a + 1) := by ring

theorem DB.prodQ {ι : Type*} [DecidableEq ι] {q : ℕ} {f : ι → E → ℂ} {u : E} {Q P : ℝ} (s : Finset ι)
    (h : ∀ i ∈ s, DB q (f i) u (Q ^ 1) P) (hP : 0 ≤ P) (h2 : (2 : ℝ) ^ q ≤ Q) :
    DB q (fun v => ∏ i ∈ s, f i v) u (Q ^ (2 * s.card)) P := by
  induction s using Finset.induction_on with
  | empty => simpa using DB.const q (1 : ℂ) u (S := 1) (by simp) hP
  | insert a s ha ih =>
    have h1 := (h a (Finset.mem_insert_self a s)).mulQ (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) hP h2
    have e : 1 + 2 * s.card + 1 = 2 * (insert a s).card := by
      rw [Finset.card_insert_of_notMem ha]; ring
    rw [e] at h1
    simpa [Finset.prod_insert ha] using h1

theorem DB.pi {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {f : E → ι → F} {u : E} {S P : ℝ}
    (h : ∀ i, DB q (fun v => f v i) u S P) (hP : 0 ≤ P) : DB q f u (Fintype.card ι * S) P := by
  have e : f = fun v => ∑ i ∈ (Finset.univ : Finset ι), (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) (f v i) := by
    funext v
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [e]
  have h1 : ∀ i ∈ (Finset.univ : Finset ι),
      DB q (fun v => (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) (f v i)) u S P := by
    intro i _
    refine DB.clm_one _ ?_ (h i)
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    show ‖(Pi.single i x : ι → F)‖ ≤ ‖x‖
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  have h2 := DB.sum Finset.univ hP h1
  simpa using h2

end Gen

section Poly

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {m q : ℕ} {tt : E → ℂ}
  {xx : E → Fin (m + 1) → ℂ} {yy : E → UT (m + 2) → ℂ} {u : E} {Q : ℝ}

theorem tri_DB (hQ0 : 0 ≤ Q) (hx : ∀ k, DB q (fun v => xx v k) u Q 1) (hy : ∀ e, DB q (fun v => yy v e) u Q 1)
    (a b : Fin (m + 2)) : DB q (fun v => triXY (xx v) (yy v) a b) u (Q ^ 1) 1 := by
  rw [pow_one]
  rcases tri_cases m a b with h | ⟨k, h⟩ | ⟨e, h⟩
  · simp only [h]; exact DB.const q 0 u (by simpa using hQ0) zero_le_one
  · simp only [h]; exact hx k
  · simp only [h]; exact hy e

theorem Xm_DB (hQ0 : 0 ≤ Q) (hx : ∀ k, DB q (fun v => xx v k) u Q 1) (hy : ∀ e, DB q (fun v => yy v e) u Q 1)
    (i j : Fin (m + 1)) : DB q (fun v => Xm m (xx v, yy v) i j) u (Q ^ 1) 1 := by
  simp only [Xm_apply]
  split_ifs
  · exact tri_DB hQ0 hx hy _ _
  · exact DB.const q 0 u (by simpa using hQ0) zero_le_one

theorem Bm_DB (hQ0 : 0 ≤ Q) (hx : ∀ k, DB q (fun v => xx v k) u Q 1) (hy : ∀ e, DB q (fun v => yy v e) u Q 1)
    (i : Fin (m + 1)) : DB q (fun v => Bm m (xx v, yy v) i) u (Q ^ 1) 1 := by
  simp only [Bm_apply]
  exact tri_DB hQ0 hx hy _ _

theorem rm_DB (hQ0 : 0 ≤ Q) (hx : ∀ k, DB q (fun v => xx v k) u Q 1) (hy : ∀ e, DB q (fun v => yy v e) u Q 1)
    (k : Fin m) : DB q (fun v => rm m (xx v, yy v) k) u (Q ^ 1) 1 := by
  simp only [rm_apply]
  exact tri_DB hQ0 hx hy _ _

theorem sm_DB (hQ0 : 0 ≤ Q) (hx : ∀ k, DB q (fun v => xx v k) u Q 1) (hy : ∀ e, DB q (fun v => yy v e) u Q 1) :
    DB q (fun v => sm m (xx v, yy v)) u (Q ^ 1) 1 := by
  simp only [sm_apply]
  exact tri_DB hQ0 hx hy _ _

theorem pow_DB (h2 : (2 : ℝ) ^ q ≤ Q) (hm : ((m : ℝ) + 1) ≤ Q) (hx : ∀ k, DB q (fun v => xx v k) u Q 1)
    (hy : ∀ e, DB q (fun v => yy v e) u Q 1) (j : ℕ) :
    ∀ i, DB q (fun v => ((-Xm m (xx v, yy v)) ^ j *ᵥ Bm m (xx v, yy v)) i) u (Q ^ (3 * j + 1)) 1 := by
  have hQ0 : 0 ≤ Q := le_trans (by positivity) h2
  induction j with
  | zero => intro i; simpa using Bm_DB hQ0 hx hy i
  | succ j ih =>
    intro i
    have e : (fun v => ((-Xm m (xx v, yy v)) ^ (j + 1) *ᵥ Bm m (xx v, yy v)) i) = fun v =>
        ∑ l ∈ (Finset.univ : Finset (Fin (m + 1))),
          (-Xm m (xx v, yy v) i l) * ((-Xm m (xx v, yy v)) ^ j *ᵥ Bm m (xx v, yy v)) l := by
      funext v
      rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
      rfl
    rw [e]
    have h1 := DB.sumQ (Finset.univ : Finset (Fin (m + 1)))
      (fun l _ => ((Xm_DB hQ0 hx hy i l).neg).mulQ (ih l) zero_le_one h2) zero_le_one hQ0
      (by simpa using hm)
    have e2 : 1 + (3 * j + 1) + 1 + 1 = 3 * (j + 1) + 1 := by ring
    rwa [e2] at h1

theorem tpow_DB (h2 : (2 : ℝ) ^ q ≤ Q) (ht : DB q tt u Q 1) (i : ℕ) :
    DB q (fun v => tt v ^ i) u (Q ^ (2 * i)) 1 := by
  induction i with
  | zero => simpa using DB.const q (1 : ℂ) u (S := 1) (by simp) zero_le_one
  | succ i ih =>
    have h1 := ih.mulQ (b := 1) (by simpa using ht) zero_le_one h2
    have e2 : 2 * i + 1 + 1 = 2 * (i + 1) := by ring
    rw [e2] at h1
    simpa [pow_succ] using h1

theorem cof_DB (h1Q : 1 ≤ Q) (h2 : (2 : ℝ) ^ q ≤ Q) (hm : ((m : ℝ) + 1) ≤ Q) (ht : DB q tt u Q 1)
    (hx : ∀ k, DB q (fun v => xx v k) u Q 1) (hy : ∀ e, DB q (fun v => yy v e) u Q 1) :
    DB q (fun v => cofXY m (tt v) (xx v, yy v)) u (Q ^ (3 * m + 3)) 1 := by
  have hQ0 : 0 ≤ Q := le_trans (by positivity) h2
  simp only [cofXY_def]
  refine DB.sumQ (a := 3 * m + 2) _ (fun j hj => ?_) zero_le_one hQ0 (by simpa using hm)
  have hj' := Finset.mem_range.mp hj
  exact ((pow_DB h2 hm hx hy j 0).mulQ (tpow_DB h2 ht (m - j)) zero_le_one h2).powle h1Q (by omega) zero_le_one

theorem first_cofactor_derivative_bound (h1Q : 1 ≤ Q) (h2 : (2 : ℝ) ^ q ≤ Q) (hm : ((m : ℝ) + 1) ≤ Q) (ht : DB q tt u Q 1)
    (hx : ∀ k, DB q (fun v => xx v k) u Q 1) (hy : ∀ e, DB q (fun v => yy v e) u Q 1) :
    DB q (fun v => cof1XY m (tt v) (xx v, yy v)) u (Q ^ (3 * m + 3)) 1 := by
  have hQ0 : 0 ≤ Q := le_trans (by positivity) h2
  simp only [cof1XY]
  refine DB.sumQ (a := 3 * m + 2) _ (fun j hj => ?_) zero_le_one hQ0 (by simp; linarith)
  have hj' := Finset.mem_range.mp hj
  exact ((pow_DB h2 hm hx hy j 0).mulQ (tpow_DB h2 ht (m - 1 - j)) zero_le_one h2).powle h1Q (by omega)
    zero_le_one

theorem remainder_derivative_bound (h1Q : 1 ≤ Q) (h2 : (2 : ℝ) ^ q ≤ Q) (hm : ((m : ℝ) + 1) ≤ Q) (ht : DB q tt u Q 1)
    (hx : ∀ k, DB q (fun v => xx v k) u Q 1) (hy : ∀ e, DB q (fun v => yy v e) u Q 1) :
    DB q (fun v => r1XY m (tt v) (xx v, yy v)) u (Q ^ (3 * m + 4)) 1 := by
  have hQ0 : 0 ≤ Q := le_trans (by positivity) h2
  simp only [r1XY]
  refine DB.sumQ (a := 3 * m + 3) _ (fun j hj => ?_) zero_le_one hQ0 (by simp; linarith)
  have hj' := Finset.mem_range.mp hj
  have h3 := DB.sumQ (Finset.univ : Finset (Fin m))
    (fun k _ => (rm_DB hQ0 hx hy k).mulQ (pow_DB h2 hm hx hy j k.succ) zero_le_one h2) zero_le_one hQ0
    (by simp; linarith)
  exact (h3.mulQ (tpow_DB h2 ht (m - 1 - j)) zero_le_one h2).powle h1Q (by omega) zero_le_one

theorem leading_cofactor_derivative_bound (h2 : (2 : ℝ) ^ q ≤ Q) (hx : ∀ k, DB q (fun v => xx v k) u Q 1) :
    DB q (fun v => cof0XY m (xx v, yy v)) u (Q ^ (2 * m + 3)) 1 := by
  simp only [cof0XY]
  have h1 := DB.prodQ (f := fun k v => xx v k) (Finset.univ : Finset (Fin (m + 1)))
    (fun k _ => by simpa using hx k) zero_le_one h2
  have h0 : DB q (fun _ : E => ((-1 : ℂ)) ^ m) u (Q ^ 0) 1 := DB.const q _ u (by simp) zero_le_one
  have h3 := h0.mulQ h1 zero_le_one h2
  have e : 0 + 2 * (Finset.univ : Finset (Fin (m + 1))).card + 1 = 2 * m + 3 := by simp; ring
  rwa [e] at h3

end Poly

theorem normSq_inv_cast (c : ℂ) : (((‖c‖ ^ 2)⁻¹ : ℝ) : ℂ) = c⁻¹ * (Complex.conjCLE : ℂ →L[ℝ] ℂ) c⁻¹ := by
  have h : c⁻¹ * (starRingEnd ℂ) c⁻¹ = ((Complex.normSq c⁻¹ : ℝ) : ℂ) := Complex.mul_conj _
  show _ = c⁻¹ * (starRingEnd ℂ) c⁻¹
  rw [h, Complex.normSq_inv, Complex.normSq_eq_norm_sq]

theorem psi_eq (β w : ℂ) :
    psi β w = (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ))) ((Complex.reCLM : ℂ →L[ℝ] ℝ) (β * w)) := rfl

theorem card_range_inf_torsion_le_index_pow (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m q : ℕ) (β D : ℂ) (tt : E → ℂ)
    (xx : E → Fin (m + 1) → ℂ) (yy : E → UT (m + 2) → ℂ) (u : E) (Q W : ℝ)
    (hQc : 2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial ≤ Q) (ht : DB q tt u Q 1)
    (hx : ∀ k, DB q (fun v => xx v k) u Q 1)
    (hy : ∀ e, DB q (fun v => yy v e) u Q 1) (hD : ‖D‖ ≤ Q) (hβ : ‖β‖ ≤ Q) (hQW : Q ^ (4 * (m + 2)) ≤ W)
    (hc : cofXY m (tt u) (xx u, yy u) ≠ 0) (hcW : ‖cofXY m (tt u) (xx u, yy u)‖⁻¹ ≤ W)
    (hp : ∏ k, xx u k ≠ 0) (hpW : ‖∏ k, xx u k‖⁻¹ ≤ W)
    (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Φ : Mat (m + 1 + 1) → V) (K' : ℝ)
    (hΦ : DB q Φ (MXY m D (tt u) (xx u, yy u)) K' 1) :
    DB q (fun v => ampE β m Φ D (tt v) (xx v, yy v)) u (K' * W ^ 11) (W ^ 16) := by

  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hf1 : (1 : ℝ) ≤ (q.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero q)
  have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ q := one_le_pow₀ (by norm_num)
  have hs1 : (4 : ℝ) ≤ ((m : ℝ) + 2) ^ 2 := by nlinarith
  have hA : (2 : ℝ) ^ q * ((m : ℝ) + 2) ^ 2 ≤ Q :=
    le_trans (le_mul_of_one_le_right (by positivity) hf1) hQc
  have h2 : (2 : ℝ) ^ q ≤ Q := le_trans (le_mul_of_one_le_right (by positivity) (by linarith)) hA
  have hs : ((m : ℝ) + 2) ^ 2 ≤ Q := le_trans (le_mul_of_one_le_left (by positivity) hp1) hA
  have hfQ : (q.factorial : ℝ) ≤ Q :=
    le_trans (le_mul_of_one_le_left (by positivity) (by nlinarith)) hQc
  have h4 : (4 : ℝ) ≤ Q := le_trans hs1 hs
  have h1Q : (1 : ℝ) ≤ Q := by linarith
  have h2Q : (2 : ℝ) ≤ Q := by linarith
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  have hm : (m : ℝ) + 1 ≤ Q := by nlinarith
  have hm2 : (m : ℝ) + 2 ≤ Q := by nlinarith
  have hQW1 : Q ≤ W := le_trans (le_self_pow₀ h1Q (by omega)) hQW
  have h1W : (1 : ℝ) ≤ W := le_trans h1Q hQW1
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have h2W : (2 : ℝ) ≤ W := le_trans h2Q hQW1
  have h2qW : (2 : ℝ) ^ q ≤ W := le_trans h2 hQW1
  have hfW : (q.factorial : ℝ) ≤ W := le_trans hfQ hQW1
  have toW : ∀ {f : E → ℂ} {a : ℕ}, DB q f u (Q ^ a) 1 → a ≤ 4 * (m + 2) → DB q f u (W ^ 1) 1 := by
    intro f a h ha
    rw [pow_one]
    exact (h.powle h1Q ha zero_le_one).mono hQW zero_le_one le_rfl
  have P2 : (0 : ℝ) ≤ W ^ 2 := by positivity
  have tableLineDegreeTwo : (0 : ℝ) ≤ W ^ 16 := by positivity
  have one2 : (1 : ℝ) ≤ W ^ 2 := one_le_pow₀ h1W
  have up2 : ∀ {f : E → ℂ} {a : ℕ}, DB q f u (W ^ a) 1 → DB q f u (W ^ a) (W ^ 2) :=
    fun h => h.mono le_rfl zero_le_one one2
  have le216 : W ^ 2 ≤ W ^ 16 := pow_le_pow_right₀ h1W (by norm_num)

  have dcof := toW (cof_DB h1Q h2 hm ht hx hy) (by omega)
  have dcof1 := toW (first_cofactor_derivative_bound h1Q h2 hm ht hx hy) (by omega)
  have dcof0 := toW (leading_cofactor_derivative_bound (yy := yy) h2 hx) (by omega)
  have dsm := sm_DB hQ0 hx hy
  have dr1 := remainder_derivative_bound h1Q h2 hm ht hx hy
  have dtQ : DB q tt u (Q ^ 1) 1 := by simpa using ht
  have dDQ : DB q (fun _ : E => D) u (Q ^ 1) 1 := DB.const q D u (by simpa using hD) zero_le_one

  have dN : DB q (fun v => tt v ^ (m + 1) * sm m (xx v, yy v) - D - tt v * r1XY m (tt v) (xx v, yy v)) u
      (W ^ 1) 1 := by
    have a1 := ((tpow_DB h2 ht (m + 1)).mulQ dsm zero_le_one h2).powle h1Q
      (show 2 * (m + 1) + 1 + 1 ≤ 3 * m + 6 by omega) zero_le_one
    have a2 := dDQ.powle h1Q (show 1 ≤ 3 * m + 6 by omega) zero_le_one
    have a3 := (dtQ.mulQ dr1 zero_le_one h2).powle h1Q (show 1 + (3 * m + 4) + 1 ≤ 3 * m + 6 + 1 by omega)
      zero_le_one
    exact toW ((a1.subQ a2 zero_le_one h2Q).subQ a3 zero_le_one h2Q) (by omega)

  have dci : DB q (fun v => (cofXY m (tt v) (xx v, yy v))⁻¹) u (W ^ 3) (W ^ 2) := by
    have h := DB.inv dcof hc hcW (by simpa using h1W) h1W zero_le_one
    refine h.mono ?_ (by positivity) (by rw [pow_one, mul_one, sq])
    calc (q.factorial : ℝ) * (q.factorial * W) ≤ W * (W * W) := by gcongr
      _ = W ^ 3 := by ring
  have hc0 : cof0XY m (xx u, yy u) ≠ 0 := by
    simp only [cof0XY]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hp
  have hc0W : ‖cof0XY m (xx u, yy u)‖⁻¹ ≤ W := by
    simpa [cof0XY, norm_mul, norm_pow] using hpW
  have dc0i : DB q (fun v => (cof0XY m (xx v, yy v))⁻¹) u (W ^ 3) (W ^ 2) := by
    have h := DB.inv dcof0 hc0 hc0W (by simpa using h1W) h1W zero_le_one
    refine h.mono ?_ (by positivity) (by rw [pow_one, mul_one, sq])
    calc (q.factorial : ℝ) * (q.factorial * W) ≤ W * (W * W) := by gcongr
      _ = W ^ 3 := by ring

  have drho : DB q (fun v => rhoXY m D (tt v) (xx v, yy v)) u (W ^ 5) (W ^ 2) := by
    simp only [rhoXY_eq]
    exact (up2 dN).mulQ dci P2 h2qW

  have dg : DB q (fun v => gExt m D (tt v) (xx v, yy v)) u (W ^ 12) (W ^ 2) := by
    simp only [gExt]
    have a1 := ((tpow_DB h2 ht m).mulQ dsm zero_le_one h2).powle h1Q
      (show 2 * m + 1 + 1 ≤ 3 * m + 4 by omega) zero_le_one
    have a2 := toW (a1.subQ dr1 zero_le_one h2Q) (by omega)
    have a3 := a2.mulQ dcof0 zero_le_one h2qW
    have dDW : DB q (fun _ : E => D) u (W ^ 1) 1 :=
      DB.const q D u (by simpa using le_trans hD hQW1) zero_le_one
    have a4 := dDW.mulQ dcof1 zero_le_one h2qW
    have a5 := a3.addQ a4 zero_le_one h2W
    exact ((up2 a5).mulQ dci P2 h2qW).mulQ dc0i P2 h2qW

  have dpsi : DB q (fun v => psi β (gExt m D (tt v) (xx v, yy v))) u (W ^ 1) (W ^ 16) := by
    simp only [psi_eq]
    have dβ : DB q (fun _ : E => β) u (W ^ 1) (W ^ 2) :=
      DB.const q β u (by simpa using le_trans hβ hQW1) P2
    have a1 := dβ.mulQ dg P2 h2qW
    have a2 := DB.clm_one (Complex.reCLM : ℂ →L[ℝ] ℝ) (by simp) a1
    have a3 := DB.comp (DB_expI q _) a2 (one_le_pow₀ h1W) le_rfl P2
    refine a3.mono (by simpa using hfW) (by positivity) (le_of_eq (by ring))

  have dn : DB q (fun v => (((‖cofXY m (tt v) (xx v, yy v)‖ ^ 2)⁻¹ : ℝ) : ℂ)) u (W ^ 7) (W ^ 2) := by
    simp only [normSq_inv_cast]
    exact dci.mulQ (DB.clm_one (Complex.conjCLE : ℂ →L[ℝ] ℂ) (by simp) dci) P2 h2qW
  have dsc := dpsi.mulQ (dn.mono le_rfl P2 le216) tableLineDegreeTwo h2qW

  have dent : ∀ i j : Fin (m + 2), DB q (fun v => MXY m D (tt v) (xx v, yy v) i j) u (W ^ 5) (W ^ 2) := by
    intro i j
    have base : ∀ {f : E → ℂ}, DB q f u Q 1 → DB q f u (W ^ 5) (W ^ 2) := fun h =>
      h.mono (le_trans hQW1 (le_self_pow₀ h1W (by norm_num))) zero_le_one one2
    rcases MXY_cases m i j with h | h | h | ⟨k, h⟩ | ⟨e, h⟩
    · simp only [h]; exact DB.const q 0 u (by simp; positivity) P2
    · simp only [h]; exact base ht
    · simp only [h]; exact drho
    · simp only [h]; exact base (hx k)
    · simp only [h]; exact base (hy e)
  have dM : DB q (fun v => MXY m D (tt v) (xx v, yy v)) u (W ^ 7) (W ^ 2) := by
    have hcard : ((Fintype.card (Fin (m + 2)) : ℕ) : ℝ) ≤ W := by
      simp only [Fintype.card_fin]; push_cast; exact le_trans hm2 hQW1
    have r1 : ∀ i : Fin (m + 2), DB q (fun v => MXY m D (tt v) (xx v, yy v) i) u (W ^ 6) (W ^ 2) := by
      intro i
      refine (DB.pi (fun j => dent i j) P2).mono ?_ P2 le_rfl
      calc ((Fintype.card (Fin (m + 2)) : ℕ) : ℝ) * W ^ 5 ≤ W * W ^ 5 := by gcongr
        _ = W ^ 6 := by ring
    refine (DB.pi (fun i => r1 i) P2).mono ?_ P2 le_rfl
    calc ((Fintype.card (Fin (m + 2)) : ℕ) : ℝ) * W ^ 6 ≤ W * W ^ 6 := by gcongr
      _ = W ^ 7 := by ring
  have dΦ : DB q (fun v => Φ (MXY m D (tt v) (xx v, yy v))) u (q.factorial * K') (W ^ 16) := by
    have a := DB.comp (g := Φ) (f := fun v => MXY m D (tt v) (xx v, yy v)) hΦ dM (one_le_pow₀ h1W) le_rfl P2
    refine a.mono le_rfl (by positivity) ?_
    calc 1 * W ^ 7 * W ^ 2 = W ^ 9 := by ring
      _ ≤ W ^ 16 := pow_le_pow_right₀ h1W (by norm_num)
  have hK : 0 ≤ K' := hΦ.nonneg
  have fin := DB.smul dsc dΦ tableLineDegreeTwo
  refine fin.mono ?_ tableLineDegreeTwo le_rfl
  calc (2 : ℝ) ^ q * W ^ (1 + 7 + 1) * (q.factorial * K') ≤ W * W ^ (1 + 7 + 1) * (W * K') := by gcongr
    _ = K' * W ^ 11 := by ring

theorem core : ∃ a b : ℕ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m q : ℕ) (β D : ℂ) (tt : E → ℂ)
    (xx : E → Fin (m + 1) → ℂ) (yy : E → UT (m + 2) → ℂ) (u : E) (Q W : ℝ),
    2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial ≤ Q → DB q tt u Q 1 → (∀ k, DB q (fun v => xx v k) u Q 1) →
    (∀ e, DB q (fun v => yy v e) u Q 1) → ‖D‖ ≤ Q → ‖β‖ ≤ Q → Q ^ (4 * (m + 2)) ≤ W →
    cofXY m (tt u) (xx u, yy u) ≠ 0 → ‖cofXY m (tt u) (xx u, yy u)‖⁻¹ ≤ W →
    ∏ k, xx u k ≠ 0 → ‖∏ k, xx u k‖⁻¹ ≤ W →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Φ : Mat (m + 1 + 1) → V) (K' : ℝ),
      DB q Φ (MXY m D (tt u) (xx u, yy u)) K' 1 →
      DB q (fun v => ampE β m Φ D (tt v) (xx v, yy v)) u (K' * W ^ a) (W ^ b) :=
  ⟨11, 16, fun E _ _ m q β D tt xx yy u Q W h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 V _ _ Φ K' h12 =>
    card_range_inf_torsion_le_index_pow E m q β D tt xx yy u Q W h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 V Φ K' h12⟩

end

end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts

namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology

noncomputable section

theorem K_nonneg {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {m k : ℕ} {Kc : Set ℂ} {A K : ℝ}
    {Φ : Mat (m + 1 + 1) → V} (h : DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ)
    {D : ℂ} (hD : D ∈ Kc) (hD0 : D ≠ 0) : 0 ≤ K := by
  set d : ℂ := (wMat (m + 1)).det * D with hd
  have hd0 : d ≠ 0 := mul_ne_zero (G2.det_wMat_ne_zero _) hD0
  let Z : Mat (m + 1 + 1) := Matrix.diagonal (Function.update (fun _ => (1 : ℂ)) 0 d)
  have hdet : detM Z = d := by
    show Matrix.det (Matrix.of Z) = d
    have : (Matrix.of Z : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ) =
        Matrix.diagonal (Function.update (fun _ => (1 : ℂ)) 0 d) := rfl
    rw [this, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  have hmem : detM Z ∈ detSet (m + 1) Kc := by
    rw [hdet]; exact ⟨D, hD, rfl⟩
  have h0 := (h Z hmem).2 0 (Nat.zero_le _)
  have hZ : 0 < ‖Z‖ := by
    have h1 : ‖Z 0 0‖ ≤ ‖Z‖ := G7.norm_entry_le Z 0 0
    have h2 : Z 0 0 = d := by simp [Z]
    rw [h2] at h1
    exact lt_of_lt_of_le (norm_pos_iff.2 hd0) h1
  have hmin : 0 < min 1 (‖Z‖ ^ (-A)) := lt_min one_pos (Real.rpow_pos_of_pos hZ _)
  by_contra hK
  have hK' : K < 0 := not_le.1 hK
  have : K * min 1 (‖Z‖ ^ (-A)) < 0 := mul_neg_of_neg_of_pos hK' hmin
  have h3 := le_trans (norm_nonneg _) h0
  exact absurd h3 (not_le.2 this)

theorem supp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ) (ε : ℝ)
    (Φ : Mat (m + 1 + 1) → V) (D t : ℂ) (p : XY m) (ht : t ≠ 0) (h : ampIn β m ε Φ D t p ≠ 0) :
    cofXY m t p ≠ 0 ∧ ‖MXY m D t p‖ < 2 * ‖t‖ ^ (-ε) := by
  have hτ : 0 < ‖t‖ ^ (-ε) := Real.rpow_pos_of_pos (norm_pos_iff.2 ht) _
  constructor
  · intro hc
    apply h
    simp [ampIn, amp, hc]
  · by_contra hM
    apply h
    have := ((matrix_cutoff_spec (m + 1 + 1)).1 (‖t‖ ^ (-ε)) (MXY m D t p) hτ).2.2.2 (not_lt.1 hM)
    simp [ampIn, amp, cutPhi, this]

theorem continuous_red (m : ℕ) (y : UT (m + 2) → ℂ) :
    Continuous (fun x : Fin (m + 1) → ℂ => redOf m (x, y)) := by
  have h : ∀ i j, Continuous (fun x : Fin (m + 1) → ℂ => triXY x y i j) := by
    intro i j
    rcases tri_cases m i j with h | ⟨k, h⟩ | ⟨e, h⟩
    · simp only [h]; exact continuous_const
    · simp only [h]; exact continuous_apply k
    · simp only [h]; exact continuous_const
  unfold redOf
  exact Continuous.prodMk (h _ _) (Continuous.prodMk (continuous_pi fun k => h _ _)
    (Continuous.prodMk (continuous_pi fun q => h _ _) (continuous_pi fun i => h _ _)))

theorem continuous_cofXY (m : ℕ) (t : ℂ) (y : UT (m + 2) → ℂ) :
    Continuous (fun x : Fin (m + 1) → ℂ => cofXY m t (x, y)) := by
  have h := (G7.continuous_cof m t).comp
    ((continuous_snd.comp (continuous_snd.comp (continuous_red m y))))
  exact h

theorem exists_derivBound_nonstationaryCutoff (m q : ℕ) (δ : ℝ) (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : ℂ) (x : Fin (m + 1) → ℂ),
    DB q (fun x : Fin (m + 1) → ℂ => ((farCut m δ D x : ℝ) : ℂ)) x C 1 := by
  obtain ⟨C, hC⟩ := (critical_cutoff_spec m δ hδ).2.1 q
  have hDB : ∀ (z : ℂ) (x : Fin (m + 1) → ℂ), DB q (critCut (n := m + 1) δ z) x C 1 := by
    intro z x
    refine ⟨(hC z).1.contDiffAt, fun j hj => ?_⟩
    simpa using (hC z).2 j hj x
  have hC0 : 0 ≤ C := (hDB 0 0).nonneg
  refine ⟨1 + ((m : ℝ) + 2) * C, by positivity, fun D x => ?_⟩
  have hsum := DB.sum (q := q) (u := x) (f := fun z => critCut (n := m + 1) δ z) (S := fun _ => C) (P := 1)
    (rootSet (m + 2) ((-1) ^ (m + 3) * D)) zero_le_one (fun z _ => hDB z x)
  have hcard : ((rootSet (m + 2) ((-1) ^ (m + 3) * D)).card : ℝ) ≤ (m : ℝ) + 2 := by
    have h1 : (rootSet (m + 2) ((-1) ^ (m + 3) * D)).card ≤ m + 2 :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
    exact_mod_cast h1
  have hone : DB q (fun _ : Fin (m + 1) → ℂ => (1 : ℝ)) x 1 1 := DB.const q 1 x (by simp) zero_le_one
  have hsub := (hone.sub hsum).mono (S' := 1 + ((m : ℝ) + 2) * C) (P' := 1) (by
    simp only [Finset.sum_const, nsmul_eq_mul]
    have := mul_le_mul_of_nonneg_right hcard hC0
    linarith) zero_le_one le_rfl
  have := DB.clm_one Complex.ofRealCLM (by simp) hsub
  exact this

theorem le_norm_sub_of_nonstationaryCutoff_ne_zero (m : ℕ) (Kc : Set ℂ) (δ : ℝ) (hδ : SmallDelta m Kc δ) (D : ℂ) (hD : D ∈ Kc)
    (x : Fin (m + 1) → ℂ) (h : farCut m δ D x ≠ 0) (z : ℂ) (hz : z ^ (m + 2) = (-1) ^ (m + 3) * D) :
    δ ≤ ‖x - fun _ => z‖ := by
  by_contra hlt
  have hlt' := not_le.1 hlt
  apply h
  have hspec := critical_cutoff_spec m δ hδ.1
  have h1 : critCut δ z x = 1 := (hspec.1 z x).2.2.1 hlt'.le
  have hzmem : z ∈ rootSet (m + 2) ((-1) ^ (m + 3) * D) :=
    ((root_set_characterization (m + 2) _ (by omega)).1 z).2 hz
  have hsum : ∑ z' ∈ rootSet (m + 2) ((-1) ^ (m + 3) * D), critCut δ z' x = critCut δ z x := by
    refine Finset.sum_eq_single z (fun z' hz' hne => ?_) (fun hn => absurd hzmem hn)
    have hz'' := ((root_set_characterization (m + 2) _ (by omega)).1 z').1 hz'
    exact hspec.2.2 z z' x (by rw [hz, hz'']) (Ne.symm hne) (hδ.2 D hD z hz) (by rw [h1]; exact one_ne_zero)
  unfold farCut
  rw [hsum, h1, sub_self]

theorem arith (a b q j m : ℕ) (hj : j ≤ q) (cW τ : ℝ) (hcW : 1 ≤ cW) (hτ : 1 ≤ τ) :
    (cW * τ ^ (4 * (m + 2))) ^ a * ((cW * τ ^ (4 * (m + 2))) ^ b) ^ j ≤
      cW ^ (a + b * q) * τ ^ (4 * (a + b) * (m + 2) * (j + 1)) := by
  have e : (cW * τ ^ (4 * (m + 2))) ^ a * ((cW * τ ^ (4 * (m + 2))) ^ b) ^ j =
      cW ^ (a + b * j) * τ ^ (4 * (m + 2) * (a + b * j)) := by
    rw [← pow_mul, ← pow_add, mul_pow, ← pow_mul]
  rw [e]
  have h1 : a + b * j ≤ a + b * q := Nat.add_le_add_left (Nat.mul_le_mul_left b hj) a
  have h2 : 4 * (m + 2) * (a + b * j) ≤ 4 * (a + b) * (m + 2) * (j + 1) := by
    calc 4 * (m + 2) * (a + b * j) ≤ 4 * (m + 2) * ((a + b) * (j + 1)) :=
          Nat.mul_le_mul_left _ (by nlinarith [Nat.zero_le (a * j), Nat.zero_le b])
      _ = 4 * (a + b) * (m + 2) * (j + 1) := by ring
  exact mul_le_mul (pow_le_pow_right₀ hcW h1) (pow_le_pow_right₀ hτ h2) (by positivity) (by positivity)

theorem proj_norm_le (n : ℕ) (k : Fin n) : ‖(ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℝ] ℂ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simpa using norm_le_pi_norm v k

end

end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far Matrix Filter Topology

theorem amplitude_bound_far : Formalism.FourierDecayAlt.G.AmpBoundFar := by
  obtain ⟨a, b, hcore⟩ := core
  refine ⟨4 * (a + b), ?_⟩
  intro m β Kc hKc h0 δ ε hδ hε hε' q
  obtain ⟨t₁, c₁, ht₁, hc₁, hCof⟩ := cofactor_lower_bound_radius m Kc hKc h0 2 two_pos
  obtain ⟨t₂, c₂, ht₂, hc₂, hProd⟩ := product_lower_bound m Kc hKc h0 2 two_pos
  obtain ⟨Cc, hCc⟩ := cutoff_phase_bound (m + 1 + 1) q
  obtain ⟨Cf, hCf0, hCf⟩ := exists_derivBound_nonstationaryCutoff m q δ hδ.1
  obtain ⟨RD, hRD⟩ := hKc.isBounded.exists_norm_le
  obtain ⟨cQ, hcQ⟩ : ∃ cQ : ℝ, cQ = 2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial + |RD| + ‖β‖ + 2 := ⟨_, rfl⟩
  obtain ⟨cW, hcW⟩ : ∃ cW : ℝ, cW = cQ ^ (4 * (m + 2)) + c₁⁻¹ + c₂⁻¹ := ⟨_, rfl⟩
  have hpos1 : (0 : ℝ) ≤ 2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial := by positivity
  have hcQ2 : 2 ≤ cQ := by
    rw [hcQ]; have := abs_nonneg RD; have := norm_nonneg β; linarith
  have hcQ1 : 1 ≤ cQ := by linarith
  have hcW1 : 1 ≤ cW := by
    rw [hcW]
    have h1 : 1 ≤ cQ ^ (4 * (m + 2)) := one_le_pow₀ hcQ1
    have h2 : 0 < c₁⁻¹ := inv_pos.2 hc₁
    have h3 : 0 < c₂⁻¹ := inv_pos.2 hc₂
    linarith
  refine ⟨2 ^ q * Cf * (max Cc 0) * cW ^ (a + b * q), min (min t₁ t₂) 1, c₂,
    lt_min (lt_min ht₁ ht₂) one_pos, hc₂, ?_⟩
  intro V _ _ _ Φ A K k hA hqk hΦ t D ht htt hD y
  have hD0 : D ≠ 0 := fun h => h0 (h ▸ hD)
  have hK : 0 ≤ K := K_nonneg hΦ hD hD0
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
  have ht1 : ‖t‖ ≤ 1 := htt.trans (min_le_right _ _)
  have htt₁ : ‖t‖ ≤ t₁ := htt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have htt₂ : ‖t‖ ≤ t₂ := htt.trans ((min_le_left _ _).trans (min_le_right _ _))
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = ‖t‖ ^ (-ε) := ⟨_, rfl⟩
  have hτ1 : 1 ≤ τ := by
    rw [hτdef]; exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos htn ht1 (by linarith)
  have hτ0 : 0 < τ := by linarith
  have hτinv : ‖t‖ ^ ε = τ⁻¹ := by rw [hτdef, Real.rpow_neg htn.le, inv_inv]
  rw [← hτdef]

  have key : ∀ x : Fin (m + 1) → ℂ, ampIn β m ε Φ D t (x, y) ≠ 0 →
      ‖y‖ ≤ 2 * τ ∧ (∀ k, ‖x k‖ ≤ 2 * τ) ∧ c₁ * τ⁻¹ ≤ ‖cofXY m t (x, y)‖ ∧ c₂ * τ⁻¹ ≤ ‖∏ k, x k‖ ∧
        ∀ k, c₂ * ‖t‖ ^ (((m : ℝ) + 2) * ε) ≤ ‖x k‖ := by
    intro x hx
    obtain ⟨hc, hM⟩ := supp β m ε Φ D t (x, y) ht hx
    rw [← hτdef] at hM
    have h2τ : (0 : ℝ) ≤ 2 * τ := by positivity
    have hxk : ∀ k, ‖(x, y).1 k‖ ≤ 2 * τ := fun k => (x_le_MXY m D t (x, y) k).trans hM.le
    have hy : ‖(x, y).2‖ ≤ 2 * τ := (y_le_MXY m D t (x, y)).trans hM.le
    have hρ : ‖rhoXY m D t (x, y)‖ ≤ 2 * τ := (rho_le_MXY m D t (x, y)).trans hM.le
    have hxo : ∀ k, xOf (Xm m (x, y)) (Bm m (x, y)) k = x k := (split_xy_matrix m t 0 (x, y)).1
    have hA1 := hCof ε hε hε' D hD t ht htt₁ (Xm m (x, y)) (Bm m (x, y)) (rhoXY m D t (x, y)) (rm m (x, y))
      (sm m (x, y)) (Xm_strict m _) (by rw [← hτdef]; exact fun i j => Xm_le m _ h2τ hxk hy i j)
      (by rw [← hτdef]; exact fun i => Bm_le m _ h2τ hxk hy i) (by rw [← hτdef]; exact hρ)
      (by rw [← hτdef]; exact fun k => rm_le m _ h2τ hxk hy k) (by rw [← hτdef]; exact sm_le m _ h2τ hxk hy)
      (corner_XY m D t (x, y) hc)
    have hA2 := hProd ε hε hε' D hD t ht htt₂ (Xm m (x, y)) (Bm m (x, y)) (rhoXY m D t (x, y)) (rm m (x, y))
      (sm m (x, y)) (Xm_strict m _) (by rw [← hτdef]; exact fun i j => Xm_le m _ h2τ hxk hy i j)
      (by rw [← hτdef]; exact fun i => Bm_le m _ h2τ hxk hy i) (by rw [← hτdef]; exact hρ)
      (by rw [← hτdef]; exact fun k => rm_le m _ h2τ hxk hy k) (by rw [← hτdef]; exact sm_le m _ h2τ hxk hy)
      (corner_XY m D t (x, y) hc)
    simp only [hxo] at hA2
    rw [hτinv] at hA1 hA2
    exact ⟨hy, hxk, hA1, hA2.1, hA2.2⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = cQ * τ := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = cW * τ ^ (4 * (m + 2)) := ⟨_, rfl⟩
  have hτp1 : 1 ≤ τ ^ (4 * (m + 2)) := one_le_pow₀ hτ1
  have hW1 : 1 ≤ W := by
    rw [hW]; exact one_le_mul_of_one_le_of_one_le hcW1 hτp1
  have hcQQ : cQ ≤ Q := by rw [hQ]; exact le_mul_of_one_le_right (by linarith) hτ1
  have h2Q : 2 * τ ≤ Q := by rw [hQ]; exact mul_le_mul_of_nonneg_right hcQ2 hτ0.le
  have hinvW : ∀ c v : ℝ, 0 < c → c⁻¹ ≤ cW → c * τ⁻¹ ≤ v → v⁻¹ ≤ W := by
    intro c v hc hcc hv
    have hp : 0 < c * τ⁻¹ := mul_pos hc (inv_pos.2 hτ0)
    calc v⁻¹ ≤ (c * τ⁻¹)⁻¹ := inv_anti₀ hp hv
      _ = c⁻¹ * τ := by rw [mul_inv, inv_inv]
      _ ≤ cW * τ ^ (4 * (m + 2)) :=
          mul_le_mul hcc (le_self_pow₀ hτ1 (by omega)) hτ0.le (by linarith)
      _ = W := hW.symm

  obtain ⟨S, hS⟩ : ∃ S : Set (Fin (m + 1) → ℂ), S = {x | ‖y‖ ≤ 2 * τ ∧ (∀ k, ‖x k‖ ≤ 2 * τ) ∧
      c₁ * τ⁻¹ ≤ ‖cofXY m t (x, y)‖ ∧ c₂ * τ⁻¹ ≤ ‖∏ k, x k‖} := ⟨_, rfl⟩
  have hprodc : Continuous fun v : Fin (m + 1) → ℂ => ∏ k, v k :=
    continuous_finsetProd _ (fun k _ => continuous_apply k)
  have hSc : IsClosed S := by
    rw [hS]
    refine IsClosed.and isClosed_const (IsClosed.and ?_ (IsClosed.and ?_ ?_))
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun k => isClosed_le (continuous_apply k).norm continuous_const
    · exact isClosed_le continuous_const (continuous_cofXY m t y).norm
    · exact isClosed_le continuous_const hprodc.norm
  have hDBF : ∀ x : Fin (m + 1) → ℂ,
      DB q (fun x : Fin (m + 1) → ℂ => ((farCut m δ D x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y)) x
        (2 ^ q * Cf * (max Cc 0 * K * W ^ a)) (W ^ b) := by
    intro x
    by_cases hx : x ∈ S
    · rw [hS] at hx
      obtain ⟨hy, hxk, hcofl, hprodl⟩ := hx
      have hcof : cofXY m t (x, y) ≠ 0 := by
        intro h
        rw [h, norm_zero] at hcofl
        exact absurd hcofl (not_le.2 (mul_pos hc₁ (inv_pos.2 hτ0)))
      have hprod : ∏ k, x k ≠ 0 := by
        intro h
        rw [h, norm_zero] at hprodl
        exact absurd hprodl (not_le.2 (mul_pos hc₂ (inv_pos.2 hτ0)))
      have hΦq : DerivBound q (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ := fun Z hZ =>
        ⟨((hΦ Z hZ).1).of_le (by exact_mod_cast hqk), fun j hj => (hΦ Z hZ).2 j (hj.trans hqk)⟩
      have h1 := (hCc V Φ (detSet (m + 1) Kc) _ τ hτ1 hΦq).1
      have hdet : detM (MXY m D t (x, y)) ∈ detSet (m + 1) Kc :=
        ⟨D, hD, (det_matrix_xy m D t (x, y) hcof).symm⟩
      have hΦ' : DB q (cutPhi τ Φ) (MXY m D t (x, y)) (max Cc 0 * K) 1 := by
        refine (DB_of_DerivBound h1 le_rfl hdet).mono ?_ zero_le_one le_rfl
        have hb0 : 0 ≤ K * min 1 (‖MXY m D t (x, y)‖ ^ (-A)) :=
          mul_nonneg hK (le_min zero_le_one (Real.rpow_nonneg (norm_nonneg _) _))
        have hb1 : K * min 1 (‖MXY m D t (x, y)‖ ^ (-A)) ≤ K := mul_le_of_le_one_right hK (min_le_left _ _)
        calc Cc * (K * min 1 (‖MXY m D t (x, y)‖ ^ (-A)))
            ≤ max Cc 0 * (K * min 1 (‖MXY m D t (x, y)‖ ^ (-A))) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hb0
          _ ≤ max Cc 0 * K := mul_le_mul_of_nonneg_left hb1 (le_max_right _ _)
      have hDBx : ∀ k, DB q (fun v : Fin (m + 1) → ℂ => v k) x Q 1 := by
        intro k
        have := DB.affine q (ContinuousLinearMap.proj k : (Fin (m + 1) → ℂ) →L[ℝ] ℂ) 0 x (S := Q)
          (by simpa using (hxk k).trans h2Q) ((proj_norm_le _ k).trans (hcQ1.trans hcQQ))
        simpa using this
      have hDBcore := hcore (Fin (m + 1) → ℂ) m q β D (fun _ => t) (fun v => v) (fun _ => y) x Q W
        (le_trans (by rw [hcQ]; have := abs_nonneg RD; have := norm_nonneg β; linarith) hcQQ)
        (DB.const q t x (ht1.trans (hcQ1.trans hcQQ)) zero_le_one) hDBx
        (fun e => DB.const q (y e) x (((norm_le_pi_norm y e).trans hy).trans h2Q) zero_le_one)
        (le_trans (by rw [hcQ]; have := hRD D hD; have := le_abs_self RD; have := norm_nonneg β; linarith) hcQQ)
        (le_trans (by rw [hcQ]; have := abs_nonneg RD; linarith) hcQQ)
        (by
          rw [hQ, hW, mul_pow]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hcW]
          have h2 : 0 < c₁⁻¹ := inv_pos.2 hc₁
          have h3 : 0 < c₂⁻¹ := inv_pos.2 hc₂
          linarith)
        hcof
        (hinvW c₁ _ hc₁ (by
          rw [hcW]
          have h1 : 0 ≤ cQ ^ (4 * (m + 2)) := by positivity
          have h3 : 0 < c₂⁻¹ := inv_pos.2 hc₂
          linarith) hcofl)
        hprod
        (hinvW c₂ _ hc₂ (by
          rw [hcW]
          have h1 : 0 ≤ cQ ^ (4 * (m + 2)) := by positivity
          have h3 : 0 < c₁⁻¹ := inv_pos.2 hc₁
          linarith) hprodl)
        V (cutPhi τ Φ) (max Cc 0 * K) hΦ'
      have hev : (fun v : Fin (m + 1) → ℂ => ampIn β m ε Φ D t (v, y)) =ᶠ[𝓝 x]
          fun v => ampE β m (cutPhi τ Φ) D t (v, y) := by
        filter_upwards [hprodc.continuousAt.eventually_ne hprod] with v hv
        rw [hτdef]
        exact amp_eq_ampE β m (cutPhi (‖t‖ ^ (-ε)) Φ) D t (v, y) ht hv
      have hAm := hDBcore.congr hev
      have hFar := (hCf D x).mono le_rfl zero_le_one (one_le_pow₀ hW1 : 1 ≤ W ^ b)
      exact hFar.smul hAm (by positivity)
    · refine DB.of_eventually_zero ?_ (by positivity) (by positivity)
      filter_upwards [hSc.isOpen_compl.mem_nhds hx] with x' hx'
      by_contra hne
      apply hx'
      have hne' : ampIn β m ε Φ D t (x', y) ≠ 0 := fun h => hne (by rw [h, smul_zero])
      obtain ⟨h1, h2, h3, h4, _⟩ := key x' hne'
      rw [hS]
      exact ⟨h1, h2, h3, h4⟩
  refine ⟨contDiff_iff_contDiffAt.2 fun x => (hDBF x).1, ?_, ?_⟩
  · intro x hx
    have hne' : ampIn β m ε Φ D t (x, y) ≠ 0 := fun h => hx (by rw [h, smul_zero])
    have hfar : farCut m δ D x ≠ 0 := fun h => hx (by rw [h]; simp)
    obtain ⟨h1, h2, _, _, h5⟩ := key x hne'
    exact ⟨h1, fun k => ⟨h2 k, h5 k⟩, fun z hz => le_norm_sub_of_nonstationaryCutoff_ne_zero m Kc δ hδ D hD x hfar z hz⟩
  · intro j hj x
    have hb := (hDBF x).2 j hj
    have hpow : τ ^ (4 * (a + b) * (m + 2) * (j + 1)) =
        ‖t‖ ^ (-(ε * (((4 * (a + b) : ℕ) : ℝ) * ((m : ℝ) + 2) * ((j : ℝ) + 1)))) := by
      rw [hτdef, ← Real.rpow_natCast, ← Real.rpow_mul htn.le]
      congr 1
      push_cast
      ring
    calc _ ≤ 2 ^ q * Cf * (max Cc 0 * K * W ^ a) * (W ^ b) ^ j := hb
      _ = (2 ^ q * Cf * max Cc 0 * K) * (W ^ a * (W ^ b) ^ j) := by ring
      _ ≤ (2 ^ q * Cf * max Cc 0 * K) * (cW ^ (a + b * q) * τ ^ (4 * (a + b) * (m + 2) * (j + 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hW]
          exact arith a b q j m hj cW τ hcW1 hτ1
      _ = _ := by rw [hpow]; ring

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology

theorem derivBound_mono {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {s k q : ℕ} {Kd : Set ℂ}
    {bd : Mat s → ℝ} {Φ : Mat s → V} (h : DerivBound k Kd bd Φ) (hq : q ≤ k) : DerivBound q Kd bd Φ :=
  fun Z hZ => ⟨(h Z hZ).1.of_le (by exact_mod_cast hq), fun j hj => (h Z hZ).2 j (hj.trans hq)⟩

theorem min_le_max {A Y M : ℝ} (hA : 0 ≤ A) (hYM : Y ≤ M) :
    min 1 (M ^ (-A)) ≤ (max 1 Y) ^ (-A) := by
  by_cases h : Y ≤ 1
  · rw [max_eq_left h, Real.one_rpow]
    exact min_le_left _ _
  · have h1 : 1 < Y := not_le.1 h
    rw [max_eq_right h1.le]
    exact (min_le_right _ _).trans
      (Real.rpow_le_rpow_of_nonpos (by linarith) hYM (by linarith))

theorem K_nonneg {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {m k : ℕ} {Kc : Set ℂ} {A K : ℝ}
    {Φ : Mat (m + 1 + 1) → V}
    (hΦ : DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ) {D z : ℂ} (hD : D ∈ Kc)
    (hz : z ≠ 0) : 0 ≤ K := by
  have hc : cofXY m 0 (fun _ => z, (0 : UT (m + 2) → ℂ)) ≠ 0 := by
    intro h
    have h2 := cofXY_zero m z (0 : UT (m + 2) → ℂ)
    rw [h, norm_zero] at h2
    exact (pow_pos (norm_pos_iff.2 hz) (m + 1)).ne h2
  have hdet : detM (MXY m D 0 (fun _ => z, (0 : UT (m + 2) → ℂ))) ∈ detSet (m + 1) Kc :=
    ⟨D, hD, (det_matrix_xy m D 0 _ hc).symm⟩
  have hM : 0 < ‖MXY m D 0 (fun _ => z, (0 : UT (m + 2) → ℂ))‖ :=
    lt_of_lt_of_le (norm_pos_iff.2 hz) (x_le_MXY m D 0 (fun _ => z, (0 : UT (m + 2) → ℂ)) 0)
  have h := (hΦ _ hdet).2 0 (Nat.zero_le _)
  have h2 : 0 ≤ K * min 1 (‖MXY m D 0 (fun _ => z, (0 : UT (m + 2) → ℂ))‖ ^ (-A)) :=
    (norm_nonneg _).trans h
  have h3 : 0 < min 1 (‖MXY m D 0 (fun _ => z, (0 : UT (m + 2) → ℂ))‖ ^ (-A)) :=
    lt_min one_pos (Real.rpow_pos_of_pos hM _)
  exact nonneg_of_mul_nonneg_left h2 h3

theorem ampIn_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ) (ε : ℝ)
    (Φ : Mat (m + 1 + 1) → V) (D t : ℂ) (p : XY m) (ht : 0 < ‖t‖ ^ (-ε)) (h : 2 * ‖t‖ ^ (-ε) ≤ ‖p.2‖) :
    ampIn β m ε Φ D t p = 0 := by
  have h2 : 2 * ‖t‖ ^ (-ε) ≤ ‖MXY m D t p‖ := h.trans (y_le_MXY m D t p)
  have h3 := ((matrix_cutoff_spec (m + 1 + 1)).1 (‖t‖ ^ (-ε)) (MXY m D t p) ht).2.2.2 h2
  simp [ampIn, amp, cutPhi, h3]

theorem DB_proj (q n : ℕ) (k : Fin n) (x : Fin n → ℂ) {S : ℝ} (h0 : ‖x k‖ ≤ S) (h1 : 1 ≤ S) :
    DB q (fun v : Fin n → ℂ => v k) x S 1 := by
  have hL : ‖(ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℝ] ℂ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      simpa using norm_le_pi_norm v k
  have h := DB.affine q (ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℝ] ℂ) 0 x (S := S) (by simpa using h0)
    (hL.trans h1)
  simpa using h

theorem cof_lower (m : ℕ) {δ c ε : ℝ} (hδ : 0 < δ) (hc : 2 ≤ c) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / (2 * ((m : ℝ) + 2))) {t : ℂ} (ht0 : t ≠ 0) (ht1 : ‖t‖ ≤ 1)
    (hts : ((m : ℝ) + 1) ^ (m + 1) * c ^ m * Real.sqrt ‖t‖ ≤ δ ^ (m + 1) / 2)
    (p : XY m) (hx : ∀ k, ‖p.1 k‖ ≤ c) (hxl : ∀ k, δ ≤ ‖p.1 k‖) (hy : ‖p.2‖ ≤ 2 * ‖t‖ ^ (-ε)) :
    δ ^ (m + 1) ≤ ‖∏ k, p.1 k‖ ∧ δ ^ (m + 1) / 2 ≤ ‖cofXY m t p‖ := by
  have htp : 0 < ‖t‖ := norm_pos_iff.2 ht0
  have hT : 1 ≤ ‖t‖ ^ (-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos htp ht1 (by linarith)
  set T := ‖t‖ ^ (-ε) with hTdef
  have hprod : δ ^ (m + 1) ≤ ‖∏ k, p.1 k‖ := by
    rw [norm_prod]
    calc δ ^ (m + 1) = ∏ _k : Fin (m + 1), δ := by simp
      _ ≤ ∏ k, ‖p.1 k‖ := Finset.prod_le_prod (fun _ _ => hδ.le) fun k _ => hxl k
  refine ⟨hprod, ?_⟩
  have hR : 1 ≤ c * T := by nlinarith
  have h1 := first_cofactor_norm_le m t p hR ht1 (fun k => (hx k).trans (by nlinarith)) (hy.trans (by nlinarith))
  have h2 : T ^ m * ‖t‖ ≤ Real.sqrt ‖t‖ := by
    refine le_trans ?_ (G6.rpow_bound m htp ht1 hε)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT (by omega)) htp.le
  have h3 : ‖t * cof1XY m t p‖ ≤ δ ^ (m + 1) / 2 := by
    rw [norm_mul]
    calc ‖t‖ * ‖cof1XY m t p‖ ≤ ‖t‖ * (((m : ℝ) + 1) ^ (m + 1) * (c * T) ^ m) :=
          mul_le_mul_of_nonneg_left h1 htp.le
      _ = ((m : ℝ) + 1) ^ (m + 1) * c ^ m * (T ^ m * ‖t‖) := by rw [mul_pow]; ring
      _ ≤ ((m : ℝ) + 1) ^ (m + 1) * c ^ m * Real.sqrt ‖t‖ :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ _ := hts
  have h4 : ‖cof0XY m p‖ = ‖∏ k, p.1 k‖ := by simp [cof0XY, norm_pow]
  have h5 : cof0XY m p = cofXY m t p - t * cof1XY m t p := by rw [cofXY_eq]; ring
  have h6 : ‖cof0XY m p‖ ≤ ‖cofXY m t p‖ + ‖t * cof1XY m t p‖ := by rw [h5]; exact norm_sub_le _ _
  linarith

theorem main : AmpBoundCrit := by
  obtain ⟨a, b, hcore⟩ := core
  refine ⟨4 * (a + 2 * b), ?_⟩
  intro m β Kc hKc h0 δ ε hδ hε0 hε
  obtain ⟨hδ0, hδz⟩ := hδ
  obtain ⟨RD, hRD⟩ : ∃ R, ∀ D ∈ Kc, ‖D‖ ≤ R := hKc.isBounded.exists_norm_le
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = 2 * (m + 1) + 2 := ⟨_, rfl⟩
  rw [← hq]
  obtain ⟨Ccut, hCcut⟩ := cutoff_phase_bound (m + 1 + 1) q
  obtain ⟨hcr1, hcr2, -⟩ := critical_cutoff_spec m δ hδ0
  obtain ⟨Ccrit, hCcrit⟩ := hcr2 q
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = max RD 1 + 2 * δ + 2 := ⟨_, rfl⟩
  have hc2 : 2 ≤ c := by
    have := le_max_right RD 1
    linarith
  have hcRD : RD ≤ c := by
    have := le_max_left RD 1
    linarith
  obtain ⟨cQ, hcQdef⟩ : ∃ cQ : ℝ, cQ = max (2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial) (max c ‖β‖) := ⟨_, rfl⟩
  have hcQ1 : 2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial ≤ cQ := hcQdef ▸ le_max_left _ _
  have hcQ2 : c ≤ cQ := hcQdef ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hcQ3 : ‖β‖ ≤ cQ := hcQdef ▸ (le_max_right _ _).trans (le_max_right _ _)
  have hcQ0 : 1 ≤ cQ := by linarith
  obtain ⟨cW, hcWdef⟩ : ∃ cW : ℝ, cW = max (cQ ^ (4 * (m + 2))) (2 / δ ^ (m + 1)) := ⟨_, rfl⟩
  have hcW1 : cQ ^ (4 * (m + 2)) ≤ cW := hcWdef ▸ le_max_left _ _
  have hcW2 : 2 / δ ^ (m + 1) ≤ cW := hcWdef ▸ le_max_right _ _
  have hcW0 : 1 ≤ cW := (one_le_pow₀ hcQ0).trans hcW1
  have hδp : 0 < δ ^ (m + 1) := pow_pos hδ0 _
  have hden : 0 < ((m : ℝ) + 1) ^ (m + 1) * c ^ m := by positivity
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = δ ^ (m + 1) / (2 * (((m : ℝ) + 1) ^ (m + 1) * c ^ m)) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκdef]; positivity
  refine ⟨2 ^ q * |Ccrit| * |Ccut| * cW ^ (a + b * q), min 1 (κ ^ 2), lt_min one_pos (by positivity), ?_⟩
  intro V _ _ _ Φ A K k hA hk hΦ t D z ht0 ht hD hz y
  have ht1 : ‖t‖ ≤ 1 := ht.trans (min_le_left _ _)
  have htp : 0 < ‖t‖ := norm_pos_iff.2 ht0
  have hts : ((m : ℝ) + 1) ^ (m + 1) * c ^ m * Real.sqrt ‖t‖ ≤ δ ^ (m + 1) / 2 := by
    have h1 : Real.sqrt ‖t‖ ≤ κ := by
      rw [← Real.sqrt_sq hκ0.le]
      exact Real.sqrt_le_sqrt (ht.trans (min_le_right _ _))
    calc ((m : ℝ) + 1) ^ (m + 1) * c ^ m * Real.sqrt ‖t‖ ≤ ((m : ℝ) + 1) ^ (m + 1) * c ^ m * κ :=
          mul_le_mul_of_nonneg_left h1 hden.le
      _ = δ ^ (m + 1) / 2 := by rw [hκdef]; field_simp
  have hzl : 100 * ((m : ℝ) + 2) * δ ≤ ‖z‖ := hδz D hD z hz
  have hz200 : 200 * δ ≤ ‖z‖ := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hzne : z ≠ 0 := norm_pos_iff.1 (by linarith)
  have hzR : ‖z‖ ≤ max RD 1 := by
    by_contra hcon
    have h1 : max RD 1 < ‖z‖ := not_le.1 hcon
    have h2 : 1 ≤ ‖z‖ := (le_max_right RD 1).trans h1.le
    have h3 : ‖z‖ ≤ ‖z‖ ^ (m + 2) := le_self_pow₀ h2 (by omega)
    have h4 : ‖z‖ ^ (m + 2) = ‖D‖ := by
      rw [← norm_pow, hz, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h5 := hRD D hD
    have h6 := le_max_left RD 1
    linarith
  have hK : 0 ≤ K := K_nonneg hΦ hD hzne
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = ‖t‖ ^ (-ε) := ⟨_, rfl⟩
  have hτ : 1 ≤ τ := hτdef ▸ Real.one_le_rpow_of_pos_of_le_one_of_nonpos htp ht1 (by linarith)
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = 1 + ‖y‖ := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := by rw [hYdef]; linarith [norm_nonneg y]
  obtain ⟨mx, hmxdef⟩ : ∃ mx : ℝ, mx = (max 1 ‖y‖) ^ (-A) := ⟨_, rfl⟩
  have hmx0 : 0 ≤ mx := by rw [hmxdef]; positivity
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cQ * Y := ⟨_, rfl⟩
  have hQle : ∀ r : ℝ, r ≤ cQ → r ≤ Q := fun r hr => by
    rw [hQdef]; exact hr.trans (le_mul_of_one_le_right (by linarith) hY1)
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = cW * Y ^ (4 * (m + 2)) := ⟨_, rfl⟩
  have hYp : 1 ≤ Y ^ (4 * (m + 2)) := one_le_pow₀ hY1
  have hWle : ∀ r : ℝ, r ≤ cW → r ≤ W := fun r hr => by
    rw [hWdef]; exact hr.trans (le_mul_of_one_le_right (by linarith) hYp)
  have hW1 : 1 ≤ W := hWle 1 hcW0
  have hQW : Q ^ (4 * (m + 2)) ≤ W := by
    rw [hQdef, hWdef, mul_pow]
    exact mul_le_mul_of_nonneg_right hcW1 (by positivity)
  obtain ⟨K', hK'def⟩ : ∃ K' : ℝ, K' = |Ccut| * (K * mx) := ⟨_, rfl⟩
  have hK'0 : 0 ≤ K' := by rw [hK'def]; positivity
  have hP0 : 0 ≤ W ^ b := by positivity
  have hS0 : 0 ≤ 2 ^ q * |Ccrit| * (K' * W ^ a) := by positivity
  have key : ∀ x : Fin (m + 1) → ℂ,
      DB q (fun x : Fin (m + 1) → ℂ => ((critCut δ z x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y)) x
        (2 ^ q * |Ccrit| * (K' * W ^ a)) (W ^ b) := by
    intro x
    by_cases hy : ‖y‖ ≤ 2 * τ
    swap
    · refine DB.of_eventually_zero (Filter.Eventually.of_forall fun v => ?_) hS0 hP0
      show ((critCut δ z v : ℝ) : ℂ) • ampIn β m ε Φ D t (v, y) = 0
      rw [ampIn_zero β m ε Φ D t (v, y) (by rw [← hτdef]; linarith) (by rw [← hτdef]; exact (not_le.1 hy).le),
        smul_zero]
    by_cases hx : ‖x - fun _ => z‖ ≤ 2 * δ
    swap
    · have hopen : IsOpen {v : Fin (m + 1) → ℂ | 2 * δ < ‖v - fun _ => z‖} :=
        isOpen_lt continuous_const (by fun_prop)
      refine DB.of_eventually_zero ?_ hS0 hP0
      filter_upwards [hopen.mem_nhds (not_le.1 hx)] with v hv
      show ((critCut δ z v : ℝ) : ℂ) • ampIn β m ε Φ D t (v, y) = 0
      rw [(hcr1 z v).2.2.2 (le_of_lt hv)]
      simp
    · have hxk : ∀ k, ‖x k - z‖ ≤ 2 * δ := fun k => (norm_le_pi_norm (x - fun _ => z) k).trans hx
      have hxu : ∀ k, ‖x k‖ ≤ c := fun k => by
        have h1 := norm_add_le (x k - z) z
        rw [sub_add_cancel] at h1
        have h2 := hxk k
        linarith
      have hxl : ∀ k, δ ≤ ‖x k‖ := fun k => by
        have h1 := norm_sub_norm_le z (x k)
        rw [norm_sub_rev] at h1
        have h2 := hxk k
        linarith
      obtain ⟨hprod, hcof⟩ := cof_lower m hδ0 hc2 hε0 hε ht0 ht1 hts (x, y) hxu hxl (by rw [← hτdef]; exact hy)
      have hcofne : cofXY m t (x, y) ≠ 0 := by
        intro h
        rw [h, norm_zero] at hcof
        linarith
      have hprodne : ∏ k, x k ≠ 0 := by
        intro h
        change δ ^ (m + 1) ≤ ‖∏ k, x k‖ at hprod
        rw [h, norm_zero] at hprod
        linarith
      have hdet : detM (MXY m D t (x, y)) ∈ detSet (m + 1) Kc := ⟨D, hD, (det_matrix_xy m D t (x, y) hcofne).symm⟩
      have hΦ' := (hCcut V Φ _ _ τ hτ (derivBound_mono hΦ hk)).1
      have hDBΦ : DB q (cutPhi τ Φ) (MXY m D t (x, y)) K' 1 := by
        refine (DB_of_DerivBound hΦ' le_rfl hdet).mono ?_ zero_le_one le_rfl
        have h1 : min 1 (‖MXY m D t (x, y)‖ ^ (-A)) ≤ mx := by
          rw [hmxdef]
          exact min_le_max hA (y_le_MXY m D t (x, y))
        have h2 : 0 ≤ min 1 (‖MXY m D t (x, y)‖ ^ (-A)) := le_min zero_le_one (by positivity)
        calc Ccut * (K * min 1 (‖MXY m D t (x, y)‖ ^ (-A)))
            ≤ |Ccut| * (K * min 1 (‖MXY m D t (x, y)‖ ^ (-A))) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
          _ ≤ |Ccut| * (K * mx) := by gcongr
          _ = K' := hK'def.symm
      have hcofW : ‖cofXY m t (x, y)‖⁻¹ ≤ W := by
        refine hWle _ (le_trans ?_ hcW2)
        calc ‖cofXY m t (x, y)‖⁻¹ ≤ (δ ^ (m + 1) / 2)⁻¹ := inv_anti₀ (by positivity) hcof
          _ = 2 / δ ^ (m + 1) := by rw [inv_div]
      have hprodW : ‖∏ k, x k‖⁻¹ ≤ W := by
        refine hWle _ (le_trans ?_ hcW2)
        calc ‖∏ k, x k‖⁻¹ ≤ (δ ^ (m + 1))⁻¹ := inv_anti₀ hδp hprod
          _ ≤ 2 / δ ^ (m + 1) := by
            rw [div_eq_mul_inv]
            have : 0 ≤ (δ ^ (m + 1))⁻¹ := by positivity
            linarith
      have hyQ : ∀ e, ‖y e‖ ≤ Q := fun e => by
        have h1 := norm_le_pi_norm y e
        have h2 : Y ≤ Q := by rw [hQdef]; exact le_mul_of_one_le_left (by linarith) hcQ0
        rw [hYdef] at h2
        linarith
      have hc := hcore (Fin (m + 1) → ℂ) m q β D (fun _ => t) (fun v => v) (fun _ => y) x Q W (hQle _ hcQ1)
        (DB.const q t x (hQle _ (ht1.trans hcQ0)) zero_le_one)
        (fun k => DB_proj q (m + 1) k x (hQle _ ((hxu k).trans hcQ2)) (hQle _ hcQ0))
        (fun e => DB.const q (y e) x (hyQ e) zero_le_one)
        (hQle _ (((hRD D hD).trans hcRD).trans hcQ2)) (hQle _ hcQ3) hQW hcofne hcofW hprodne hprodW V
        (cutPhi τ Φ) K' hDBΦ
      have hamp : DB q (fun v : Fin (m + 1) → ℂ => ampIn β m ε Φ D t (v, y)) x (K' * W ^ a) (W ^ b) := by
        refine hc.congr ?_
        have hev : ∀ᶠ v : Fin (m + 1) → ℂ in 𝓝 x, ∏ k, v k ≠ 0 :=
          ContinuousAt.eventually_ne (g := fun v : Fin (m + 1) → ℂ => ∏ k, v k) (by fun_prop) hprodne
        filter_upwards [hev] with v hv
        show amp β m (cutPhi (‖t‖ ^ (-ε)) Φ) D t (v, y) = _
        rw [← hτdef]
        exact amp_eq_ampE β m _ D t (v, y) ht0 hv
      have hcc0 : DB q (critCut (n := m + 1) δ z) x |Ccrit| 1 :=
        ⟨(hCcrit z).1.contDiffAt, fun j hj => by
          rw [one_pow, mul_one]
          exact ((hCcrit z).2 j hj x).trans (le_abs_self _)⟩
      have hcc : DB q (fun v : Fin (m + 1) → ℂ => ((critCut δ z v : ℝ) : ℂ)) x |Ccrit| (W ^ b) :=
        (hcc0.clm_one Complex.ofRealCLM (by simp)).mono le_rfl zero_le_one (one_le_pow₀ hW1)
      exact hcc.smul hamp hP0
  refine ⟨contDiff_iff_contDiffAt.2 fun x => (key x).1, fun j hj x => ?_⟩
  have hexp : 4 * (m + 2) * (a + b * q) ≤ 4 * (a + 2 * b) * (m + 2) ^ 2 := by
    have h1 : m + 2 ≤ (m + 2) ^ 2 := Nat.le_self_pow two_ne_zero _
    have h2 : 4 * a * (m + 2) ≤ 4 * a * (m + 2) ^ 2 := Nat.mul_le_mul_left _ h1
    have h3 : q = 2 * (m + 2) := by omega
    rw [h3]
    calc 4 * (m + 2) * (a + b * (2 * (m + 2))) = 4 * a * (m + 2) + 8 * b * (m + 2) ^ 2 := by ring
      _ ≤ 4 * a * (m + 2) ^ 2 + 8 * b * (m + 2) ^ 2 := Nat.add_le_add_right h2 _
      _ = 4 * (a + 2 * b) * (m + 2) ^ 2 := by ring
  have hWpow : W ^ a * (W ^ b) ^ j ≤ cW ^ (a + b * q) * Y ^ (4 * (a + 2 * b) * (m + 2) ^ 2) := by
    calc W ^ a * (W ^ b) ^ j = W ^ (a + b * j) := by rw [← pow_mul, ← pow_add]
      _ ≤ W ^ (a + b * q) := pow_le_pow_right₀ hW1 (by gcongr)
      _ = cW ^ (a + b * q) * Y ^ (4 * (m + 2) * (a + b * q)) := by rw [hWdef, mul_pow, ← pow_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 hexp) (by positivity)
  calc _ ≤ 2 ^ q * |Ccrit| * (K' * W ^ a) * (W ^ b) ^ j := (key x).2 j hj
    _ = (2 ^ q * |Ccrit| * |Ccut| * K * mx) * (W ^ a * (W ^ b) ^ j) := by rw [hK'def]; ring
    _ ≤ (2 ^ q * |Ccrit| * |Ccut| * K * mx) * (cW ^ (a + b * q) * Y ^ (4 * (a + 2 * b) * (m + 2) ^ 2)) :=
        mul_le_mul_of_nonneg_left hWpow (by positivity)
    _ = _ := by rw [hYdef, hmxdef]; ring

end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit

theorem Formalism.FourierDecayAlt.P.amplitude_bound_critical : Formalism.FourierDecayAlt.G.AmpBoundCrit := Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit.main

namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology MeasureTheory

noncomputable section

theorem min_le_max {A : ℝ} (hA : 0 ≤ A) {a b : ℝ} (hab : b ≤ a) :
    min 1 (a ^ (-A)) ≤ (max 1 b) ^ (-A) := by
  by_cases h : b ≤ 1
  · rw [max_eq_left h, Real.one_rpow]
    exact min_le_left _ _
  · push Not at h
    rw [max_eq_right h.le]
    refine (min_le_right _ _).trans ?_
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hab (by linarith)

theorem z_bounds (m : ℕ) {z : ℂ} {d r R : ℝ} (h : ‖z‖ ^ (m + 2) = d) (hr : r ≤ d) (hR : d ≤ R) :
    min 1 r ≤ ‖z‖ ∧ ‖z‖ ≤ max 1 R := by
  constructor
  · by_cases h1 : 1 ≤ ‖z‖
    · exact (min_le_left _ _).trans h1
    · push Not at h1
      refine (min_le_right _ _).trans (hr.trans ?_)
      rw [← h]
      exact pow_le_of_le_one (norm_nonneg _) h1.le (by omega)
  · by_cases h1 : ‖z‖ ≤ 1
    · exact h1.trans (le_max_left _ _)
    · push Not at h1
      refine le_trans ?_ (hR.trans (le_max_right _ _))
      rw [← h]
      exact le_self_pow₀ h1.le (by omega)

theorem Tpow (m : ℕ) {τ ε : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε0 : 0 < ε) (hε : ε ≤ 1 / (2 * ((m : ℝ) + 2))) {i : ℕ}
    (hi : i ≤ m + 2) : (τ ^ (-ε)) ^ i * τ ≤ Real.sqrt τ := by
  have hT : 1 ≤ τ ^ (-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ hτ1 (by linarith)
  refine le_trans ?_ (G6.rpow_bound m hτ hτ1 hε)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT hi) hτ.le

theorem cof_lower (m : ℕ) (z τ' : ℂ) (y : UT (m + 2) → ℂ) {R c : ℝ} (hR : 1 ≤ R) (hτ : ‖τ'‖ ≤ 1) (hz : ‖z‖ ≤ R)
    (hy : ‖y‖ ≤ R) (hc : c ≤ ‖z‖ ^ (m + 1)) (hs : ‖τ'‖ * (((m : ℝ) + 1) ^ (m + 1) * R ^ m) ≤ c / 2) :
    c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖ := by
  have h1 := first_cofactor_norm_le m τ' (fun _ => z, y) hR hτ (fun _ => hz) hy
  have h0 : ‖cof0XY m (fun _ => z, y)‖ = ‖z‖ ^ (m + 1) := by
    rw [← cofXY_at_zero, cofXY_zero]
  have h2 : ‖τ' * cof1XY m τ' (fun _ => z, y)‖ ≤ c / 2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans hs
  rw [cofXY_eq]
  have h3 := norm_sub_le_norm_add (cof0XY m (fun _ => z, y)) (τ' * cof1XY m τ' (fun _ => z, y))
  linarith [h3]

theorem geom (m : ℕ) (Kc : Set ℂ) (hK : IsCompact Kc) (h0 : (0 : ℂ) ∉ Kc) (ε : ℝ) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / (2 * ((m : ℝ) + 2))) :
    ∃ t₁ c Rz : ℝ, 0 < t₁ ∧ t₁ ≤ 1 ∧ 0 < c ∧ 1 ≤ Rz ∧ ∀ D ∈ Kc, ∀ z : ℂ, z ^ (m + 2) = (-1) ^ (m + 3) * D →
      ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ t₁ →
      z ≠ 0 ∧ ‖z‖ ≤ Rz ∧ ‖D‖ ≤ Rz ∧ c ≤ ‖z‖ ^ (m + 1) ∧
      (∀ (y : UT (m + 2) → ℂ) (τ' : ℂ), ‖y‖ ≤ 2 * ‖t‖ ^ (-ε) → ‖τ'‖ ≤ ‖t‖ →
        c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖) ∧
      (∀ y : UT (m + 2) → ℂ, ‖y‖ ≤ ‖t‖ ^ (-ε) → ‖MXY m D t (fun _ => z, y)‖ ≤ ‖t‖ ^ (-ε)) := by
  obtain ⟨RD, hRD⟩ := hK.isBounded.exists_norm_le
  obtain ⟨rD, hrD0, hrD⟩ : ∃ r : ℝ, 0 < r ∧ ∀ D ∈ Kc, r ≤ ‖D‖ := by
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl 0 h0
    refine ⟨r, hr, fun D hD => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hb (by simpa using hlt) hD
  set Rz : ℝ := max 1 RD with hRz
  set rz : ℝ := min 1 rD with hrz
  have hRz1 : 1 ≤ Rz := le_max_left _ _
  have hrz0 : 0 < rz := lt_min one_pos hrD0
  set c : ℝ := rz ^ (m + 1) with hc
  have hc0 : 0 < c := pow_pos hrz0 _
  set C₁ : ℝ := ((m : ℝ) + 1) ^ (m + 1) * (2 * Rz) ^ m with hC₁
  set C₂ : ℝ := ((m : ℝ) + 1) ^ (m + 2) * (2 * Rz) ^ (m + 1) with hC₂
  have hC₁0 : 0 < C₁ := by positivity
  have hC₂0 : 0 < C₂ := by positivity
  set Rb : ℝ := max ((2 * Rz + Rz + C₂) * (2 / c)) Rz with hRb
  have hRb1 : 1 ≤ Rb := hRz1.trans (le_max_right _ _)
  have hRb0 : 0 < Rb := by linarith
  refine ⟨min 1 (min ((c / (2 * C₁)) ^ 2) (Rb ^ (-(1 / ε)))), c, Rz, ?_, min_le_left _ _, hc0, hRz1, ?_⟩
  · refine lt_min one_pos (lt_min (by positivity) (Real.rpow_pos_of_pos hRb0 _))
  intro D hD z hzD t ht htle
  have ht0 : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have ht1 : ‖t‖ ≤ 1 := htle.trans (min_le_left _ _)
  have ht2 : ‖t‖ ≤ (c / (2 * C₁)) ^ 2 := htle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht3 : ‖t‖ ≤ Rb ^ (-(1 / ε)) := htle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hnz : ‖z‖ ^ (m + 2) = ‖D‖ := by
    rw [← norm_pow, hzD, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  obtain ⟨hzl, hzu⟩ := z_bounds m hnz (hrD D hD) (hRD D hD)
  have hz0 : z ≠ 0 := by
    rw [← norm_pos_iff]
    exact lt_of_lt_of_le hrz0 hzl
  have hcz : c ≤ ‖z‖ ^ (m + 1) := pow_le_pow_left₀ hrz0.le hzl _
  set T : ℝ := ‖t‖ ^ (-ε) with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith)
  have hsq : Real.sqrt ‖t‖ ≤ c / (2 * C₁) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ c / (2 * C₁))]
    exact Real.sqrt_le_sqrt ht2
  have hsq1 : Real.sqrt ‖t‖ ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ht1
  have hRbT : Rb ≤ T := by
    have h1 : (Rb ^ (-(1 / ε))) ^ (-ε) ≤ T := Real.rpow_le_rpow_of_nonpos ht0 ht3 (by linarith)
    rw [← Real.rpow_mul hRb0.le] at h1
    have h2 : -(1 / ε) * -ε = 1 := by field_simp
    rwa [h2, Real.rpow_one] at h1
  have hR1 : 1 ≤ 2 * Rz * T := by nlinarith
  have hzR : ‖z‖ ≤ 2 * Rz * T := by nlinarith
  have hcof : ∀ (y : UT (m + 2) → ℂ) (τ' : ℂ), ‖y‖ ≤ 2 * T → ‖τ'‖ ≤ ‖t‖ →
      c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖ := by
    intro y τ' hy hτ'
    refine cof_lower m z τ' y hR1 (hτ'.trans ht1) hzR (by nlinarith) hcz ?_
    calc ‖τ'‖ * (((m : ℝ) + 1) ^ (m + 1) * (2 * Rz * T) ^ m)
        ≤ ‖t‖ * (((m : ℝ) + 1) ^ (m + 1) * (2 * Rz * T) ^ m) :=
          mul_le_mul_of_nonneg_right hτ' (by positivity)
      _ = C₁ * (T ^ m * ‖t‖) := by rw [hC₁, mul_pow]; ring
      _ ≤ C₁ * Real.sqrt ‖t‖ :=
          mul_le_mul_of_nonneg_left (Tpow m ht0 ht1 hε0 hε (by omega)) hC₁0.le
      _ ≤ C₁ * (c / (2 * C₁)) := mul_le_mul_of_nonneg_left hsq hC₁0.le
      _ = c / 2 := by field_simp
  refine ⟨hz0, hzu, (hRD D hD).trans (le_max_right _ _), hcz, hcof, ?_⟩
  intro y hy
  have hyR : ‖y‖ ≤ 2 * Rz * T := by nlinarith
  have hcl := hcof y t (by linarith) le_rfl
  have hρ : ‖rhoXY m D t (fun _ => z, y)‖ ≤ (2 * Rz + Rz + C₂) * (2 / c) := by
    rw [rhoXY_eq, norm_mul, norm_inv]
    have e1 : ‖cofXY m t (fun _ => z, y)‖⁻¹ ≤ 2 / c := by
      rw [inv_le_comm₀ (by linarith) (by positivity)]
      rw [inv_div]
      exact hcl
    have e2 : ‖t ^ (m + 1) * sm m (fun _ => z, y)‖ ≤ 2 * Rz := by
      rw [norm_mul, norm_pow]
      have a1 : ‖sm m (fun _ => z, y)‖ ≤ 2 * Rz * T :=
        sm_le m (fun _ => z, y) (by linarith) (fun _ => hzR) hyR
      have a2 : ‖t‖ ^ (m + 1) ≤ ‖t‖ := pow_le_of_le_one ht0.le ht1 (by omega)
      calc ‖t‖ ^ (m + 1) * ‖sm m (fun _ => z, y)‖ ≤ ‖t‖ * (2 * Rz * T) :=
            mul_le_mul a2 a1 (norm_nonneg _) ht0.le
        _ = 2 * Rz * (T ^ 1 * ‖t‖) := by ring
        _ ≤ 2 * Rz * Real.sqrt ‖t‖ :=
            mul_le_mul_of_nonneg_left (Tpow m ht0 ht1 hε0 hε (by omega)) (by positivity)
        _ ≤ 2 * Rz * 1 := mul_le_mul_of_nonneg_left hsq1 (by positivity)
        _ = 2 * Rz := by ring
    have e3 : ‖t * r1XY m t (fun _ => z, y)‖ ≤ C₂ := by
      rw [norm_mul]
      have a1 := remainder_norm_le m t (fun _ => z, y) hR1 ht1 (fun _ => hzR) hyR
      calc ‖t‖ * ‖r1XY m t (fun _ => z, y)‖ ≤ ‖t‖ * (((m : ℝ) + 1) ^ (m + 2) * (2 * Rz * T) ^ (m + 1)) :=
            mul_le_mul_of_nonneg_left a1 ht0.le
        _ = C₂ * (T ^ (m + 1) * ‖t‖) := by rw [hC₂, mul_pow]; ring
        _ ≤ C₂ * Real.sqrt ‖t‖ :=
            mul_le_mul_of_nonneg_left (Tpow m ht0 ht1 hε0 hε (by omega)) hC₂0.le
        _ ≤ C₂ * 1 := mul_le_mul_of_nonneg_left hsq1 hC₂0.le
        _ = C₂ := by ring
    have e4 : ‖t ^ (m + 1) * sm m (fun _ => z, y) - D - t * r1XY m t (fun _ => z, y)‖ ≤ 2 * Rz + Rz + C₂ := by
      refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add e2 ?_)) e3)
      exact (hRD D hD).trans (le_max_right _ _)
    exact mul_le_mul e4 e1 (by positivity) (by positivity)
  refine MXY_le m D t (fun _ => z, y) (by linarith) (ht1.trans hT1) ?_ (fun _ => ?_) hy
  · exact hρ.trans ((le_max_left _ _).trans hRbT)
  · exact hzu.trans ((le_max_right _ _).trans hRbT)

def CoreProp (a b : ℕ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m q : ℕ) (β D : ℂ) (tt : E → ℂ)
    (xx : E → Fin (m + 1) → ℂ) (yy : E → UT (m + 2) → ℂ) (u : E) (Q W : ℝ),
    2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial ≤ Q → DB q tt u Q 1 → (∀ k, DB q (fun v => xx v k) u Q 1) →
    (∀ e, DB q (fun v => yy v e) u Q 1) → ‖D‖ ≤ Q → ‖β‖ ≤ Q → Q ^ (4 * (m + 2)) ≤ W →
    cofXY m (tt u) (xx u, yy u) ≠ 0 → ‖cofXY m (tt u) (xx u, yy u)‖⁻¹ ≤ W →
    ∏ k, xx u k ≠ 0 → ‖∏ k, xx u k‖⁻¹ ≤ W →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Φ : Mat (m + 1 + 1) → V) (K' : ℝ),
      DB q Φ (MXY m D (tt u) (xx u, yy u)) K' 1 →
      DB q (fun v => ampE β m Φ D (tt v) (xx v, yy v)) u (K' * W ^ a) (W ^ b)

theorem core' : ∃ a b : ℕ, CoreProp a b := core

section

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem norm_psi (β w : ℂ) : ‖psi β w‖ = 1 := (additive_character_psi β w 0).2.1

theorem det_mem (m : ℕ) (Kc : Set ℂ) {D : ℂ} (hD : D ∈ Kc) (t : ℂ) (p : XY m) (hc : cofXY m t p ≠ 0) :
    detM (MXY m D t p) ∈ detSet (m + 1) Kc := by
  rw [det_matrix_xy m D t p hc]
  exact ⟨D, hD, rfl⟩

theorem K_nonneg (m : ℕ) (Kc : Set ℂ) (Φ : Mat (m + 1 + 1) → V) (A K : ℝ) (k : ℕ)
    (h : DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ) {D z : ℂ} (hD : D ∈ Kc)
    (hz : z ≠ 0) : 0 ≤ K := by
  have hc : cofXY m 0 ((fun _ => z, 0) : XY m) ≠ 0 := by
    rw [← norm_pos_iff, cofXY_zero]
    exact pow_pos (norm_pos_iff.mpr hz) _
  have h1 := (DB_of_DerivBound h (Nat.zero_le k) (det_mem m Kc hD 0 _ hc)).nonneg
  have h2 : 0 < ‖MXY m D 0 ((fun _ => z, 0) : XY m)‖ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hz) (x_le_MXY m D 0 ((fun _ => z, 0) : XY m) 0)
  have h3 : 0 < min 1 (‖MXY m D 0 ((fun _ => z, 0) : XY m)‖ ^ (-A)) :=
    lt_min one_pos (Real.rpow_pos_of_pos h2 _)
  by_contra hK
  push Not at hK
  have := mul_neg_of_neg_of_pos hK h3
  linarith

theorem Phi_DB (m : ℕ) (Kc : Set ℂ) (Φ : Mat (m + 1 + 1) → V) (A K : ℝ) (k q : ℕ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hq : q ≤ k) (h : DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ) {D : ℂ} (hD : D ∈ Kc)
    (t : ℂ) (p : XY m) (hc : cofXY m t p ≠ 0) :
    DB q Φ (MXY m D t p) (K * (max 1 ‖p.2‖) ^ (-A)) 1 := by
  refine (DB_of_DerivBound h hq (det_mem m Kc hD t p hc)).mono ?_ zero_le_one le_rfl
  exact mul_le_mul_of_nonneg_left (min_le_max hA (y_le_MXY m D t p)) hK

theorem f_bound (m : ℕ) (β : ℂ) (ε : ℝ) (Φ : Mat (m + 1 + 1) → V) (D t : ℂ) (p : XY m) {c K' : ℝ} (hc : 0 < c)
    (ht : t ≠ 0) (hK' : 0 ≤ K') (hcof : ‖p.2‖ ≤ 2 * ‖t‖ ^ (-ε) → c / 2 ≤ ‖cofXY m t p‖)
    (hΦ : cofXY m t p ≠ 0 → ‖Φ (MXY m D t p)‖ ≤ K') :
    ‖ampIn β m ε Φ D t p‖ ≤ (2 / c) ^ 2 * K' := by
  have hT : 0 < ‖t‖ ^ (-ε) := Real.rpow_pos_of_pos (norm_pos_iff.mpr ht) _
  obtain ⟨hc0, hc1, -, hcz⟩ := (matrix_cutoff_spec (m + 1 + 1)).1 (‖t‖ ^ (-ε)) (MXY m D t p) hT
  by_cases hy : ‖p.2‖ ≤ 2 * ‖t‖ ^ (-ε)
  · have hl := hcof hy
    have hne : cofXY m t p ≠ 0 := by
      rw [← norm_pos_iff]
      linarith
    rw [ampIn, amp, cutPhi, norm_smul, norm_smul, norm_mul, norm_psi, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc0,
      abs_of_nonneg (by positivity)]
    have e1 : (‖cofXY m t p‖ ^ 2)⁻¹ ≤ (2 / c) ^ 2 := by
      rw [← inv_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]
      exact hl
    have e2 : cutM (‖t‖ ^ (-ε)) (MXY m D t p) * ‖Φ (MXY m D t p)‖ ≤ K' := by
      calc cutM (‖t‖ ^ (-ε)) (MXY m D t p) * ‖Φ (MXY m D t p)‖ ≤ 1 * K' :=
            mul_le_mul hc1 (hΦ hne) (norm_nonneg _) zero_le_one
        _ = K' := one_mul _
    exact mul_le_mul e1 e2 (by positivity) (by positivity)
  · push Not at hy
    have h0 := hcz (hy.le.trans (y_le_MXY m D t p))
    rw [ampIn, amp, cutPhi, h0]
    simp only [Complex.ofReal_zero, zero_smul, smul_zero, norm_zero]
    positivity

theorem f_eq (m : ℕ) (β : ℂ) (ε : ℝ) (Φ : Mat (m + 1 + 1) → V) (D t : ℂ) (p : XY m) (ht : t ≠ 0)
    (hp : ∏ k, p.1 k ≠ 0) (hM : ‖MXY m D t p‖ ≤ ‖t‖ ^ (-ε)) : ampIn β m ε Φ D t p = ampE β m Φ D t p := by
  have hT : 0 < ‖t‖ ^ (-ε) := Real.rpow_pos_of_pos (norm_pos_iff.mpr ht) _
  obtain ⟨-, -, h1, -⟩ := (matrix_cutoff_spec (m + 1 + 1)).1 (‖t‖ ^ (-ε)) (MXY m D t p) hT
  rw [← amp_eq_ampE β m Φ D t p ht hp, ampIn, amp, amp, cutPhi, h1 hM]
  simp

theorem ampE_zero (m : ℕ) (β : ℂ) (Φ : Mat (m + 1 + 1) → V) (D z : ℂ) (y : UT (m + 2) → ℂ) (hz : z ≠ 0)
    (hzD : z ^ (m + 2) = (-1) ^ (m + 3) * D) :
    ampE β m Φ D 0 (fun _ => z, y) =
      (((‖z‖ ^ (2 * (m + 1)))⁻¹ : ℝ) : ℂ) • (psi β (superSum (strictUpper y) / z) •
        Φ (wMat (m + 2) * (z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y))) := by
  rw [ampE, gExt_zero m D z y hz hzD, cofXY_zero, MXY_zero m D z y hz hzD, smul_smul, mul_comm, ← pow_mul,
    mul_comm (m + 1) 2]

theorem g_bound (m : ℕ) (β : ℂ) (Φ : Mat (m + 1 + 1) → V) (D z : ℂ) (y : UT (m + 2) → ℂ) {c K' : ℝ} (hc : 0 < c)
    (hcz : c ≤ ‖z‖ ^ (m + 1)) (hΦ : ‖Φ (MXY m D 0 (fun _ => z, y))‖ ≤ K') :
    ‖ampE β m Φ D 0 (fun _ => z, y)‖ ≤ (2 / c) ^ 2 * K' := by
  rw [ampE, norm_smul, norm_mul, norm_psi, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), cofXY_zero]
  have e1 : ((‖z‖ ^ (m + 1)) ^ 2)⁻¹ ≤ (2 / c) ^ 2 := by
    rw [← inv_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]
    linarith
  exact mul_le_mul e1 hΦ (norm_nonneg _) (by positivity)

theorem diff_key {a b : ℕ} (hcore : CoreProp a b) (m : ℕ) (β D z τ' : ℂ) (y : UT (m + 2) → ℂ) {c Rz K' : ℝ}
    (Φ : Mat (m + 1 + 1) → V) (hc0 : 0 < c) (hRz : 1 ≤ Rz) (hz0 : z ≠ 0) (hzR : ‖z‖ ≤ Rz) (hDR : ‖D‖ ≤ Rz)
    (hcz : c ≤ ‖z‖ ^ (m + 1)) (hτ1 : ‖τ'‖ ≤ 1) (hl : c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖)
    (hΦ : DB 1 Φ (MXY m D τ' (fun _ => z, y)) K' 1) :
    DB 1 (fun v : ℂ => ampE β m Φ D v (fun _ => z, y)) τ'
      (K' * (((4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖) ^ (4 * (m + 2)) + 2 / c) * (1 + ‖y‖) ^ (4 * (m + 2))) ^ a)
      ((((4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖) ^ (4 * (m + 2)) + 2 / c) * (1 + ‖y‖) ^ (4 * (m + 2))) ^ b) := by
  set cQ : ℝ := 4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖ with hcQ
  set cW : ℝ := cQ ^ (4 * (m + 2)) + 2 / c with hcW
  set Y : ℝ := 1 + ‖y‖ with hY
  have hy0 := norm_nonneg y
  have hY1 : 1 ≤ Y := by linarith
  have hβ0 := norm_nonneg β
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm2 : (0 : ℝ) ≤ ((m : ℝ) + 2) ^ 2 := by positivity
  have hcQ1 : 1 ≤ cQ := by linarith
  have hcQ0 : 0 ≤ cQ := by linarith
  have h2c : 0 ≤ 2 / c := by positivity
  have hcQp : 0 ≤ cQ ^ (4 * (m + 2)) := by positivity
  have hcW0 : 0 ≤ cW := by linarith
  have hYp : 1 ≤ Y ^ (4 * (m + 2)) := one_le_pow₀ hY1
  have hQ : ∀ r : ℝ, r ≤ cQ → r ≤ cQ * Y := fun r hr =>
    hr.trans (le_mul_of_one_le_right hcQ0 hY1)
  have hW : ∀ r : ℝ, r ≤ cW → r ≤ cW * Y ^ (4 * (m + 2)) := fun r hr =>
    hr.trans (le_mul_of_one_le_right hcW0 hYp)
  have g1 : (2 : ℝ) ^ 1 * ((m : ℝ) + 2) ^ 2 * (Nat.factorial 1 : ℕ) ≤ cQ * Y := by
    refine hQ _ ?_
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one]
    linarith
  have g2 : DB 1 (fun v : ℂ => v) τ' (cQ * Y) 1 := by
    have h := DB.affine 1 (ContinuousLinearMap.id ℝ ℂ) (0 : ℂ) τ' (S := cQ * Y)
      (by
        simp only [ContinuousLinearMap.id_apply, add_zero]
        exact hQ _ (by linarith))
      (ContinuousLinearMap.norm_id_le.trans (hQ _ hcQ1))
    simpa using h
  have g3 : ∀ _k : Fin (m + 1), DB 1 (fun _ : ℂ => z) τ' (cQ * Y) 1 := fun _ =>
    DB.const 1 z τ' (hQ _ (by linarith)) zero_le_one
  have g4 : ∀ e : UT (m + 2), DB 1 (fun _ : ℂ => y e) τ' (cQ * Y) 1 := fun e => by
    refine DB.const 1 (y e) τ' ((norm_le_pi_norm y e).trans ?_) zero_le_one
    calc ‖y‖ ≤ 1 * Y := by linarith
      _ ≤ cQ * Y := mul_le_mul_of_nonneg_right hcQ1 (by linarith)
  have g5 : ‖D‖ ≤ cQ * Y := hQ _ (by linarith)
  have g6 : ‖β‖ ≤ cQ * Y := hQ _ (by linarith)
  have g7 : (cQ * Y) ^ (4 * (m + 2)) ≤ cW * Y ^ (4 * (m + 2)) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have g8 : cofXY m τ' (fun _ => z, y) ≠ 0 := by
    rw [← norm_pos_iff]
    linarith
  have g9 : ‖cofXY m τ' (fun _ => z, y)‖⁻¹ ≤ cW * Y ^ (4 * (m + 2)) := by
    refine hW _ ?_
    have e1 : ‖cofXY m τ' (fun _ => z, y)‖⁻¹ ≤ 2 / c := by
      rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]
      exact hl
    linarith
  have g10 : ∏ _k : Fin (m + 1), z ≠ 0 := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_ne_zero _ hz0
  have g11 : ‖∏ _k : Fin (m + 1), z‖⁻¹ ≤ cW * Y ^ (4 * (m + 2)) := by
    refine hW _ ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_pow]
    have e1 : (‖z‖ ^ (m + 1))⁻¹ ≤ 2 / c := by
      rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]
      linarith
    linarith
  exact hcore ℂ m 1 β D (fun v => v) (fun _ _ => z) (fun _ => y) τ' (cQ * Y) (cW * Y ^ (4 * (m + 2)))
    g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 V Φ K' hΦ

theorem diff_bound {a b : ℕ} (hcore : CoreProp a b) (m : ℕ) (β D z t : ℂ) (y : UT (m + 2) → ℂ) {c Rz K' : ℝ}
    (Φ : Mat (m + 1 + 1) → V) (hc0 : 0 < c) (hRz : 1 ≤ Rz) (hz0 : z ≠ 0) (hzR : ‖z‖ ≤ Rz) (hDR : ‖D‖ ≤ Rz)
    (hcz : c ≤ ‖z‖ ^ (m + 1)) (ht1 : ‖t‖ ≤ 1)
    (hcof : ∀ τ' : ℂ, ‖τ'‖ ≤ ‖t‖ → c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖)
    (hΦ : ∀ τ' : ℂ, ‖τ'‖ ≤ ‖t‖ → DB 1 Φ (MXY m D τ' (fun _ => z, y)) K' 1) :
    ‖ampE β m Φ D t (fun _ => z, y) - ampE β m Φ D 0 (fun _ => z, y)‖ ≤
      K' * ((4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖) ^ (4 * (m + 2)) + 2 / c) ^ (a + b) *
        (1 + ‖y‖) ^ (4 * (m + 2) * (a + b)) * ‖t‖ := by
  set cW : ℝ := (4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖) ^ (4 * (m + 2)) + 2 / c with hcW
  have key : ∀ τ' ∈ Metric.closedBall (0 : ℂ) ‖t‖,
      DB 1 (fun v : ℂ => ampE β m Φ D v (fun _ => z, y)) τ' (K' * (cW * (1 + ‖y‖) ^ (4 * (m + 2))) ^ a)
        ((cW * (1 + ‖y‖) ^ (4 * (m + 2))) ^ b) := by
    intro τ' hτ'
    have hτ : ‖τ'‖ ≤ ‖t‖ := by simpa using hτ'
    exact diff_key hcore m β D z τ' y Φ hc0 hRz hz0 hzR hDR hcz (hτ.trans ht1) (hcof τ' hτ) (hΦ τ' hτ)
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (f := fun v : ℂ => ampE β m Φ D v (fun _ => z, y))
    (C := K' * (cW * (1 + ‖y‖) ^ (4 * (m + 2))) ^ a * (cW * (1 + ‖y‖) ^ (4 * (m + 2))) ^ b)
    (s := Metric.closedBall (0 : ℂ) ‖t‖) (x := 0) (y := t)
    (fun τ' hτ' => (key τ' hτ').1.differentiableAt (by norm_num))
    (fun τ' hτ' => by
      have h := (key τ' hτ').2 1 le_rfl
      rwa [norm_iteratedFDeriv_one, pow_one] at h)
    (convex_closedBall _ _) (by simp) (by simp)
  rw [sub_zero] at hmv
  refine hmv.trans (le_of_eq ?_)
  rw [mul_assoc K', ← pow_add, mul_pow, ← pow_mul]
  ring

end

theorem int_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f g : α → V) (maj : α → ℝ) (S : Set α) (hS : MeasurableSet S)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (hmaj : Integrable maj μ)
    (hmaj0 : ∀ y, 0 ≤ maj y) {B τ : ℝ} (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hfb : ∀ y, ‖f y‖ ≤ B * maj y)
    (hgb : ∀ y, ‖g y‖ ≤ B * maj y) (hin : ∀ y, y ∉ S → ‖f y - g y‖ ≤ B * τ * maj y) :
    ‖∫ y, f y ∂μ - ∫ y, g y ∂μ‖ ≤ B * τ * ∫ y, maj y ∂μ + 2 * B * ∫ y in S, maj y ∂μ := by
  have hfi : Integrable f μ := (hmaj.const_mul B).mono' hf (Eventually.of_forall hfb)
  have hgi : Integrable g μ := (hmaj.const_mul B).mono' hg (Eventually.of_forall hgb)
  have hind : Integrable (S.indicator maj) μ := hmaj.indicator hS
  rw [← integral_sub hfi hgi]
  have hb : Integrable (fun y => B * τ * maj y + 2 * B * S.indicator maj y) μ :=
    (hmaj.const_mul _).add (hind.const_mul _)
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun y => ?_)).trans (le_of_eq ?_)
  · by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy]
      have h1 := norm_sub_le (f y) (g y)
      have h2 := hfb y
      have h3 := hgb y
      have h4 : 0 ≤ B * τ * maj y := mul_nonneg (mul_nonneg hB hτ) (hmaj0 y)
      linarith
    · rw [Set.indicator_of_notMem hy]
      have := hin y hy
      linarith
  · rw [integral_add (hmaj.const_mul _) (hind.const_mul _), integral_const_mul, integral_const_mul,
      integral_indicator hS]

theorem cont_g {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (m : ℕ) (β : ℂ) (Kc : Set ℂ)
    (Φ : Mat (m + 1 + 1) → V) (bd : Mat (m + 1 + 1) → ℝ) (k : ℕ) (h : DerivBound k (detSet (m + 1) Kc) bd Φ)
    {D z : ℂ} (hD : D ∈ Kc) (hz : z ≠ 0) (hzD : z ^ (m + 2) = (-1) ^ (m + 3) * D) :
    Continuous (fun y : UT (m + 2) → ℂ => ampE β m Φ D 0 (fun _ => z, y)) := by
  have e : (fun y : UT (m + 2) → ℂ => ampE β m Φ D 0 (fun _ => z, y)) = fun y =>
      (((‖z‖ ^ (2 * (m + 1)))⁻¹ : ℝ) : ℂ) • (psi β (superSum (strictUpper y) / z) •
        Φ (wMat (m + 2) * (z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y))) := by
    funext y
    exact ampE_zero m β Φ D z y hz hzD
  rw [e]
  have hpath : Continuous (fun y : UT (m + 2) → ℂ =>
      (wMat (m + 2) * (z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)) :=
    continuous_const.matrix_mul (continuous_const.add (G7.continuous_strictUpper _))
  have hΦc : Continuous (fun y : UT (m + 2) → ℂ =>
      Φ (wMat (m + 2) * (z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y))) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hc : cofXY m 0 ((fun _ => z, y) : XY m) ≠ 0 := by
      rw [← norm_pos_iff, cofXY_zero]
      exact pow_pos (norm_pos_iff.mpr hz) _
    have h1 := (h _ (det_mem m Kc hD 0 _ hc)).1.continuousAt
    rw [MXY_zero m D z y hz hzD] at h1
    exact ContinuousAt.comp (g := Φ) h1 hpath.continuousAt
  have hps : Continuous (fun y : UT (m + 2) → ℂ => psi β (superSum (strictUpper y) / z)) :=
    (G7.continuous_psi β).comp
      (((G7.continuous_superSum (m + 1)).comp (G7.continuous_strictUpper _)).div_const z)
  exact (hps.smul hΦc).const_smul _

theorem arith (a b m : ℕ) {ε A : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / (2 * ((m : ℝ) + 2)))
    (hA : ((4 * (a + b) + 1 : ℕ) : ℝ) * ((m : ℝ) + 2) ^ 2 + 3 * ((m : ℝ) + 2) / ε ≤ A) :
    0 ≤ A ∧ ((4 * (m + 2) * (a + b) : ℕ) : ℝ) + ((m : ℝ) + 2) * ((m : ℝ) + 1) + 1 ≤ A ∧
      1 ≤ -ε * (((4 * (m + 2) * (a + b) : ℕ) : ℝ) + ((m : ℝ) + 2) * ((m : ℝ) + 1) - A) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hε1 : ε ≤ 1 := by
    refine hε.trans ?_
    rw [div_le_one (by positivity)]
    linarith
  set u : ℝ := 3 * ((m : ℝ) + 2) / ε with hu
  have hεu : ε * u = 3 * ((m : ℝ) + 2) := by
    rw [hu]
    field_simp
  have hu1 : 1 ≤ u := by
    rw [hu, le_div_iff₀ hε0]
    linarith
  have hab : (0 : ℝ) ≤ ((a : ℝ) + b) * ((m : ℝ) + 2) * ((m : ℝ) + 1) := by positivity
  have key : ((4 * (m + 2) * (a + b) : ℕ) : ℝ) + ((m : ℝ) + 2) * ((m : ℝ) + 1) + u ≤ A := by
    refine le_trans ?_ hA
    push_cast
    nlinarith
  have hE0 : (0 : ℝ) ≤ ((4 * (m + 2) * (a + b) : ℕ) : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, by linarith, ?_⟩
  · have : (0 : ℝ) ≤ ((m : ℝ) + 2) * ((m : ℝ) + 1) := by positivity
    linarith
  · have h1 : ε * u ≤ ε * (A - ((4 * (m + 2) * (a + b) : ℕ) : ℝ) - ((m : ℝ) + 2) * ((m : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hε0.le
    nlinarith

set_option maxHeartbeats 1000000 in
theorem ampLimit : AmpLimit := by
  obtain ⟨a, b, hcore⟩ := core'
  refine ⟨4 * (a + b) + 1, ?_⟩
  intro m β Kc hK h0 ε hε0 hε
  obtain ⟨t₁, c, Rz, ht₁0, ht₁1, hc0, hRz, hgeom⟩ := geom m Kc hK h0 ε hε0 hε
  obtain ⟨t₂, ht₂0, hcont⟩ := amplitude_continuous_at_critical m β Kc hK h0 ε hε0 hε
  obtain ⟨Cm, hmaj⟩ := majorant_y m (4 * (m + 2) * (a + b)) β
  set cW : ℝ := (4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖) ^ (4 * (m + 2)) + 2 / c with hcW
  have hcW0 : 0 ≤ cW := by positivity
  set C₃ : ℝ := cW ^ (a + b) + (2 / c) ^ 2 with hC₃
  have hC₃0 : 0 ≤ C₃ := by positivity
  refine ⟨3 * C₃ * Cm, min t₁ t₂, lt_min ht₁0 ht₂0, ?_⟩
  intro V _ _ _ Φ A K k hA hk hΦ t D z ht htle hD hzD
  obtain ⟨hA0, hA1, hA2⟩ := arith a b m hε0 hε hA
  obtain ⟨hz0, hzR, hDR, hcz, hcof, hM⟩ := hgeom D hD z hzD t ht (htle.trans (min_le_left _ _))
  have ht0 : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have ht1 : ‖t‖ ≤ 1 := (htle.trans (min_le_left _ _)).trans ht₁1
  have hK0 : 0 ≤ K := K_nonneg m Kc Φ A K k hΦ hD hz0
  obtain ⟨hmi, hmI, hmT⟩ := hmaj A hA1
  set T : ℝ := ‖t‖ ^ (-ε) with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith)
  set maj : (UT (m + 2) → ℂ) → ℝ := fun y => (1 + ‖y‖) ^ (4 * (m + 2) * (a + b)) * (max 1 ‖y‖) ^ (-A) with hmajdef
  have hmx0 : ∀ y : UT (m + 2) → ℂ, 0 ≤ (max 1 ‖y‖) ^ (-A) := fun y =>
    Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  have hmaj0 : ∀ y, 0 ≤ maj y := fun y => mul_nonneg (by positivity) (hmx0 y)
  have hmxle : ∀ y : UT (m + 2) → ℂ, (max 1 ‖y‖) ^ (-A) ≤ maj y := fun y =>
    le_mul_of_one_le_left (hmx0 y) (one_le_pow₀ (by linarith [norm_nonneg y]))
  have hne : ∀ (y : UT (m + 2) → ℂ) (τ' : ℂ), c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖ →
      cofXY m τ' (fun _ => z, y) ≠ 0 := fun y τ' h => by
    rw [← norm_pos_iff]
    linarith
  have hCm0 : 0 ≤ Cm := le_trans (integral_nonneg hmaj0) hmI
  have hprod : ∏ _k : Fin (m + 1), z ≠ 0 := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_ne_zero _ hz0

  have hfb : ∀ y : UT (m + 2) → ℂ, ‖ampIn β m ε Φ D t (fun _ => z, y)‖ ≤ K * C₃ * maj y := by
    intro y
    have h1 := f_bound m β ε Φ D t (fun _ => z, y) (K' := K * (max 1 ‖y‖) ^ (-A)) hc0 ht
      (mul_nonneg hK0 (hmx0 y)) (fun hy => hcof y t hy le_rfl)
      (fun hc => (Phi_DB m Kc Φ A K k 0 hA0 hK0 (Nat.zero_le _) hΦ hD t (fun _ => z, y) hc).norm_le)
    calc ‖ampIn β m ε Φ D t (fun _ => z, y)‖ ≤ (2 / c) ^ 2 * (K * (max 1 ‖y‖) ^ (-A)) := h1
      _ ≤ C₃ * (K * maj y) := by
          refine mul_le_mul ?_ (mul_le_mul_of_nonneg_left (hmxle y) hK0) (mul_nonneg hK0 (hmx0 y)) hC₃0
          rw [hC₃]
          have : 0 ≤ cW ^ (a + b) := by positivity
          linarith
      _ = K * C₃ * maj y := by ring
  have hc00 : ∀ y : UT (m + 2) → ℂ, cofXY m 0 ((fun _ => z, y) : XY m) ≠ 0 := fun y => by
    rw [← norm_pos_iff, cofXY_zero]
    exact pow_pos (norm_pos_iff.mpr hz0) _
  have hgb : ∀ y : UT (m + 2) → ℂ, ‖ampE β m Φ D 0 (fun _ => z, y)‖ ≤ K * C₃ * maj y := by
    intro y
    have h1 := g_bound m β Φ D z y (K' := K * (max 1 ‖y‖) ^ (-A)) hc0 hcz
      (Phi_DB m Kc Φ A K k 0 hA0 hK0 (Nat.zero_le _) hΦ hD 0 (fun _ => z, y) (hc00 y)).norm_le
    calc ‖ampE β m Φ D 0 (fun _ => z, y)‖ ≤ (2 / c) ^ 2 * (K * (max 1 ‖y‖) ^ (-A)) := h1
      _ ≤ C₃ * (K * maj y) := by
          refine mul_le_mul ?_ (mul_le_mul_of_nonneg_left (hmxle y) hK0) (mul_nonneg hK0 (hmx0 y)) hC₃0
          rw [hC₃]
          have : 0 ≤ cW ^ (a + b) := by positivity
          linarith
      _ = K * C₃ * maj y := by ring
  have hin : ∀ y : UT (m + 2) → ℂ, y ∉ {y : UT (m + 2) → ℂ | T ≤ ‖y‖} →
      ‖ampIn β m ε Φ D t (fun _ => z, y) - ampE β m Φ D 0 (fun _ => z, y)‖ ≤ K * C₃ * ‖t‖ * maj y := by
    intro y hy
    have hyT : ‖y‖ ≤ T := by
      exact (not_le.mp hy).le
    rw [f_eq m β ε Φ D t (fun _ => z, y) ht hprod (hM y hyT)]
    have h1 := diff_bound hcore m β D z t y (K' := K * (max 1 ‖y‖) ^ (-A)) Φ hc0 hRz hz0 hzR hDR hcz ht1
      (fun τ' hτ' => hcof y τ' (by linarith) hτ')
      (fun τ' hτ' => Phi_DB m Kc Φ A K k 1 hA0 hK0 hk hΦ hD τ' (fun _ => z, y)
        (hne y τ' (hcof y τ' (by linarith) hτ')))
    refine h1.trans ?_
    calc K * (max 1 ‖y‖) ^ (-A) * cW ^ (a + b) * (1 + ‖y‖) ^ (4 * (m + 2) * (a + b)) * ‖t‖
        = cW ^ (a + b) * (K * ‖t‖ * maj y) := by rw [hmajdef]; ring
      _ ≤ C₃ * (K * ‖t‖ * maj y) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg hK0 ht0.le) (hmaj0 y))
          rw [hC₃]
          have : 0 ≤ (2 / c) ^ 2 := by positivity
          linarith
      _ = K * C₃ * ‖t‖ * maj y := by ring
  have hΦ0 : DerivBound 0 (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ := fun Z hZ =>
    ⟨(hΦ Z hZ).1.of_le (by exact_mod_cast Nat.zero_le k), fun j hj => (hΦ Z hZ).2 j (hj.trans (Nat.zero_le k))⟩
  have hfc := hcont V Φ _ hΦ0 t D z ht (htle.trans (min_le_right _ _)) hD hzD
  have hgc := cont_g m β Kc Φ _ k hΦ hD hz0 hzD
  have hS : MeasurableSet {y : UT (m + 2) → ℂ | T ≤ ‖y‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hmain := int_bound (muPi β (UT (m + 2))) (fun y => ampIn β m ε Φ D t (fun _ => z, y))
    (fun y => ampE β m Φ D 0 (fun _ => z, y)) maj _ hS hfc.aestronglyMeasurable hgc.aestronglyMeasurable hmi hmaj0
    (mul_nonneg hK0 hC₃0) ht0.le hfb hgb hin
  have hgint : ∫ y : UT (m + 2) → ℂ, ampE β m Φ D 0 (fun _ => z, y) ∂(muPi β (UT (m + 2))) =
      (((‖z‖ ^ (2 * (m + 1)))⁻¹ : ℝ) : ℂ) •
        ∫ y : UT (m + 2) → ℂ, psi β (superSum (strictUpper y) / z) •
          Φ (wMat (m + 2) * (z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y))
          ∂(muPi β (UT (m + 2))) := by
    rw [← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    exact ampE_zero m β Φ D z y hz0 hzD
  rw [← hgint]
  refine hmain.trans ?_
  have hTx : T ^ (((4 * (m + 2) * (a + b) : ℕ) : ℝ) + ((m : ℝ) + 2) * ((m : ℝ) + 1) - A) ≤ ‖t‖ := by
    rw [hT, ← Real.rpow_mul ht0.le]
    calc ‖t‖ ^ (-ε * (((4 * (m + 2) * (a + b) : ℕ) : ℝ) + ((m : ℝ) + 2) * ((m : ℝ) + 1) - A)) ≤ ‖t‖ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hA2
      _ = ‖t‖ := Real.rpow_one _
  have htail := (hmT T hT1).trans (mul_le_mul_of_nonneg_left hTx hCm0)
  have hB0 : 0 ≤ K * C₃ := mul_nonneg hK0 hC₃0
  calc K * C₃ * ‖t‖ * ∫ y, maj y ∂(muPi β (UT (m + 2))) +
        2 * (K * C₃) * ∫ y in {y : UT (m + 2) → ℂ | T ≤ ‖y‖}, maj y ∂(muPi β (UT (m + 2)))
      ≤ K * C₃ * ‖t‖ * Cm + 2 * (K * C₃) * (Cm * ‖t‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hmI (mul_nonneg hB0 ht0.le))
          (mul_le_mul_of_nonneg_left htail (by positivity))
    _ = 3 * C₃ * Cm * K * ‖t‖ := by ring

end

end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim

theorem Formalism.FourierDecayAlt.P.amplitude_limit : Formalism.FourierDecayAlt.G.AmpLimit := Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.ampLimit
