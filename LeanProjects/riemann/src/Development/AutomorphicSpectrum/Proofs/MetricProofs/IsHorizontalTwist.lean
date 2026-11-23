import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def Tb (ι : K → Type) : Option K → Type
  | none => Fin 2
  | some k => ι k

instance (o : Option K) : Fintype (Tb ι o) := by
  cases o <;> (unfold Tb; infer_instance)

def basePart₂ (u : (Σ o, Tb ι o) → ℂ) : (Σ k, ι k) → ℂ := fun q => u ⟨some q.1, q.2⟩

def oldIdx (p : Σ k, ι k) : Σ o, Tb ι o := ⟨some p.1, p.2⟩

def inc : MRing ι →+* MRing (Tb ι) :=
  (rename (oldIdx (ι := ι)) : MRing ι →ₐ[ℤ] MRing (Tb ι)).toRingHom

def xN : MRing (Tb ι) := X ⟨none, (0 : Fin 2)⟩

def yN : MRing (Tb ι) := X ⟨none, (1 : Fin 2)⟩

def quad (p : ℕ) : MRing (Tb ι) := xN ^ 2 + C (p : ℤ) * yN ^ 2

def twist (p : ℕ) (W : Ideal (MRing ι)) : Ideal (MRing (Tb ι)) :=
  W.map inc ⊔ Ideal.span {quad p}

def NoRoot (p : ℕ) (W : Ideal (MRing ι)) : Prop :=
  ∀ a b : MRing ι, a ^ 2 + C (p : ℤ) * b ^ 2 ∈ W → b ∈ W

def ret : MRing (Tb ι) →+* MRing ι :=
  (aeval (fun q : Σ o, Tb ι o => match q with
    | ⟨none, _⟩ => (0 : MRing ι)
    | ⟨some k, i⟩ => X ⟨k, i⟩) : MRing (Tb ι) →ₐ[ℤ] MRing ι).toRingHom

theorem ret_inc (f : MRing ι) : ret (inc f) = f := by
  have : (ret.comp inc : MRing ι →+* MRing ι) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ret, inc]
    · intro i; simp [ret, inc, oldIdx]
  exact congrArg (fun g => g f) this

theorem ret_quad (p : ℕ) : ret (quad p : MRing (Tb ι)) = 0 := by
  simp [ret, quad, xN, yN]

theorem twist_le_comap_ret (p : ℕ) (W : Ideal (MRing ι)) : twist p W ≤ W.comap ret := by
  refine sup_le (Ideal.map_le_iff_le_comap.mpr fun f hf => ?_) ?_
  · rw [Ideal.mem_comap, Ideal.mem_comap, ret_inc]; exact hf
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show quad p ∈ W.comap ret
    rw [Ideal.mem_comap, ret_quad]; exact W.zero_mem

theorem comap_inc_twist (p : ℕ) (W : Ideal (MRing ι)) : (twist p W).comap inc = W := by
  refine le_antisymm (fun f hf => ?_) (fun f hf => ?_)
  · have := twist_le_comap_ret p W hf
    simpa [ret_inc] using this
  · exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)

theorem twist_injective (p : ℕ) : Function.Injective (twist p : Ideal (MRing ι) → _) := fun W W' h => by
  rw [← comap_inc_twist p W, h, comap_inc_twist]

def glue (z : (Σ k, ι k) → ℂ) (v : Fin 2 → ℂ) : (Σ o, Tb ι o) → ℂ
  | ⟨none, j⟩ => v j
  | ⟨some k, i⟩ => z ⟨k, i⟩

def cRoot (p : ℕ) : ℂ := Complex.I * (Real.sqrt p : ℝ)

def vPlus (p : ℕ) : Fin 2 → ℂ := ![cRoot p, 1]

def vMinus (p : ℕ) : Fin 2 → ℂ := ![-cRoot p, 1]

def embL (v : Fin 2 → ℂ) :
    (((k : K) → ι k) → ℂ) →ₗ[ℂ] (((o : Option K) → Tb ι o) → ℂ) where
  toFun w := fun J => w (fun k => J (some k)) * v (J none)
  map_add' w w' := by funext J; exact add_mul _ _ _
  map_smul' c w := by funext J; exact mul_assoc _ _ _

def pj {e : ℕ} (v : Fin 2 → ℂ)
    (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
  Ψ ∘ₗ embL v

def chi (p : ℕ) (u : (Σ o, Tb ι o) → ℂ) : ℝ :=
  1 / 2 + ((p : ℝ) + 1) / (2 * Real.sqrt p) *
    ((u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)).im /
      (‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 + ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2))

theorem chi_smul (p : ℕ) (c : Option K → ℂ) (hc : c none ≠ 0) (u : (Σ o, Tb ι o) → ℂ) :
    chi p (fun q => c q.1 * u q) = chi p u := by
  have hn : (0 : ℝ) < ‖c none‖ ^ 2 := by positivity
  have hm : (c none * u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (c none * u ⟨none, (1 : Fin 2)⟩)).im =
      ‖c none‖ ^ 2 * (u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)).im := by
    have : c none * u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (c none * u ⟨none, (1 : Fin 2)⟩) =
        ((‖c none‖ ^ 2 : ℝ) : ℂ) * (u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)) := by
      rw [map_mul, Complex.ofReal_pow, ← Complex.mul_conj']
      ring
    rw [this, Complex.im_ofReal_mul]
  simp only [chi, norm_mul, mul_pow, hm, ← mul_add]
  rw [mul_div_mul_left _ _ hn.ne']

theorem oldPart_ne {u : (Σ o, Tb ι o) → ℂ} (hu : ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0) (k : K) :
    ∃ i, basePart₂ u ⟨k, i⟩ ≠ 0 := hu (some k)

open Classical in

def twH (p : ℕ) (A : HermLine ι) (u : (Σ o, Tb ι o) → ℂ) : ℝ :=
  if ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0 then
    Real.exp (chi p u * Real.log (A.h (basePart₂ u)) +
      (1 - chi p u) * Real.log (A.h fun q => starRingEnd ℂ (basePart₂ u q)))
  else 0

def conjLine (A : HermLine ι) : HermLine ι where
  a := A.a
  h z := A.h fun q => starRingEnd ℂ (z q)
  pos z hz := A.pos _ fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact ⟨i, by simpa using hi⟩
  smul c z hc := by
    have h1 := A.smul (fun k => starRingEnd ℂ (c k)) (fun q => starRingEnd ℂ (z q))
      (fun k => by simpa using hc k)
    simp only [RCLike.norm_conj] at h1
    simpa only [map_mul] using h1

def invLine (A : HermLine ι) : HermLine ι where
  a := -A.a
  h z := (A.h z)⁻¹
  pos z hz := inv_pos.mpr (A.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [zpow_neg]

def twDeg (a : K → ℤ) : Option K → ℤ
  | none => 0
  | some k => a k

theorem log_smul_old (A : HermLine ι) (c : K → ℂ) (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun q => c q.1 * z q) = ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ + Real.log (A.h z) := by
  rw [A.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ =>
    zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))) (A.pos z hz).ne',
    Real.log_prod (fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k)))]
  simp only [Real.log_zpow]

def twLine (p : ℕ) (A : HermLine ι) : HermLine (Tb ι) where
  a := twDeg A.a
  h := twH p A
  pos z hz := by
    rw [twH, if_pos hz]; exact Real.exp_pos _
  smul c z hc := by
    classical
    have hsame : (∀ o, ∃ i, (fun q : Σ o, Tb ι o => c q.1 * z q) ⟨o, i⟩ ≠ 0) ↔
        ∀ o, ∃ i, z ⟨o, i⟩ ≠ 0 := by
      refine forall_congr' fun o => exists_congr fun i => ?_
      simp [hc o]
    by_cases hz : ∀ o, ∃ i, z ⟨o, i⟩ ≠ 0
    · rw [twH, twH, if_pos (hsame.mpr hz), if_pos hz, chi_smul p c (hc none)]
      have hz1 : ∀ k, ∃ i, basePart₂ z ⟨k, i⟩ ≠ 0 := oldPart_ne hz
      have hz2 : ∀ k, ∃ i, (fun q => starRingEnd ℂ (basePart₂ z q)) ⟨k, i⟩ ≠ 0 := fun k => by
        obtain ⟨i, hi⟩ := hz1 k
        exact ⟨i, by simpa using hi⟩
      have e1 : basePart₂ (fun q : Σ o, Tb ι o => c q.1 * z q) =
          fun q => (fun k => c (some k)) q.1 * basePart₂ z q := rfl
      have e2 : (fun q => starRingEnd ℂ (basePart₂ (fun q : Σ o, Tb ι o => c q.1 * z q) q)) =
          fun q => (fun k => starRingEnd ℂ (c (some k))) q.1 * starRingEnd ℂ (basePart₂ z q) := by
        funext q; simp [basePart₂]
      rw [e2, e1, log_smul_old A _ (fun k => hc (some k)) hz1,
        log_smul_old A (fun k => starRingEnd ℂ (c (some k))) (fun k => by simpa using hc (some k))
          (z := fun q => starRingEnd ℂ (basePart₂ z q)) hz2]
      have hprod : (∏ o, ‖c o‖ ^ twDeg A.a o) = Real.exp (∑ k, (A.a k : ℝ) * Real.log ‖c (some k)‖) := by
        rw [Fintype.prod_option, Real.exp_sum]
        simp only [twDeg, zpow_zero, one_mul]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [mul_comm, Real.exp_mul, Real.exp_log (norm_pos_iff.mpr (hc (some k))), Real.rpow_intCast]
      rw [hprod, ← Real.exp_add]
      congr 1
      simp only [RCLike.norm_conj]
      ring
    · rw [twH, twH, if_neg (fun h => hz (hsame.mp h)), if_neg hz, mul_zero]

theorem eval_inc (z : (Σ k, ι k) → ℂ) (v : Fin 2 → ℂ) (f : MRing ι) :
    eval (glue z v) (map (Int.castRingHom ℂ) (inc f)) = eval z (map (Int.castRingHom ℂ) f) := by
  simp only [inc, RingHom.coe_coe, AlgHom.toRingHom_eq_coe]
  rw [map_rename, eval_rename]
  rfl

theorem eval_quad (z : (Σ o, Tb ι o) → ℂ) (p : ℕ) :
    eval z (map (Int.castRingHom ℂ) (quad p : MRing (Tb ι))) =
      z ⟨none, (0 : Fin 2)⟩ ^ 2 + (p : ℂ) * z ⟨none, (1 : Fin 2)⟩ ^ 2 := by
  simp [quad, xN, yN]

theorem segre_glue (z : (Σ k, ι k) → ℂ) (v : Fin 2 → ℂ) :
    segre (glue z v) = embL v (segre z) := by
  funext J
  show ∏ o, glue z v ⟨o, J o⟩ = (∏ k, z ⟨k, J (some k)⟩) * v (J none)
  rw [Fintype.prod_option, mul_comm]
  rfl

theorem glue_mem_mcPts {p : ℕ} {Q : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts Q)
    {v : Fin 2 → ℂ} (hv : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0) (hv1 : v 1 ≠ 0) :
    glue z v ∈ mcPts (twist p Q) := by
  refine ⟨fun o => ?_, fun f hf => ?_⟩
  · cases o with
    | none => exact ⟨(1 : Fin 2), hv1⟩
    | some k => exact hz.1 k
  · have hle : twist p Q ≤ RingHom.ker ((eval (glue z v)).comp (map (Int.castRingHom ℂ))) := by
      refine sup_le (Ideal.map_le_iff_le_comap.mpr fun g hg => ?_) ?_
      · show eval (glue z v) (map (Int.castRingHom ℂ) (inc g)) = 0
        rw [eval_inc]; exact hz.2 g hg
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        show eval (glue z v) (map (Int.castRingHom ℂ) (quad p)) = 0
        rw [eval_quad]; exact hv
    exact hle hf

theorem cRoot_sq (p : ℕ) : cRoot p ^ 2 = -(p : ℂ) := by
  rw [cRoot, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
  simp

theorem vPlus_root (p : ℕ) : vPlus p 0 ^ 2 + (p : ℂ) * vPlus p 1 ^ 2 = 0 := by
  simp [vPlus, cRoot_sq]

theorem vMinus_root (p : ℕ) : vMinus p 0 ^ 2 + (p : ℂ) * vMinus p 1 ^ 2 = 0 := by
  simp [vMinus, cRoot_sq]

theorem xN_not_mem_twist (p : ℕ) {W : Ideal (MRing ι)} (hW : W ≠ ⊤) :
    (xN : MRing (Tb ι)) ∉ twist p W := by
  classical
  haveI : Nontrivial (MRing ι ⧸ W) := Ideal.Quotient.nontrivial_iff.mpr hW
  let θ : MRing (Tb ι) →+* Polynomial (MRing ι ⧸ W) :=
    (aeval (fun q : Σ o, Tb ι o => match q with
      | ⟨none, j⟩ => if j = (0 : Fin 2) then Polynomial.X else 0
      | ⟨some k, i⟩ => Polynomial.C (Ideal.Quotient.mk W (X ⟨k, i⟩))) :
        MRing (Tb ι) →ₐ[ℤ] Polynomial (MRing ι ⧸ W)).toRingHom
  have hinc : ∀ f : MRing ι, θ (inc f) = Polynomial.C (Ideal.Quotient.mk W f) := by
    intro f
    have : (θ.comp inc) = (Polynomial.C.comp (Ideal.Quotient.mk W)) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [θ, inc]
      · intro i; simp [θ, inc, oldIdx]
    exact congrArg (fun g => g f) this
  have h1 : θ (xN) = Polynomial.X := by
    simp only [θ, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    exact if_pos rfl
  have h2 : θ (yN) = 0 := by
    simp only [θ, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    exact if_neg (show ¬ ((1 : Fin 2) = 0) by decide)
  have hle : twist p W ≤ (Ideal.span {(Polynomial.X : Polynomial (MRing ι ⧸ W)) ^ 2}).comap θ := by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr fun f hf => ?_) ?_
    · rw [Ideal.mem_comap, Ideal.mem_comap, hinc, Ideal.Quotient.eq_zero_iff_mem.mpr hf]
      simp
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show quad p ∈ (Ideal.span {(Polynomial.X : Polynomial (MRing ι ⧸ W)) ^ 2}).comap θ
      rw [Ideal.mem_comap]
      simp only [quad, map_add, map_mul, map_pow, h1, h2]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
      exact Ideal.mem_span_singleton_self _
  intro hx
  have h3 := hle hx
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at h3
  rw [h1, Polynomial.X_pow_dvd_iff] at h3
  have := h3 1 (by norm_num)
  simp at this

theorem isRelevant_twist (p : ℕ) {W : Ideal (MRing ι)} (hW : W ≠ ⊤) (hr : IsRelevant W) :
    IsRelevant (twist p W) := by
  intro o
  cases o with
  | none => exact ⟨(0 : Fin 2), xN_not_mem_twist p hW⟩
  | some k =>
    obtain ⟨i, hi⟩ := hr k
    refine ⟨i, fun h => hi ?_⟩
    have : inc (X ⟨k, i⟩ : MRing ι) ∈ twist p W := by
      simpa [inc, oldIdx] using h
    rw [← comap_inc_twist p W]
    exact this

theorem isHorizontal_twist (p : ℕ) {W : Ideal (MRing ι)} (hW : IsHorizontal W) :
    IsHorizontal (twist p W) := by
  rw [IsHorizontal, eq_bot_iff] at hW ⊢
  intro n hn
  refine hW ?_
  have := twist_le_comap_ret p W hn
  simpa [ret] using this

end GlobalTheory.CompanionTheory.Ar.Tw
