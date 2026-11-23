import Formalism.LocalToGlobal.Columns.ChainLawPhiA
import Formalism.LocalToGlobal.Columns.OcbTIntOfStab
import Formalism.LocalToGlobal.Columns.FirstUnfoldingEqZeroOfNotIntegral

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

section ClPfAssoc

variable {k : Type} [CommRing k]

theorem clPf_mul_assoc (N A : ℕ) (G X C : ℕ → ℕ → k) :
    clPfMul A (clPfMul N G X) C = clPfMul N G (clPfMul A X C) := by
  funext p p'
  unfold clPfMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

end ClPfAssoc

section ClPfE

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem clPf_sum_fIdx {M : Type} [AddCommMonoid M] {k₀ c n : ℕ} (hk : k₀ ≤ n) (f : ℕ → M) :
    ∑ u ∈ Finset.range (n + c), f (LocE.fIdx k₀ c n u) = ∑ u ∈ Finset.range (n + c), f u :=
  Finset.sum_nbij' (fun u => LocE.fIdx k₀ c n u) (fun u => LocE.fPos k₀ c n u)
    (fun _ ha => Finset.mem_range.2 (symFIdx_lt hk (Finset.mem_range.1 ha)))
    (fun _ ha => Finset.mem_range.2 (framePos_lt hk (Finset.mem_range.1 ha)))
    (fun _ ha => symFPos_fIdx hk (Finset.mem_range.1 ha)) (fun _ ha => frameIndex_framePos hk (Finset.mem_range.1 ha)) (fun _ _ => rfl)

theorem clPf_bEnt_compR (hq0 : (q : E) ≠ 0) {n' c' n c : ℕ} (y : HomE E (n' + c') (n + c)) (κ : Sp E (n' + c') →ₗ[E] Sp E (n' + c'))
    {l s : ℕ} (hl : l < n + c) (hs : s < n' + c') :
    ocbBEnt n' n q (y ∘ₗ κ) l s = ∑ m : Fin (n' + c'), ocbBEnt n' n q y l m.1 * ocbBEnt n' n' q κ m.1 s := by
  unfold ocbBEnt
  rw [ocbS_atN_comp y κ hl hs, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) l =
      (LocE.scE n' (fun i => i + 1) m.1 - LocE.scE n (fun i => i + 1) l) +
        (LocE.scE n' (fun i => i + 1) s - LocE.scE n' (fun i => i + 1) m.1) := by ring
  rw [e, zpow_add₀ hq0]
  ring

theorem clPf_entB_compL (hq0 : (q : E) ≠ 0) {k₀ n' c' n c : ℕ} (hk : k₀ ≤ n) (hk' : k₀ ≤ n') (g : Sp E (n + c) →ₗ[E] Sp E (n + c))
    (y : HomE E (n' + c') (n + c)) {p p' : ℕ} (hp : p < n + c) (hp' : p' < n' + c') :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (g ∘ₗ y) p p' =
      ∑ u ∈ Finset.range (n + c), LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) g p u *
        LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) y u p' := by
  rw [ocbBEnt_entB, ocbT_bEnt_comp hq0 g y (symFIdx_lt hk hp) (symFIdx_lt hk' hp'),
    Fin.sum_univ_eq_sum_range (fun m => ocbBEnt n n q g (LocE.fIdx k₀ c n p) m * ocbBEnt n' n q y m (LocE.fIdx k₀ c' n' p')) (n + c),
    ← clPf_sum_fIdx hk]
  rfl

theorem clPf_entB_compR (hq0 : (q : E) ≠ 0) {k₀ n' c' n c : ℕ} (hk : k₀ ≤ n) (hk' : k₀ ≤ n') (y : HomE E (n' + c') (n + c))
    (κ : Sp E (n' + c') →ₗ[E] Sp E (n' + c')) {p p' : ℕ} (hp : p < n + c) (hp' : p' < n' + c') :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (y ∘ₗ κ) p p' =
      ∑ v ∈ Finset.range (n' + c'), LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) y p v *
        LocE.entB q k₀ c' n' c' n' (fun i => i + 1) (fun i => i + 1) κ v p' := by
  rw [ocbBEnt_entB, clPf_bEnt_compR hq0 y κ (symFIdx_lt hk hp) (symFIdx_lt hk' hp'),
    Fin.sum_univ_eq_sum_range (fun m => ocbBEnt n' n q y (LocE.fIdx k₀ c n p) m * ocbBEnt n' n' q κ m (LocE.fIdx k₀ c' n' p')) (n' + c'),
    ← clPf_sum_fIdx hk']
  rfl

def clPfRed (P : HeightOneSpectrum (𝓞 E)) (q k₀ c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) : ℕ → ℕ → 𝓞 E ⧸ P.asIdeal :=
  fun p p' => redP P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p')

theorem clPf_red_comp (hq0 : (q : E) ≠ 0) {k₀ n' c' n c : ℕ} (hk : k₀ ≤ n) (hk' : k₀ ≤ n')
    {γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hγ : γ ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1))
    {κ : Sp E (n' + c') ≃ₗ[E] Sp E (n' + c')} (hκ : κ ∈ stabL E (n' + c') (LocE.lamY P q n' c' fun i => i + 1))
    {x : HomE E (n' + c') (n + c)}
    (hx : ∀ p p', p < n + c → p' < n' + c' → IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p'))
    {p p' : ℕ} (hp : p < n + c) (hp' : p' < n' + c') :
    IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap) p p') ∧
      clPfRed P q k₀ c' n' c n (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap) p p' =
        clPfMul (n + c) (clPfRed P q k₀ c n c n γ.toLinearMap) (clPfMul (n' + c') (clPfRed P q k₀ c' n' c n x)
          (clPfRed P q k₀ c' n' c' n' κ.toLinearMap)) p p' := by
  have hG : ∀ u, u < n + c → IntAt P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) γ.toLinearMap p u) :=
    fun u hu => frameEntry_integral_of_stabilizer hq0 hk hp hu hγ
  have hK : ∀ u v, u < n' + c' → v < n' + c' → IntAt P (LocE.entB q k₀ c' n' c' n' (fun i => i + 1) (fun i => i + 1) κ.toLinearMap u v) :=
    fun u v hu hv => frameEntry_integral_of_stabilizer hq0 hk' hu hv hκ
  have hin : ∀ u, u < n + c → IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (x ∘ₗ κ.toLinearMap) u p') ∧
      redP P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (x ∘ₗ κ.toLinearMap) u p') =
        clPfMul (n' + c') (clPfRed P q k₀ c' n' c n x) (clPfRed P q k₀ c' n' c' n' κ.toLinearMap) u p' := by
    intro u hu
    rw [clPf_entB_compR hq0 hk hk' x κ.toLinearMap hu hp']
    have hI : ∀ v ∈ Finset.range (n' + c'), IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x u v *
        LocE.entB q k₀ c' n' c' n' (fun i => i + 1) (fun i => i + 1) κ.toLinearMap v p') :=
      fun v hv => (hx u v hu (Finset.mem_range.1 hv)).mul (hK v p' (Finset.mem_range.1 hv) hp')
    refine ⟨ciIntAt_sum _ _ hI, ?_⟩
    rw [redP_sum _ _ hI]
    refine Finset.sum_congr rfl fun v hv => ?_
    exact reduction_mul (hx u v hu (Finset.mem_range.1 hv)) (hK v p' (Finset.mem_range.1 hv) hp')
  rw [clPf_entB_compL hq0 hk hk' γ.toLinearMap (x ∘ₗ κ.toLinearMap) hp hp']
  have hI : ∀ u ∈ Finset.range (n + c), IntAt P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) γ.toLinearMap p u *
      LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (x ∘ₗ κ.toLinearMap) u p') :=
    fun u hu => (hG u (Finset.mem_range.1 hu)).mul (hin u (Finset.mem_range.1 hu)).1
  refine ⟨ciIntAt_sum _ _ hI, ?_⟩
  unfold clPfRed
  rw [clPf_entB_compL hq0 hk hk' γ.toLinearMap (x ∘ₗ κ.toLinearMap) hp hp', redP_sum _ _ hI]
  unfold clPfMul
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [reduction_mul (hG u (Finset.mem_range.1 hu)) (hin u (Finset.mem_range.1 hu)).1, (hin u (Finset.mem_range.1 hu)).2]
  rfl

end ClPfE

section ClPfCast

variable {k : Type} [CommRing k] {k₀ rS r t : ℕ}

theorem clPf_pat_cast {X : ℕ → ℕ → k} {N A N' A' : ℕ} (hN : N = N') (hA : A = A') (h : clPfPat k₀ rS r t N A X) :
    clPfPat k₀ rS r t N' A' X := by
  subst hN hA
  exact h

theorem clPf_mul_cast {X Y : ℕ → ℕ → k} {N N' : ℕ} (h : N = N') : clPfMul N X Y = clPfMul N' X Y := by
  subst h
  rfl

theorem clPf_top_cast (X : ℕ → ℕ → k) {A A' : ℕ} (h : A = A') : (clPfTop A X).det = (clPfTop A' X).det := by
  subst h
  rfl

theorem clPf_pat_congr {X Y : ℕ → ℕ → k} {N A : ℕ} (hrA : r ≤ A) (hAN : A ≤ N) (h : ∀ p p', p < N → p' < A → X p p' = Y p p')
    (hX : clPfPat k₀ rS r t N A X) : clPfPat k₀ rS r t N A Y := by
  refine ⟨fun p' hp' => ?_, fun p p' hp hp' hne hnz => hX.2 p p' hp hp' hne (by rw [h p p' hp hp']; exact hnz)⟩
  rw [← h p' p' (by omega) (by omega)]
  exact hX.1 p' hp'

theorem clPf_lam_congr {K : Type} [Field K] (ψ₀ : AddChar k K) (χ : ℕ → kˣ →* Kˣ) {J A : ℕ} (hk : k₀ ≤ r) (hJ : r + J * t ≤ A)
    {X Y : ℕ → ℕ → k} (h : ∀ p p', p < A → p' < A → X p p' = Y p p') :
    clPfLam ψ₀ χ k₀ r t J X = clPfLam ψ₀ χ k₀ r t J Y := by
  have hrA : r ≤ A := le_trans (Nat.le_add_right r _) hJ
  unfold clPfLam clPfS
  congr 1
  · congr 1
    congr 1
    · exact Finset.sum_congr rfl fun i hi => h _ _ (by have := Finset.mem_range.1 hi; omega) (by have := Finset.mem_range.1 hi; omega)
    · exact Finset.sum_congr rfl fun i hi => h _ _ (by have := Finset.mem_range.1 hi; omega) (by have := Finset.mem_range.1 hi; omega)
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    have hit : r + i * t + t ≤ A := by
      have : (i + 1) * t ≤ J * t := Nat.mul_le_mul_right t hi'
      rw [Nat.add_mul, one_mul] at this
      omega
    congr 2
    ext s s'
    exact h _ _ (by have := s.2; omega) (by have := s'.2; omega)

theorem clPf_top_congr {A : ℕ} {X Y : ℕ → ℕ → k} (h : ∀ p p', p < A → p' < A → X p p' = Y p p') : clPfTop A X = clPfTop A Y := by
  ext s s'
  exact h _ _ s.2 s'.2

end ClPfCast

section ClPfVal

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem clPf_unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : LocE.unitV χ a = clPfUV χ (redP P a) := by
  unfold LocE.unitV clPfUV
  by_cases h : IsUnit (redP P a)
  · simp only [dif_pos h]
  · simp only [dif_neg h]

theorem clPf_cond_iff (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {k₀ rS r t j c n : ℕ}
    (hr : k₀ + rS < r) (han : r + (j - 1) * t ≤ n + c) (M : ℕ → ℕ → E) :
    symPhiCond P q k₀ rS r t j c n M ↔
      (∀ p p', p < n + c → p' < r + (j - 1) * t → IntAt P (M p p')) ∧
        clPfPat k₀ rS r t (n + c) (r + (j - 1) * t) (fun p p' => redP P (M p p')) := by
  have hq0 := ciQ_ne_zero hu
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, fun p' hp' => (h3 p' hp').1, fun p p' hp hp' hne hnz => ?_⟩
    have hpa : p < r + (j - 1) * t := by
      by_contra hpa
      exact hnz (ciRed_of_div hq hq0 (h2 p p' (not_lt.1 hpa) hp hp')).2
    have hb : betaExponentOfRanks k₀ rS r t p ≤ betaExponentOfRanks k₀ rS r t p' := by
      by_contra hlt
      rw [not_le] at hlt
      by_cases hp'r : p' < r
      · apply hnz
        refine (h3 p' hp'r).2 p hpa hne ?_
        by_cases hpr : p < r
        · right; left
          unfold betaExponentOfRanks at hlt
          rwa [if_pos hp'r, if_pos hpr] at hlt
        · left; omega
      · by_cases hpr : p < r
        · have h5 := (clPf_beta_lt_iff (t := t) hr p).2 hpr
          have h6 := (clPf_beta_lt_iff (t := t) hr p').not.2 hp'r
          omega
        · rw [clPf_beta_of_ge (not_lt.1 hpr), clPf_beta_of_ge (not_lt.1 hp'r)] at hlt
          exact hnz (h4 p p' (not_lt.1 hp'r) hp' hpa (by omega))
    refine ⟨hpa, hb, fun ⟨e1, e2⟩ => hnz ((h3 p' (by omega)).2 p hpa hne (Or.inr (Or.inr ⟨e1, e2⟩)))⟩
  · rintro ⟨h1, hD, hO⟩
    refine ⟨h1, fun p p' h0 hp hp' => ?_, fun p' hp' => ⟨hD p' hp', fun p hp hne hor => ?_⟩, fun p p' hrp' hp' hp hlt => ?_⟩
    · have hz : redP P (M p p') = 0 := by
        by_contra hnz
        have := (hO p p' hp hp' (by omega) hnz).1
        omega
      exact ciIntAt_div hq hu (h1 p p' hp hp') hz
    · by_contra hnz
      obtain ⟨-, hb, he⟩ := hO p p' (by omega) (by omega) hne hnz
      rcases hor with h | h | h
      · have h5 := (clPf_beta_lt_iff (t := t) hr p).not.2 (by omega)
        have h6 := (clPf_beta_lt_iff (t := t) hr p').2 hp'
        omega
      · by_cases hpr : p < r
        · unfold betaExponentOfRanks at hb
          rw [if_pos hpr, if_pos hp'] at hb
          omega
        · have h5 := (clPf_beta_lt_iff (t := t) hr p).not.2 hpr
          have h6 := (clPf_beta_lt_iff (t := t) hr p').2 hp'
          omega
      · exact he h
    · by_contra hnz
      have hne : p ≠ p' := by
        rintro rfl
        exact lt_irrefl _ hlt
      obtain ⟨-, hb, -⟩ := hO p p' (by omega) hp' hne hnz
      by_cases hpr : p < r
      · have e0 : (p - r) / t = 0 := by rw [show p - r = 0 by omega, Nat.zero_div]
        rw [e0] at hlt
        exact absurd hlt (Nat.not_lt_zero _)
      · rw [clPf_beta_of_ge (not_lt.1 hpr), clPf_beta_of_ge hrp'] at hb
        omega

theorem clPf_lamGvS (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r t J : ℕ} (hkr : k₀ < r)
    (M : ℕ → ℕ → E) (hM : ∀ p p', p < r + J * t → p' < r + J * t → IntAt P (M p p')) :
    LocE.lamGvS ψ₀ χ k₀ r t J M = clPfLam ψ₀ χ k₀ r t J (fun p p' => redP P (M p p')) := by
  unfold LocE.lamGvS clPfLam clPfS
  rw [reduction_sum_superdiagonal hkr M fun p hp => hM p (p + 1) (by omega) (by omega)]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have hit : r + i * t + t ≤ r + J * t := by
    have : (i + 1) * t ≤ J * t := Nat.mul_le_mul_right t hi'
    rw [Nat.add_mul, one_mul] at this
    omega
  rw [clPf_unitV, redP_det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1))
    fun s s' => hM _ _ (by have := s.2; omega) (by have := s'.2; omega)]
  rfl

theorem clPf_phiGS_val (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ rS r t j c' n' c n : ℕ}
    (hkr : k₀ < r) (han : r + (j - 1) * t ≤ n + c) (x : HomE E (n' + c') (n + c))
    (hC : symPhiCond P q k₀ rS r t j c n (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x)) :
    LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n x =
      clPfLam ψ₀ χ k₀ r t (j - 1) (clPfRed P q k₀ c' n' c n x) *
        (clPfUV (χ (j - 1)) (clPfTop (r + (j - 1) * t) (clPfRed P q k₀ c' n' c n x)).det)⁻¹ := by
  rw [phiGS_eq, if_pos hC, clPf_lamGvS ψ₀ χ hkr _ (fun p p' hp hp' => hC.1 p p' (by omega) hp'), clPf_unitV,
    redP_det (Matrix.of fun s s' : Fin (r + (j - 1) * t) => LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x s.1 s'.1)
      fun s s' => hC.1 _ _ (by have := s.2; omega) s'.2]
  rfl

theorem clPf_lamGBS (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r t J n c : ℕ}
    (hk : k₀ ≤ n) (hkr : k₀ < r) (hJ : r + J * t ≤ n + c) {γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hγ : γ ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1)) :
    LocE.lamGBS q ψ₀ χ k₀ r t J n c γ.toLinearMap = clPfLam ψ₀ χ k₀ r t J (clPfRed P q k₀ c n c n γ.toLinearMap) := by
  unfold LocE.lamGBS
  exact clPf_lamGvS ψ₀ χ hkr _ (fun p p' hp hp' => frameEntry_integral_of_stabilizer hq0 hk (by omega) (by omega) hγ)

theorem clPf_top_ob2M {k₀ n c : ℕ} (hk : k₀ ≤ n) (γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    (clPfTop (n + c) (clPfRed P q k₀ c n c n γ.toLinearMap)).det = (ob2M P q γ).det := by
  let eσ : Fin (n + c) ≃ Fin (n + c) :=
    { toFun := fun s => ⟨LocE.fIdx k₀ c n s.1, symFIdx_lt hk s.2⟩
      invFun := fun l => ⟨LocE.fPos k₀ c n l.1, framePos_lt hk l.2⟩
      left_inv := fun s => Fin.ext (symFPos_fIdx hk s.2)
      right_inv := fun l => Fin.ext (frameIndex_framePos hk l.2) }
  have h1 : clPfTop (n + c) (clPfRed P q k₀ c n c n γ.toLinearMap) = (ob2M P q γ).submatrix eσ eσ := by
    ext s s'
    exact reduction_frameEntry_eq_matrix hk s.2 s'.2 γ
  rw [h1, Matrix.det_submatrix_equiv_self]

theorem clPf_det_red (hq0 : (q : E) ≠ 0) {k₀ n c : ℕ} (hk : k₀ ≤ n) {γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hγ : γ ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1)) :
    redP P ((LinearEquiv.det γ : Eˣ) : E) = (clPfTop (n + c) (clPfRed P q k₀ c n c n γ.toLinearMap)).det := by
  rw [clPf_top_ob2M hk]
  have h2 : ob2M P q γ = (Matrix.of fun l l' : Fin (n + c) => γ (Pi.single l' 1) l *
      (q : E) ^ (LocE.scE n (fun i => i + 1) l'.1 - LocE.scE n (fun i => i + 1) l.1)).map (redP P) := rfl
  rw [h2, ← redP_det (Matrix.of fun l l' : Fin (n + c) => γ (Pi.single l' 1) l *
      (q : E) ^ (LocE.scE n (fun i => i + 1) l'.1 - LocE.scE n (fun i => i + 1) l.1)) fun l l' => scaledCoord_integral_of_stabilizer hq0 hγ l l']
  congr 1
  have h3 : (Matrix.of fun l l' : Fin (n + c) => γ (Pi.single l' 1) l *
      (q : E) ^ (LocE.scE n (fun i => i + 1) l'.1 - LocE.scE n (fun i => i + 1) l.1)) =
      Matrix.diagonal (fun l : Fin (n + c) => ((q : E) ^ LocE.scE n (fun i => i + 1) l.1)⁻¹) * LinearMap.toMatrix' γ.toLinearMap *
        Matrix.diagonal (fun l : Fin (n + c) => (q : E) ^ LocE.scE n (fun i => i + 1) l.1) := by
    ext l l'
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, LinearMap.toMatrix'_apply, Matrix.of_apply, zpow_sub₀ hq0]
    simp only [LinearEquiv.coe_coe]
    field_simp
  have hd : ∏ l : Fin (n + c), (q : E) ^ LocE.scE n (fun i => i + 1) l.1 ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => zpow_ne_zero _ hq0
  rw [h3, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, LinearMap.det_toMatrix', Finset.prod_inv_distrib,
    LinearEquiv.coe_det]
  field_simp

theorem clPf_det_unit (hq0 : (q : E) ≠ 0) {k₀ n c : ℕ} (hk : k₀ ≤ n) {γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hγ : γ ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1)) :
    IsUnit (clPfTop (n + c) (clPfRed P q k₀ c n c n γ.toLinearMap)).det := by
  rw [clPf_top_ob2M hk]
  refine Matrix.isUnit_det_of_right_inverse (B := ob2M P q γ⁻¹) ?_
  rw [← reducedMatrix_mul hq0 hγ (Subgroup.inv_mem _ hγ), mul_inv_cancel, reducedMatrix_one]

theorem clPf_pat_JGsym (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {k₀ rS r t n c : ℕ}
    (hk : k₀ ≤ n) (hr : k₀ + rS < r) (hrN : r ≤ n + c) {γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hγ : γ ∈ LocE.JGsym P q k₀ rS r t n c) :
    clPfPat k₀ rS r t (n + c) (n + c) (clPfRed P q k₀ c n c n γ.toLinearMap) := by
  refine ⟨fun p' hp' => ?_, fun p p' hp hp' hne hnz => ⟨hp, ?_, ?_⟩⟩
  · unfold clPfRed
    rw [reduction_frameEntry_eq_matrix hk (by omega) (by omega)]
    exact reducedMatrix_parahoric_diag_one hq hu hk hr hγ _ (by rw [symFPos_fIdx hk (by omega)]; exact hp')
  · by_contra hlt
    apply hnz
    unfold clPfRed
    rw [reduction_frameEntry_eq_matrix hk hp hp']
    refine reducedMatrix_parahoric_blockTriangular hq hu hk hr hγ ?_
    show betaExponentOfRanks k₀ rS r t (LocE.fPos k₀ c n (LocE.fIdx k₀ c n p')) < betaExponentOfRanks k₀ rS r t (LocE.fPos k₀ c n (LocE.fIdx k₀ c n p))
    rw [symFPos_fIdx hk hp', symFPos_fIdx hk hp]
    omega
  · rintro ⟨e1, e2⟩
    apply hnz
    unfold clPfRed
    rw [reduction_frameEntry_eq_matrix hk hp hp']
    exact reducedMatrix_parahoric_corner_zero hq hu hk hr hγ _ _ (by rw [symFPos_fIdx hk hp]; exact e2) (by rw [symFPos_fIdx hk hp']; exact e1)

end ClPfVal

section ClPfLaw

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem clPf_main {P : HeightOneSpectrum (𝓞 E)} {q k₀ rS r t j c' n' c n : ℕ} (h : PhiGSLawHyp P q k₀ rS r t j c' n' c n)
    (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hγ : γ ∈ LocE.JGsym P q k₀ rS r t n c)
    {κ : Sp E (n' + c') ≃ₗ[E] Sp E (n' + c')} (hκ : κ ∈ LocE.JGsym P q k₀ rS r t n' c') (x : HomE E (n' + c') (n + c))
    (hC : symPhiCond P q k₀ rS r t j c n (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x)) :
    symPhiCond P q k₀ rS r t j c n (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap)) ∧
      LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap) =
        LocE.lamGBS q ψ₀ χ k₀ r t j n c γ.toLinearMap * (LocE.unitV (χ (j - 1)) ((LinearEquiv.det γ : Eˣ) : E))⁻¹ *
          (LocE.lamGBS q ψ₀ χ k₀ r t (j - 1) n' c' κ.toLinearMap * (LocE.unitV (χ (j - 1)) ((LinearEquiv.det κ : Eˣ) : E))⁻¹) *
            LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n x := by
  obtain ⟨hq, hu, hj, hk', hk, hr, ht, hsrc, htgt⟩ := h
  have hq0 := ciQ_ne_zero hu
  have hBt : n + c = r + (j - 1) * t + t := by
    rw [htgt]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  have hra : r ≤ r + (j - 1) * t := Nat.le_add_right _ _
  have hkr : k₀ < r := by omega
  have hrN : r ≤ n + c := by omega
  have hrN' : r ≤ n' + c' := by omega
  obtain ⟨hXI, hXP⟩ := (clPf_cond_iff hq hu hr (by omega) _).1 hC
  have hGP : clPfPat k₀ rS r t (r + (j - 1) * t + t) (r + (j - 1) * t + t) (clPfRed P q k₀ c n c n γ.toLinearMap) :=
    clPf_pat_cast hBt hBt (clPf_pat_JGsym hq hu hk hr hrN hγ)
  have hKP : clPfPat k₀ rS r t (r + (j - 1) * t) (r + (j - 1) * t) (clPfRed P q k₀ c' n' c' n' κ.toLinearMap) :=
    clPf_pat_cast hsrc hsrc (clPf_pat_JGsym hq hu hk' hr hrN' hκ)
  have hXP' : clPfPat k₀ rS r t (r + (j - 1) * t + t) (r + (j - 1) * t) (clPfRed P q k₀ c' n' c n x) := clPf_pat_cast hBt rfl hXP
  have hGu : IsUnit (clPfTop (r + (j - 1) * t + t) (clPfRed P q k₀ c n c n γ.toLinearMap)).det := by
    rw [← clPf_top_cast _ hBt]
    exact clPf_det_unit hq0 hk hγ.1
  obtain ⟨hpat, hval⟩ := clPf_core (k₀ := k₀) (rS := rS) hr ht (A := r + (j - 1) * t) (J := j - 1) rfl ψ₀ χ hGP hXP' hKP hGu
  have hx : ∀ p p', p < n + c → p' < n' + c' → IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p') :=
    fun p p' hp hp' => hXI p p' hp (by omega)
  have hR : ∀ p p', p < n + c → p' < r + (j - 1) * t →
      IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap) p p') ∧
        clPfRed P q k₀ c' n' c n (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap) p p' =
          clPfMul (r + (j - 1) * t) (clPfMul (r + (j - 1) * t + t) (clPfRed P q k₀ c n c n γ.toLinearMap) (clPfRed P q k₀ c' n' c n x))
            (clPfRed P q k₀ c' n' c' n' κ.toLinearMap) p p' := by
    intro p p' hp hp'
    obtain ⟨h1, h2⟩ := clPf_red_comp (p := p) (p' := p') hq0 hk hk' hγ.1 hκ.1 hx hp (by omega)
    refine ⟨h1, ?_⟩
    rw [h2, clPf_mul_assoc, clPf_mul_cast hBt, clPf_mul_cast hsrc]
  have hC' : symPhiCond P q k₀ rS r t j c n
      (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap)) := by
    refine (clPf_cond_iff hq hu hr (by omega) _).2 ⟨fun p p' hp hp' => (hR p p' hp hp').1, ?_⟩
    refine clPf_pat_congr hra (by omega) (fun p p' hp hp' => ((hR p p' hp hp').2).symm) ?_
    exact clPf_pat_cast hBt.symm rfl hpat
  refine ⟨hC', ?_⟩
  have hanc : r + (j - 1) * t ≤ n + c := by omega
  rw [clPf_phiGS_val ψ₀ χ hkr hanc _ hC', clPf_phiGS_val ψ₀ χ hkr hanc _ hC,
    clPf_lamGBS hq0 ψ₀ χ (J := j) hk hkr (by omega) hγ.1, clPf_lamGBS hq0 ψ₀ χ (J := j - 1) hk' hkr (by omega) hκ.1,
    clPf_unitV, clPf_unitV, clPf_det_red hq0 hk hγ.1, clPf_det_red hq0 hk' hκ.1,
    clPf_top_cast (clPfRed P q k₀ c n c n γ.toLinearMap) hBt, clPf_top_cast (clPfRed P q k₀ c' n' c' n' κ.toLinearMap) hsrc]
  have e1 : clPfLam ψ₀ χ k₀ r t (j - 1) (clPfRed P q k₀ c' n' c n (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap)) =
      clPfLam ψ₀ χ k₀ r t (j - 1) (clPfMul (r + (j - 1) * t) (clPfMul (r + (j - 1) * t + t) (clPfRed P q k₀ c n c n γ.toLinearMap)
        (clPfRed P q k₀ c' n' c n x)) (clPfRed P q k₀ c' n' c' n' κ.toLinearMap)) :=
    clPf_lam_congr ψ₀ χ (by omega) (le_refl _) fun p p' hp hp' => (hR p p' (by omega) hp').2
  have e2 : clPfTop (r + (j - 1) * t) (clPfRed P q k₀ c' n' c n (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap)) =
      clPfTop (r + (j - 1) * t) (clPfMul (r + (j - 1) * t) (clPfMul (r + (j - 1) * t + t) (clPfRed P q k₀ c n c n γ.toLinearMap)
        (clPfRed P q k₀ c' n' c n x)) (clPfRed P q k₀ c' n' c' n' κ.toLinearMap)) :=
    clPf_top_congr fun p p' hp hp' => (hR p p' (by omega) hp').2
  rw [Nat.sub_add_cancel hj] at hval
  rw [e1, e2]
  exact hval

theorem clPf_phiGSLaw {P : HeightOneSpectrum (𝓞 E)} {q k₀ rS r t j c' n' c n : ℕ} (h : PhiGSLawHyp P q k₀ rS r t j c' n' c n)
    (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : PhiGSLaw P q ψ₀ χ k₀ rS r t j c' n' c n := by
  intro γ hγ κ hκ x
  by_cases hC : symPhiCond P q k₀ rS r t j c n (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x)
  · exact (clPf_main h ψ₀ χ hγ hκ x hC).2
  · have hC' : ¬ symPhiCond P q k₀ rS r t j c n
        (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap)) := by
      intro h'
      have h2 := (clPf_main h ψ₀ χ (Subgroup.inv_mem _ hγ) (Subgroup.inv_mem _ hκ) _ h').1
      have e : (γ⁻¹ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap ∘ₗ (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap) ∘ₗ
          (κ⁻¹ : Sp E (n' + c') ≃ₗ[E] Sp E (n' + c')).toLinearMap = x := by
        refine LinearMap.ext fun v => ?_
        change γ.symm (γ (x (κ (κ.symm v)))) = x v
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      rw [e] at h2
      exact hC h2
    rw [phiGS_eq, if_neg hC', phiGS_eq, if_neg hC, mul_zero]

end ClPfLaw

end Formalism.L2.Col
