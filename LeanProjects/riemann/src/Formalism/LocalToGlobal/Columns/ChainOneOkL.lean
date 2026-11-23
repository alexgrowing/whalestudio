import Formalism.LocalToGlobal.Columns.OcbPhiFIdxFPos
import Formalism.LocalToGlobal.Columns.FirstUnfoldingEqZeroOfNotIntegral

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section E1

variable {E K L : Type} [Field E] [NumberField E] [Field K] [CharZero K] [Field L] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

variable (P) in

def ookRed {n' n : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) :
    (Fin n' → 𝓞 E ⧸ P.asIdeal) →ₗ[𝓞 E ⧸ P.asIdeal] (Fin n → 𝓞 E ⧸ P.asIdeal) :=
  Matrix.toLin' (Matrix.of fun (l : Fin n) (s : Fin n') => redP P (Loc.atN (xj (Loc.eN E n' s.1)) l.1))

theorem ookRed_spec {n' n : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) : ocbXRed P xj (ookRed P xj) := by
  intro l s hl hs
  unfold ookRed
  rw [ocbS_atN_toLin' _ hl hs]
  rfl

theorem ookAtN_add {N : ℕ} (v w : Fin N → E) (l : ℕ) : Loc.atN (v + w) l = Loc.atN v l + Loc.atN w l := by
  unfold Loc.atN
  split_ifs
  · rfl
  · rw [add_zero]

theorem xInt_of_firstUnfolding_ne_zero {n' c' n c : ℕ} (hc' : c' = c + 1) (Ψ : Loc.SF E K (n' + c') (n + c))
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (psi : E → K) (vals : Finset E) (wt : K) (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (h : Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt Ψ xj ≠ 0) : ocbXInt P xj := by
  by_contra hx
  exact h (firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi vals wt xj hx)

theorem firstUnfolding_reduction_independent (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) {n' c' n c : ℕ} (hc' : c' = c + 1) (σ : K →+* L)
    (Ψ : Loc.SF E K (n' + c') (n + c)) (Ψr : Loc.SF (𝓞 E ⧸ P.asIdeal) L (n' + (c + 1)) (n + c))
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) → σ (Ψ y) = Ψr ybar)
    (psi : E → K) (ψ₀ : 𝓞 E ⧸ P.asIdeal → L) (hpsi : ∀ a, IntAt P a → σ (psi (a / (q : E))) = ψ₀ (redP P a))
    {A B A' B' : ℕ} (hA : c + 1 ≤ A) (hB : 1 ≤ B) (hA' : c + 1 ≤ A') (hB' : 1 ≤ B') (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A' B') ((q : K) ^ B')⁻¹ Ψ xj =
      Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A B) ((q : K) ^ B)⁻¹ Ψ xj := by
  by_cases hx : ocbXInt P xj
  · apply σ.injective
    rw [firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA' hB' xj (ookRed P xj) hx (ookRed_spec xj),
      firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA hB xj (ookRed P xj) hx (ookRed_spec xj)]
  · rw [firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ xj hx, firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ xj hx]

theorem firstUnfolding_add_eq_self_of_intAt_div (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) {n' c' n c : ℕ} (hc' : c' = c + 1) (σ : K →+* L)
    (Ψ : Loc.SF E K (n' + c') (n + c)) (Ψr : Loc.SF (𝓞 E ⧸ P.asIdeal) L (n' + (c + 1)) (n + c))
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) → σ (Ψ y) = Ψr ybar)
    (psi : E → K) (ψ₀ : 𝓞 E ⧸ P.asIdeal → L) (hpsi : ∀ a, IntAt P a → σ (psi (a / (q : E))) = ψ₀ (redP P a))
    {A B : ℕ} (hA : c + 1 ≤ A) (hB : 1 ≤ B) (xj z : (Fin n' → E) →ₗ[E] (Fin n → E))
    (hz : ∀ l s, l < n → s < n' → IntAt P (Loc.atN (z (Loc.eN E n' s)) l / (q : E))) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A B) ((q : K) ^ B)⁻¹ Ψ (xj + z) =
      Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A B) ((q : K) ^ B)⁻¹ Ψ xj := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  have hD : ∀ l s, l < n → s < n' → Loc.atN ((xj + z) (Loc.eN E n' s)) l =
      Loc.atN (xj (Loc.eN E n' s)) l + (q : E) * (Loc.atN (z (Loc.eN E n' s)) l / (q : E)) := by
    intro l s _ _
    rw [LinearMap.add_apply, ookAtN_add, mul_div_cancel₀ _ hq0]
  have hint : ocbXInt P (xj + z) ↔ ocbXInt P xj := by
    constructor
    · intro h l s hl hs
      have h1 := h l s hl hs
      rw [hD l s hl hs] at h1
      exact (ciIntAt_add_iff ((ciIntAt_q (q := q)).mul (hz l s hl hs))).1 h1
    · intro h l s hl hs
      rw [hD l s hl hs]
      exact (ciIntAt_add_iff ((ciIntAt_q (q := q)).mul (hz l s hl hs))).2 (h l s hl hs)
  by_cases hx : ocbXInt P xj
  · have hred' : ocbXRed P (xj + z) (ookRed P xj) := by
      intro l s hl hs
      rw [ookRed_spec xj l s hl hs, hD l s hl hs, redP_add_natCast_mul hq (hz l s hl hs)]
    apply σ.injective
    rw [firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA hB (xj + z) (ookRed P xj) (hint.2 hx) hred',
      firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA hB xj (ookRed P xj) hx (ookRed_spec xj)]
  · rw [firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ xj hx, firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ (xj + z) (fun h => hx (hint.1 h))]

end E1

section Cong

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ookLamGvS_congr (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r t j a : ℕ} (M M' : ℕ → ℕ → E)
    (hkr : k₀ ≤ r) (hra : r ≤ a) (hja : r + j * t ≤ a)
    (h : ∀ p p', p < a → p' < a → IntAt P (M p p') ∧ IntAt P (M' p p') ∧ redP P (M' p p') = redP P (M p p')) :
    LocE.lamGvS ψ₀ χ k₀ r t j M' = LocE.lamGvS ψ₀ χ k₀ r t j M := by
  unfold LocE.lamGvS
  congr 1
  · congr 1
    have hb1 : ∀ i ∈ Finset.range (k₀ - 1), i < a ∧ i + 1 < a := fun i hi => by simp at hi; omega
    have hb2 : ∀ i ∈ Finset.range (r - k₀ - 1), k₀ + i < a ∧ k₀ + i + 1 < a := fun i hi => by simp at hi; omega
    rw [reduction_add (ciIntAt_sum _ _ fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).2.1)
        (ciIntAt_sum _ _ fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).2.1),
      reduction_add (ciIntAt_sum _ _ fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).1)
        (ciIntAt_sum _ _ fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).1),
      redP_sum _ _ (fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).2.1),
      redP_sum _ _ (fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).2.1),
      redP_sum _ _ (fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).1),
      redP_sum _ _ (fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).1)]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).2.2)
      (Finset.sum_congr rfl fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).2.2)
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < j := by simpa using hi
    have hb : ∀ s : Fin t, r + i * t + s.1 < a := fun s => by
      have h1 := s.2
      have h2 : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right _ hi'
      nlinarith
    apply ciUnitV_congr
    rw [redP_det (Matrix.of fun s s' : Fin t => M' (r + i * t + s.1) (r + i * t + s'.1)) (fun s s' => (h _ _ (hb s) (hb s')).2.1),
      redP_det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1)) (fun s s' => (h _ _ (hb s) (hb s')).1)]
    congr 1
    ext s s'
    exact (h _ _ (hb s) (hb s')).2.2

open Classical in

theorem ookPhiGS_congr (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ rS r t j c' n' c n : ℕ} (x x' : HomE E (n' + c') (n + c))
    (hkr : k₀ ≤ r) (han : r + (j - 1) * t ≤ n + c)
    (hD : ∀ p p', p < n + c → p' < r + (j - 1) * t → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p' + q * d) :
    LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x' = LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x := by
  rw [phiGS_eq, phiGS_eq]
  set M := LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x with hM
  set M' := LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' with hM'
  set a := r + (j - 1) * t with ha
  have hra : r ≤ a := Nat.le_add_right _ _
  have k1 : ∀ p p', p < n + c → p' < a → (IntAt P (M' p p') ↔ IntAt P (M p p')) := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he]
    exact ciIntAt_add_iff ((ciIntAt_q (q := q)).mul hd)
  have k2 : ∀ p p', p < n + c → p' < a → (IntAt P (M' p p' / q) ↔ IntAt P (M p p' / q)) := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he, add_div, mul_div_cancel_left₀ _ hq0]
    exact ciIntAt_add_iff hd
  have k3 : ∀ p p', p < n + c → p' < a → redP P (M' p p') = redP P (M p p') := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he]
    exact redP_add_natCast_mul hq hd
  have hc : symPhiCond P q k₀ rS r t j c n M' ↔ symPhiCond P q k₀ rS r t j c n M := by
    unfold symPhiCond
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun p p' hp hp' => (k1 p p' hp hp').1 (h1 p p' hp hp'), fun p p' h0 hp hp' => (k2 p p' hp hp').1 (h2 p p' h0 hp hp'),
        fun p' hp' => ⟨?_, fun p hp hne hc => ?_⟩, fun p p' h0 hp' hp hpp => ?_⟩
      · rw [← k3 p' p' (by omega) (by omega)]; exact (h3 p' hp').1
      · rw [← k3 p p' (by omega) (by omega)]; exact (h3 p' hp').2 p hp hne hc
      · rw [← k3 p p' (by omega) hp']; exact h4 p p' h0 hp' hp hpp
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun p p' hp hp' => (k1 p p' hp hp').2 (h1 p p' hp hp'), fun p p' h0 hp hp' => (k2 p p' hp hp').2 (h2 p p' h0 hp hp'),
        fun p' hp' => ⟨?_, fun p hp hne hc => ?_⟩, fun p p' h0 hp' hp hpp => ?_⟩
      · rw [k3 p' p' (by omega) (by omega)]; exact (h3 p' hp').1
      · rw [k3 p p' (by omega) (by omega)]; exact (h3 p' hp').2 p hp hne hc
      · rw [k3 p p' (by omega) hp']; exact h4 p p' h0 hp' hp hpp
  by_cases hC : symPhiCond P q k₀ rS r t j c n M
  · rw [if_pos (hc.2 hC), if_pos hC]
    have htrip : ∀ p p', p < a → p' < a → IntAt P (M p p') ∧ IntAt P (M' p p') ∧ redP P (M' p p') = redP P (M p p') :=
      fun p p' hp hp' => ⟨hC.1 p p' (by omega) hp', (hc.2 hC).1 p p' (by omega) hp', k3 p p' (by omega) hp'⟩
    congr 1
    · exact ookLamGvS_congr ψ₀ χ M M' hkr hra (le_refl _) htrip
    · congr 1
      apply ciUnitV_congr
      rw [redP_det (Matrix.of fun s s' : Fin a => M' s.1 s'.1) (fun s s' => (htrip s.1 s'.1 s.2 s'.2).2.1),
        redP_det (Matrix.of fun s s' : Fin a => M s.1 s'.1) (fun s s' => (htrip s.1 s'.1 s.2 s'.2).1)]
      congr 1
      ext s s'
      exact (htrip s.1 s'.1 s.2 s'.2).2.2
  · rw [if_neg (fun h => hC (hc.1 h)), if_neg hC]

theorem ookEntB_joinX (q : ℕ) {k₀ n' c' n c : ℕ} (hc' : c' = 1) (hc : c = 0) (hk : k₀ ≤ n') (x₀ : HomE E n' n) (y' : Sp E n)
    {p s : ℕ} (hp : p < n) (hs : s < n') :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (joinCol (c' := c') (c := c) x₀ y') p (LocE.fPos k₀ c' n' s) =
      x₀ (Pi.single ⟨s, hs⟩ 1) ⟨p, hp⟩ := by
  subst hc' hc
  have f1 : LocE.fIdx k₀ 1 n' (LocE.fPos k₀ 1 n' s) = s := ocbPhi_fIdx_fPos hk (by omega)
  have f2 : LocE.fIdx k₀ 0 n p = p := ciFIdx (Or.inl rfl) (by omega)
  unfold LocE.entB joinCol atNL
  rw [f1, f2, ciScE_lt _ hp, ciScE_lt _ hs, dif_pos (show n' < n' + 1 by omega)]
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  rw [ciAtN_inX hp]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : (LinearMap.funLeft E E (Fin.castAdd 1)) (Loc.eN E (n' + 1) s) = (Pi.single ⟨s, hs⟩ 1 : Fin n' → E) := by
    funext i
    show Loc.eN E (n' + 1) s (Fin.castAdd 1 i) = _
    unfold Loc.eN
    simp only [Fin.val_castAdd, Pi.single_apply, Fin.ext_iff]
  have e2 : Loc.eN E (n' + 1) s ⟨n', by omega⟩ = 0 := by
    unfold Loc.eN
    rw [if_neg (by simp; omega)]
  rw [e1, e2, zero_mul, add_zero, sub_zero, zpow_zero, mul_one]

theorem ookFIdx_lt {k₀ c' n' p' : ℕ} (hc' : c' = 1) (hk : k₀ ≤ n') (hp' : p' < n' + c') (hne : p' ≠ k₀) :
    LocE.fIdx k₀ c' n' p' < n' ∧ LocE.fPos k₀ c' n' (LocE.fIdx k₀ c' n' p') = p' := by
  subst hc'
  exact ⟨by unfold LocE.fIdx; split_ifs <;> omega, symFPos_fIdx hk hp'⟩

theorem ookPrX_le {k₀ rS r t n c : ℕ} :
    Loc.prX (Loc.Cbe (LocE.JGsym P q k₀ rS r t n c) 1) ≤ GLint E n P := by
  rintro g ⟨ρ, hr, hg⟩ x
  have hr' : ρ ∈ LocE.JGsym P q k₀ rS r t n c := by
    have := hr.2
    simpa [MulAut.conj_apply] using this
  rw [← ciMem_lamY (P := P) (q := q) (c := c) (fun i => i + 1) (g x), ← hg]
  exact (hr'.1 _).trans (ciMem_lamY _ _)

end Cong

end Formalism.L2.Col
