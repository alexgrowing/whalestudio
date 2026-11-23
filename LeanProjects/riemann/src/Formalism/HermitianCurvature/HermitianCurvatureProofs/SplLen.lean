import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CompRB

open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma dif {E₁ F₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    {f : E₁ → F₁} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  exact hf.differentiable (by simp)

lemma hdx (x : Bool × Mat k r) {f : Mat k r → E} (hf : Differentiable ℝ f) (g : Mat k r) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (fderiv ℝ f g (dirv x g)) 0 := by
  have hd : HasFDerivAt f (fderiv ℝ f g) (crv x g 0) := by
    rw [crv_zero]
    exact (hf g).hasFDerivAt
  exact hd.comp_hasDerivAt 0 (crv_hasDerivAt x g)

private theorem dx_eq_deriv_crv (x : Bool × Mat k r) (f : Mat k r → E) (g : Mat k r) :
    Dx x f g = deriv (fun t : ℝ => f (crv x g t)) 0 := by
  rcases x with ⟨b, X⟩
  cases b <;> rfl

private theorem dirL_eq_dirv (x : Bool × Mat k r) (g : Mat k r) : dirL x g = dirv x g := by
  rcases x with ⟨b, X⟩
  cases b <;> first | rfl | simp [dirL, dirv]

lemma dx_fd (x : Bool × Mat k r) {f : Mat k r → E} (hf : Differentiable ℝ f) :
    Dx x f = fun g => fderiv ℝ f g (dirL x g) := by
  funext g
  rw [dx_eq_deriv_crv, (hdx x hf g).deriv, dirL_eq_dirv]

lemma cdx (x : Bool × Mat k r) {f : Mat k r → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dx x f) := by
  rw [dx_fd x (dif hf)]
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply (dirL x).contDiff

lemma cdw (w : List (Bool × Mat k r)) {f : Mat k r → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dw w f) := by
  induction w with
  | nil => simpa [Dw] using hf
  | cons a w ih => simpa [Dw] using cdx a ih

lemma dx_add (x : Bool × Mat k r) {a b : Mat k r → E} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    Dx x (fun g => a g + b g) = fun g => Dx x a g + Dx x b g := by
  rw [dx_fd x (f := fun g => a g + b g) (ha.add hb), dx_fd x ha, dx_fd x hb]
  funext g
  exact congrArg (fun T => T (dirL x g)) (fderiv_add (ha g) (hb g))

lemma dw_add (w : List (Bool × Mat k r)) {a b : Mat k r → E} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    Dw w (fun g => a g + b g) = fun g => Dw w a g + Dw w b g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => a g + b g) = fun g => Dx x (Dw w a) g + Dx x (Dw w b) g
    rw [ih]
    exact dx_add x (dif (cdw w ha)) (dif (cdw w hb))

lemma dx_clm {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] (L : E →L[ℝ] E₂) (x : Bool × Mat k r)
    {f : Mat k r → E} (hf : Differentiable ℝ f) : Dx x (fun g => L (f g)) = fun g => L (Dx x f g) := by
  rw [dx_fd x (f := fun g => L (f g)) (L.differentiable.comp hf), dx_fd x hf]
  funext g
  have h := (L.hasFDerivAt.comp g (hf g).hasFDerivAt).fderiv
  rw [show (fun g => L (f g)) = ⇑L ∘ f from rfl]
  exact congrArg (fun T => T (dirL x g)) h

lemma dw_clm {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] (L : E →L[ℝ] E₂) (w : List (Bool × Mat k r))
    {f : Mat k r → E} (hf : ContDiff ℝ ∞ f) : Dw w (fun g => L (f g)) = fun g => L (Dw w f g) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => L (f g)) = fun g => L (Dx x (Dw w f) g)
    rw [ih]
    exact dx_clm L x (dif (cdw w hf))

section app

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma dx_app (x : Bool × Mat k r) {a : Mat k r → (F →L[ℝ] E)} {b : Mat k r → F} (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) :
    Dx x (fun g => a g (b g)) = fun g => Dx x a g (b g) + a g (Dx x b g) := by
  rw [dx_fd x (ha.clm_apply hb), dx_fd x ha, dx_fd x hb]
  funext g
  have h2 := congrArg (fun T => T (dirL x g)) (fderiv_clm_apply (ha g) (hb g))
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at h2
  exact h2.trans (add_comm _ _)

lemma cd_app {a : Mat k r → (F →L[ℝ] E)} {b : Mat k r → F} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun g => a g (b g)) := ha.clm_apply hb

private lemma dw_append_singleton' {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (w : List (Bool × Mat k r))
    (x : Bool × Mat k r) (f : Mat k r → E') : Dw (w ++ [x]) f = Dw w (Dx x f) := by
  unfold Dw
  rw [List.foldr_append]
  rfl

lemma leibA (g : Mat k r) (M : ℝ) (w : List (Bool × Mat k r)) :
    ∀ (a : Mat k r → (F →L[ℝ] E)) (b : Mat k r → F), ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      (∀ w₁ w₂, Spl w w₁ w₂ → ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) →
      ‖Dw w (fun g => a g (b g)) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a b ha hb h
    have h0 := h [] [] ⟨List.Sublist.slnil, List.Sublist.slnil, List.Perm.nil⟩
    simp only [Dw, List.foldr_nil, List.length_nil, pow_zero, one_mul] at h0 ⊢
    exact (ContinuousLinearMap.le_opNorm _ _).trans h0
  | append_singleton w x ih =>
    intro a b ha hb h
    have splL : ∀ {w₁ w₂ : List (Bool × Mat k r)}, Spl w w₁ w₂ → Spl (w ++ [x]) (w₁ ++ [x]) w₂ := by
      intro w₁ w₂ hs
      refine ⟨hs.1.append (List.Sublist.refl [x]), hs.2.1.trans (List.sublist_append_left w [x]), ?_⟩
      have hp : (w₁ ++ [x] ++ w₂).Perm (w₁ ++ w₂ ++ [x]) := by
        simpa [List.append_assoc] using (List.perm_append_comm (l₁ := [x]) (l₂ := w₂)).append_left w₁
      exact hp.trans (hs.2.2.append_right [x])
    have splR : ∀ {w₁ w₂ : List (Bool × Mat k r)}, Spl w w₁ w₂ → Spl (w ++ [x]) w₁ (w₂ ++ [x]) := by
      intro w₁ w₂ hs
      refine ⟨hs.1.trans (List.sublist_append_left w [x]), hs.2.1.append (List.Sublist.refl [x]), ?_⟩
      rw [← List.append_assoc]
      exact hs.2.2.append_right [x]
    have h1 : ‖Dw w (fun g => Dx x a g (b g)) g‖ ≤ 2 ^ w.length * M :=
      ih (Dx x a) b (cdx x ha) hb fun w₁ w₂ hs => by
        have h' := h (w₁ ++ [x]) w₂ (splL hs)
        rwa [dw_append_singleton'] at h'
    have h2 : ‖Dw w (fun g => a g (Dx x b g)) g‖ ≤ 2 ^ w.length * M :=
      ih a (Dx x b) ha (cdx x hb) fun w₁ w₂ hs => by
        have h' := h w₁ (w₂ ++ [x]) (splR hs)
        rwa [dw_append_singleton'] at h'
    rw [dw_append_singleton', dx_app x (dif ha) (dif hb), dw_add w (cd_app (cdx x ha) hb) (cd_app ha (cdx x hb))]
    beta_reduce
    refine (norm_add_le _ _).trans ?_
    rw [List.length_append, List.length_singleton, pow_succ]
    linarith

lemma dx_comp (x : Bool × Mat k r) {ψ : Mat k r → F} {Φ : F → E} (hψ : Differentiable ℝ ψ)
    (hΦ : Differentiable ℝ Φ) : Dx x (fun g => Φ (ψ g)) = fun g => fderiv ℝ Φ (ψ g) (Dx x ψ g) := by
  rw [dx_fd x (f := fun g => Φ (ψ g)) (hΦ.comp hψ), dx_fd x hψ]
  funext g
  rw [show (fun g => Φ (ψ g)) = Φ ∘ ψ from rfl]
  exact congrArg (fun T => T (dirL x g)) (fderiv_comp g (hΦ (ψ g)) (hψ g))

lemma spl_len {w w₁ w₂ : List (Bool × Mat k r)} (h : Spl w w₁ w₂) : w₁.length + w₂.length = w.length := by
  obtain ⟨-, -, hp⟩ := h
  rw [← List.length_append]
  exact hp.length_eq

private theorem adm_of_sublist {n : ℕ} {w w' : List (Bool × Mat k r)} (h : admitted n w)
    (hw : w'.Sublist w) : admitted n w' := by
  obtain ⟨u, v, hu, hv, hlen, rfl⟩ := h
  obtain ⟨l₁, l₂, rfl, h1, h2⟩ := List.sublist_append_iff.1 hw
  unfold wL at h1
  unfold wR at h2
  obtain ⟨u', hu', rfl⟩ := List.sublist_map_iff.1 h1
  obtain ⟨v', hv', rfl⟩ := List.sublist_map_iff.1 h2
  exact ⟨u', v', fun X hX => hu X (hu'.subset hX), fun X hX => hv X (hv'.subset hX),
    by have := hu'.length_le; have := hv'.length_le; omega, rfl⟩

theorem fdb (ψ : Mat k r → F) (hψ : ContDiff ℝ ∞ ψ) (S : Set (Mat k r)) (K : Set F) (hK : ∀ g ∈ S, ψ g ∈ K)
    (Y : Mat k r → ℝ) (hY : ∀ g ∈ S, 1 ≤ Y g) (α β : ℕ) (M : ℝ) (n : ℕ)
    (H : ∀ w, admitted n w → w ≠ [] → ∀ g ∈ S, ‖Dw w ψ g‖ ≤ M * Y g ^ (α * w.length + β)) :
    ∀ m : ℕ, ∀ (E₁ : Type) [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] (Φ : F → E₁), ContDiff ℝ ∞ Φ →
      (∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted n w → w.length ≤ m → ∀ g ∈ S,
        ‖Dw w (fun g => Φ (ψ g)) g‖ ≤ C * Y g ^ ((α + β) * w.length) := by
  intro m
  induction m with
  | zero =>
    intro E₁ _ _ Φ hΦ hB
    obtain ⟨B0, hB0⟩ := hB 0
    refine ⟨max B0 0, le_max_right _ _, fun w _ hw g hg => ?_⟩
    have hw0 : w = [] := List.length_eq_zero_iff.1 (by omega)
    subst hw0
    simp only [Dw, List.foldr_nil, List.length_nil, mul_zero, pow_zero, mul_one]
    have h0 := hB0 (ψ g) (hK g hg)
    rw [norm_iteratedFDeriv_zero] at h0
    exact h0.trans (le_max_left _ _)
  | succ m ih =>
    intro E₁ _ _ Φ hΦ hB
    obtain ⟨C', hC'0, hC'⟩ := ih (F →L[ℝ] E₁) (fderiv ℝ Φ) (hΦ.fderiv_right (m := ∞) (by simp))
      (fun j => by
        obtain ⟨B, hB'⟩ := hB (j + 1)
        exact ⟨B, fun y hy => by rw [norm_iteratedFDeriv_fderiv]; exact hB' y hy⟩)
    obtain ⟨B0, hB0⟩ := hB 0
    have hM' : 0 ≤ max M 0 := le_max_right _ _
    refine ⟨max B0 0 + 2 ^ m * (C' * max M 0),
      add_nonneg (le_max_right _ _) (mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg hC'0 hM')),
      fun w hwA hw g hg => ?_⟩
    have hY1 := hY g hg
    have hY0 : 0 ≤ Y g := by linarith
    have hrest : 0 ≤ 2 ^ m * (C' * max M 0) :=
      mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg hC'0 hM')
    rcases List.eq_nil_or_concat w with rfl | ⟨w', x, rfl⟩
    · simp only [Dw, List.foldr_nil, List.length_nil, mul_zero, pow_zero, mul_one]
      have h0 := hB0 (ψ g) (hK g hg)
      rw [norm_iteratedFDeriv_zero] at h0
      linarith [le_max_left B0 0]
    · rw [List.concat_eq_append] at hwA hw ⊢
      rw [dw_append_singleton', dx_comp x (dif hψ) (dif hΦ)]
      have hlen : w'.length ≤ m := by
        rw [List.length_append, List.length_singleton] at hw
        omega
      have key := leibA g (C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1))) w'
        (fun g => fderiv ℝ Φ (ψ g)) (Dx x ψ) ((hΦ.fderiv_right (m := ∞) (by simp)).comp hψ) (cdx x hψ)
        (fun w₁ w₂ hs => by
          have hl := spl_len hs
          have h1 : ‖Dw w₁ (fun g => fderiv ℝ Φ (ψ g)) g‖ ≤ C' * Y g ^ ((α + β) * w₁.length) :=
            hC' w₁ (adm_of_sublist hwA (hs.1.trans (List.sublist_append_left _ _))) (by omega) g hg
          have h2 : ‖Dw w₂ (Dx x ψ) g‖ ≤ max M 0 * Y g ^ (α * (w₂ ++ [x]).length + β) := by
            rw [← dw_append_singleton']
            exact (H (w₂ ++ [x]) (adm_of_sublist hwA (hs.2.1.append_right [x])) (by simp) g hg).trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hY0 _))
          have hexp : (α + β) * w₁.length + (α * (w₂ ++ [x]).length + β) ≤
              (α + β) * (w'.length + 1) := by
            rw [List.length_append, List.length_singleton]
            nlinarith
          calc ‖Dw w₁ (fun g => fderiv ℝ Φ (ψ g)) g‖ * ‖Dw w₂ (Dx x ψ) g‖
              ≤ (C' * Y g ^ ((α + β) * w₁.length)) * (max M 0 * Y g ^ (α * (w₂ ++ [x]).length + β)) :=
                mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC'0 (pow_nonneg hY0 _))
            _ = C' * max M 0 * Y g ^ ((α + β) * w₁.length + (α * (w₂ ++ [x]).length + β)) := by
                rw [pow_add]
                ring
            _ ≤ C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1)) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 hexp) (mul_nonneg hC'0 hM'))
      have hP : 0 ≤ C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1)) :=
        mul_nonneg (mul_nonneg hC'0 hM') (pow_nonneg hY0 _)
      calc _ ≤ 2 ^ w'.length * (C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1))) := key
        _ ≤ 2 ^ m * (C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1))) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) hP
        _ ≤ (max B0 0 + 2 ^ m * (C' * max M 0)) * Y g ^ ((α + β) * (w' ++ [x]).length) := by
            rw [List.length_append, List.length_singleton]
            have : 0 ≤ max B0 0 * Y g ^ ((α + β) * (w'.length + 1)) :=
              mul_nonneg (le_max_right _ _) (pow_nonneg hY0 _)
            nlinarith

end app

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
