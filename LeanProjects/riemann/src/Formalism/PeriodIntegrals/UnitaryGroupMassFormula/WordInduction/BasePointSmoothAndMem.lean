import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WordInduction.DzFamilySmooth

open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def BasePointSmoothAndMem : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (γ : B.Mat k (r - (j + 1))), γ ∈ B.GV k (r - (j + 1)) →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => x0 k r j hj (Matrix.of q.2) q.1 γ)
      {q | q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0} ∧
    ∀ q : ℂ × (Fin j → Fin j → ℂ), q.1 ≠ 0 → (Matrix.of q.2).det ≠ 0 →
      x0 k r j hj (Matrix.of q.2) q.1 γ ∈ Q.Glev k r 0

def Om (k r j : ℕ) (hj : j + 1 ≤ r) (Dm : Set (Q.Mx k r)) (γ : B.Mat k (r - (j + 1))) :
    Set (ℂ × (Fin j → Fin j → ℂ)) :=
  {q | q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0} ∩ (fun q => x0 k r j hj (Matrix.of q.2) q.1 γ) ⁻¹' Dm

theorem isOpen_O (j : ℕ) : IsOpen {q : ℂ × (Fin j → Fin j → ℂ) | q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0} := by
  have h1 : IsOpen {q : ℂ × (Fin j → Fin j → ℂ) | q.1 ≠ 0} := isOpen_ne.preimage continuous_fst
  have hd : Continuous fun q : ℂ × (Fin j → Fin j → ℂ) => (Matrix.of q.2).det := Continuous.matrix_det continuous_snd
  have h2 : IsOpen {q : ℂ × (Fin j → Fin j → ℂ) | (Matrix.of q.2).det ≠ 0} := isOpen_ne.preimage hd
  exact h1.inter h2

section geom

variable {k r j : ℕ} {hj : j + 1 ≤ r} {Dm : Set (Q.Mx k r)} {γ : B.Mat k (r - (j + 1))}

theorem isOpen_Om (hX : BasePointSmoothAndMem) (hγ : γ ∈ B.GV k (r - (j + 1))) (hDm : IsOpen Dm) : IsOpen (Om k r j hj Dm γ) :=
  (hX k r j hj γ hγ).1.continuousOn.isOpen_inter_preimage (isOpen_O j) hDm

theorem Om_sub {q : ℂ × (Fin j → Fin j → ℂ)} (hq : q ∈ Om k r j hj Dm γ) :
    q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0 ∧ x0 k r j hj (Matrix.of q.2) q.1 γ ∈ Dm :=
  ⟨hq.1.1, hq.1.2, hq.2⟩

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem family_smooth (hX : BasePointSmoothAndMem) (hγ : γ ∈ B.GV k (r - (j + 1))) {F : Q.Mx k r → E}
    (hF : Q.SmoothLev k r 0 Dm F) :
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => F (x0 k r j hj (Matrix.of q.2) q.1 γ)) (Om k r j hj Dm γ) := by
  intro q hq
  obtain ⟨hsm, hG⟩ := hX k r j hj γ hγ
  obtain ⟨U', F', hU', hg0, hF', hag⟩ := hF _ ⟨hG q hq.1.1 hq.1.2, hq.2⟩
  have hx : ContDiffWithinAt ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => x0 k r j hj (Matrix.of q.2) q.1 γ)
      (Om k r j hj Dm γ) q := (hsm q hq.1).mono Set.inter_subset_left
  have hc := (hF'.contDiffAt (hU'.mem_nhds hg0)).comp_contDiffWithinAt q hx
  refine hc.congr_of_eventuallyEq ?_ (hag _ hg0 (hG q hq.1.1 hq.1.2))
  have hca : ContinuousAt (fun q : ℂ × (Fin j → Fin j → ℂ) => x0 k r j hj (Matrix.of q.2) q.1 γ) q :=
    hsm.continuousOn.continuousAt ((isOpen_O j).mem_nhds hq.1)
  have h1 : (fun q : ℂ × (Fin j → Fin j → ℂ) => x0 k r j hj (Matrix.of q.2) q.1 γ) ⁻¹' U' ∈ nhds q :=
    hca.preimage_mem_nhds (hU'.mem_nhds hg0)
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with q' h1' h2'
  exact hag _ h1' (hG q' h2'.1.1 h2'.1.2)

end geom

section main

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rules_uw (hR : RulesClosed) {k r j : ℕ} (hj : j + 1 ≤ r) {z z' : Fin (2 * r + k + 1) → ℂ}
    {Dm : Set (Q.Mx k r)} {Φ : Q.Mx k r → E} (hz : inWb k r z) (hz' : inWb k r z') (hDm : IsOpen Dm)
    (hDs : Dm ⊆ domJ k r j hj z z') (hΦ : RulesOn k r j hj z z' Dm Φ) (i : ℕ) (hi : i ≤ r) (hor : i = j ∨ i = j + 1) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), RulesOn k r j hj z z' Dm (D.uwG k r z z' Φ i hi w e) := by
  intro w
  induction w with
  | nil => intro e; exact hΦ
  | cons l w ih =>
    intro e
    exact hR k r j hj z z' E Dm _ hz hz' hDm hDs (ih _) i (by omega) hor l (e 0)

theorem core (hH : HeadLetter) (hZ : ZOnly) (hR : RulesClosed) (hX : BasePointSmoothAndMem) {k r j : ℕ} (hj : j + 1 ≤ r)
    {z z' : Fin (2 * r + k + 1) → ℂ} {Dm : Set (Q.Mx k r)} {Φ : Q.Mx k r → E} (hz : inWb k r z)
    (hz' : inWb k r z') (hDm : IsOpen Dm) (hDs : Dm ⊆ domJ k r j hj z z') (hΦ : RulesOn k r j hj z z' Dm Φ)
    {γ : B.Mat k (r - (j + 1))} (hγ : γ ∈ B.GV k (r - (j + 1))) :
    ∀ (w : List C.Letter), ∀ q ∈ Om k r j hj Dm γ, ∀ e,
      D.uwG k r z z' Φ (j + 1) hj w e (x0 k r j hj (Matrix.of q.2) q.1 γ) =
        rawBT (levelZeroKernel k r j) (D.positionted w)
          (fun b τ => D.uwG k r z z' Φ j (by omega) w b (x0 k r j hj (Matrix.of q.2) τ γ)) e q.1 := by
  have hO := isOpen_Om (hj := hj) hX hγ hDm
  have hOd : Om k r j hj Dm γ ⊆ {q | (Matrix.of q.2).det ≠ 0} := fun q hq => hq.1.2
  have hO0 : Om k r j hj Dm γ ⊆ {q | q.1 ≠ 0} := fun q hq => hq.1.1
  intro w
  induction w with
  | nil => intro q _ e; rfl
  | cons l w ih =>
    intro q hq e
    obtain ⟨pl, Y⟩ := l
    set κ := levelZeroKernel k r j with hκ
    set Ψ := D.uwG k r z z' Φ (j + 1) hj w (Fin.tail e) with hΨ
    have hRΨ : RulesOn k r j hj z z' Dm Ψ := rules_uw hR hj hz hz' hDm hDs hΦ (j + 1) hj (Or.inr rfl) w _
    have hV : IsOpen {τ : ℂ | (τ, q.2) ∈ Om k r j hj Dm γ} := hO.preimage (continuous_id.prodMk continuous_const)

    have key : ∀ s : Fin 2, ∀ τ ∈ {τ : ℂ | (τ, q.2) ∈ Om k r j hj Dm γ},
        D.vLet k r z z' j (by omega) (pl, Y) s Ψ (x0 k r j hj (Matrix.of q.2) τ γ) =
          rawBT κ (D.positionted w) (fun b τ' => D.vLet k r z z' j (by omega) (pl, Y) s
            (D.uwG k r z z' Φ j (by omega) w b) (x0 k r j hj (Matrix.of q.2) τ' γ)) (Fin.tail e) τ := by
      intro s τ hτ
      obtain ⟨Aop, hPC, hAz⟩ := hZ k r j hj z z' E (pl, Y) s hz hz'
      obtain ⟨hτ0, hτd, hτx⟩ := Om_sub hτ
      rw [hAz Dm Ψ hDm hDs hRΨ.1 (Matrix.of q.2) τ γ hτd hτ0 hγ hτx]
      have hW : IsOpen {Z' : Fin j → Fin j → ℂ | (τ, Z') ∈ Om k r j hj Dm γ} :=
        hO.preimage (continuous_const.prodMk continuous_id)
      rw [paramComm_local hPC hW (fun Z' hZ' => hZ'.1.2)
        (g := fun Z' => rawBT κ (D.positionted w)
          (fun b τ' => D.uwG k r z z' Φ j (by omega) w b (x0 k r j hj Z' τ' γ)) (Fin.tail e) τ)
        (fun Z' hZ' => ih (τ, Z') hZ' (Fin.tail e)) q.2 hτ]
      have hsm : ∀ b, ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) =>
          D.uwG k r z z' Φ j (by omega) w b (x0 k r j hj (Matrix.of q.2) q.1 γ)) (Om k r j hj Dm γ) :=
        fun b => family_smooth hX hγ (rules_uw hR hj hz hz' hDm hDs hΦ j (by omega) (Or.inl rfl) w b).1
      rw [(comm_rawBT hPC hO hOd hO0 κ (D.positionted w)
        (fun b τ' Z' => D.uwG k r z z' Φ j (by omega) w b (x0 k r j hj Z' τ' γ)) hsm).2 (Fin.tail e) (τ, q.2) hτ]
      refine rawBT_congr κ (D.positionted w) hV (fun b τ' hτ' => ?_) (Fin.tail e) τ hτ
      obtain ⟨h0', hd', hx'⟩ := Om_sub hτ'
      exact (hAz Dm _ hDm hDs (rules_uw hR hj hz hz' hDm hDs hΦ j (by omega) (Or.inl rfl) w b).1
        (Matrix.of q.2) τ' γ hd' h0' hγ hx').symm
    obtain ⟨hq0, hqd, hqx⟩ := Om_sub hq
    have hHL := hH k r j hj z z' E Dm Ψ hz hz' hDm hDs hRΨ (Matrix.of q.2) γ q.1 hqd hq0 hγ hqx Y
    show D.vLet k r z z' (j + 1) hj (pl, Y) (e 0) Ψ (x0 k r j hj (Matrix.of q.2) q.1 γ) = _
    rw [rawBT_indexed_cons]
    have hcons : ∀ s : Fin 2, (fun b : Wd.Ix (Fin w.length) => fun τ =>
        D.uwG k r z z' Φ j (by omega) ((pl, Y) :: w) (Fin.cons s b : Wd.Ix (Fin (w.length + 1)))
          (x0 k r j hj (Matrix.of q.2) τ γ)) =
        fun b τ => D.vLet k r z z' j (by omega) (pl, Y) s (D.uwG k r z z' Φ j (by omega) w b)
          (x0 k r j hj (Matrix.of q.2) τ γ) := by
      intro s
      funext b τ
      simp only [D.uwG, Fin.cons_zero, Fin.cons_succ]
    simp only [hcons]
    have hq' : q.1 ∈ {τ : ℂ | (τ, q.2) ∈ Om k r j hj Dm γ} := hq
    rw [← row_congr κ pl (Y : ℂ) hV (key 0) (key 1) (e 0) hq']
    unfold row
    rcases two_cases (e 0) with h | h <;> cases pl <;>
      simp only [h, if_true, Bool.false_eq_true, if_false, one_ne_zero, Complex.conj_ofReal] <;>
      (try simp only [hκ]) <;> first | exact hHL.2.2.1 | exact hHL.1 | exact hHL.2.2.2 | exact hHL.2.1

theorem wordIndOfParts_of (hX : BasePointSmoothAndMem) : WordIndOfParts := by
  intro hH hZ hR k r j hj z z' E _ _ Dm Φ hz hz' hDm hDs hΦ Z γ hZd hγ hline w φ hφ t ht e
  have hq : ((t, Matrix.of.symm Z) : ℂ × (Fin j → Fin j → ℂ)) ∈ Om k r j hj Dm γ :=
    ⟨⟨ht, by simpa using hZd⟩, by simpa using hline t ht⟩
  have h1 := core hH hZ hR hX hj hz hz' hDm hDs hΦ hγ w _ hq e
  simp only [Equiv.apply_symm_apply] at h1
  unfold oneBT
  rw [h1, oneBT_eq_raw (levelZeroKernel k r j) (D.positionted w) φ e t ht]
  exact rawBT_congr _ _ (isOpen_ne (x := (0 : ℂ))) (fun b τ hτ => (hφ b τ hτ).symm) e t ht

end main

end Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf
