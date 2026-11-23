import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep
open scoped ComplexConjugate

namespace PositivityTheory.RgJS

namespace RankinSelbergUnitary

theorem conj_cpow_nat (N : ℕ) (z : ℂ) : conj ((N : ℂ) ^ z) = (N : ℂ) ^ (conj z) := by
  have harg : ((N : ℕ) : ℂ).arg ≠ Real.pi := by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have := Complex.cpow_conj ((N : ℕ) : ℂ) z harg
  rw [map_natCast] at this
  exact this.symm

theorem conj_eul {W : Type} (q : W → ℕ) {A B : Type} [Fintype A] [Fintype B] (α : W → A → ℂ) (β : W → B → ℂ) (s : ℂ) :
    conj (eul q α β s) = eul q β α (conj s) := by
  unfold eul
  rw [Complex.isometry_conj.isClosedEmbedding.map_tprod]
  refine tprod_congr fun w => ?_
  simp only [map_prod, map_inv₀, map_sub, map_one, map_mul, Complex.conj_conj, conj_cpow_nat, map_neg]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => Finset.prod_congr rfl fun a _ => ?_
  ring

theorem nq_ne_zero {E : Type} [Field E] [NumberField E] {S : Finset (HeightOneSpectrum (𝓞 E))} (w : Off E S) :
    (nq w : ℂ) ≠ 0 := by
  unfold nq
  exact Nat.cast_ne_zero.2 fun h => w.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem shift_term (N : ℕ) (hN : (N : ℂ) ≠ 0) (a b : ℂ) (σ τ τ' : ℝ) :
    a * (N : ℂ) ^ ((τ : ℂ) * Complex.I) * conj (b * (N : ℂ) ^ ((τ' : ℂ) * Complex.I)) *
        (N : ℂ) ^ (-((σ : ℂ) + ((τ - τ' : ℝ) : ℂ) * Complex.I)) = a * conj b * (N : ℂ) ^ (-(σ : ℂ)) := by
  rw [map_mul, conj_cpow_nat]
  have e : a * (N : ℂ) ^ ((τ : ℂ) * Complex.I) * (conj b * (N : ℂ) ^ (conj ((τ' : ℂ) * Complex.I))) *
      (N : ℂ) ^ (-((σ : ℂ) + ((τ - τ' : ℝ) : ℂ) * Complex.I)) =
      a * conj b * ((N : ℂ) ^ ((τ : ℂ) * Complex.I) * (N : ℂ) ^ (conj ((τ' : ℂ) * Complex.I)) *
        (N : ℂ) ^ (-((σ : ℂ) + ((τ - τ' : ℝ) : ℂ) * Complex.I))) := by ring
  rw [e, ← Complex.cpow_add _ _ hN, ← Complex.cpow_add _ _ hN]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem LS_shift {E : Type} [Field E] [NumberField E] {S : Finset (HeightOneSpectrum (𝓞 E))} {m k : ℕ}
    (α : Off E S → Fin m → ℂˣ) (β : Off E S → Fin k → ℂˣ) (cα cβ : Off E S → ℂˣ) (τ τ' : ℝ)
    (hα : ∀ w, (cα w : ℂ) = (nq w : ℂ) ^ ((τ : ℂ) * Complex.I))
    (hβ : ∀ w, (cβ w : ℂ) = (nq w : ℂ) ^ ((τ' : ℂ) * Complex.I)) (σ : ℝ) :
    LS S (fun w a => α w a * cα w) (fun w b => β w b * cβ w) ((σ : ℂ) + ((τ - τ' : ℝ) : ℂ) * Complex.I) = LS S α β σ := by
  unfold LS eul
  refine tprod_congr fun w => Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  simp only [Units.val_mul, hα, hβ]
  rw [shift_term _ (nq_ne_zero w)]

theorem transfer {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (hT : SatTw) {m : ℕ} (ρ : CG E m)
    (χ : HChar E) (S : Finset (HeightOneSpectrum (𝓞 E))) (hχ : ∀ w, χ.UnrAt w) (α : Off E S → Fin m → ℂˣ)
    (hα : SatOff (ρ.twist χ) S α) : SatOff ρ S (fun w a => α w a * (χ⁻¹).val w.1) := by
  intro w
  have h := hT E m (ρ.twist χ) χ⁻¹ w.1 _ (hχ w.1).inv (hα w)
  rw [← CG.twist_mul, mul_inv_cancel, CG.twist_one, Multiset.map_map] at h
  exact h

theorem val_inv_eq {E : Type} [Field E] [NumberField E] {S : Finset (HeightOneSpectrum (𝓞 E))} (χ : HChar E) (τ : ℝ)
    (h : ∀ w, ((χ.val w : ℂˣ) : ℂ) = (Ideal.absNorm w.asIdeal : ℂ) ^ (-((τ : ℂ) * Complex.I))) (w : Off E S) :
    (((χ⁻¹).val w.1 : ℂˣ) : ℂ) = (nq w : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  rw [HChar.val_inv, Units.val_inv_eq_inv_val, h, Complex.cpow_neg, inv_inv]
  rfl

theorem openRe : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re

theorem re_mem {z : ℂ} (hz : 0 < z.re) : {s : ℂ | 0 < s.re} ∈ nhds z := openRe.mem_nhds hz

theorem re_shift (σ u : ℝ) : ((σ : ℂ) + (u : ℂ) * Complex.I).re = σ := by simp

open Classical in

theorem core (hR : RSPole) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (ρ : CuspSub E a)
    (ρ' : CuspSub E b) (u : ℝ) (hb : 1 ≤ b) (hab : b ≤ a) (hn : GlobalTheory.DiscSpec.IsNormalised ρ)
    (hn' : GlobalTheory.DiscSpec.IsNormalised ρ') :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 E)), ∀ S, S₀ ⊆ S → ∀ (α : Off E S → Fin a → ℂˣ) (β : Off E S → Fin b → ℂˣ),
      SatOff (CG.mk ρ) S α → SatOff (CG.mk ρ') S β → ∃ (G : ℂ → ℂ) (σ₀ : ℝ), (∀ σ : ℝ, 0 < σ → AnalyticAt ℂ G σ) ∧
        ∀ σ : ℝ, σ₀ < σ → G σ = (if ((⟨a, CG.mk ρ⟩ : Σ a, CG E a) = ⟨b, CG.mk ρ'⟩ ∧ u = 0) then (σ : ℂ) - 1 else 1) *
          LS S α β ((σ : ℂ) + (u : ℂ) * Complex.I) := by
  obtain ⟨S₀, h⟩ := hR E a b ρ ρ' u hb hab hn hn'
  refine ⟨S₀, fun S hS α β hα hβ => ?_⟩
  obtain ⟨Z, ZS, σ₀, hZ, hZS, hne, heq, hz⟩ := h S hS α β hα hβ
  by_cases hP : (⟨a, CG.mk ρ⟩ : Σ a, CG E a) = ⟨b, CG.mk ρ'⟩ ∧ u = 0
  · obtain ⟨hP1, rfl⟩ := hP
    refine ⟨fun s => Z s / ZS s, max σ₀ 1, fun σ hσ => ?_, fun σ hσ => ?_⟩
    · have h1 : ZS σ ≠ 0 := by simpa using hne σ hσ
      have hσ' : 0 < (σ : ℂ).re := by simpa using hσ
      exact (hZ.analyticAt (re_mem hσ')).div (hZS.analyticAt (re_mem hσ')) h1
    · have hσ1 : 1 < σ := lt_of_le_of_lt (le_max_right _ _) hσ
      have hσ0 : σ₀ < σ := lt_of_le_of_lt (le_max_left _ _) hσ
      have h1 : ZS σ ≠ 0 := by simpa using hne σ (by linarith)
      have h2 := heq σ (by simpa using hσ0)
      rw [if_pos ⟨hP1, rfl⟩]
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      rw [h2]
      field_simp
  · by_cases hu : u = 0
    · subst hu
      have hs : (⟨a, CG.mk ρ⟩ : Σ a, CG E a) ≠ ⟨b, CG.mk ρ'⟩ := fun h => hP ⟨h, rfl⟩
      have hz1 := hz hs
      have hD : DifferentiableOn ℂ (dslope Z 1) {s : ℂ | 0 < s.re} :=
        (Complex.differentiableOn_dslope (re_mem (by simp))).2 hZ
      refine ⟨fun s => dslope Z 1 s / ZS s, max σ₀ 1, fun σ hσ => ?_, fun σ hσ => ?_⟩
      · have h1 : ZS σ ≠ 0 := by simpa using hne σ hσ
        have hσ' : 0 < (σ : ℂ).re := by simpa using hσ
        exact (hD.analyticAt (re_mem hσ')).div (hZS.analyticAt (re_mem hσ')) h1
      · have hσ1 : 1 < σ := lt_of_le_of_lt (le_max_right _ _) hσ
        have hσ0 : σ₀ < σ := lt_of_le_of_lt (le_max_left _ _) hσ
        have h1 : ZS σ ≠ 0 := by simpa using hne σ (by linarith)
        have h2 := heq σ (by simpa using hσ0)
        have hne1 : (σ : ℂ) ≠ 1 := by
          intro h; have := congrArg Complex.re h; simp at this; linarith
        have hsub : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.2 hne1
        rw [if_neg hP]
        simp only [Complex.ofReal_zero, zero_mul, add_zero, one_mul]
        rw [dslope_of_ne _ hne1, slope_def_field, h2, hz1]
        field_simp
        ring
    · refine ⟨fun s => Z (s + u * Complex.I) / ((s + u * Complex.I - 1) * ZS (s + u * Complex.I)), max σ₀ 1,
        fun σ hσ => ?_, fun σ hσ => ?_⟩
      · have hre : 0 < ((σ : ℂ) + (u : ℂ) * Complex.I).re := by rw [re_shift]; exact hσ
        have hsh : AnalyticAt ℂ (fun s : ℂ => s + (u : ℂ) * Complex.I) (σ : ℂ) :=
          analyticAt_id.add analyticAt_const
        have hZa : AnalyticAt ℂ (fun s : ℂ => Z (s + u * Complex.I)) (σ : ℂ) :=
          AnalyticAt.comp (g := Z) (f := fun s : ℂ => s + (u : ℂ) * Complex.I) (x := (σ : ℂ)) (hZ.analyticAt (re_mem hre)) hsh
        have hZSa : AnalyticAt ℂ (fun s : ℂ => ZS (s + u * Complex.I)) (σ : ℂ) :=
          AnalyticAt.comp (g := ZS) (f := fun s : ℂ => s + (u : ℂ) * Complex.I) (x := (σ : ℂ)) (hZS.analyticAt (re_mem hre)) hsh
        have hlin : AnalyticAt ℂ (fun s : ℂ => s + u * Complex.I - 1) (σ : ℂ) := hsh.sub analyticAt_const
        have hne2 : ((σ : ℂ) + u * Complex.I - 1) ≠ 0 := by
          intro h; have := congrArg Complex.im h; simp at this; exact hu this
        exact hZa.div (hlin.mul hZSa) (mul_ne_zero hne2 (hne σ hσ))
      · have hσ1 : 1 < σ := lt_of_le_of_lt (le_max_right _ _) hσ
        have hσ0 : σ₀ < σ := lt_of_le_of_lt (le_max_left _ _) hσ
        have hne2 : ((σ : ℂ) + u * Complex.I - 1) ≠ 0 := by
          intro h; have := congrArg Complex.im h; simp at this; exact hu this
        have h1 := hne σ (by linarith)
        have h2 := heq ((σ : ℂ) + u * Complex.I) (by rw [re_shift]; exact hσ0)
        rw [if_neg hP, one_mul]
        show Z ((σ : ℂ) + u * Complex.I) / (((σ : ℂ) + u * Complex.I - 1) * ZS ((σ : ℂ) + u * Complex.I)) = _
        rw [h2]
        field_simp

theorem analyticAt_conj {G : ℂ → ℂ} {σ : ℝ} (h : AnalyticAt ℂ G σ) :
    AnalyticAt ℂ (fun s => conj (G (conj s))) σ := by
  obtain ⟨t, ht, hto, hσt⟩ := eventually_nhds_iff.1 h.eventually_analyticAt
  have hU : IsOpen ((starRingEnd ℂ) ⁻¹' t) := hto.preimage Complex.continuous_conj
  have hσU : (σ : ℂ) ∈ (starRingEnd ℂ) ⁻¹' t := by simpa [Complex.conj_ofReal] using hσt
  refine DifferentiableOn.analyticAt (s := (starRingEnd ℂ) ⁻¹' t) (fun z hz => ?_) (hU.mem_nhds hσU)
  have h1 := ((ht _ hz).differentiableAt).conj_conj
  rw [Complex.conj_conj] at h1
  exact h1.differentiableWithinAt

end RankinSelbergUnitary

open RankinSelbergUnitary Classical in
theorem rankin_selberg_unitary_of_pole : NormEx → SatTw → RSPole → RSU := by
  intro hN hT hR E _ _ _ m k π π' hm hk hu hu'
  obtain ⟨ν, hν, hrep⟩ := hN E
  obtain ⟨π₀, τ, hn, rfl⟩ := hrep m π hm hu
  obtain ⟨π₀', τ', hn', rfl⟩ := hrep k π' hk hu'
  have hval : ∀ (t : ℝ) {S : Finset (HeightOneSpectrum (𝓞 E))} (w : Off E S),
      ((((ν t)⁻¹).val w.1 : ℂˣ) : ℂ) = (nq w : ℂ) ^ ((t : ℂ) * Complex.I) :=
    fun t S w => val_inv_eq (ν t) t (fun w => (hν t w).2) w
  have hunr : ∀ t w, (ν t).UnrAt w := fun t w => (hν t w).1
  rcases le_or_gt k m with hkm | hmk
  · obtain ⟨S₀, hc⟩ := core hR m k π₀ π₀' (τ - τ') hk hkm hn hn'
    refine ⟨S₀, fun S hS α β hα hβ => ?_⟩
    obtain ⟨G, σ₀, hG, hGe⟩ := hc S hS _ _ (transfer hT _ (ν τ) S (hunr τ) α hα)
      (transfer hT _ (ν τ') S (hunr τ') β hβ)
    set Q : Prop := (⟨m, (CG.mk π₀).twist (ν τ)⟩ : Σ a, CG E a) = ⟨k, (CG.mk π₀').twist (ν τ')⟩ with hQ
    set P : Prop := (⟨m, CG.mk π₀⟩ : Σ a, CG E a) = ⟨k, CG.mk π₀'⟩ ∧ τ - τ' = 0 with hPd
    have hPQ : P → Q := by
      rintro ⟨h1, h2⟩
      have e : τ' = τ := by linarith
      subst e
      obtain ⟨rfl, h3⟩ := Sigma.mk.inj_iff.1 h1
      rw [hQ, eq_of_heq h3]
    refine ⟨fun s => (if Q ∧ ¬ P then s - 1 else 1) * G s, σ₀, fun σ hσ => ?_, fun σ hσ => ?_⟩
    · by_cases hc' : Q ∧ ¬ P
      · simp only [if_pos hc']
        exact (analyticAt_id.sub analyticAt_const).mul (hG σ hσ)
      · simp only [if_neg hc', one_mul]
        exact hG σ hσ
    · show (if Q ∧ ¬ P then (σ : ℂ) - 1 else 1) * G σ = _
      rw [hGe σ hσ, ← LS_shift α β _ _ τ τ' (hval τ) (hval τ') σ]
      by_cases hq : Q <;> by_cases hp : P
      · rw [if_neg (fun h => h.2 hp), if_pos hp, if_pos hq, one_mul]
      · rw [if_pos ⟨hq, hp⟩, if_neg hp, if_pos hq, one_mul]
      · exact absurd (hPQ hp) hq
      · rw [if_neg (fun h => hq h.1), if_neg hp, if_neg hq, one_mul]
  · obtain ⟨S₀, hc⟩ := core hR k m π₀' π₀ (τ' - τ) hm hmk.le hn' hn
    refine ⟨S₀, fun S hS α β hα hβ => ?_⟩
    obtain ⟨G, σ₀, hG, hGe⟩ := hc S hS _ _ (transfer hT _ (ν τ') S (hunr τ') β hβ)
      (transfer hT _ (ν τ) S (hunr τ) α hα)
    set Q : Prop := (⟨m, (CG.mk π₀).twist (ν τ)⟩ : Σ a, CG E a) = ⟨k, (CG.mk π₀').twist (ν τ')⟩ with hQ
    set P : Prop := (⟨k, CG.mk π₀'⟩ : Σ a, CG E a) = ⟨m, CG.mk π₀⟩ ∧ τ' - τ = 0 with hPd
    have hPQ : P → Q := by
      rintro ⟨h1, h2⟩
      have e : τ' = τ := by linarith
      subst e
      obtain ⟨rfl, h3⟩ := Sigma.mk.inj_iff.1 h1
      rw [hQ, eq_of_heq h3]
    refine ⟨fun s => (if Q ∧ ¬ P then s - 1 else 1) * conj (G (conj s)), σ₀, fun σ hσ => ?_, fun σ hσ => ?_⟩
    · by_cases hc' : Q ∧ ¬ P
      · simp only [if_pos hc']
        exact (analyticAt_id.sub analyticAt_const).mul (analyticAt_conj (hG σ hσ))
      · simp only [if_neg hc', one_mul]
        exact analyticAt_conj (hG σ hσ)
    · show (if Q ∧ ¬ P then (σ : ℂ) - 1 else 1) * conj (G (conj (σ : ℂ))) = _
      rw [Complex.conj_ofReal, hGe σ hσ, map_mul]
      have hL : conj (LS S (fun w b => β w b * ((ν τ')⁻¹).val w.1) (fun w a => α w a * ((ν τ)⁻¹).val w.1)
          ((σ : ℂ) + ((τ' - τ : ℝ) : ℂ) * Complex.I)) =
          LS S (fun w a => α w a * ((ν τ)⁻¹).val w.1) (fun w b => β w b * ((ν τ')⁻¹).val w.1)
            ((σ : ℂ) + ((τ - τ' : ℝ) : ℂ) * Complex.I) := by
        unfold LS
        rw [conj_eul]
        congr 1
        simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
        push_cast
        ring
      rw [hL, LS_shift α β _ _ τ τ' (hval τ) (hval τ') σ]
      have hcif : conj (if P then (σ : ℂ) - 1 else 1) = if P then (σ : ℂ) - 1 else 1 := by
        split_ifs <;> simp [Complex.conj_ofReal]
      rw [hcif]
      by_cases hq : Q <;> by_cases hp : P
      · rw [if_neg (fun h => h.2 hp), if_pos hp, if_pos hq, one_mul]
      · rw [if_pos ⟨hq, hp⟩, if_neg hp, if_pos hq, one_mul]
      · exact absurd (hPQ hp) hq
      · rw [if_neg (fun h => hq h.1), if_neg hp, if_neg hq, one_mul]

end PositivityTheory.RgJS
