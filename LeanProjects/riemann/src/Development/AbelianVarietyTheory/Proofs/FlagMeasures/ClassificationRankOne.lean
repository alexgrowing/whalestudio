import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.DSSU.Triv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_iso_of_irred {H' : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [Nontrivial H']
    (h : ∀ S : Submodule ℂ H', IsClosed (S : Set H') → S = ⊥ ∨ S = ⊤) : Nonempty (H' ≃ₗᵢ[ℂ] ℂ) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H')
  have hu : ‖((‖v‖⁻¹ : ℂ) • v)‖ = 1 := norm_smul_inv_norm hv
  set u := ((‖v‖⁻¹ : ℂ) • v)
  have hu0 : u ≠ 0 := by intro h0; rw [h0, norm_zero] at hu; exact zero_ne_one hu
  have hS : (ℂ ∙ u) = ⊤ := by
    rcases h (ℂ ∙ u) (Submodule.closed_of_finiteDimensional _) with h0 | h1
    · exact absurd (Submodule.span_singleton_eq_bot.1 h0) hu0
    · exact h1
  have hsurj : Function.Surjective (LinearIsometry.toSpanSingleton ℂ H' hu) := by
    intro x
    have hx : x ∈ (ℂ ∙ u) := by rw [hS]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨a, by simpa using ha⟩
  exact ⟨(LinearIsometryEquiv.ofSurjective _ hsurj).symm⟩

theorem det_eq_one_fin_one (g : Matrix (Fin 1) (Fin 1) ℂ) (h : g.det = 1) : g = 1 := by
  ext i j
  fin_cases i; fin_cases j
  rw [Matrix.det_unique] at h
  simpa using h

instance subsingleton_SUJ (ε : Fin 1 → Bool) : Subsingleton (SUJ ε) :=
  ⟨fun a b => Subtype.ext (Subtype.ext (Units.ext
    ((det_eq_one_fin_one _ a.2).trans (det_eq_one_fin_one _ b.2).symm)))⟩

theorem E0_fin_one (a b : Fin 1) : E0 a b = 0 := by
  fin_cases a; fin_cases b
  ext i j
  fin_cases i; fin_cases j
  simp [E0]

theorem Ec_zero_fin_one (ε : Fin 1 → Bool) (G : Matrix (Fin 1) (Fin 1) ℂ → ℂ) : Ec ε 0 G = 0 := by
  funext g
  simp [Ec, Rd, cpart1, cpart2]

theorem eq_zero_of_sum_fin_one (μ : Fin 1 → ℝ) (h : ∑ a, μ a = 0) : μ = 0 := by
  funext a; fin_cases a; simpa using h

theorem above_self {n : ℕ} (P : Fin n → Fin n → Prop) (μ : Fin n → ℝ) : Above P μ μ :=
  ⟨0, fun a b h => absurd rfl h, by simp⟩

theorem lowCh_fin_one_zero (ε : Fin 1 → Bool) : lowCh ε 0 = 0 := by
  funext a; fin_cases a; simp [lowCh, rhoNh, rhoCh]

theorem gelfVal_fin_one_zero (k : ℕ) : gelfVal (fun a : Fin 1 => ((0 : Fin 1 → ℝ) a : ℂ)) (k + 1) = 0 := by
  have hA : Formalism.REAL.Amat (fun c : Fin 1 => ((0 : Fin 1 → ℝ) c : ℂ) + (((1 : ℕ) : ℂ) - 1) / 2) = 0 := by
    ext i j; fin_cases i; fin_cases j; simp [Formalism.REAL.Amat]
  rw [gelfVal, hA]; simp

abbrev famOne : Fam 1 := ⟨fun _ => ℂ, fun _ => inferInstance, fun _ => inferInstance, fun _ _ => 1⟩

theorem classS_one (ε : Fin 1 → Bool) : ClassS ε := by
  have hSU : ∀ g ∈ SUset ε, g = 1 := fun g hg => det_eq_one_fin_one g hg.2
  have hpar : ∀ lam : Fin 1 → ℝ, IsParS lam → lam = 0 := fun lam h => eq_zero_of_sum_fin_one lam h.1
  have hpar0 : IsParS (0 : Fin 1 → ℝ) :=
    ⟨by simp, fun a b _ => Subsingleton.elim a b, fun a b => ⟨0, by simp⟩⟩
  refine ⟨famOne, ⟨?_, ?_⟩, ?_⟩
  · intro lam hlam
    obtain rfl := hpar lam hlam
    have hK : IsKTypeS ε 0 (famOne.π 0) (lowCh ε 0) ⊤ := by
      rw [lowCh_fin_one_zero]
      refine ⟨by simp, inferInstance, fun g _ v _ => Submodule.mem_top, fun S' _ _ => eq_bot_or_eq_top S',
        ⟨(1 : ℂ), Submodule.mem_top, one_ne_zero, fun θ _ => by simp [famOne]⟩, ?_⟩
      intro μ v hμ _ _ _
      rw [eq_zero_of_sum_fin_one μ hμ]
      exact above_self _ _
    refine ⟨⟨inferInstance, inferInstance, ⟨⟨rfl, fun a _ b _ => by ext; simp [famOne]⟩,
      fun g _ v => by simp [famOne], fun v => continuousOn_const⟩, fun S _ _ => eq_bot_or_eq_top S, ?_⟩, ?_, ?_, ?_⟩
    · intro μ hμ v w
      haveI := hμ
      exact (continuous_const : Continuous fun _ : SUJ ε => ⟪w, v⟫_ℂ).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · intro v w _ _
      refine ⟨fun g₀ _ => ⟨Set.univ, fun _ => ⟪w, v⟫_ℂ, isOpen_univ, trivial, contDiffOn_const,
        fun g _ _ => by simp [famOne]⟩, ?_⟩
      intro m g _
      rw [gelfVal_fin_one_zero, zero_mul]
      simp [gelfS, EwordS, cycWord, List.ofFn_succ, E0_fin_one, Ec_zero_fin_one]
    · refine ⟨⊤, hK, fun S hS => ?_⟩
      obtain ⟨v, hvS, hv0, _⟩ := hS.2.2.2.2.1
      rcases eq_bot_or_eq_top S with h | h
      · rw [h, Submodule.mem_bot] at hvS; exact absurd hvS hv0
      · exact h
    · intro μ S hS
      rw [eq_zero_of_sum_fin_one μ hS.1, lowCh_fin_one_zero]
      exact above_self _ _
  · intro lam lam' h h'
    obtain rfl := hpar lam h
    obtain rfl := hpar lam' h'
    exact ⟨fun _ => ⟨Equiv.refl _, fun _ => rfl, rfl⟩, fun _ => ⟨LinearIsometryEquiv.refl ℂ ℂ, fun _ _ _ => rfl⟩⟩
  · intro H' _ _ σ hσ
    obtain ⟨_, hnt, hu, hirr, _⟩ := hσ
    have h1 : ∀ g ∈ SUset ε, σ g = 1 := fun g hg => by rw [hSU g hg]; exact hu.1.1
    obtain ⟨T⟩ := exists_iso_of_irred (fun S hS => hirr S hS (fun g hg v hv => by rw [h1 g hg]; exact hv))
    refine ⟨0, hpar0, T, fun g hg v => ?_⟩
    rw [h1 g hg]
    simp [famOne]

theorem classU_zero : ClassU 0 := by
  refine ⟨fun _ _ => ℂ, fun _ _ => inferInstance, fun _ _ => inferInstance, fun _ _ _ => 1, ?_, ?_⟩
  · intro ε lam _
    have hK : ∀ μ : Fin 0 → ℝ, IsKTypeOf ε (fun _ => (1 : ℂ →L[ℂ] ℂ)) μ ⊤ := by
      intro μ
      exact ⟨inferInstance, fun g _ v _ => Submodule.mem_top, fun S' _ _ => eq_bot_or_eq_top S',
        ⟨(1 : ℂ), Submodule.mem_top, one_ne_zero, fun θ _ => by simp⟩,
        fun μ' v _ _ _ => ⟨0, by simp, Subsingleton.elim _ _⟩⟩
    refine ⟨⟨inferInstance, inferInstance, ⟨⟨rfl, fun a _ b _ => by ext; simp⟩,
      fun g _ v => by simp, fun v => continuousOn_const⟩, fun S _ _ => eq_bot_or_eq_top S, ?_⟩, ?_, ?_, ?_⟩
    · intro v w
      exact continuous_const.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · intro v w _ _
      refine ⟨fun g₀ _ => ⟨Set.univ, fun _ => ⟪w, v⟫_ℂ, isOpen_univ, trivial, contDiffOn_const,
        fun g _ _ => by simp⟩, ?_⟩
      intro m g _
      simp [gelf, gelfVal]
    · refine ⟨⊤, hK _, fun S hS => ?_⟩
      obtain ⟨v, hvS, hv0, _⟩ := hS.2.2.2.1
      rcases eq_bot_or_eq_top S with h | h
      · rw [h, Submodule.mem_bot] at hvS; exact absurd hvS hv0
      · exact h
    · intro μ S _
      exact ⟨0, by simp, Subsingleton.elim _ _⟩
  · intro ε H' _ _ σ hσ
    obtain ⟨_, hnt, hu, hirr, _⟩ := hσ
    have h1 : ∀ g : Matrix (Fin 0) (Fin 0) ℂ, σ g = 1 := fun g => by
      rw [Subsingleton.elim g 1]; exact hu.1.1
    obtain ⟨T⟩ := exists_iso_of_irred (fun S hS => hirr S hS (fun g _ v hv => by rw [h1 g]; exact hv))
    refine ⟨1, 0, ⟨fun a => a.elim0, fun a => a.elim0⟩, fun a => a.elim0, T, fun g _ v => ?_⟩
    simp [h1]

theorem classS_one_classU_zero : (∀ ε : Fin 1 → Bool, ClassS ε) ∧ ClassU 0 :=
  ⟨classS_one, classU_zero⟩

end GlobalTheory.DSSU.Triv
