import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SecondDerivativeHolds

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

section

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kSpan_top_B {x : smD ε σ} (hW : IsKStableSub ε (smE ε σ) (Formalism.REAL.kSpan ε (smE ε σ) x))
    (x' : Formalism.REAL.kSpan ε (smE ε σ) x) {c : ℂ} (hc : c ≠ 0) (hx' : (x' : smD ε σ) = c • x) :
    Formalism.REAL.kSpan ε (resB _ hW) x' = ⊤ := by
  let M : Submodule ℂ (smD ε σ) := (Formalism.REAL.kSpan ε (resB _ hW) x').map (Formalism.REAL.kSpan ε (smE ε σ) x).subtype
  have hM : Formalism.REAL.KStable ε (smE ε σ) M := by
    rintro a b hab _ ⟨z, hz, rfl⟩
    refine ⟨resB _ hW a b z, Formalism.REAL.compact_span_stable x' a b hab z hz, ?_⟩
    simp [resB_apply hW hab]
  have hxM : x ∈ M := by
    have h1 : (x' : smD ε σ) ∈ M := ⟨x', Formalism.REAL.mem_compact_span_self x', rfl⟩
    have h2 := M.smul_mem c⁻¹ h1
    rwa [hx', smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
  have hle : Formalism.REAL.kSpan ε (smE ε σ) x ≤ M := Formalism.REAL.compact_span_le_stable hxM hM
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨z', hz', he⟩ := hle z.2
  have : z' = z := Subtype.ext he
  exact this ▸ hz'

theorem kSpan_fin_B (hK : KFSm) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) {v : smD ε σ} (hv : v ∈ KF ε σ) :
    FiniteDimensional ℂ (Formalism.REAL.kSpan ε (smE ε σ) v) ∧
      IsKStableSub ε (smE ε σ) (Formalism.REAL.kSpan ε (smE ε σ) v) := by
  obtain ⟨S, hSf, hvS, -, hSst, -⟩ := exists_sub_B hK hσ hirr hv
  exact ⟨Submodule.finiteDimensional_of_le (Formalism.REAL.compact_span_le_stable hvS hSst), Formalism.REAL.compact_span_stable v⟩

end

theorem uAdm_of (hK : KFSm) : UAdm := by
  classical
  intro n ε H _ _ _ σ hσ hirr μ
  have hD := isDerivedOn_smE hσ
  set A := {v : smD ε σ | v ∈ KF ε σ ∧ IsKHWVec ε (smE ε σ) μ v} with hA
  by_cases h0 : ∀ v ∈ A, v = 0
  · have : Submodule.span ℂ A = ⊥ := Submodule.span_eq_bot.2 h0
    rw [this]; infer_instance
  push_neg at h0
  obtain ⟨v₀, hv₀A, hv₀0⟩ := h0

  have key : ∀ v ∈ A, v ≠ 0 → ∃ (hf : FiniteDimensional ℂ (Formalism.REAL.kSpan ε (smE ε σ) v))
      (hst : IsKStableSub ε (smE ε σ) (Formalism.REAL.kSpan ε (smE ε σ) v)) (w : Formalism.REAL.kSpan ε (smE ε σ) v),
      ((w : smD ε σ) = ((‖v‖⁻¹ : ℝ) : ℂ) • v) ∧ ‖w‖ = 1 ∧ Formalism.REAL.KHighest ε (resB _ hst) μ w ∧
      Formalism.REAL.kSpan ε (resB _ hst) w = ⊤ := by
    intro v hvA hv0
    obtain ⟨hf, hst⟩ := kSpan_fin_B hK hσ hirr hvA.1
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    let w : Formalism.REAL.kSpan ε (smE ε σ) v :=
      ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, Submodule.smul_mem _ _ (Formalism.REAL.mem_compact_span_self v)⟩
    refine ⟨hf, hst, w, rfl, ?_, ⟨fun a => ?_, fun a b hab he => ?_⟩, kSpan_top_B hst w ?_ rfl⟩
    · show ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]
    · apply Subtype.ext
      rw [resB_apply hst rfl]
      show smE ε σ a a (((‖v‖⁻¹ : ℝ) : ℂ) • v) = _
      rw [map_smul, hvA.2.1 a, smul_comm]
      rfl
    · apply Subtype.ext
      rw [resB_apply hst he]
      show smE ε σ a b (((‖v‖⁻¹ : ℝ) : ℂ) • v) = _
      rw [map_smul, hvA.2.2 a b hab he, smul_zero]
      rfl
    · exact_mod_cast inv_ne_zero hn
  obtain ⟨hf₀, hst₀, w₀, hw₀, hw₀1, hw₀h, hw₀T⟩ := key v₀ hv₀A hv₀0
  let Sh : Submodule ℂ H := (Formalism.REAL.kSpan ε (smE ε σ) v₀).map (smD ε σ).subtype
  have hShf : FiniteDimensional ℂ Sh := Module.Finite.map (Formalism.REAL.kSpan ε (smE ε σ) v₀) _
  have hShK : Formalism.MainNotions.S.IsKStableOn ε σ Sh := by
    rintro g hg _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hye⟩ := kStable_of_isKStableSub hσ hD (Formalism.REAL.kSpan ε (smE ε σ) v₀) hf₀ hst₀ g hg x hx
    exact ⟨y, hy, hye⟩
  have hM : Formalism.MainNotions.BridgeCPX.HCMult := CompanionTheory.HCMult.harish_chandra_multiplicity
  have hfin := hM n ε H σ hσ hirr Sh hShf hShK
  set Q := Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) Sh
  let e₀ : (Formalism.REAL.kSpan ε (smE ε σ) v₀) ≃ₗ[ℂ] Sh := Submodule.equivMapOfInjective _ Subtype.val_injective (Formalism.REAL.kSpan ε (smE ε σ) v₀)
  have hmem : ∀ v ∈ A, (v : H) ∈ Q := by
    intro v hvA
    by_cases hv0 : v = 0
    · rw [hv0]; exact Q.zero_mem
    obtain ⟨hf, hst, w, hw, hw1, hwh, hwT⟩ := key v hvA hv0
    obtain ⟨φ, hφ, hφw⟩ := ReciprocityTheory.ChartRestriction.DS.HW.uq_exists_isometry ε (resB (Formalism.REAL.kSpan ε (smE ε σ) v₀) hst₀) (resB _ hst) μ w₀ w
      (kRel_resB hσ hst₀) (kRel_resB hσ hst) (kUnit_resB hσ hst₀) (kUnit_resB hσ hst) hw₀h hwh hw₀1 hw1 hw₀T hwT
    let Θ : Sh →ₗ[ℂ] H := (smD ε σ).subtype ∘ₗ (Formalism.REAL.kSpan ε (smE ε σ) v).subtype ∘ₗ
      (φ.toLinearEquiv : (Formalism.REAL.kSpan ε (smE ε σ) v₀) →ₗ[ℂ] _) ∘ₗ (e₀.symm : Sh →ₗ[ℂ] (Formalism.REAL.kSpan ε (smE ε σ) v₀))
    have hΘ : ∀ (a : Formalism.REAL.KG ε) (x y : Sh), (y : H) = σ (Formalism.REAL.toMK a) x →
        Θ y = σ (Formalism.REAL.toMK a) (Θ x) := by
      intro a x y hxy
      have hx : ((e₀.symm x : (Formalism.REAL.kSpan ε (smE ε σ) v₀)) : smD ε σ) = (x : H) := by
        obtain ⟨x', rfl⟩ := e₀.surjective x; simp; rfl
      have hy : ((e₀.symm y : (Formalism.REAL.kSpan ε (smE ε σ) v₀)) : smD ε σ) = (y : H) := by
        obtain ⟨y', rfl⟩ := e₀.surjective y; simp; rfl
      have := intertwiner_comm_kset (W' := Formalism.REAL.kSpan ε (smE ε σ) v) hσ hst₀ hst φ.toLinearEquiv.toLinearMap
        (fun a b hab z => hφ a b hab z) a.2 (e₀.symm x) (e₀.symm y) (by rw [hx, hy]; exact hxy)
      exact this
    have hrange : LinearMap.range Θ ≤ Q := le_sSup ⟨Θ, hΘ, rfl⟩
    refine hrange ⟨((‖v‖ : ℝ) : ℂ) • e₀ w₀, ?_⟩
    rw [map_smul]
    have h1 : Θ (e₀ w₀) = (((φ w₀ : Formalism.REAL.kSpan ε (smE ε σ) v) : smD ε σ) : H) := by
      show ((smD ε σ).subtype ((Formalism.REAL.kSpan ε (smE ε σ) v).subtype
        (φ.toLinearEquiv (e₀.symm (e₀ w₀))))) = _
      rw [LinearEquiv.symm_apply_apply]
      rfl
    rw [h1, hφw, hw]
    simp only [Submodule.coe_smul]
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv0), Complex.ofReal_one, one_smul]
  have hle : Submodule.span ℂ A ≤ Q.comap (smD ε σ).subtype := Submodule.span_le.2 fun v hv => hmem v hv
  have hcf : FiniteDimensional ℂ (Q.comap (smD ε σ).subtype) := by
    have e := Submodule.equivMapOfInjective (smD ε σ).subtype Subtype.val_injective (Q.comap (smD ε σ).subtype)
    have : FiniteDimensional ℂ ((Q.comap (smD ε σ).subtype).map (smD ε σ).subtype) :=
      Submodule.finiteDimensional_of_le (Submodule.map_comap_le _ _)
    exact LinearEquiv.finiteDimensional e.symm
  exact Submodule.finiteDimensional_of_le hle

end CompanionTheory.D.gk.HC
