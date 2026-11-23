import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoNuFin

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter
open scoped TensorProduct

def qV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (Nat.card (𝓞 F ⧸ v.asIdeal) : ℝ)

def QvSum : Prop := ∀ (F : Type) [Field F] [NumberField F],
  Summable fun v : HeightOneSpectrum (𝓞 F) => (qV v)⁻¹ ^ 2

def ArchPos : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∃ Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φinf ∧ HasCompactSupport Φinf ∧
      ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) ≠ 0

def LocPos : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ∃ Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φv ∧
      ∫ X, Φv X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) ≠ 0

def DensAA : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ C : ℝ,
    ∀ᶠ v in cofinite,
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ‖∫ X, (latV b v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) - 1‖ ≤
      C * (qV v)⁻¹ ^ 2

theorem nuNeZero_of_dens (hA : ArchPos) (hL : LocPos) (hD : DensAA) (hQ : QvSum) : NuNeZero := by
  classical
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν h0
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨⟨μinf, hμinf⟩, a1⟩ := hν.2
  obtain ⟨⟨νinf, hνinf⟩, a2⟩ := a1 μinf hμinf
  obtain ⟨⟨μv, hμv⟩, a3⟩ := a2 νinf hνinf
  obtain ⟨⟨νv, hνv⟩, a4⟩ := a3 μv hμv
  obtain ⟨⟨fibInf, hfi⟩, a5⟩ := a4 νv hνv
  obtain ⟨⟨fibV, hfv⟩, a6⟩ := a5 fibInf hfi
  let b := Module.finBasis F E
  obtain ⟨C, hC⟩ := hD F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ _ b
  obtain ⟨Φinf, hcΦ, hcs, hIinf⟩ :=
    hA F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fibInf hfi
  have hpos := fun v => hL F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v)
    (νv v) (hνv v) (fibV v) (hfv v)
  choose Φp hΦpSB hΦp using hpos
  let I : HeightOneSpectrum (𝓞 F) → ℂ := fun v =>
    ∫ X, (latV b v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 F) => C * (qV v)⁻¹ ^ 2 := (hQ F).mul_left C
  have hsmall : ∀ᶠ v in cofinite, C * (qV v)⁻¹ ^ 2 < 1 :=
    hsum.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)
  let good : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    ‖I v - 1‖ ≤ C * (qV v)⁻¹ ^ 2 ∧ C * (qV v)⁻¹ ^ 2 < 1
  have hgood : ∀ᶠ v in cofinite, good v := by
    filter_upwards [hC, hsmall] with v hv1 hv2
    exact ⟨hv1 (μv v) (hμv v) (νv v) (hνv v) (fibV v) (hfv v), hv2⟩
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ := fun v =>
    if good v then (latV b v).indicator 1 else Φp v
  let Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ := fun Y => ∏ᶠ v, Φv v (projV v Y)
  let Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ := fun X => Φinf (projInf X) * Φf (projFin X)
  have hSB : ∀ v, IsSB (Φv v) := fun v => by
    by_cases h : good v
    · rw [show Φv v = (latV b v).indicator 1 from if_pos h]
      exact PositiveNearLattice.isSB_latV b v a M
    · rw [show Φv v = Φp v from if_neg h]
      exact hΦpSB v
  have hpure : IsPureFin b Φf Φv := by
    refine ⟨hSB, ?_, fun _ => rfl⟩
    filter_upwards [hgood] with v hv
    exact if_pos hv
  obtain ⟨-, -, heq⟩ := a6 fibV hfv _ b Φ Φinf Φf Φv hcΦ hcs hpure (fun _ => rfl)
  rw [h0, integral_zero_measure] at heq
  let Jv : HeightOneSpectrum (𝓞 F) → ℂ := fun v =>
    ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))
  have hJ0 : ∀ v, Jv v ≠ 0 := fun v => by
    by_cases h : good v
    · have e : Jv v = I v := by
        simp only [Jv, I, Φv, if_pos h]
      rw [e]
      intro hI
      have := h.1
      rw [hI, zero_sub, norm_neg, norm_one] at this
      linarith [h.2]
    · have e : Jv v = ∫ X, Φp v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) := by
        simp only [Jv, Φv, if_neg h]
      rw [e]
      exact hΦp v
  have hJs : Summable fun v => ‖Jv v - 1‖ := by
    refine Summable.of_norm_bounded_eventually hsum ?_
    filter_upwards [hgood] with v hv
    have e : Jv v = I v := by
      simp only [Jv, I, Φv, if_pos hv]
    rw [e, norm_norm]
    exact hv.1
  have hne : ∏' v, (1 + (Jv v - 1)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (fun v => by rw [add_sub_cancel]; exact hJ0 v) hJs
  simp only [add_sub_cancel] at hne
  exact mul_ne_zero hIinf hne heq.symm

end PI.VolStabSW
