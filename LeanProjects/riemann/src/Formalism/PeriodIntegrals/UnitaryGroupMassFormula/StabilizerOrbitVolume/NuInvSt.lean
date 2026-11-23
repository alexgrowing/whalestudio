import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoNuFin

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

def DetAdm : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  ∀ ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E),
    (∀ K, IsCompact K → ν1 K < ⊤) → (∀ K, IsCompact K → ν2 K < ⊤) →
    (∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2) → ν1 = ν2

def OmUniq : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ ν1 ν2, IsOmT F E σ M J ψ (gramE σ J X0) hT ν1 →
    IsOmT F E σ M J ψ (gramE σ J X0) hT ν2 → ν1 = ν2

def OmInv : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ g : HA (AF F) σ J, IsOmT F E σ M J ψ (gramE σ J X0) hT (νX.map fun y => g • y)

theorem continuous_smul_tup {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA (AF F) σ J) :
    Continuous (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) := by
  refine continuous_pi fun x => ?_
  change Continuous fun y : Fin a → Fin M → AF F ⊗[F] E =>
    ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec (y x)
  exact continuous_const.matrix_mulVec (continuous_apply x)

theorem nuInv_of (hU : OmUniq) (hI : OmInv) : NuInv := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν g s hs
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hm : Measurable (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) :=
    (continuous_smul_tup σ J g).measurable
  rw [← Measure.map_apply hm hs,
    hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ _ _
      (hI F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν g) hν]

theorem omUniq_of (hD : DetAdm) : OmUniq := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ ν1 ν2 h1 h2
  refine hD F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ν1 ν2
    (nuFin_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ ν1 h1)
    (nuFin_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ ν2 h2) fun Φ hΦ => ?_
  obtain ⟨d, b, Φinf, Φf, Φv, hcΦ, hcs, hpure, hprod⟩ := hΦ
  obtain ⟨⟨μinf, hμinf⟩, a1⟩ := h1.2
  obtain ⟨⟨νinf, hνinf⟩, a2⟩ := a1 μinf hμinf
  obtain ⟨⟨μv, hμv⟩, a3⟩ := a2 νinf hνinf
  obtain ⟨⟨νv, hνv⟩, a4⟩ := a3 μv hμv
  obtain ⟨⟨fibInf, hfi⟩, a5⟩ := a4 νv hνv
  obtain ⟨⟨fibV, hfv⟩, a6⟩ := a5 fibInf hfi
  have e1 := (a6 fibV hfv d b Φ Φinf Φf Φv hcΦ hcs hpure hprod).2.2
  have e2 := ((((((h2.2.2 μinf hμinf).2 νinf hνinf).2 μv hμv).2 νv hνv).2 fibInf hfi).2
    fibV hfv d b Φ Φinf Φf Φv hcΦ hcs hpure hprod).2.2
  rw [e1, e2]

end PI.VolStabSW
