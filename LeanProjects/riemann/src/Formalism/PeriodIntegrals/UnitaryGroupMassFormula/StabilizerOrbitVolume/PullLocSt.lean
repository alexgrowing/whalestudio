import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.NuInvLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoMeas

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Matrix
open scoped TensorProduct

def CompG : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ g : HA (AF F) σ J, ∃ (hInf : HA (Ainf F) σ J) (hv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J),
    (∀ X : Fin a → Fin M → AF F ⊗[F] E, projInf (g • X) = hInf • projInf X) ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin a → Fin M → AF F ⊗[F] E),
      projV v (projFin (g • X)) = hv v • projV v (projFin X)) ∧
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in Filter.cofinite,
      ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, hv v • Y ∈ latV b v ↔ Y ∈ latV b v

def FibInvInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∀ (h : HA (Ainf F) σ J) (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ),
      Continuous Φinf → HasCompactSupport Φinf →
      ∫ X, Φinf (h • X) ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) =
        ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))

def FibInvV : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ∀ (h : HA (Fv F v) σ J) (Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φv →
      ∫ X, Φv (h • X) ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
        ∫ X, Φv X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT))

def smulHomeo {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) :
    (Fin a → Fin M → R ⊗[F] E) ≃ₜ (Fin a → Fin M → R ⊗[F] E) where
  toEquiv := MulAction.toPerm h
  continuous_toFun := by
    refine continuous_pi fun x => ?_
    change Continuous fun y : Fin a → Fin M → R ⊗[F] E =>
      ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (y x)
    exact continuous_const.matrix_mulVec (continuous_apply x)
  continuous_invFun := by
    refine continuous_pi fun x => ?_
    change Continuous fun y : Fin a → Fin M → R ⊗[F] E =>
      ((HA.mat R σ J h⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (y x)
    exact continuous_const.matrix_mulVec (continuous_apply x)

theorem pullLoc_of (hC : CompG) (hI : FibInvInf) (hV : FibInvV) : PullLoc := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ g d b Φ Φinf Φf Φv hcΦ hcs
    hpure hprod
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨hInf, hv, h1, h2, h3⟩ := hC F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g
  let eI := smulHomeo (Ainf F) σ (a := a) J hInf
  let eV := fun v => smulHomeo (Fv F v) σ (a := a) J (hv v)
  refine ⟨fun Y => Φinf (hInf • Y), fun Y => ∏ᶠ v, Φv v (hv v • projV v Y),
    fun v Y => Φv v (hv v • Y), hcΦ.comp eI.continuous, hcs.comp_homeomorph eI, ⟨?_, ?_, fun _ => rfl⟩,
    ?_, ?_, ?_⟩
  · intro v
    exact ⟨(hpure.1 v).1.comp_continuous (eV v).continuous, (hpure.1 v).2.comp_homeomorph (eV v)⟩
  · filter_upwards [hpure.2.1, h3 d b] with v hv1 hv2
    funext Y
    simp only [hv1, Set.indicator, Pi.one_apply]
    by_cases hY : Y ∈ latV b v
    · rw [if_pos ((hv2 Y).2 hY), if_pos hY]
    · rw [if_neg (fun h => hY ((hv2 Y).1 h)), if_neg hY]
  · intro X
    show Φ (g • X) = Φinf (hInf • projInf X) * ∏ᶠ v, Φv v (hv v • projV v (projFin X))
    rw [hprod (g • X), h1 X, hpure.2.2]
    congr 1
    refine finprod_congr fun v => ?_
    rw [h2 v X]
  · exact fun μinf hμinf νinf hνinf fibInf hfi =>
      hI F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fibInf hfi hInf Φinf
        hcΦ hcs
  · exact fun v μv hμv νv hνv fibV hfv =>
      hV F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμv νv hνv fibV hfv (hv v) (Φv v)
        (hpure.1 v)

end PI.VolStabSW
