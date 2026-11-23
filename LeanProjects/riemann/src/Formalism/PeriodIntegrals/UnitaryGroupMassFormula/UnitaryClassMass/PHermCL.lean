import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermSk

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def TensLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∃ δ : 𝓞 F, δ ≠ 0 ∧ ∀ (t : HeightOneSpectrum (𝓞 F)) (e : E) (c : 𝓞 F),
      (∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (t.adicCompletion F) (PI.UnitaryApproxDefs.intOE E) (t.adicCompletionIntegers F).toSubring,
        PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) e =
          PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) (algebraMap F E (c : F)) * s) →
      ∃ r ∈ Sw F E t, ∃ y : 𝓞 E, (r : E) * (algebraMap F E (δ : F) * e) = algebraMap F E (c : F) * (y : E)

def LatClose : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ e, σ (σ e) = e) → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J → IsUnit J.det → Submodule.IsLattice E L0 →
    ∀ g : GL (Fin M) E, g ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ D' : 𝓞 F, D ∣ D' → ∀ γ : GL (Fin M) E, γ ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
      ∀ S : Submonoid (𝓞 E), (∀ r ∈ S, σ (r : E) = r) →
      (∀ i j, ∃ r ∈ S, ∃ y : 𝓞 E,
        (r : E) * ((g : Matrix (Fin M) (Fin M) E) i j - (γ : Matrix (Fin M) (Fin M) E) i j) =
          algebraMap F E (D' : F) * (y : E)) →
      locS S (gmap (linOf b γ) L0) = locS S (gmap (linOf b g) L0)

theorem closeLoc_of (hT : TensLoc) (hL : LatClose) : CloseLoc := by
  intro F E _ _ _ _ _ σ V _ _ _ _ _ M J b L0 hσσ hH hdet hL0 g hg
  obtain ⟨δ, hδ, hTδ⟩ := hT F E
  obtain ⟨D, hD, hDcl⟩ := hL F E σ V M J b L0 hσσ hH hdet hL0 g hg
  refine ⟨δ * D, mul_ne_zero hδ hD, fun D' hD' γ hγ t hcong => ?_⟩
  obtain ⟨k, rfl⟩ := hD'
  refine hDcl (D * k) (dvd_mul_right D k) γ hγ (Sw F E t) ?_ ?_
  · rintro r ⟨a, -, rfl⟩
    change σ (algebraMap F E (a : F)) = algebraMap F E (a : F)
    exact σ.commutes _
  · intro i j
    obtain ⟨s, hs, he⟩ := hcong i j
    obtain ⟨r, hr, y, hry⟩ := hTδ t (((g : Matrix (Fin M) (Fin M) E) i j) - (γ : Matrix (Fin M) (Fin M) E) i j)
      (δ * D * k) ⟨s, hs, by rw [map_sub]; exact he⟩
    refine ⟨r, hr, y, ?_⟩
    have hδF : (δ : F) ≠ 0 := by simpa using hδ
    have hδE : algebraMap F E (δ : F) ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).2 hδF
    apply mul_left_cancel₀ hδE
    have e1 : ((δ * D * k : 𝓞 F) : F) = (δ : F) * ((D * k : 𝓞 F) : F) := by push_cast; ring
    rw [e1, map_mul] at hry
    linear_combination hry

theorem hermitian_approximation_of_parts (hL : LocSw) (hT : TensLoc) (hC : LatClose) (hW : WPlace) (hB : BcU) (hG : GramOK) :
    HermApprox := hermApprox_of hL (closeLoc_of hT hC) hW hB hG

end PI.UnitaryGroupMassFormula.UJClassMass

end
