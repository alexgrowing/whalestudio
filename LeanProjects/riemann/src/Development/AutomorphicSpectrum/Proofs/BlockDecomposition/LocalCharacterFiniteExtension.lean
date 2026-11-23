import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisCharacterPadicAlgClosureEqOne
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.HeckeChar

theorem exists_unit_model : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (μ : G E Ω →* (Qbar l)ˣ), Continuous μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
    ∃ (LL' : FinExt l) (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ), Bw.LL.1 ≤ LL'.1 ∧
      IsModel Bw ((rk1 μ).comp (Dec (F := E) A).subtype) LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) ∧
      (∀ g, ((ψ g : ↥LL'.1) : Qbar l) = ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l)) ∧
      Continuous (fun g => ((ψ g : ↥LL'.1) : Qbar l)) ∧ ∀ g, ‖((ψ g : ↥LL'.1) : Qbar l)‖ = 1 := by
  intro E Ω _ _ _ _ _ l _ μ hμ w A _ O _ _ _ Bw
  have hc : Continuous fun g : G E Ω => ((μ g : (Qbar l)ˣ) : Qbar l) := Units.continuous_val.comp hμ
  have hent : ∀ (g : G E Ω) (i j : Fin 1),
      ((rk1 μ g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) i j = ((μ g : (Qbar l)ˣ) : Qbar l) := by
    intro g i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp [rk1]
  have hr : Continuous (fun g : G E Ω => ((rk1 μ g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l))) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact hc.congr fun g => (hent g i j).symm
  obtain ⟨L, hle, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) 1 (rk1 μ) hr Bw.LL
  have hmem : ∀ g : G E Ω, ((μ g : (Qbar l)ˣ) : Qbar l) ∈ L.1 := fun g => by
    have h := hL g 0 0
    rwa [hent] at h
  let ψ : ↥(Dec (F := E) A) →* (↥L.1)ˣ :=
    { toFun := fun g =>
        ⟨⟨((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l), hmem _⟩,
          ⟨((μ ((g : G E Ω)⁻¹) : (Qbar l)ˣ) : Qbar l), hmem _⟩,
          Subtype.ext (by simp [← Units.val_mul, ← map_mul]),
          Subtype.ext (by simp [← Units.val_mul, ← map_mul])⟩
      map_one' := Units.ext (Subtype.ext (by simp))
      map_mul' := fun g h => Units.ext (Subtype.ext (by simp)) }
  have hψ : ∀ g, ((ψ g : ↥L.1) : Qbar l) = ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l) := fun g => rfl
  refine ⟨L, ψ, hle, ⟨hle, ?_⟩, hψ, ?_, fun g => ?_⟩
  · refine MonoidHom.ext fun g => Units.ext ?_
    ext i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp [Formalism.MainNotions.N.mapRep, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, rk1, hψ]
  · exact hc.comp continuous_subtype_val
  · exact GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact μ hc _

end GlobalTheory.CompanionTheory.HeckeChar
