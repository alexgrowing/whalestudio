import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharactersDeRhamJumpZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_induced_agree : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ),
      Continuous (fun g => ((ψ g : ↥LL'.1) : Qbar l)) → (∀ g, ‖((ψ g : ↥LL'.1) : Qbar l)‖ = 1) →
      ∀ V : Subgroup (G E Ω), IsOpen (V : Set (G E Ω)) →
      (∀ σ : ↥(Dec (F := E) A), (σ : G E Ω) ∈ V → (σ : G E Ω) ∈ Ine (F := E) A → ψ σ = 1) →
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ 0 := by
  first | exact @GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia | exact GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia | (intros; apply GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia <;> assumption)
