import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterInducedTied
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_induced_tied : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ₁ ψ₂ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ)
      (J₁ J₂ : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ),
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ₁ J₁ → PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ₂ J₂ →
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' (ψ₁ * ψ₂) (J₁ + J₂) := by
  first | exact @GlobalTheory.CompanionTheory.HLCMul.isdRJ_mul | exact GlobalTheory.CompanionTheory.HLCMul.isdRJ_mul | (intros; apply GlobalTheory.CompanionTheory.HLCMul.isdRJ_mul <;> assumption)
