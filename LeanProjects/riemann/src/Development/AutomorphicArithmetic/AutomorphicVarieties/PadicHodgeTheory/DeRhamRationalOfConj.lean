import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.deRhamRational_of_conj :
    GlobalTheory.Published.DeRhamPotSemistable → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {n : ℕ} (r r' : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)) (p : GL (Fin n) (Qbar l)), Continuous r → (∀ g, r' g = p * r g * p⁻¹) → ∀ (HT : (F →+* Qbar l) → Multiset ℤ) (Q : ↥(Weil h) → ℂ[X]), DRat ι h r HT Q → DRat ι h r' HT Q := by
  intro hD F Ω _ _ _ _ _ l _ ι A w h n r r' p hc e HT Q H O _ _ _ Bw hj
  obtain ⟨h1, h2, h3⟩ := H O Bw hj
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨c1, -, -, c4⟩ := GlobalTheory.ConjLocal.local_conj l (UpperTheory.V.Loc.PP l) F Ω O _ Bw n _ _ p e
  have hp := hD.isPstAt T Bw r (Units.continuous_val.comp hc) h1
  have hw := (GlobalTheory.PstConj.main F Ω l ι n _ _ ⟨T⟩ w A h O Bw hj r r' p e hp).2
  exact ⟨c1 h1, fun τ L τ' hτ => c4 _ _ (h2 τ L τ' hτ), fun s => by rw [hw]; exact h3 s⟩
