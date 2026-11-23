import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.MainNotions.TruncatedSeriesCountingIdentities (Decl CoefExt locC chi1C)

namespace GlobalTheory.AmbWT

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : CoefExt D i w hw)

def coef : D.nd.O i →+* ↥C.LL.1 := C.inc.comp (D.nbr i w hw).toLL

def grp (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Br.G D.nbr i w hw →* GE D.nd :=
  (decS D.nd w).comp (Br.iota D.nbr i w hw)

theorem locC_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    locC C M g = (M (grp hw g)).map (coef C) := rfl

theorem localizedCoefficientChar_apply (g : Br.G D.nbr i w hw) :
    chi1C C g = Units.map (coef C : D.nd.O i →* ↥C.LL.1) (chiU D.nd i 1 (grp hw g)) := rfl

theorem locC_rTwO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    locC C (rTwO D.nd i r x) = twistM (locC C (rO D.nd i r x)) (chi1C C)⁻¹ := by
  refine MonoidHom.ext fun g => Matrix.ext fun a b => ?_
  rw [locC_apply]
  show coef C ((((chiU D.nd i 1)⁻¹ (grp hw g) : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (grp hw g) a b) =
    ((((chi1C C)⁻¹ g) : (↥C.LL.1)ˣ) : ↥C.LL.1) * (locC C (rO D.nd i r x) g) a b
  rw [map_mul, locC_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, localizedCoefficientChar_apply]
  rfl

open Classical in

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambW (D := D) i ρ π dc ∧ EmbeddingTypes.ambT2 (D := D) i ρ π dc := by
  intro D i r ρ π dc hG hd
  have hd' : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
    obtain ⟨e, he⟩ := hd
    refine ⟨e, fun g u => ?_⟩
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.overK, GlobalTheory.SummandJumps.matRep_apply]
    exact he g u
  have hc : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : CoefExt D i w hw),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locC C (WpO D.nd i ρ π))) ∧
        IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locC C (T2O D.nd i ρ π))) := by
    intro w hw C
    have h1 := (hG w hw C).2 π
    rw [← locC_rTwO] at h1
    exact (GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hd').1 h1
  refine ⟨fun _ w hw _ C => (hc w hw C).1, fun _ w hw _ C => ⟨(hc w hw C).2, ?_, ?_⟩⟩
  · exact (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) (D.nbr i w hw).Kw C.LL _ _ (hc w hw C).2).1
  · exact (hG w hw C).1.2.2.2.2.2.2

end GlobalTheory.AmbWT
