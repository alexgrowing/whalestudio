import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DictionaryRationalElementAnalyticPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem laws_cast {D : D7} {T : CoreJ D} (L : LawsJ T) {j : ℕ} (hj : InR D j) {σ : T.Q.c.F →+* ℂ}
    (hσ : GoodEmb T.Q.c σ) {W : HSp D} (hV : T.V j σ = W) (hr : W.rank = D.R.r) :
    (∀ k, ModelW W hr ((T.U j σ).X k)) ∧
    (∀ h, (castDict hV (T.dict j σ) h).2 ∈ ((T.U j σ).X (castDict hV (T.dict j σ) h).1).dom) ∧
    (∀ h, IsUnitFr ((T.U j σ).X (castDict hV (T.dict j σ) h).1) (castDict hV (T.dict j σ) h).2) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
      (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif (T.Q.Xo j) (σ.comp (IntermediateField.inclusion T.Q.c.le).toRingHom)
        (fun i => relab T.Q.c σ (e i).1))
      (ik : (T.U j σ).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ)
      (th : ∀ k, ((T.U j σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧
        DictLat (T.U j σ) W hr (castDict hV (T.dict j σ))
          (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) e F ik φ th (T.x₀ j σ) := by
  subst hV
  obtain ⟨_, hm⟩ := L.modelW j hj σ hσ
  obtain ⟨_, _, -, hd⟩ := L.dictU j hj σ hσ
  obtain ⟨_, g, e, F, ik, φ, th, -, -, h1, h2⟩ := L.adPin j hj σ hσ
  exact ⟨hm, hd.2.2.2.1, (L.muUnit j hj σ hσ).2.2.2, g, e, F, ik, φ, th, h1, h2⟩

theorem exists_type_equiv {D : D7} (Q : Par D) (hp : Q.PinHost) (Ψ : Finset (D.host.E →+* ℂ))
    (hΨ : ∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ τ (Q.H.rt : D.host.E) = Q.H.rt0) :
    ∃ eT : D.what₂.Tau ≃ Ψ, ∀ ρ, (eT ρ).1 = tauE D ρ := by
  refine ⟨Equiv.ofBijective (fun ρ => ⟨tauE D ρ, (hΨ _).2 (hp.2.2.2 ρ)⟩) ⟨fun a b h => ?_, fun τ => ?_⟩, fun _ => rfl⟩
  · exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 (congrArg Subtype.val h)))
  · obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi Q hp τ.1 ((hΨ _).1 τ.2)
    exact ⟨t, Subtype.ext ht.symm⟩

end GlobalTheory.OneMapRef
