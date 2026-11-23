import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistedTriples
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicEmbeddingsConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicAutomorphismUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompareIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelGLengthConjStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions GlobalTheory.TwistedSelmerCompare

namespace GlobalTheory.ConjLatticeSelmer

theorem extCond_eq_bkG (L : LocTheory) {l₁ l₂ : ℕ} [i₁ : Fact l₁.Prime] [i₂ : Fact l₂.Prime] (h : l₁ = l₂)
    {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [Algebra ℤ_[l₁] O₀] [Module.Finite ℤ_[l₁] O₀] [TopologicalSpace O₀] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l₂] O] [Module.Finite ℤ_[l₂] O] [TopologicalSpace O]
    (B₀ : LocBridge l₁ E Ω Gw O₀) (B : LocBridge l₂ E Ω Gw O) (h₀ : ∀ x, x ∈ A ↔ ‖B₀.j x‖ ≤ 1)
    (h₁ : ∀ x, x ∈ A ↔ ‖B.j x‖ ≤ 1) (f : O₀ →+* O) (hf : Function.Injective f) {k : ℕ}
    (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀) (M : ↥Gw →* Matrix (Fin k) (Fin k) O) (hM : M = mapM f M₀) :
    extCond f hf (WKG M₀) (Br.bkG B₀ (L l₁) (WKG M₀) M₀) (WKG M) = Br.bkG B (L l₂) (WKG M) M := by
  subst h hM
  cases Subsingleton.elim i₁ i₂
  obtain ⟨σ, hσ⟩ := GlobalTheory.EmbUnitBallConj.exists_conj l₁ Ω B₀.j B.j fun x => (h₀ x).symm.trans (h₁ x)
  have he : ∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l₁) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l₁) * σ⁻¹ := by
    intro g
    refine GlobalTheory.padicAlgCl_algEquiv_eq_of_eq_on_isAlgClosed l₁ Ω B.j _ _ fun x => ?_
    rw [B.e_comm, ← hσ, ← hσ, ← B₀.e_comm]
    simp
  have hz := DFunLike.congr_fun
    (padicInt_hom_ext (natCast_mem_maximalIdeal O) (f.comp (algebraMap ℤ_[l₁] O₀)) (algebraMap ℤ_[l₁] O))
  exact le_antisymm (GlobalTheory.BlochKatoBaseChangeLe.extCond_le_bkG l₁ (L l₁) E Ω Gw O₀ O B₀ B σ he f hf hz k M₀)
    (GlobalTheory.BlochKatoBaseChange.bkG_le_extCond l₁ (L l₁) E Ω Gw O₀ O B₀ B σ he f hf hz k M₀)

variable (D : D7)

theorem selT_eq_selG (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.nd.O a)ˣ)
    (hψ : ∀ v ∈ placesOver D.host.E (D.nd.l a), ∀ g ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ g = 1) :
    selT D.loc D.ntwbr _ s (D.nd.Q a) (D.ntw.twist₂ a) (twO_inj D.ntw a) ψ =
      Br.selG D.nd.plOm (D.nd.l a) (D.loc (D.nd.l a)) (D.nbr a) (↑(D.nd.S a) ∪ ↑(D.nd.Q a))
        (latTpsi D.ntw _ s (D.ntw.twist₂ a) ψ) := by
  have hl := D.ntw.twOf_l a
  have hS : setS D.ntw (D.ntw.twOf a) = ↑(D.nd.S a) := by
    rw [← TwistedTriples.badS_eq D a]
    unfold setS TwistedTriples.badS
    rw [hl]
  unfold selT Br.selG
  congr 1
  funext v
  unfold Formalism.GaloisCohomology.bkCond
  rw [hS]
  by_cases hv : v ∈ placesOver D.host.E (D.nd.l a)
  · have hv' : v ∈ placesOver D.host.E (D.ntw.l (D.ntw.twOf a)) := by rw [hl]; exact hv
    refine (if_pos hv').trans (Eq.trans ?_ (if_pos hv).symm)
    unfold condL Br.LlG
    rw [dif_pos hv, dif_pos hv']
    have := IsAlgClosure.isAlgClosed D.host.E (K := D.nd.Om)
    refine extCond_eq_bkG D.loc hl (D.nd.plOm.1 v) (D.ntwbr _ v hv') (D.nbr a v hv) (D.ntwbr_ind _ v hv')
      (D.nbr_ind a v hv) (D.ntw.twist₂ a) (twO_inj D.ntw a) ((latT D.ntw _ s).comp (decS D.nd v))
      ((latTpsi D.ntw _ s (D.ntw.twist₂ a) ψ).comp (decS D.nd v)) ?_
    ext g i j
    simp [latTpsi, twistM, mapM, hψ v hv g.1 g.2]
  · have hv' : v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf a)) := by rw [hl]; exact hv
    exact (if_neg hv').trans (if_neg hv).symm

theorem nlen_congr {O : Type} [CommRing O] (l : ℕ) (M N : Type) [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (h : Module.length O M = Module.length O N) :
    nlen (O := O) l M = nlen (O := O) l N := by
  unfold nlen lenUnit
  rw [h]

theorem sPiTop_eq_sTLoc (a : D.nd.Loc) (π : D.nd.X a)
    (ρ : D.nd.X a → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (s : D.ntw.Sig (D.ntw.twOf a))
    (U : GL (Fin D.R.r) (D.nd.O a))
    (hU : ∀ g, WpO D.nd a ρ π g * (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) =
      (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) * latTpsi D.ntw _ s (D.ntw.twist₂ a) (D.ntw.psiL a) g) :
    sPiTop D a ρ π = sTLoc D a s := by
  unfold sPiTop sTLoc sT
  rw [selT_eq_selG D a s _ fun v hv => D.ntw.psiL_l a v hv _ (D.nd.plOm.2 v), D.ntw.twOf_l]
  exact nlen_congr _ _ _ (GlobalTheory.T.selG_length_eq_of_conj _ _ D.nd.plOm (D.nd.l a) (D.nd.O a) (D.loc (D.nd.l a)) (D.nbr a)
    (↑(D.nd.S a) ∪ ↑(D.nd.Q a)) _ _ _ U hU).symm

end GlobalTheory.ConjLatticeSelmer

end
