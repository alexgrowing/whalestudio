import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRhoConjLatTpsi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SPiTopEqSTLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalHomOfNatCast
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NlenLeLenN

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.PtSel

theorem sameChar_eq_one {O₀ O₁ O₂ Γ : Type} [CommRing O₀] [CommRing O₁] [CommRing O₂] [Group Γ]
    {f₁ : O₀ →+* O₁} {f₂ : O₀ →+* O₂} {ψ₁ : Γ →* O₁ˣ} {ψ₂ : Γ →* O₂ˣ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f₁ f₂ ψ₁ ψ₂) (g : Γ) (hg : ψ₁ g = 1) : ψ₂ g = 1 := by
  have h1 := h (Finsupp.single g 1 + Finsupp.single 1 (-1))
  rw [Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul]),
    Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul])] at h1
  simp only [Finsupp.sum_single_index, map_zero, zero_mul, map_one, one_mul, map_neg, hg, Units.val_one,
    mul_one, add_neg_cancel, true_iff] at h1
  ext
  rw [Units.val_one]
  exact add_neg_eq_zero.1 h1

theorem sel_at (hC : GlobalTheory.TwSys.Cheb) (D : D7) (hT : TriplesGood D) (hG : GoodPtRow D) (hR : ResAbsIrr D)
    (a : D.nd.Loc) (ρ : D.nd.X a → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (π : D.nd.X a)
    (hπ : π ∈ D.nd.Zgood a) (hρ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π (ρ π))
    (j : D.ntw.Tw) (hj : D.ntw.twOf a = j) (k : ℕ) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok j k)ˣ)
    (f : D.ntw.O0 j →+* D.nd.O a) (hf : HEq f (D.ntw.twist₂ a))
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f (BlochKatoReduction.Gen.phiK D.ntw j k) (D.ntw.psiL a) ψ) :
    ∃ s : D.ntw.Sig j, BlochKatoReduction.Gen.goodS (BlochKatoReduction.bk0 D) j s ∧ D.ntw.side _ s = D.ntw.twSide a ∧
      (BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) j s k (D.nd.Q a) ψ ≠ ⊤ → Br.sFin D.loc D.nbr a ρ π) ∧
      ENNReal.ofReal (Br.sPi D.loc D.nbr a ρ π : ℝ) ≤ BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) j s k (D.nd.Q a) ψ ∧
      AttachedIn D a π j s := by
  subst hj
  obtain rfl := eq_of_heq hf
  obtain ⟨σ, Sg, hrow, hW, hX⟩ := hG a π hπ
  obtain ⟨s, htr, hgood⟩ := hT a σ Sg hrow hW
  obtain ⟨U, hU⟩ := GlobalTheory.PtCore.twistedRho_conj_latTpsi hC D a π ρ s Sg hρ hX htr (hR a π hπ _ hρ)
  have e1 := GlobalTheory.ConjLatticeSelmer.sPiTop_eq_sTLoc D a π ρ s U hU
  have e2 := GlobalTheory.SelmerSameChar.sTLoc_eq D a s k ψ hS
  have hψ : ∀ v ∈ placesOver D.host.E (D.ntw.l (D.ntw.twOf a)),
      ∀ g ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ g = 1 := by
    intro v hv g hg
    rw [D.ntw.twOf_l] at hv
    exact sameChar_eq_one hS g (D.ntw.psiL_l a v hv _ (D.nd.plOm.2 v) g hg)
  obtain ⟨h1, h2⟩ := GlobalTheory.SelTwistLe.sT_le_sLen D _ s k (D.nd.Q a) ψ hψ
  rw [← e2, ← e1] at h1 h2
  refine ⟨s, hgood, htr.2.1, ?_, ?_, ⟨rfl, σ, Sg, hrow, hW, hX, htr⟩⟩
  · intro hne
    have h3 := h1 hne
    unfold Br.sFin
    rw [lt_top_iff_ne_top]
    intro h4
    exact h3 (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_true])
  · by_cases h4 : Module.length (D.nd.O a) ↥(Br.selPi D.loc D.nbr a ρ π) = ⊤
    · have h5 : BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) _ s k (D.nd.Q a) ψ = ⊤ := by
        by_contra hne
        exact h1 hne (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_true])
      rw [h5]
      exact le_top
    · exact h2 _ (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_false, Br.sPi])

theorem selCore : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (C : NChoice D), NChTie D C → TriplesGood D → GoodPtRow D →
    ResAbsIrr D → SameTwist D C →
    ∀ ρ : ∀ i : D.nd.Loc, D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i)),
      (∀ i, ∀ π ∈ D.nd.Zgood i, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D i π (ρ i π)) → SelCore D C ρ := by
  intro hC D C hTie hT hG hR hS ρ hρ i π hπ
  obtain ⟨f, hf, hs⟩ := hS.exists_heq i
  obtain ⟨s, h1, h2, h3⟩ := sel_at hC D hT hG hR i (ρ i) π hπ (hρ i π hπ) _ (hTie.twOf_eq i) _ _ f hf hs
  rw [hTie.Q_eq i] at h3
  exact ⟨s, h1, h2.trans (hTie.twSide_eq i), h3⟩

end GlobalTheory.PtSel

end
