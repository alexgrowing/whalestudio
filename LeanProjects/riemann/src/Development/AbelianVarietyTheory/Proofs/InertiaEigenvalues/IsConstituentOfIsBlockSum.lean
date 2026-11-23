import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockJumpCount
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInclusion

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.ChiOneEnl

open GlobalTheory.IndefiniteRowSideFullHecke

theorem isConstituent_of_isBlockSum (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (h : BlockJumpCount.IsBlockSum D.nd i r ρ π) :
    BlockCharactersCrystallineNonGaloisCusps.IsConstituent D i (chiU D.nd i 1) (rO D.nd i r π) := by
  obtain ⟨e, he⟩ := h
  let c : Fin D.R.t := ⟨0, D.R.t_odd.pos⟩
  refine ⟨e.symm (0, Pi.single c 1), ?_, fun g => ?_⟩
  · intro h0
    have h1 := congrArg (fun u => (e u).2 c) h0
    simp at h1
  · apply e.injective
    have h2 := he g (e.symm (0, Pi.single c 1))
    rw [map_smul, e.apply_symm_apply]
    rw [e.apply_symm_apply] at h2
    refine h2.trans ?_
    refine Prod.ext ?_ ?_
    · simp
    · funext a
      by_cases ha : a = c
      · subst ha
        simp [c, Algebra.smul_def]
      · simp [ha]

theorem isCrys_chiE_of_constituent (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (L' : FinExt (D.nd.l i)) (hL : (D.nbr i w hw).LL.1 ≤ L'.1)
    (hS : CrystallineSubrepresentation.SubCrys (Br.PD D.loc D.nbr i w hw) ↥L'.1) {n : ℕ}
    (χ : Formalism.MainNotions.N.GE D.nd →* (D.nd.O i)ˣ) (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin n) (Fin n) (D.nd.O i))
    (h : BlockCharactersCrystallineNonGaloisCusps.IsConstituent D i χ M)
    (hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locE D i w hw L' hL M))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (chiE D i w hw L' hL χ)) := by
  obtain ⟨v, hv, hg⟩ := h
  let f := (inc D i w hw L' hL).comp (Br.toLLK (D.nbr i w hw))
  let v' : Fin n → ↥L'.1 := fun a => f (v a)
  have hv' : v' ≠ 0 := by
    intro h0
    apply hv
    funext a
    exact f.injective ((congrFun h0 a).trans (map_zero _).symm)
  have hf : ∀ x, f (toK D.nd i x) = inc D i w hw L' hL ((D.nbr i w hw).toLL x) := fun x =>
    congrArg (inc D i w hw L' hL) (WordJumpsCompare.toLLK_toK _ _ _ _ _)
  have key : ∀ g : Br.G D.nbr i w hw, (locE D i w hw L' hL M g).mulVec v' =
      ((chiE D i w hw L' hL χ g : (↥L'.1)ˣ) : ↥L'.1) • v' := by
    intro g
    funext a
    have h1 := congrArg f (congrFun (hg (decS D.nd w (Br.iota D.nbr i w hw g))) a)
    have h2 : (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).mulVec v a =
        ∑ b, toK D.nd i (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b) * v b := rfl
    rw [h2, map_sum, Pi.smul_apply, smul_eq_mul, map_mul, hf] at h1
    simp only [map_mul, hf] at h1
    rw [Pi.smul_apply, smul_eq_mul]
    exact h1
  refine hS _ (matRep (locE D i w hw L' hL M)) _ _ (LinearMap.toSpanSingleton _ _ v') (fun g c => ?_)
    (LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton _ hv')) hc
  change (((chiE D i w hw L' hL χ g : (↥L'.1)ˣ) : ↥L'.1) • c) • v' =
    (locE D i w hw L' hL M g).mulVec (c • v')
  rw [Matrix.mulVec_smul, key, smul_smul, smul_eq_mul, mul_comm]

theorem chiOneE_of_isBlockSum (hF : GlobalTheory.Published.FontaineBcris) (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum D.nd i r ρ π)
    (hc : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r π)))) :
    ChiOneE D i := by
  intro w hw L' hL
  have hR := GlobalTheory.BlockCrys.subDualRules_of_fontaine hF (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩
  have hE : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locE D i w hw L' hL (rO D.nd i r π))) :=
    GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL L' hL _ _ (hc w hw)
  exact GlobalTheory.BlockCrys.isCrys_inv _ (hR.1 _ _) (hR.2 _ _) _
    (isCrys_chiE_of_constituent D i w hw L' hL (hR.1 _ _) _ _
      (isConstituent_of_isBlockSum D i r ρ π hs) hE)

end GlobalTheory.ChiOneEnl

end
