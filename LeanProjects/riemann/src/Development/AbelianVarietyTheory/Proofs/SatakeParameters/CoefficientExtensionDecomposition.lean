import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsConstituentOfIsBlockSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShift
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.CrysFromGTwo

theorem matRep_twistM {K Γ : Type} [Field K] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) K)
    (χ : Γ →* Kˣ) (g : Γ) (v : Fin k → K) :
    matRep (twistM M χ) g v = ((χ g : Kˣ) : K) • matRep M g v := by
  change (((χ g : Kˣ) : K) • M g).mulVec v = ((χ g : Kˣ) : K) • (M g).mulVec v
  exact Matrix.smul_mulVec _ _ _

theorem crys_loc (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (hG : SumRepresentations.At.G2 D.nd D.naut i r) (h0 : D.nd.l i ≠ D.host.g 0)
    (h1 : D.nd.l i ≠ D.host.g 1) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x))) := by
  have hc := ((hG w hw).1 h0 h1 x).1
  exact ((D.loc_tie i w hw).2.1 D.R.nV (r x) (hr x).1).1.mp hc

theorem crys_coef (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i) (h : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := by
  have := D.nd.lPrime i
  exact GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL C.LL C.le _ _ h

theorem crys_chi (hF : GlobalTheory.Published.FontaineBcris) (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r π))))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) := by
  have hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum D.nd i r ρ π := by
    obtain ⟨e, he⟩ := hD
    exact ⟨e, fun g u => he g u⟩
  exact GlobalTheory.ChiOneEnl.chiOneE_of_isBlockSum hF D i r ρ π hs hc w hw C.LL C.le

theorem twist_mat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K LL : FinExt l)
    {k : ℕ} (M M' : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (χ : ↥(GK K) →* (↥LL.1)ˣ)
    (ht : IsTwistRep χ (matRep M) (matRep M')) (hχ : IsCrys (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ))
    (h : IsCrys (P.PD K) (matRep M)) : IsCrys (P.PD K) (matRep M') :=
  (GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l P AI T K LL _ _ _ _ χ ht hχ h).1

theorem crys_tw (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i) (hχ : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹))
    (h : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  have := D.nd.lPrime i
  have ht : IsTwistRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))
      (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
    refine ⟨LinearEquiv.refl _ _, fun g v => ?_⟩
    rw [locC_rTwO]
    exact matRep_twistM _ _ g v
  exact twist_mat (D.nd.l i) (D.loc _) (D.locA _) (D.locT _) (D.nbr i w hw).Kw C.LL _ _ _ ht hχ h

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → SumRepresentations.At.G2 D.nd D.naut i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) ∧ ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  intro hF D i r ρ π hr hG h0 h1 hD w hw C
  have hχ := crys_chi hF D i r ρ π hD (fun w' hw' => crys_loc D i r hr hG h0 h1 w' hw' π) w hw C
  have hx : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := fun x =>
    crys_coef D i r w hw C x (crys_loc D i r hr hG h0 h1 w hw x)
  exact ⟨hχ, fun x => ⟨hx x, crys_tw D i r w hw C x hχ (hx x)⟩⟩

end GlobalTheory.CrysFromGTwo
