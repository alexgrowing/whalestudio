import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousLoc
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Classical

noncomputable section

namespace GlobalTheory.TwistPotCrys

section

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem loc_rTwO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    Br.loc D.nbr i w hw (rTwO D.nd i r x) =
      twistM (Br.loc D.nbr i w hw (rO D.nd i r x)) (Br.locChi D.nbr i w hw (D.nd.chi i 1))⁻¹ := by
  refine MonoidHom.ext fun g => Matrix.ext fun a b => ?_
  show (D.nbr i w hw).toLL ((((chiU D.nd i 1)⁻¹ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) *
      rO D.nd i r x (decS D.nd w (Br.iota D.nbr i w hw g)) a b) = _
  rw [map_mul]
  rfl

theorem matRep_loc_rO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    matRep (Br.loc D.nbr i w hw (rO D.nd i r x)) = (D.nbr i w hw).rep ((r x).comp (decS D.nd w)) := rfl

theorem isTwistRep_loc (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    IsTwistRep (Br.locChi D.nbr i w hw (D.nd.chi i 1))⁻¹ (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) := by
  refine ⟨LinearEquiv.refl _ _, fun g v => ?_⟩
  rw [loc_rTwO]
  change ((((Br.locChi D.nbr i w hw (D.nd.chi i 1))⁻¹ g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) •
      Br.loc D.nbr i w hw (rO D.nd i r x) g).mulVec v = _
  exact Matrix.smul_mulVec _ _ _

theorem continuous_rTwO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i)
    (hc : Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))) :
    Continuous fun g => rTwO D.nd i r x g := by
  have h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) :=
    (D.nd.chi_cont i 1).comp continuous_inv
  refine (h1.smul hc).congr fun g => ?_
  simp [rTwO, twistM, rO]

end

set_option maxHeartbeats 1600000 in

theorem twist_potCrys : ∀ (D : D7), PcrisTensorL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (K' : FinExt (D.nd.l i))
    (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (Sig0 : Finset ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ))
    (c : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ),
    Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) Sig0 →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (WeaklyAdmissibleFiltrations.charRep (Br.locChi D.nbr i w hw (D.nd.chi i 1))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough (WeaklyAdmissibleFiltrations.charRep (Br.locChi D.nbr i w hw (D.nd.chi i 1))) {c} →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) ∧
      (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
        (Sig0.image (fun a => a * c⁻¹)) := by
  intro D hT i w hw r x K' h hN hF hS Sig0 c hcont hpot hit hχpot hχit
  have hcO : Continuous fun g => rO D.nd i r x g := hcont
  have hcT := continuous_rTwO D i r x hcont
  rw [← matRep_loc_rO] at hpot hit
  exact (hT (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS
      (GlobalTheory.PotDual.bundle _ _ (Br.loc D.nbr i w hw (rO D.nd i r x)) (GlobalTheory.PotDual.continuous_loc D i w hw _ hcO))
      (GlobalTheory.PotDual.bundle _ _ (Br.loc D.nbr i w hw (rTwO D.nd i r x)) (GlobalTheory.PotDual.continuous_loc D i w hw _ hcT))
      Sig0 (Sig0.image (fun a => a * c⁻¹)) hpot hit).1 _ c (isTwistRep_loc D i w hw r x) hχpot hχit
      (fun b => by
        rw [Finset.mem_image]
        exact ⟨fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩, fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩⟩)

end GlobalTheory.TwistPotCrys

end
