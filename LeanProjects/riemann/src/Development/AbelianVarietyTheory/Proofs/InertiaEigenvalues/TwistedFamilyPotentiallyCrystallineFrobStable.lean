import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobStableInertiaThrough
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapTensorOneCommDiagonalAction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRTwO

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

noncomputable section

namespace GlobalTheory.PotTwist

theorem frob : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c'),
    finrank ℚ_[l] ↥K.1 = 1 → ∃ F : ↥(GK K), (pc P h hN hF hS).IsFrob F := by
  intro l _ P K K' h hN hF hS hK
  have hbot : K.1 = ⊥ := IntermediateField.finrank_eq_one_iff.1 hK
  obtain ⟨g, hg⟩ : ∃ g : GQ l, ∀ x : ↥(Loc.K0 K'), g x = (((P.PD K').σ x : ↥(Loc.K0 K')) : Om l) := by
    let τ : ↥(Loc.K0 K') →ₐ[ℚ_[l]] Om l := (Loc.K0 K').val.comp (P.PD K').σ
    exact ⟨AlgEquiv.ofBijective (τ.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _),
      fun x => τ.liftNormal_commutes (Om l) x⟩
  have hmem : g ∈ GK K := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hbot] at hx
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact g.commutes a
  refine ⟨⟨g, hmem⟩, fun c => ?_⟩
  change (P.PD K).actB _ _ = algebraMap _ _ ((P.PD K').σ c)
  rw [P.PD_actB]
  exact P.actQ_Kur g (IntermediateField.inclusion (inf_le_right : Loc.K0 K' ≤ MaximalUnramifiedExtension l) c)
    (IntermediateField.inclusion (inf_le_right : Loc.K0 K' ≤ MaximalUnramifiedExtension l) ((P.PD K').σ c)) (hg c)

theorem main : ∀ (D : D7), PcrisTensorL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (Sig0 : Finset ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ)) (c : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ) (n : ℕ),
  c ∈ Sig0 → Sig0.card ≤ n →
  (∀ x ∈ Xs, Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))) →
  (∀ x ∈ Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) ∧
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) Sig0) →
  (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w))) →
  (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w))) {c} →
  PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n := by
  intro D hT i w hw hdeg r Xs K' h hN hF hS Sig0 c n hc hcard hcont hx hχ1 hχ2

  have hequiv : ∀ (g : Br.G D.nbr i w hw) (v : Br.LL D.nbr i w hw),
      (LinearEquiv.funUnique (Fin 1) (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)).symm
        (WeaklyAdmissibleFiltrations.charRep (Br.locChi D.nbr i w hw (D.nd.chi i 1)) g v) =
      (D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w)) g
        ((LinearEquiv.funUnique (Fin 1) (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)).symm v) := by
    intro g v
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [WeaklyAdmissibleFiltrations.charRep, LocBridge.rep, Br.locChi, Br.chiG, chiGL, Br.ι, Matrix.mulVec, dotProduct, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply, mul_comm]
  obtain ⟨tr1, tr2⟩ := GlobalTheory.HTW.Rec.potCrysData_transport (pc (D.loc (D.nd.l i)) h hN hF hS) _ _ _ hequiv
  have htw : ∀ x : ↥Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) ∧
      (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
        (Sig0.image (fun a => a * c⁻¹)) := fun x =>
    GlobalTheory.TwistPotCrys.twist_potCrys D hT i w hw r x K' h hN hF hS Sig0 c (hcont x x.2) (hx x x.2).1 (hx x x.2).2 (tr1 hχ1) (tr2 _ hχ2)
  obtain ⟨Fr, hFr⟩ := frob (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' h hN hF hS hdeg
  have h1 : (1 : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ) ∈ Sig0.image (fun a => a * c⁻¹) :=
    Finset.mem_image.2 ⟨c, hc, mul_inv_cancel c⟩
  obtain ⟨Sig, hsub, h1', hst, hit⟩ := GlobalTheory.frobStable_inertial_subset (pc (D.loc (D.nd.l i)) h hN hF hS)
    (fun x : ↥Xs => matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) (Fr : Br.G D.nbr i w hw) _ h1 (fun x => (htw x).2)
  exact ⟨K', h, hN, hF, hS, Sig, Fr, hFr, hst, h1',
    le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le hcard), fun x => ⟨(htw x).1, hit x⟩⟩

end GlobalTheory.PotTwist

end
