import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc
theorem twistM_repV_cont : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ), (Continuous fun g => M g) → Continuous (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1)) → ∀ x, Continuous fun g => repV C (twistM (locOC C M) θ) g x := by
  intro D i w hw C k M θ hM hθ x
  have hinc : Continuous fun y : ↥(OL (D.nbr i w hw).LL) => ((incO C.le y : ↥(OL C.LL)) : ↥C.LL.1) := by
    have e : (fun y : ↥(OL (D.nbr i w hw).LL) => ((incO C.le y : ↥(OL C.LL)) : ↥C.LL.1)) =
        fun y => IntermediateField.inclusion C.le y.1 := rfl
    rw [e]
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hmat : Continuous fun g => mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g := by
    refine continuous_matrix fun a b => ?_
    have h1 : Continuous fun g : Br.G D.nbr i w hw =>
        M ((decS D.nd w) ((Br.ι (D.nbr i w hw)) g)) a b :=
      (hM.matrix_elem a b).comp (continuous_subtype_val.comp (Br.ι_cont (D.nbr i w hw)))
    have h2 := hinc.comp ((D.nbr i w hw).eO_cont.comp h1)
    have e : (fun g => mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g a b) =
        fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1) *
          ((incO C.le ((D.nbr i w hw).eO (M ((decS D.nd w) ((Br.ι (D.nbr i w hw)) g)) a b)) : ↥(OL C.LL)) : ↥C.LL.1) := by
      funext g
      simp [mapM, twistM, locOC, Br.locO, tableLineDegreeTwo.charL, Matrix.smul_apply]
    rw [e]
    exact hθ.mul h2
  have e2 : (fun g => repV C (twistM (locOC C M) θ) g x) =
      fun g => (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g).mulVec x := by
    funext g
    rfl
  rw [e2]
  exact hmat.matrix_mulVec continuous_const
end GlobalTheory.UseLoc
