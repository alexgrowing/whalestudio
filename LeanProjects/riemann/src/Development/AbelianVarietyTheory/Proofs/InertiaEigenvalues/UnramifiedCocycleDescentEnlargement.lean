import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionFiniteExtensionQl
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc

theorem descUr_entry (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (a b : Fin k) :
    (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M)) g a b =
      IntermediateField.inclusion C.le ((Br.loc D.nbr i w hw M) g a b) := by
  simp only [mapM, locOC, Br.loc, Br.locM, MonoidHom.coe_comp, Function.comp_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

set_option maxHeartbeats 2000000 in

theorem descUr_mem : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (I : Subgroup (Br.G D.nbr i w hw))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ Z1urD (latC C (locOC C M)) I → z ∈ Z1urD (Br.locLat D.nbr i w hw M) I := by
  intro D i w hw C k M I z hz
  obtain ⟨r, hrl, hr1, hrO⟩ :=
    GlobalTheory.CoefRetraction.exists_integral_retraction (D.nd.l i) (D.nbr i w hw).LL C.LL C.le
  have hri : ∀ a, r (IntermediateField.inclusion C.le a) = a := fun a => by
    have := hrl a 1
    simpa [hr1] using this
  obtain ⟨x', hx'⟩ := hz
  obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ x'
  refine ⟨Submodule.Quotient.mk (fun j => r (v' j)), fun g hg => ?_⟩
  have h : liftQ C.le k (z g) = actD (latC C (locOC C M)) g (Submodule.Quotient.mk v') - Submodule.Quotient.mk v' := hx' g hg
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective (Br.locLat D.nbr i w hw M).T (z g)
  rw [← hu] at h ⊢
  have h1 : (Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) (incV C.le k u)) =
      Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) ((repV C (locOC C M)) g v') -
        Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) v' := h
  rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq] at h1
  show (Submodule.Quotient.mk (p := stdG ↥(OL (D.nbr i w hw).LL) ↥(D.nbr i w hw).LL.1 k) u) =
      Submodule.Quotient.mk (p := stdG ↥(OL (D.nbr i w hw).LL) ↥(D.nbr i w hw).LL.1 k) ((matRep (Br.loc D.nbr i w hw M)) g (fun j => r (v' j))) -
        Submodule.Quotient.mk (p := stdG ↥(OL (D.nbr i w hw).LL) ↥(D.nbr i w hw).LL.1 k) (fun j => r (v' j))
  rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]
  obtain ⟨t, ht⟩ := h1
  refine ⟨fun j => ⟨r (t j), hrO _ (t j).2⟩, ?_⟩
  funext j
  have hj := congrFun ht j
  have hrl' : ∀ a x, r (IntermediateField.inclusion C.le a * x) = a * r x := hrl
  have hj' : ((t j : ↥(OL C.LL)) : ↥C.LL.1) = IntermediateField.inclusion C.le (u j) -
      ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec v' j - v' j) := hj
  change r ((t j : ↥(OL C.LL)) : ↥C.LL.1) =
    u j - ((Br.loc D.nbr i w hw M g).mulVec (fun j => r (v' j)) j - r (v' j))
  rw [hj', map_sub, map_sub, hri]
  congr 2
  simp only [Matrix.mulVec, dotProduct, map_sum, descUr_entry, hrl']

end GlobalTheory.UseLoc
