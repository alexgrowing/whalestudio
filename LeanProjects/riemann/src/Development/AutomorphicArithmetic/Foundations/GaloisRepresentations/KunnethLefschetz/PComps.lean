import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.LCompIntPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

theorem comps_holds : Comps := by
  classical
  unfold Comps
  intro k _ _ d X p hp hX
  obtain ⟨hfin, hopen⟩ := comp_fin d p hp
  let m := Nat.card (_root_.ConnectedComponents X)
  let e : Fin m ≃ _root_.ConnectedComponents X := (Finite.equivFin _).symm
  let rep : Fin m → X := fun j => (ConnectedComponents.surjective_coe (e j)).choose
  have hrep : ∀ j, (rep j : _root_.ConnectedComponents X) = e j := fun j =>
    (ConnectedComponents.surjective_coe (e j)).choose_spec
  let U : Fin m → X.Opens := fun j => ⟨connectedComponent (rep j), hopen _⟩
  have hUc : ∀ j, IsClosed (U j : Set X) := fun j => isClosed_connectedComponent
  have hmem : ∀ j (x : X), x ∈ (U j : Set X) ↔ e j = (x : _root_.ConnectedComponents X) := by
    intro j x
    rw [← hrep]
    exact ⟨fun h => ConnectedComponents.coe_eq_coe.mpr (connectedComponent_eq h),
      fun h => by
        have := ConnectedComponents.coe_eq_coe.mp h
        show x ∈ connectedComponent (rep j)
        rw [this]; exact mem_connectedComponent⟩
  refine ⟨m, U, fun j => ?_, fun x => ?_, fun j j' hj => ?_⟩
  · have h2 := clopen_smoothProper_projective d p hp hX (U j) (hUc j)
    have hc : ConnectedSpace (U j) := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    exact ⟨h2.1, h2.2, LCompInt_of k d ((U j).ι ≫ p) h2.1 hc⟩
  · refine ⟨e.symm (x : _root_.ConnectedComponents X), ?_⟩
    show x ∈ (U _ : Set X)
    rw [hmem]
    exact e.apply_symm_apply _
  · rw [disjoint_iff_inf_le]
    intro x hx
    exact (hj (e.injective (((hmem j x).mp hx.1).trans ((hmem j' x).mp hx.2).symm))).elim

end UpperTheory.Gal.KunnethLefschetz
