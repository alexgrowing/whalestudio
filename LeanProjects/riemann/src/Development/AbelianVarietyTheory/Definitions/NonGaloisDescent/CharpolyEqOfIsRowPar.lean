import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyResidueFieldUnitBallEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemisimplificationMatrixRepSameCharpoly

noncomputable section

namespace GlobalTheory.EigTie

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.Triple (IsParam IsResidual FbAt)
open GlobalTheory.HeightCounting (RowSide PlSide IotaOk setTy factRes)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)

variable {D : D7}

theorem mem_plB (Pl : PlSide D) (w : D.what₂.places.Pl) (z : Zbar (D.what₂.places.resChar w)) :
    Pl.ι w (z : Qbar (D.what₂.places.resChar w)) ∈ Pl.plB w := by
  rw [Pl.plB_eq, RingEquiv.symm_apply_apply]
  exact z.2

def plRed (Pl : PlSide D) (w : D.what₂.places.Pl) : Zbar (D.what₂.places.resChar w) →+* FbAt D w :=
  ((Pl.plκ w).toRingHom.comp (IsLocalRing.residue (Pl.plB w))).comp
    (((Pl.ι w).toRingHom.comp (Zbar (D.what₂.places.resChar w)).subtype).codRestrict (Pl.plB w) (mem_plB Pl w))

theorem plRed_eq (Pl : PlSide D) (w : D.what₂.places.Pl) (z : Zbar (D.what₂.places.resChar w)) :
    plRed Pl w z = Formalism.L2.NT.redThrough (Pl.plB w) (Pl.plκ w) (Pl.ι w z) := by
  rw [Formalism.L2.NT.redThrough, dif_pos (mem_plB Pl w z)]
  rfl

theorem teichAt_of_iotaOk {Pl : PlSide D} (h : IotaOk D Pl) (w : D.what₂.places.Pl) : TeichAt (Pl.ι w) w (plRed Pl w) :=
  fun k _ v x _ z hz => by rw [plRed_eq, hz, RingEquiv.apply_symm_apply, h]

theorem resTied_of_plSide {Rw : RowSide D} {Pl : PlSide D} (h : IotaOk D Pl)
    (hr : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ σ π r, D.nd.goodRow σ → OnW D σ → IsRowPar Rw σ π →
      IsGaloisRepOf D π _ (Pl.ι w) r → IsSSRep (D.ntypes.rbar σ w) ∧ ∀ g, ∃ p : (Zbar (D.what₂.places.resChar w))[X],
        p.map (Zbar (D.what₂.places.resChar w)).subtype = ((r g : GL (Fin D.R.r) (Qbar (D.what₂.places.resChar w))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.what₂.places.resChar w))).charpoly ∧
        p.map (plRed Pl w) =
          ((D.ntypes.rbar σ w g : GL (Fin D.R.r) (FbAt D w)) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w)).charpoly) :
    ResTied D Rw := by
  intro w hw l _ e
  subst e
  exact ⟨Pl.ι w, plRed Pl w, Pl.ι_w w, teichAt_of_iotaOk h w, fun σ π r h1 h2 h3 h4 =>
    ⟨(hr w hw σ π r h1 h2 h3 h4).1, (hr w hw σ π r h1 h2 h3 h4).2, teichAt_of_iotaOk h w⟩⟩

def HasIntForm {Γ : Type} [Group Γ] {l n : ℕ} [Fact l.Prime] (r : Γ →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ A : GL (Fin n) (Qbar l), ∀ g p q, ‖((A⁻¹ * r g * A : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) p q‖ ≤ 1

end GlobalTheory.EigTie

end
