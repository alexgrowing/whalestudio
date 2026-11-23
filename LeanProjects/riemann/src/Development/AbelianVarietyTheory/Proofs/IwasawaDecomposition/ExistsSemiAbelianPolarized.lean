import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTrivialTorusAbelianLocus
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonvanishingOfInvertiblePushforward
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasisOnAny
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan.Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem isOpenImmersion_j_id (Y : Model Xo c (RingHom.id c.F)) : IsOpenImmersion Y.j := by
  unfold Model.j
  have : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
      infer_instance
    infer_instance
  have := Y.jQ_open
  infer_instance

theorem range_j_subset_abLocus {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨w, rfl⟩
  have h : Y.jQ w ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by rw [Y.ab_gen]; exact ⟨w, rfl⟩
  exact h

theorem exists_sab (Y : Model Xo c (RingHom.id c.F)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ Y.X) (_ : IsCN R) (hr : Set.range ξ ⊆ Set.range Y.j) :
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), PolAt t (jK R) ∧ ThetaNZ t.G t.PP.L ∧ ∀ x, x ∈ abLocus t.G := by
  have hj := isOpenImmersion_j_id Y
  have hab : Set.range ξ ⊆ abLocus Y.t.G := hr.trans (range_j_subset_abLocus Y)
  obtain ⟨ξ', hξ'⟩ : ∃ ξ' : Sp R ⟶ Xo.XF c, ξ' ≫ Y.j = ξ := ⟨IsOpenImmersion.lift Y.j ξ hr, IsOpenImmersion.lift_fac _ _ _⟩
  subst hξ'
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp R), Nonempty (SABMap t Y.t (ξ' ≫ Y.j)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (ξ' ≫ Y.j) Y.t
    exact ⟨_, ⟨m⟩⟩
  have m' : SABMap t Y.oF.t ξ' := (sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m m).choose
  have hPI : PushInvertible Y.oF.t.G Y.oF.t.PP.L :=
    PushInv.pushInvertible_any GlobalTheory.allSixLaws.2.1.secBaseChangeAny GlobalTheory.allSixLaws.1.globalSectionsRank _ (GlobalTheory.Obj.toPolAV Y.oF)
  refine ⟨t, m, GoodTrait.polAt_of_point Y m (jK R) (jK R ≫ ξ') (Category.assoc _ _ _),
    ThetaLocal.thetaNZ_of_pushInvertible E H _ Y.oF.t hPI R ξ' t m', fun x => ?_⟩
  exact (abLocus_pullback abLocusOne Y.t.semi m.cart.1 x).1 (hab ⟨x, rfl⟩)

end GlobalTheory.GenFan.Tri
