import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryExtensionIndependentOfModel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSectionAndDegree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits

set_option autoImplicit false

noncomputable section

open MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntEigTransport

theorem isTan_iff_isTangent' {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] (w : epsR V ⟶ G) :
    IsTan (V := V) (R := V) (G := G) w ↔ IsTangent w := by
  have : (1 : ptOver V V ⟶ G).left = η[G].left := by
    show spMap (algebraMap V V) ≫ _ = _
    rw [show spMap (algebraMap V V) = 𝟙 _ from Spec.map_id _]
    exact Category.id_comp _
  unfold IsTan IsTangent
  rw [this]

theorem transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (G : SAB H (Sp T.V)) (S : Scheme.{0}) (t : SAB H S) (x : Sp T.V ⟶ S) (n : SABMap G t x) (τ : E →+* ℂ) (k : ℕ) (ub : Fin k → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i, IsEigV c io G τ (ub i)) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin k → T.V, IsComb ub a w) → ∃ v : Fin k → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt x ⟶ t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis t.act x (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (v i).left = (ub i).left ≫ n.φ := by
  intro E _ _ _ H l c T io φ hio G S t x n τ k ub htan heig hbas
  have hz : ∀ (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c τ a) → z = φ (embK c τ a) := by
    intro a z hz
    apply IsFractionRing.injective T.V T.Fr
    rw [hz, ← hio]; rfl
  have hE : ∀ w : epsR T.V ⟶ G.G, IsEigV c io G τ w ↔
      ∀ a, (w ≫ G.act.act a).left = spMap (epsScaleR (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ a)) ≫ w.left := by
    intro w
    constructor
    · intro h a
      exact h a (φ (embK c τ a)) (by rw [← hio]; rfl)
    · intro h a z hz'
      rw [hz a z hz']
      exact h a
  have hC : ∀ (a : Fin k → T.V) (w : epsR T.V ⟶ G.G), IsComb ub a w ↔ IsLieComb a ub w := fun a w => Iff.rfl
  have hv : GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsEigBasis G.act (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) ub := by
    refine ⟨fun i => ⟨(isTan_iff_isTangent' _).1 (htan i), (hE _).1 (heig i)⟩, fun w hw => ?_⟩
    exact (existsUnique_congr fun a => hC a w).1 (hbas w ((isTan_iff_isTangent' _).2 hw.1) ((hE w).2 hw.2))
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.FlatRow.exists_eigenBasis n hv
  exact ⟨u, hu, fun i => (hu' i).symm⟩

end GlobalTheory.IntEigTransport
