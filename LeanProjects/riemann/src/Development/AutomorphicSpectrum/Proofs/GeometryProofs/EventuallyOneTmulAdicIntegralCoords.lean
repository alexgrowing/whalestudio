import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOfSmoothStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

def lieModelOfEquiv {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {F F' : Type} [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R F']
    (M : LieModel G x F) (e : F' ≃ₗ[R] F) : LieModel G x F' where
  pt v := M.pt (e v)
  tan v := M.tan _
  inj := M.inj.comp e.injective
  onto v hv := by
    obtain ⟨w, h⟩ := M.onto v hv
    exact ⟨e.symm w, by simpa using h⟩
  add v w := by rw [map_add, M.add]
  smul c v := by rw [map_smul, M.smul]

theorem exists_bdryChart_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (y : Sp ℂ ⟶ Xo.X) (n a : ℕ), a ≤ n → y ≫ Xo.s = spMap σ →
    ∃ C : BdryChart Xo σ n a, ∀ z, C.pt z ≫ C.k = y := by
  intro E _ _ _ H D l Xo σ y n a ha hy
  obtain ⟨t, ⟨m⟩⟩ := exists_sab y Xo.univ.t
  obtain ⟨i, -⟩ := ObjMaps.exists_sab_id t
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t.G.hom (eSec t.G (default : PrimeSpectrum ℂ))
  obtain ⟨F, _, _, ⟨M⟩⟩ := lieModel_exists _ t.G ℂ (𝟙 _)
  obtain ⟨b⟩ := GlobalTheory.T.lie_model_free_of_smooth _ t.G g hg ℂ (𝟙 _) F M
  refine ⟨{ a_le := ha, R := ℂ, t := t, g := g, dim := hg, M := lieModelOfEquiv M b.equivFun.symm,
            ψ := fun _ => RingHom.id ℂ, hol := ⟨Metric.isOpen_ball, fun r => differentiableOn_const _⟩,
            V := Sp ℂ, j := 𝟙 _, j_open := inferInstance, k := y, tV := t, m₁ := i, m₂ := m,
            pt := fun _ => 𝟙 _, pt_eq := fun z _ => ⟨by simp [spMap], by simpa using hy⟩ }, fun z => Category.id_comp _⟩

end GlobalTheory.CompanionTheory.Ar.Flat
