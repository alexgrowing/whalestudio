import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory

theorem FlagBundle.bears_self : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y : Var F) (Eb : Fr (ratOf X) m 0) (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Reps Eb S φ f → ∀ (K : Type) [Field K] (w : Sp K ⟶ Y.X), ∃ A ∈ Eb.S ((w ≫ f) (IsLocalRing.closedPoint K)), ∃ h : Mat m K, Par 0 ⊤ h ∧ Bears S φ A h w := by
  intro F _ ι _ m X Y Eb S φ f hR K _ w
  obtain ⟨A, hA⟩ := Eb.nonempty ((w ≫ f) (IsLocalRing.closedPoint K))
  obtain ⟨A', hA'⟩ := S.nonempty (w (IsLocalRing.closedPoint K))
  have hA₁ : A ∈ Eb.S (f (w (IsLocalRing.closedPoint K))) := (Scheme.Hom.comp_apply w f (IsLocalRing.closedPoint K)) ▸ hA
  have hN := hR.2.1 _ A' hA' A hA₁
  have hh : Par 0 ⊤ ((A' * (A.map φ)⁻¹).map ((ratOf Y).val w)) := by
    have hz := RatModel.range_eq_singleton (M := ratOf Y) w (IsLocalRing.closedPoint K)
    exact hN.map_of ((ratOf Y).val w) (RatModel.valHom (M := ratOf Y) w _ hz)
      (fun x => (RatModel.valHom_apply (M := ratOf Y) w _ hz x).symm)
  refine ⟨A, hA, _, hh, A', hA', ?_⟩
  rw [Mat.mul_inv hh.det_ne]
  exact Par.one
end GlobalTheory
