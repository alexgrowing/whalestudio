import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor CategoryTheory.MonObj

namespace GlobalTheory.AbelianLetters

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory NumberField in
open CategoryTheory.MonObj in

theorem _root_.GlobalTheory.AbelianLetters.mul_comp_of_isGrpPullback_id {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] (f : G' ⟶ G)
    (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (𝟙 S) f.left) {T : Over S} (x y : T ⟶ G') : (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  let e : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have key := h.2 T x y (e ≫ x ≫ f) (e ≫ y ≫ f) (by simp [e]) (by simp [e])
  rw [← MonObj.comp_mul] at key
  ext1
  simpa [e] using key.symm

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory NumberField in
open CategoryTheory.MonObj in

theorem _root_.GlobalTheory.AbelianLetters.exists_linear_lift_of_isGrpPullback :
    ∀ (P P' : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) (φ : P'.A.left ⟶ P.A.left), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback P'.A P.A (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (RingHom.id ℂ)) φ →
    ∀ (u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif P'.A P'.L P'.g) (g : ℕ) (T : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) (i : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ T.left), i ≫ T.hom = 𝟙 _ →
    ∀ G : (Fin g → ℂ) → (T ⟶ P.A), (∀ z z', G (z + z') = G z * G z') →
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ (fun z => i ≫ (G z).left) →
    ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ), (∀ z, (u.ex (F z)).left ≫ φ = i ≫ (G z).left) ∧
      (∀ z, G z = 1 → F z ∈ u.Λ) ∧ ∀ (z : Fin g → ℂ) (z' : Fin P'.g → ℂ) (η' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR ℂ ⟶ P'.A),
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => i ≫ (G z).left) z (η'.left ≫ φ) → u.IsDiff z' η' → z' = F z := by
  intro P P' φ hφ u g T i hi G hG hhol
  obtain ⟨h1, h2, -⟩ :=
    _root_.GlobalTheory.AnyUnif.tangent_and_unimodular _root_.GlobalTheory.thetaUnifAV_all P' u
  have hlift := _root_.GlobalTheory.existsUnique_linear_lift_of_isHolTo P'.A P'.isAb P'.L P'.g g u h1 h2
  have hpb : IsPullback φ P'.A.hom P.A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (RingHom.id ℂ)) := hφ.1
  rw [_root_.GlobalTheory.Cris.spMap_id] at hpb
  haveI : IsIso φ := hpb.isIso_fst_of_isIso
  obtain ⟨e, he⟩ := _root_.GlobalTheory.LiePull.exists_pushEquiv hφ (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ))) _ rfl
  let j : Over.mk ((𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ))).hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (RingHom.id ℂ)) ⟶ T :=
    Over.homMk i (by simp [hi, _root_.GlobalTheory.Cris.spMap_id, Over.tensorUnit_hom])
  let G' : (Fin g → ℂ) → (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) ⟶ P'.A) := fun z => e.symm (j ≫ G z)
  have hG'φ : ∀ z, (G' z).left ≫ φ = i ≫ (G z).left := by
    intro z
    rw [← he]
    simp [G', j]
  have hG'add : ∀ z w, G' (z + w) = G' z * G' w := by
    intro z w
    simp only [G', hG, MonObj.comp_mul, map_mul]
  have hG'fun : (fun z => (G' z).left) = fun z => (i ≫ (G z).left) ≫ inv φ := by
    funext z
    rw [← hG'φ z, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hG'hol : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ fun z => (G' z).left := by
    rw [hG'fun]
    exact _root_.GlobalTheory.HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
      (_root_.GlobalTheory.HolHom.holAt_of_isHolTo hhol (Set.mem_univ z)).comp (inv φ)
  obtain ⟨F, hF, -⟩ := hlift G' hG'add hG'hol
  refine ⟨F, ?_, ?_, ?_⟩
  · intro z
    rw [hF]
    exact hG'φ z
  · intro z hz
    rw [← u.ker, hF]
    simp [G', hz, MonObj.comp_one]
  · intro z z' η' hder hdiff
    have hfam : (fun w => (u.ex (F w)).left) = fun w => (i ≫ (G w).left) ≫ inv φ := by
      funext w
      rw [hF, ← hG'φ w, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have h3 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun w => (u.ex (F w)).left) z η'.left := by
      have hd := (_root_.GlobalTheory.HolHom.isDerivAt0_iff _ _ _).1 hder
      have hd' := hd.comp (inv φ)
      have hη : (η'.left ≫ φ) ≫ inv φ = η'.left := by simp
      rw [hη] at hd'
      rw [hfam, _root_.GlobalTheory.HolHom.isDerivAt0_iff]
      exact hd'
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 at h3
    obtain ⟨hbase, hdF⟩ := h3
    have hF0 : F 0 = 0 := map_zero F
    have htan : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent η' := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent
      rw [hbase]
      simp only [hF0]
      exact _root_.GlobalTheory.TangentOrigin.ex_zero_left u
    have hdiffF : u.IsDiff (F z) η' := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif.IsDiff
      intro U hU f
      rw [hdF U hU f]
      have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := _root_.GlobalTheory.HomLinear.top_le_ex_zero u htan U hU
      have hd : DifferentiableAt ℂ (fun w => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex w).left U f)
          (LinearMap.toContinuousLinearMap F 0) := by
        rw [map_zero]
        exact _root_.GlobalTheory.TangentOrigin.differentiableAt_val u h0 f
      have hc := hd.hasFDerivAt.comp (0 : Fin g → ℂ)
        (LinearMap.toContinuousLinearMap F).hasFDerivAt
      rw [map_zero] at hc
      have hfun : ((fun w => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex w).left U f) ∘ LinearMap.toContinuousLinearMap F) =
          fun w => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex (F w)).left U f := rfl
      rw [hfun] at hc
      rw [hc.fderiv]
      rfl
    obtain ⟨w, -, huniq⟩ := h1 η' htan
    exact (huniq z' hdiff).trans (huniq (F z) hdiffF).symm

end GlobalTheory.AbelianLetters
