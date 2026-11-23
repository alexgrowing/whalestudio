import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryEqReflOfCongrModGeThree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseMatchingMonomialsRatioUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialsDifferByUnitsPositiveBoundaryCombinatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeSumGeneratorsEqOfCommonInteriorPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lattice_iso_eq_of_tautPts : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (ψ : InvFun ℤ) (m N n : ℕ) (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), 3 ≤ n → IsCone id ψ (fun k => ε (.inl k)) → (∀ x, x ≠ 0 → ∃ k, 0 < ε (.inl k) x x) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : (Fin m ⊕ Fin N) → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : (Fin m ⊕ Fin N) → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → Match D₁ D₂ b φ F → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → ∀ y, e₂ (φ y) = e₁ y := by
  intro o W _ _ _ T ψ m N n ε hn hcone hdef V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hτ₁ hτ₂ hF₁ hF₂
    hs₁ hu₁ hs₂ hu₂ hM hpts
  let ga : (Fin T.r → ℤ) ≃ₗ[ℤ] (Fin T.r → ℤ) := ((e₁.symm.trans φ).trans e₂).toIntLinearEquiv
  have hga : ∀ a, ga a = e₂ (φ (e₁.symm a)) := fun _ => rfl

  have hcong : ∀ a, GlobalTheory.Poinc.CongMod n (ga a) a := by
    intro a
    obtain ⟨p₁, p₂, hy₁, -, hy₂, -, p', hp', -, z, hz, -⟩ := hpts a
    have h : e₂ p₂.y = e₂ (φ p₁.y) + n • e₂ z := by rw [hz, map_add, hp', map_nsmul]
    rw [hy₂, hy₁, AddEquiv.apply_symm_apply] at h
    refine ⟨-(e₂ z), ?_⟩
    rw [smul_neg, eq_add_neg_iff_add_eq, hga]
    exact h.symm

  have hpu := GlobalTheory.T.tautologicalBase_matching_monomials_ratio_unit T ε n V D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F hτ₁ hτ₂ hF₁ hF₂ hM
  have hab : ∀ a b, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (ga a) (ga b)) =
      algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i a b) := by
    intro a b
    obtain ⟨u, hu⟩ := hpu (e₁.symm a) (e₁.symm b)
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at hu
    exact ⟨u, hu⟩
  obtain ⟨c₁, c₂, hc₁, hc₂, hsum⟩ := GlobalTheory.T.monomials_differ_by_units_positive_boundaryCombination V T.r m N n (by omega) ε s₁ s₂ ga hs₁ hu₁ hs₂ hu₂ hab
  have hS := GlobalTheory.T.smoothCone_sum_generators_eq_of_common_interiorPoint ψ (Fin T.r → ℤ) m m (fun k => ε (.inl k)) (fun k => pull ga.toLinearMap (ε (.inl k))) hcone
    (hcone.pull_equiv ga) c₁ c₂ hc₁ hc₂ hsum

  have he : ∀ x y, (∑ k, ε (.inl k)) (ga x) (ga y) = (∑ k, ε (.inl k)) x y := by
    intro x y
    have h := LinearMap.congr_fun₂ hS x y
    simp only [LinearMap.sum_apply, pull_apply, LinearEquiv.coe_coe] at h ⊢
    exact h.symm
  have hpos : ∀ x, x ≠ 0 → 0 < (∑ k, ε (.inl k)) x x := by
    intro x hx
    obtain ⟨k, hk⟩ := hdef x hx
    simp only [LinearMap.sum_apply]
    exact Finset.sum_pos' (fun i _ => hcone.nonneg i x) ⟨k, Finset.mem_univ _, hk⟩
  have hrefl := GlobalTheory.Poinc.eq_refl_of_isometry_congMod (Fin T.r → ℤ) (∑ k, ε (.inl k)) hpos ga he n hn hcong
  intro y
  have h := DFunLike.congr_fun hrefl (e₁ y)
  rw [hga, AddEquiv.symm_apply_apply, LinearEquiv.refl_apply] at h
  exact h

end GlobalTheory.TInj
