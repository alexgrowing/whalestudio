import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfPullbackInjectiveDomains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataRescaleCoboundary
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TInj

theorem from_rescale_pull : ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (n : ℕ) (D₀ : DegPre W), D₀.PsiEven → D₀.TauBimult → (∀ y, PsiUnitOn D₀ y Set.univ) → ∀ (ib : D₀.X ≃+ (Fin T.r → ℤ)) (β : D₀.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ T.B T.M.L).pull ββ)), From T (RingHom.id W) (fun _ : Empty => (1 : W)) (fun _ => 0) n D₀ ib β ββ w → ∀ (V : Type) [CommRing V] [IsDomain V] (iw : W →+* V), Function.Injective iw → ∀ (Q : DegPre V) (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw D₀ (rescale Q g)) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (e : Q.X ≃+ (Fin T.r → ℤ)), (∀ y : Q.X, e y = ib (hD.xe y)) → (∀ a a' : Q.X, (((g (a + a'))⁻¹ * g a * g a' : (FractionRing V)ˣ) : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e a'))) → ∃ (β' : Q.P.A.left ⟶ T.B.left) (ββ' : (G2 Q.P.A).left ⟶ (G2 T.B).left) (w' : LB.Iso (abelian₂ Q.P.A Q.P.L) ((abelian₂ T.B T.M.L).pull ββ')), From T iw s ε n Q e β' ββ' w' := by
  intro o W _ _ _ _ T n D₀ hev hbi hun ib β ββ w hF V _ _ iw hiw Q g hD I _ s ε e he hg
  have hin : ∀ χ, D₀.PsiIn χ ⊤ := fun χ j U hU hle h => by
    obtain ⟨r, -, hr⟩ := hun χ j U hU (Set.subset_univ _) hle h
    exact ⟨r, by rw [Ideal.map_top]; trivial, hr⟩
  let D₁ : DegData W ⊤ :=
    { toPre := D₀
      psi_even := hev
      tau_bimult := hbi
      psi_pos := fun χ _ => hin χ
      psi_tendsto := fun m => by
        rw [Ideal.top_pow]
        exact Set.finite_empty.subset fun χ hχ => hχ (hin χ) }
  obtain ⟨ββ', w', pb, sq, gen, hc, hτ⟩ :=
    from_pull T (fun _ : Empty => 0) n W V ⊤ D₁ (RingHom.id W) (fun _ => 1) ib β ββ w iw (rescale Q g) hD hiw hF
  rw [RingHom.comp_id] at pb hc hτ
  refine ⟨_, ββ', w', pb, sq, gen, fun a => ?_, fun a b => ?_⟩
  · rw [he a]; exact hc a
  · obtain ⟨k, hk, hv⟩ := hτ a b
    have hk1 : k = 1 := Units.ext (by rw [hk]; simp)
    refine ⟨_, hg a b, fun z J J' hJ hJ' => ?_⟩
    have H := hv z J J' hJ hJ'
    have E := rescale_tau_val Q g a b hJ'
    have H' := E.symm.trans H
    rw [hk1] at H'
    rw [he a, he b]
    have aux : ∀ {G : Type} [CommGroup G] (x y u t p : G), x * y⁻¹ * u⁻¹ * t = 1 * p → t = x⁻¹ * y * u * p := by
      intro G _ x y u t p h
      rw [_root_.one_mul] at h
      rw [← h, ← _root_.mul_assoc]
      have h1 : x⁻¹ * y * u * (x * y⁻¹ * u⁻¹) = (x⁻¹ * x) * (y * y⁻¹) * (u * u⁻¹) := by ac_rfl
      rw [h1]
      simp
    simp only [unitOn, map_mul, map_inv, map_one] at H' ⊢
    exact aux _ _ _ _ _ H'

end GlobalTheory.TInj
