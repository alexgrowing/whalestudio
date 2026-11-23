import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateEqUnitMulTauCoordinate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.TauCoordQuot

open GlobalTheory.PsiTauCoordRel GlobalTheory.PeriodBalance

theorem gm_psi {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
    (ξ : Spec (CommRingCat.of (FractionRing R))) (χ : D.X) (j : PUnit → D.P.L.ι)
    (hj : IsIntChart D (D.c χ) (j PUnit.unit)) (x : (FractionRing R)ˣ) (hx : IsPsiCoord D χ x) :
    ∃ u : Rˣ, gm (𝟙 _) ξ (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j) =
      Units.map (kst ξ).toMonoidHom (Units.map (algebraMap R (FractionRing R)).toMonoidHom u * x) := by
  have h : ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j :=
    fun y _ => Set.mem_iInter.2 fun _ => hj (Set.mem_univ (jK R y))
  obtain ⟨u, hu⟩ := IsPsiCoord.unique (⟨j, h, hj, rfl⟩ : IsPsiCoord D χ (genVal (D.psi χ) j h)) hx
  refine ⟨u, ?_⟩
  rw [← hu]
  exact Units.ext (gm_genVal ξ (D.psi χ) j h)

theorem alg_quot {A B C : Type} [CommGroup A] [CommGroup B] [CommGroup C] (k : B →* C) (f : A →* B)
    (c1 c2 c3 c4 : A) (x₁ x₂ x₃ : B) :
    k (f c1 * x₁) * (k (f c2 * x₂))⁻¹ * (k (f c3 * x₃))⁻¹ * (k (f c4))⁻¹ =
      k (f (c1 * c2⁻¹ * c3⁻¹ * c4⁻¹) * x₁ * x₂⁻¹ * x₃⁻¹) := by
  simp only [map_mul, map_inv, mul_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (a b : D.X)
    (x x₁ x₂ x₃ : (FractionRing R)ˣ), IsTauCoord D a b x → IsPsiCoord D (a + b) x₁ → IsPsiCoord D a x₂ →
      IsPsiCoord D b x₃ → ∃ u : Rˣ, (x : FractionRing R) =
        algebraMap R (FractionRing R) u * x₁ * (x₂ : FractionRing R)⁻¹ * (x₃ : FractionRing R)⁻¹ := by
  intro R _ _ _ D a b x x₁ x₂ x₃ hx h₁ h₂ h₃
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  let kU : (FractionRing R)ˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (kst ξ).toMonoidHom
  let aU : Rˣ →* (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom
  obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
  have hm := h (show ξ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
  have eT := gm_genVal ξ (D.tau a b) j h
  have dT : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) = _ := gm_mulGen _ _ ξ j hm
  rw [gm_mulGen _ _ ξ _ (mem_inl hm), gm_mulGen _ _ ξ _ (mem_inl (mem_inl hm)), gm_invGen, gm_invGen,
    gm_invGen] at dT
  obtain ⟨c1, g1⟩ := gm_psi D ξ (a + b) (((j ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inl) i1 x₁ h₁
  obtain ⟨c2, g2⟩ := gm_psi D ξ a (((j ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inr) i2 x₂ h₂
  obtain ⟨c3, g3⟩ := gm_psi D ξ b ((j ∘ Sum.inl) ∘ Sum.inr) i3 x₃ h₃
  obtain ⟨c4, g4⟩ := gm_rigK D ξ (j ∘ Sum.inr) i4 (mem_inr hm)
  have g4' : gm (𝟙 _) ξ (LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) (j ∘ Sum.inr))
      (D.rigK.s (j ∘ Sum.inr)) = kU (aU c4) := g4
  have eT' : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) =
      kU (genVal (D.tau a b) j h) := Units.ext eT
  have key : kU (genVal (D.tau a b) j h) =
      kU (aU c1 * x₁) * (kU (aU c2 * x₂))⁻¹ * (kU (aU c3 * x₃))⁻¹ * (kU (aU c4))⁻¹ :=
    eT'.symm.trans (dT.trans (by rw [g1, g2, g3, g4']))
  have key2 : genVal (D.tau a b) j h = aU (c1 * c2⁻¹ * c3⁻¹ * c4⁻¹) * x₁ * x₂⁻¹ * x₃⁻¹ := by
    refine Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_
    exact key.trans (alg_quot kU aU c1 c2 c3 c4 x₁ x₂ x₃)
  refine ⟨c1 * c2⁻¹ * c3⁻¹ * c4⁻¹, ?_⟩
  rw [key2, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  rfl

end GlobalTheory.TauCoordQuot
