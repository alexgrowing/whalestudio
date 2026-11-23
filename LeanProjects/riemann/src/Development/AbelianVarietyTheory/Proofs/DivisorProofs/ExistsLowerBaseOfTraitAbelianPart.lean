import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibrePowerPointFiniteExtensionDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointLiftsToLowerBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

theorem exists_lowBase_of_trait : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (L : LowBase (zetaAway n) n) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : L.W →+* V') (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)), L.h = PB.g ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ ∃ (B' : Over (Sp V')) (_ : GrpObj B') (β' : B'.left ⟶ PB.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 PB.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsGrpPullback B' PB.A (spMap f) β' ∧ IsGrpPullback B' L.T.B (spMap κ) β'' ∧ IsSquare β' β₂ ∧ IsSquare β'' β₂' ∧ LBIso ((abelian₂ PB.A PB.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') ∧ ∀ a : Fin L.T.r → ℤ, ∃ x : Sp V' ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f ≫ (c (e a)).left ∧ x ≫ β'' = spMap κ ≫ (L.T.c₀ ((n : ℤ) • a)).left := by
  intro n hn ho V _ _ _ hV hd b PB r c hc
  obtain ⟨F, V₁, _, _, _, f₁, v, hs, hV₁, hd₁, hi₁, hf₁, hl₁, β₁, β₁₂, hp₁, hq₁, hL₁, hc₁⟩ :=
    GlobalTheory.T.exists_fibrePower_point_finite_extension_dvr n hn ho V hV hd b PB r c hc
  obtain ⟨L, V', _, _, _, f, κ, e, hh, hV', hd', hi, hf, hl, hκ, hb, B', _, β', β'', β₂, β₂', hp, hp', hq, hq', hL, hx⟩ :=
    GlobalTheory.T.siegelFibrePower_point_lifts_to_lower_base n hn ho PB.g F r V₁ hV₁ hd₁ (f₁.comp b) v hs
  have es : spMap (f.comp f₁) = spMap f ≫ spMap f₁ := by
    rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hl' : IsLocalHom (f.comp f₁) := RingHom.isLocalHom_comp f f₁
  refine ⟨L, V', inferInstance, inferInstance, inferInstance, f.comp f₁, κ, e, hh, hV', hd', hi.comp hi₁,
    hf.comp hf₁, hl', hκ, ?_, B', inferInstance, β' ≫ β₁, β'', β₂ ≫ β₁₂, β₂', ?_, hp', isSquare_comp hq hq₁, hq', ?_, ?_⟩
  · rw [hb, RingHom.comp_assoc]
  · rw [es]
    exact hp.comp hp₁
  · have h1 : LBIso ((LowChart.siegAt F v _ hs).P.pull β₂) ((abelian₂ PB.A PB.L).pull (β₂ ≫ β₁₂)) :=
      lbIso_pull_comp hL₁ β₂ rfl
    exact LBIso.trans (pull_isLB (LB.isLB_linComb PB.isLB _ _) _) (pull_isLB (LowChart.siegAt F v _ hs).isLB _)
      (pull_isLB (LB.isLB_linComb L.T.M.isLB _ _) _) h1.symm hL
  · intro a
    obtain ⟨x, h1, h2, h3⟩ := hx a
    refine ⟨x, h1, ?_, h3⟩
    rw [← Category.assoc, h2, Category.assoc, hc₁, es, Category.assoc]

end GlobalTheory.TChart
