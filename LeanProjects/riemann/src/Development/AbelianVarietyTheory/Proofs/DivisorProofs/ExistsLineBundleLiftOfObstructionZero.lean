import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfThinBasisCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfIsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResPullURes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBasOfPreimageEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartsSquareZeroPresentedSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftOfObstructionEqZeroStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LBObs.exists_lift_of_isObL_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L₀ : LB X₀), IsPullback i s₀ s (spMap π) → L₀.IsLB → IsObL S α L₀ 0 → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S X s i P L₀ hpb hL₀ hob
  obtain ⟨C', _, _, G, hbas, u, hfr, hobu⟩ := hob
  rw [map_zero] at hobu
  obtain ⟨v, hvp, hvc⟩ := GlobalTheory.T.unitCocycle_lift_of_obstruction_eq_zero R R₀ I hI π hπ hk R₁ α C' (G ⋙ OAff s₀) ((ofSys S).restrict G) u hobu
  obtain ⟨V, hV, hi, e, hpre, he, hred⟩ := GlobalTheory.T.exists_charts_squareZero_presented_scheme R R₀ I hI π hπ hk X₀ s₀ S X s i P hpb
  let V' : C' → X.Opens := fun T => V (G.obj T)
  have hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T := fun T T' a => hV (G.map a)
  let u' : ∀ (T T' : C') (_ : T ⟶ T'), Γ(X, V' T')ˣ := fun T T' a => Units.map (e (G.obj T')).toMonoidHom (v T T' a)
  have hcoc : IsCoc V' hV' u' := by
    intro T T' T'' a b
    ext
    have h1 := hvc T T' T'' a b
    change e (G.obj T'') (v T T'' (a ≫ b)).val = _
    rw [h1]
    refine ((e (G.obj T'')).map_mul _ _).trans ?_
    exact congrArg (· * e (G.obj T'') (v T' T'' b).val) (he (G.obj T') (G.obj T'') (G.map b) (v T T' a).val)
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip
    (IsClosedImmersion.spec_of_surjective _ hπ)
  haveI : Surjective i := surjective_of_isPullback_sqZero hI hπ hk hpb
  have hbas' : IsBas V' := GlobalTheory.LBObs.isBas_of_preimage_eq X X₀ i C' V' (opOf G) (fun T => hpre _) hbas
  obtain ⟨L, hL, hfrL⟩ := GlobalTheory.T.exists_lineBundle_of_thinBasis_cocycle X C' V' hV' u' hbas' hcoc
  have hH : ∀ T, opOf G T ≤ i ⁻¹ᵁ V' ((𝟭 C').obj T) := fun T => (hpre _).ge
  have hfr2 := GlobalTheory.LBObs.isFrame_pull X C' V' hV' L u' X₀ i C' (opOf G) (opOf_le G) (𝟭 C') hH hfrL
  have hueq : (fun T T' (a : T ⟶ T') => res (hH T') (pullU i _ (u' _ _ ((𝟭 C').map a)))) = u := by
    funext T T' a
    ext
    have h2 := hred (G.obj T') (v T T' a).val
    have h3 := hvp T T' a
    refine Eq.trans ?_ (h2.trans h3)
    rfl
  rw [hueq] at hfr2
  exact ⟨L, hL, GlobalTheory.LBObs.lbIso_of_isFrame X₀ C' (opOf G) (opOf_le G) (L.pull i) L₀ u hbas (LB.isLB_pull hL i) hL₀ hfr2 hfr⟩
