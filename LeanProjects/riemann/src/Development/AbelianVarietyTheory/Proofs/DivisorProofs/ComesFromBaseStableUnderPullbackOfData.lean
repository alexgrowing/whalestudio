import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegUniqueAndComp
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverPullbackMapLeftCompPullbackFstScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegWholeSpectrumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompOfFirstTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegRescaleBothSidesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.DivFromPull

theorem divFrom_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (Q : DegPre R) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (Q' : DegPre V) [Module (𝓞 E) Q'.X] (oQ' : letI := H.starRing; Q'.OAct (𝓞 E)) (iw : L.W →+* R) (θ : R →+* V) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (hD : IsPullDeg θ Q Q') (e' : Q'.X ≃ₗ[𝓞 E] L.D.X), (∀ y, e' y = e (hD.xe y)) → (letI := H.starRing; ∀ x, oQ'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (oQ.onB.act x)) → (∀ k, θ (s k) ≠ 0) → DivFrom L Q oQ iw s ε e → DivFrom L Q' oQ' (θ.comp iw) (fun k => θ (s k)) ε e' := by
  intro E _ _ _ H D' l c L R V _ _ _ _ Q _ oQ Q' _ oQ' iw θ I _ s ε e hD e' he' hact hs hdiv
  obtain ⟨g, hD0, hg, hxe, hac⟩ := hdiv
  have ψL : Nonempty (PsiOn (mulDeg L.D l.M') ⊤) := GlobalTheory.ArcPull.nonempty_psiOn_top _ (fun y => L.gen (l.M' • y))
  obtain ⟨hD1, hW1, hp1, hx1⟩ := GlobalTheory.T.exists_isPullDeg_whole_spectrum hD0 ψL
  have ψR : Nonempty (PsiOn (GlobalTheory.PolDeg.rescale Q g) ⊤) := by
    have := GlobalTheory.PullDegUniq.nonempty_psiOn_pull hD1
    rw [hW1] at this
    simpa using this

  let n : Q'.X → I → ℤ := fun y k => (l.M' : ℤ) * ε k (e' y) (H.w0 • e' y)
  have hs0 : ∀ k, algebraMap V (FractionRing V) (θ (s k)) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs k)
  have hr0 : ∀ k, algebraMap R (FractionRing R) (s k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (fun h => hs k (by rw [h, map_zero]))
  let g' : Q'.X → (FractionRing V)ˣ := fun y =>
    (Units.mk0 (∏ k, algebraMap V (FractionRing V) (θ (s k)) ^ n y k)
      (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hs0 k)))⁻¹
  have hab : ∀ y, ∃ a b : R, θ b ≠ 0 ∧ (g (hD.xe y) : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a ∧
      (g' y : FractionRing V) * algebraMap V (FractionRing V) (θ b) = algebraMap V (FractionRing V) (θ a) := by
    intro y
    have key : ∀ {K : Type} [Field K] (x : K), x ≠ 0 → ∀ m : ℤ, x ^ (-m) * x ^ m.toNat = x ^ (-m).toNat := by
      intro K _ x hx m
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hx]
      congr 1
      omega
    have hgz : (g (hD.xe y) : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (s k) ^ (-n y k) := by
      have h := hg (hD.xe y)
      rw [Units.val_inv_eq_inv_val] at h
      rw [← inv_inv (g (hD.xe y) : FractionRing R), h, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg]
      simp only [n, he' y]
    have hg'y : (g' y : FractionRing V) = ∏ k, algebraMap V (FractionRing V) (θ (s k)) ^ (-n y k) := by
      simp only [g', Units.val_inv_eq_inv_val, Units.val_mk0, ← Finset.prod_inv_distrib, zpow_neg]
    refine ⟨∏ k, s k ^ (-n y k).toNat, ∏ k, s k ^ (n y k).toNat, ?_, ?_, ?_⟩
    · rw [map_prod]
      exact Finset.prod_ne_zero_iff.2 fun k _ => by rw [map_pow]; exact pow_ne_zero _ (hs k)
    · rw [hgz, map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_pow, map_pow]
      exact key _ (hr0 k) _
    · rw [hg'y, map_prod, map_prod, map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_pow, map_pow, map_pow, map_pow]
      exact key _ (hs0 k) _
  obtain ⟨h1, hp2, hx2⟩ := GlobalTheory.T.exists_isPullDeg_rescale_both_sides hD g g' ψR hab
  obtain ⟨r, hpr, hxr⟩ := GlobalTheory.T.exists_isPullDeg_comp_of_first_top hD1 h1 hW1
  refine ⟨g', r, fun y => ?_, fun y => ?_, fun x => ?_⟩
  · simp only [g', Units.val_inv_eq_inv_val, inv_inv, Units.val_mk0, map_zpow]
    rfl
  · exact (hxr y).trans ((hx1 _).trans ((congrArg hD0.xe (hx2 y)).trans ((hxe _).trans (he' y).symm)))
  · letI := H.starRing
    have c₁ : (oQ'.onB.act x).left ≫ hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) =
        hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) ≫ (oQ.onB.act x).left := by
      have := congrArg (fun m => m.left ≫ pullback.fst Q.P.A.hom (specOf θ)) (hact x)
      simpa only [Over.comp_left, Category.assoc, GlobalTheory.Mum.over_pullback_map_left_comp_pullbackFst_scheme] using this
    have hpr' : r.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf (θ.comp iw)) =
        (hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ)) ≫ hD0.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) :=
      hpr.trans (by rw [hp1]; exact congrArg (· ≫ _) hp2)
    have key : (oQ'.onB.act x).left ≫ ((hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ)) ≫ hD0.e.hom.left ≫
        pullback.fst L.D.P.A.hom (specOf iw)) = ((hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ)) ≫
        hD0.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) ≫ (L.oa.onB.act x).left := by
      simp only [Category.assoc] at c₁ hac ⊢
      rw [reassoc_of% c₁]
      exact congrArg _ (congrArg _ ((hac x).trans (Category.assoc _ _ _).symm))
    exact (congrArg _ hpr').trans (key.trans (congrArg (· ≫ _) hpr'.symm))

end GlobalTheory.UCanon.DivFromPull
