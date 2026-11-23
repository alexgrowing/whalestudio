import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DimEqOfFiniteSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorBundleSectionGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitValueTranslatedBundleSectionStatement

set_option autoImplicit false

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralFamTriple

variable {R : Type} [CommRing R] [IsDomain R]

def Rel (Q : DegPre R) {k : ℕ} {β : Q.X} (σ : Q.SecB k β)
    (s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) β) (DegPre.famε k))) (r : R) : Prop :=
  ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι),
    Good Q.P.L z J → sval σ (x ≫ (DegPre.prB Q (FractionRing R)).left) z J =
      gs (x ≫ (DegPre.BF Q (FractionRing R)).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) * sval s x z J

theorem gs_zero {Y Z : Scheme.{0}} (f : Z ⟶ Y) (z : Z) : gs f z ⊤ (0 : Γ(Y, ⊤)) = 0 := by
  rw [gs_eq f z ⊤ trivial, map_zero, map_zero]

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem rel_scale {Q : DegPre R} {k : ℕ} {β : Q.X} {σ : Q.SecB k β}
    {s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) β) (DegPre.famε k))} {r : R} (h : Rel Q σ s r) (a : R) :
    Rel Q (DVR.SecOps.secScale (Out.scal Q.P.A.hom a) σ) s (a * r) := by
  intro Z x z J hJ
  rw [sval_secScale _ _ _ _ hJ, h Z x z J hJ, ← _root_.mul_assoc, map_mul, gs_mul _ z ⊤ trivial]
  refine congrArg (· * _) (congrArg (· * _) ?_)
  have e : (x ≫ (DegPre.prB Q (FractionRing R)).left) ≫ Q.P.A.hom = x ≫ (DegPre.BF Q (FractionRing R)).hom := by
    rw [Category.assoc, Over.w]
  rw [← e]
  exact gs_pull _ Q.P.A.hom z ⊤ trivial _

theorem rel_cast {Q : DegPre R} {k : ℕ} {F : Fam Q (FractionRing R) k} {a b : Q.X} (h : a = b) (σ : Q.SecB k b)
    (e : Q.SecB k b = Q.SecB k a) {r : R} (H : Rel Q σ (F.s b) r) : Rel Q (cast e σ) (F.s a) r := by
  subst h
  simpa only [cast_eq] using H

theorem isUnit_gs {Q : DegPre R} {r : R} (hr : r ≠ 0) {Z : Scheme.{0}} (x : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (z : Z) :
    IsUnit (gs (x ≫ (DegPre.BF Q (FractionRing R)).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  have e : x ≫ (DegPre.BF Q (FractionRing R)).hom =
      (x ≫ (fst (TF (R := R) (FractionRing R)) Q.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
    rw [← Over.w (fst (TF (R := R) (FractionRing R)) Q.P.A)]
    simp only [Category.assoc]
    rfl
  rw [e]
  set q := x ≫ (fst (TF (R := R) (FractionRing R)) Q.P.A).left ≫ jFK (R := R) (FractionRing R)
  rw [← gs_pull q (jK R) z ⊤ (Set.mem_univ _), gs_eq q z (jK R ⁻¹ᵁ ⊤) (Set.mem_univ _)]
  have n := congrArg (fun t => t.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  have u : IsUnit (algebraMap R (FractionRing R) r) := by
    have : algebraMap R (FractionRing R) r ≠ 0 := fun h0 =>
      hr (IsFractionRing.injective R (FractionRing R) (by rw [h0, map_zero]))
    exact this.isUnit
  have u' : IsUnit ((jK R).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
    rw [show jK R = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) from rfl, ← n]; exact u.map _
  exact (u'.map _).map _

theorem shiftEq_of_rel (Q : DegPre R) (k : ℕ) (F : Fam Q (FractionRing R) k) (mu α : Q.X) (r : R) (σ : Q.SecB k α)
    (σ₁ : Q.SecB k (α + k • mu)) (h₀ : Rel Q σ (F.s α) r) (h₁ : Rel Q σ₁ (F.s (α + k • mu)) r) :
    ShiftEq Q k mu α σ σ₁ 0 σ₁ := by
  intro u hu hc z J hJ
  have fe := (secRel_iff Q.P.isLB _ _ (F.s (α + k • mu)) _ _ (F.s α) (DegPre.trF Q (FractionRing R) mu).left _ _ u).1
    (F.fe mu α u hu hc) _ (𝟙 _) z J hJ
  have a₁ := h₁ _ (𝟙 _) z J hJ
  have a₀ := h₀ _ (DegPre.trF Q (FractionRing R) mu).left z J hJ
  have w : (DegPre.trF Q (FractionRing R) mu).left ≫ (DegPre.BF Q (FractionRing R)).hom =
      (DegPre.BF Q (FractionRing R)).hom := Over.w _
  simp only [Category.id_comp] at a₁ fe
  rw [w] at a₀
  have z0 : Out.scal (DegPre.BF Q (FractionRing R)).hom (0 : R) = 0 := by simp [Out.scal]
  rw [Over.comp_left, a₀, a₁, fe, z0, gs_zero, zero_mul, add_zero]
  ring

theorem exists_triple : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] (Dd : DegData R (maximalIdeal R)) (k : ℕ), 1 ≤ k → ∀ (mu mu' α : Dd.toPre.X), ∃ (σ : Dd.toPre.SecB k α) (σ₁ : Dd.toPre.SecB k (α + k • mu)) (σ₂ : Dd.toPre.SecB k (α + k • mu + k • mu')) (e : Dd.toPre.SecB k (α + k • mu + k • mu') = Dd.toPre.SecB k (α + k • (mu + mu'))), ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ ∧ ShiftEq Dd.toPre k mu' (α + k • mu) σ₁ σ₂ 0 σ₂ ∧ ShiftEq Dd.toPre k (mu + mu') α σ (cast e σ₂) 0 (cast e σ₂) ∧ ∃ (z : (DegPre.BF Dd.toPre (FractionRing R)).left) (J : ((DegPre.BF Dd.toPre (FractionRing R)).left ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J ∧ IsUnit (sval σ (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J) := by
  intro R _ _ _ _ _ Dd k hk mu mu' α
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.FamFree.exists_sec_ne_zero (D := Dd.toPre) (F := FractionRing R) GlobalTheory.CMClaims.secTwist hk α
  obtain ⟨F, hFα, -⟩ := GlobalTheory.FamFree.exists_fam_single GlobalTheory.CMClaims.laws.globalFns Dd.tau_bimult hk α s₀
  obtain ⟨r₀, hr₀, σ₀, h₀⟩ := GlobalTheory.T.exists_clear_denominator_bundleSection_genericFibre R Dd.toPre k α (F.s α)
  obtain ⟨r₁, hr₁, σ₁, h₁⟩ := GlobalTheory.T.exists_clear_denominator_bundleSection_genericFibre R Dd.toPre k (α + k • mu) (F.s (α + k • mu))
  obtain ⟨r₂, hr₂, σ₂, h₂⟩ := GlobalTheory.T.exists_clear_denominator_bundleSection_genericFibre R Dd.toPre k (α + k • (mu + mu')) (F.s (α + k • (mu + mu')))
  have g₀ := rel_scale (Q := Dd.toPre) (σ := σ₀) h₀ (r₁ * r₂)
  have g₁ := rel_scale (Q := Dd.toPre) (σ := σ₁) h₁ (r₀ * r₂)
  have g₂ := rel_scale (Q := Dd.toPre) (σ := σ₂) h₂ (r₀ * r₁)
  rw [show r₁ * r₂ * r₀ = r₀ * r₁ * r₂ by ring] at g₀
  rw [show r₀ * r₂ * r₁ = r₀ * r₁ * r₂ by ring] at g₁
  have hX : α + k • mu + k • mu' = α + k • (mu + mu') := by rw [smul_add, add_assoc]
  have e : Dd.toPre.SecB k (α + k • mu + k • mu') = Dd.toPre.SecB k (α + k • (mu + mu')) := by rw [hX]
  have g₂' := rel_cast (F := F) hX _ e.symm g₂
  refine ⟨_, _, cast e.symm (DVR.SecOps.secScale (Out.scal Dd.toPre.P.A.hom (r₀ * r₁)) σ₂), e,
    shiftEq_of_rel Dd.toPre k F mu α _ _ _ g₀ g₁,
    shiftEq_of_rel Dd.toPre k F mu' (α + k • mu) _ _ _ g₁ g₂', ?_, ?_⟩
  · rw [cast_cast, cast_eq]
    exact shiftEq_of_rel Dd.toPre k F (mu + mu') α _ _ _ g₀ g₂
  · obtain ⟨z, J, hJ, hu⟩ := GlobalTheory.T.exists_unit_value_translated_bundleSection R Dd.toPre k α (mu + mu') (F.s α) (by rw [hFα]; exact hs₀)
    refine ⟨z, J, hJ, ?_⟩
    rw [Over.comp_left, g₀ _ _ z J hJ]
    exact (isUnit_gs (mul_ne_zero (mul_ne_zero hr₀ hr₁) hr₂) _ z).mul hu

end GlobalTheory.IntegralFamTriple
