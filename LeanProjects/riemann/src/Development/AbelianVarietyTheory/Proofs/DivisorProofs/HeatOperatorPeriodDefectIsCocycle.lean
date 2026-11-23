import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorActsOnFourierTermsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionsThetaShiftTripleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.HeatDefect

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ h) z U a = (r.stalkMap z).hom (gs h (r z) U a) := by
  rw [← gs_pull r h z U hU, gs_eq r z (h ⁻¹ᵁ U) hU, gs_eq h (r z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply r (h ⁻¹ᵁ U) z hU _).symm

theorem sval_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp_stalk r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem val_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    (val t (r ≫ h) z J).val = (r.stalkMap z).hom (val t h (r z) (fun ψ => J (r ≫ ψ))).val := by
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc]),
    val_of t h (r z) (fun ψ => J (r ≫ ψ)) (fun k => J (r ≫ h ≫ φ k)) (fun k => rfl)]
  have hm : (r ≫ h) z ∈ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) := Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  exact (gs_unit _ z _ hm _).symm.trans ((gs_comp_stalk r h z _ hm _).trans (congrArg _ (gs_unit h (r z) _ hm _)))

theorem good_comp {X Z : Scheme.{0}} {L : LB X} (r : Z ⟶ Z) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => by
  have := hJ (r ≫ ψ)
  rwa [Scheme.Hom.comp_apply] at this

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R}

theorem gs_scal (m : DegPre.BF Q (FractionRing R) ⟶ DegPre.BF Q (FractionRing R)) (z : (DegPre.BF Q (FractionRing R)).left)
    (c : R) : (m.left.stalkMap z).hom (gs (𝟙 _) (m.left z) ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c)) =
      gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c) := by
  rw [← gs_comp_stalk m.left (𝟙 _) z ⊤ trivial, Category.comp_id]
  unfold ReciprocityTheory.ChartRestriction.G.Out.scal
  have e₁ := gs_pull m.left (DegPre.BF Q (FractionRing R)).hom z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
  have e₂ := gs_pull (𝟙 _) (DegPre.BF Q (FractionRing R)).hom z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
  rw [Over.w m] at e₁
  rw [Category.id_comp] at e₂
  exact e₁.trans e₂.symm

end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect
variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R}

theorem shiftEq_at {k : ℕ} {mu α : Q.X} {σ : Q.SecB k α} {σ₁ σ₂ : Q.SecB k (α + k • mu)} {c : R}
    (H : ShiftEq Q k mu α σ σ₁ c σ₂)
    (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left)
      (DegPre.famMult Q (FractionRing R) k mu α))
    (m : DegPre.BF Q (FractionRing R) ⟶ DegPre.BF Q (FractionRing R)) (z : (DegPre.BF Q (FractionRing R)).left)
    (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι) (hJ : Good Q.P.L z J) :
    sval σ₁ (m ≫ DegPre.prB Q (FractionRing R)).left z J =
      (val u m.left z J).val *
          sval σ (m ≫ DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)).left z J +
        gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom c) *
          sval σ₂ (m ≫ DegPre.prB Q (FractionRing R)).left z J := by
  have e := congrArg (m.left.stalkMap z).hom (H u hu hc (m.left z) _ (good_comp m.left z hJ))
  rw [Over.comp_left, Over.comp_left, Over.comp_left, sval_comp_stalk _ _ _ _ hJ, sval_comp_stalk _ _ _ _ hJ,
    sval_comp_stalk _ _ _ _ hJ, e, map_add, map_mul, map_mul, gs_scal]
  congr 2
  have := val_comp_stalk u (𝟙 _) m.left z hJ
  rw [Category.comp_id] at this
  exact this.symm

end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect

theorem scal_injective (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) :
    Function.Injective (fun r : R => gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom r)) := by
  let F := FractionRing R
  let χ : F →+* (DegPre.BF Q F).left.presheaf.stalk z :=
    ((DegPre.BF Q F).left.presheaf.germ ⊤ z trivial).hom.comp
      ((fst (TF (R := R) F) Q.P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)
  have hT : (DegPre.BF Q F).hom = (fst (TF (R := R) F) Q.P.A).left ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
    rw [← Over.w (fst (TF (R := R) F) Q.P.A)]
    show _ ≫ (jFK (R := R) F ≫ jK R) = _
    rw [jFK, jK, ← Spec.map_comp]
    rfl
  have key : ∀ r : R, gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q F).hom r) = χ (algebraMap R F r) := by
    intro r
    unfold ReciprocityTheory.ChartRestriction.G.Out.scal
    rw [hT, gs_eq _ z ⊤ trivial]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R F))
    have n' := congrArg (fun f => f.hom r) n
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n'
    simp only [χ, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, n']
    rfl
  intro a b hab
  have : χ (algebraMap R F a) = χ (algebraMap R F b) := (key a).symm.trans (hab.trans (key b))
  exact IsFractionRing.injective R F (χ.injective this)
end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect

theorem sval_cast {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {k : ℕ} {x y : Q.X} (e : x = y)
    (he : Q.SecB k x = Q.SecB k y) (σ : Q.SecB k x) {Z : Scheme.{0}} (r : Z ⟶ Q.P.A.left) (z : Z)
    (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) : sval (cast he σ) r z J = sval σ r z J := by
  subst e; rfl

theorem tActs_cast {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} {Y : Ray oa} {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R}
    {h : Heat Y.H Y.q.left Q.P.L dd D} {k : ℕ} {x y : Q.X} (e : x = y) (he : Q.SecB k x = Q.SecB k y)
    {σ σ' : Q.SecB k x} (H : TActs Y h k x σ σ') : TActs Y h k y (cast he σ) (cast he σ') := by
  subst e; exact H

theorem scal_add {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) (a b : R) :
    gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom (a + b)) =
      gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom a) +
        gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom b) := by
  unfold ReciprocityTheory.ChartRestriction.G.Out.scal
  rw [map_add, map_add]
  exact gs_add (𝟙 _) z ⊤ trivial _ _

theorem scal_zero {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) :
    gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom 0) = 0 := by
  have := scal_add Q z 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem defect_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (c : ℕ → Dd.toPre.X → Dd.toPre.X → R), IsBasic Y h → HasDefect Y h c → ∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α, c k (mu + mu') α = c k mu α + c k mu' (α + k • mu) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv D h c hB hD k hk mu mu' α
  obtain ⟨σ, σ₁, σ₂, he, h1, h2, h3, z, J, hJ, hs⟩ := GlobalTheory.T.exists_integral_sections_thetaShift_triple R Dd k hk mu mu' α
  have e : α + k • mu + k • mu' = α + k • (mu + mu') := by rw [smul_add, add_assoc]
  obtain ⟨σ', a1⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h hB k α σ
  obtain ⟨σ₁', a2⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h hB k _ σ₁
  obtain ⟨σ₂', a3⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h hB k _ σ₂
  have d1 := hD k mu α σ σ' σ₁ σ₁' hk h1 a1 a2
  have d2 := hD k mu' (α + k • mu) σ₁ σ₁' σ₂ σ₂' hk h2 a2 a3
  have d3 := hD k (mu + mu') α σ σ' _ _ hk h3 a1 (tActs_cast e he a3)
  obtain ⟨⟨u1, hu1, hc1⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu α
  obtain ⟨⟨u2, hu2, hc2⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu' (α + k • mu)
  obtain ⟨⟨u3, hu3, hc3⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k (mu + mu') α
  have E1 := shiftEq_at d1 u1 hu1 hc1 (DegPre.trF Dd.toPre (FractionRing R) mu') z J hJ
  have E10 := shiftEq_at h1 u1 hu1 hc1 (DegPre.trF Dd.toPre (FractionRing R) mu') z J hJ
  have E2 := shiftEq_at d2 u2 hu2 hc2 (𝟙 _) z J hJ
  have E20 := shiftEq_at h2 u2 hu2 hc2 (𝟙 _) z J hJ
  have E3 := shiftEq_at d3 u3 hu3 hc3 (𝟙 _) z J hJ
  have E30 := shiftEq_at h3 u3 hu3 hc3 (𝟙 _) z J hJ
  simp only [Category.id_comp, scal_zero, zero_mul, add_zero] at E1 E10 E2 E20 E3 E30
  rw [sval_cast e he, sval_cast e he] at E3
  rw [sval_cast e he] at E30
  rw [← Category.assoc, UUA.trF_add, add_comm mu' mu] at E1 E10
  set s := sval σ (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set s' := sval σ' (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set v1 := (val u1 (DegPre.trF Dd.toPre (FractionRing R) mu').left z J).val
  set v2 := (val u2 (Over.Hom.left (𝟙 (DegPre.BF Dd.toPre (FractionRing R)))) z J).val
  set v3 := (val u3 (Over.Hom.left (𝟙 (DegPre.BF Dd.toPre (FractionRing R)))) z J).val
  set p1 := sval σ₁ (DegPre.trF Dd.toPre (FractionRing R) mu' ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set q := sval σ₂ (DegPre.prB Dd.toPre (FractionRing R)).left z J
  set C1 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k mu α))
  set C2 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k mu' (α + k • mu)))
  set C3 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k (mu + mu') α))
  have k1 : (v2 * v1 - v3) * s = 0 := by linear_combination (-v2) * E10 - E20 + E30
  have hv' : v2 * v1 - v3 = 0 := hs.mul_left_eq_zero.mp k1
  have k2 : (C3 - (C1 + C2)) * q = 0 := by linear_combination E2 - E3 + v2 * E1 + s' * hv' - C1 * E20
  have hq : IsUnit q := by
    rw [E30]; exact (Units.isUnit _).mul hs
  have hC : C3 = C1 + C2 := sub_eq_zero.mp (hq.mul_left_eq_zero.mp k2)
  rw [← scal_add] at hC
  exact scal_injective R Dd.toPre z hC

end GlobalTheory.HeatDefect
