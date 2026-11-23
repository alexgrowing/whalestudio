import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolZeroEqConnectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleSectionUnitAtClosedPointTorusChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftedSectionDivMonomialOverChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorShiftDivMonomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorActsOnFourierTerms
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitsEval

section Pts
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem c_zero_one : D.c 0 = 1 := by
  have h : D.c 0 = D.c 0 * D.c 0 := by
    have := D.c_add 0 0
    rwa [add_zero] at this
  exact (mul_eq_left.1 h.symm)

theorem left_toUnit {T : Scheme.{0}} (f : T ⟶ Spec (CommRingCat.of R)) :
    (toUnit (Over.mk f)).left = f := by
  have := Over.w (toUnit (Over.mk f))
  simpa using this

theorem famφB_pt {T : Scheme.{0}} (f : T ⟶ Spec (CommRingCat.of R)) (a b : D.X) :
    (f ≫ (D.c a).left) ≫ D.famφB b 0 = f ≫ (D.c a).left ∧
    (f ≫ (D.c a).left) ≫ D.famφB b 1 = f ≫ (D.c (a + b)).left ∧
    (f ≫ (D.c a).left) ≫ D.famφB b 2 = f ≫ (D.c b).left ∧
    (f ≫ (D.c a).left) ≫ D.famφB b 3 = f ≫ (D.c 0).left := by
  have hf : ∀ x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A, f ≫ x.left = (toUnit (Over.mk f) ≫ x).left := by
    intro x; rw [Over.comp_left, left_toUnit]
  refine ⟨by simp [DegPre.famφB], ?_, ?_, ?_⟩
  · change (f ≫ (D.c a).left) ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c b)).left = _
    have hp : ∀ (x y : D.P.A ⟶ D.P.A), padd D.P.A x y = x * y := fun _ _ => rfl
    have hp' : ∀ (x y : 𝟙_ _ ⟶ D.P.A), padd D.P.A x y = x * y := fun _ _ => rfl
    rw [hf, hf, ← Over.comp_left, D.c_add, hp, hp', comp_mul, comp_mul]
    congr 2
    all_goals simp [← Category.assoc]
  · change (f ≫ (D.c a).left) ≫ (toUnit D.P.A ≫ D.c b).left = _
    rw [hf, hf, ← Over.comp_left]; congr 1; simp [← Category.assoc]
  · change (f ≫ (D.c a).left) ≫ (toUnit D.P.A ≫ η[D.P.A]).left = _
    rw [hf, hf, ← Over.comp_left, c_zero_one]; congr 1
    rw [comp_one, ← Category.assoc, toUnit_unique ((toUnit _ ≫ D.c a) ≫ toUnit _) (toUnit _)]; rfl

end Pts
end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

section Ev
variable {A : Type} [CommRing A]

noncomputable def ev (z : Sp A) : A →+* (Sp A).presheaf.stalk z where
  toFun a := gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
  map_one' := by rw [map_one, gs_eq _ z ⊤ trivial, map_one, map_one]
  map_mul' a b := by rw [map_mul, gs_mul _ z ⊤ trivial]
  map_zero' := by rw [map_zero, gs_eq _ z ⊤ trivial, map_zero, map_zero]
  map_add' a b := by rw [map_add, gs_add _ z ⊤ trivial]

theorem ev_apply (z : Sp A) (a : A) : ev z a = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := rfl

theorem gs_spMap {R : Type} [CommRing R] (g : R →+* A) (z : Sp A) (r : R) :
    gs (spMap g) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = ev z (g r) := by
  have h := gs_pull (𝟙 _) (spMap g) z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  rw [Category.id_comp] at h
  rw [← h, ev_apply]
  congr 1
  have := congrArg (fun f => f.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact this.symm

theorem gm_unitOn (z : Sp A) (u : Aˣ) : gm (𝟙 _) z ⊤ (unitOn u) = Units.map (ev z).toMonoidHom u := by
  ext
  rw [← gs_unit _ z ⊤ trivial]
  rfl

end Ev
end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

theorem alg_eval {k S : Type} [Field k] [CharZero k] [CommRing S] (φ : DualNumber k →+* S) (e : ℕ) (he : 1 ≤ e)
    (κ ee : (DualNumber k)ˣ) (ℓα ℓμ s : k)
    (hee : (ee : DualNumber k) = 1 + TrivSqZeroExt.inr ((e : k) * ℓμ - s))
    (Uρ Uc Wi W0 Wt : Sˣ) (Aρ Ac A'c : S) (hAc : IsUnit Ac) (hWt : Wt * W0 = Wi)
    (hi : Aρ * Wi.val = φ (κ.val * (1 + TrivSqZeroExt.inr ℓα)) *
      (Ac + φ (TrivSqZeroExt.inr ((2 * (e : k))⁻¹)) * A'c))
    (hii : Uρ.val * Aρ * W0.val = φ (κ.val * (1 + TrivSqZeroExt.inr (ℓα + (e : k) * ℓμ))) *
      (Uc.val * Ac + φ (TrivSqZeroExt.inr ((2 * (e : k))⁻¹)) *
        (Uc.val * A'c - φ (TrivSqZeroExt.inl (2 * (e : k) * s)) * (Uc.val * Ac)))) :
    Uρ = Wt * Units.map φ.toMonoidHom ee * Uc := by
  set c₁ : k := (2 * (e : k))⁻¹ with hc₁
  have he0 : (2 * (e : k)) ≠ 0 := by
    have : (e : k) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
    exact mul_ne_zero two_ne_zero this
  have hnil : IsNilpotent (φ (TrivSqZeroExt.inr c₁) * A'c) := by
    refine ⟨2, ?_⟩
    rw [mul_pow, ← map_pow, pow_two, TrivSqZeroExt.inr_mul_inr, map_zero, zero_mul]
  have hX : IsUnit (Ac + φ (TrivSqZeroExt.inr c₁) * A'c) := by
    first
      | exact hnil.isUnit_add_left_of_commute hAc (Commute.all _ _)
      | exact IsUnit.add_of_isNilpotent hAc hnil
  have hK : IsUnit (φ (κ.val * (1 + TrivSqZeroExt.inr ℓα))) := by
    refine IsUnit.map φ (IsUnit.mul κ.isUnit ?_)
    refine ⟨⟨1 + TrivSqZeroExt.inr ℓα, 1 - TrivSqZeroExt.inr ℓα, ?_, ?_⟩, rfl⟩ <;>
      ext <;> simp
  have hY := hK.mul hX
  have d1 : φ (κ.val * (1 + TrivSqZeroExt.inr (ℓα + (e : k) * ℓμ))) -
      φ (κ.val * (1 + TrivSqZeroExt.inr (ℓα + (e : k) * ℓμ))) * φ (TrivSqZeroExt.inr c₁) *
        φ (TrivSqZeroExt.inl (2 * (e : k) * s)) = φ ee.val * φ (κ.val * (1 + TrivSqZeroExt.inr ℓα)) := by
    rw [← map_mul, ← map_mul, ← map_sub, ← map_mul, hee]
    congr 1
    have h1 : c₁ * (2 * (e : k) * s) = s := by rw [hc₁, ← _root_.mul_assoc, inv_mul_cancel₀ he0, _root_.one_mul]
    ext <;> simp <;> linear_combination (-(TrivSqZeroExt.fst (κ : DualNumber k))) * h1
  have d2 : φ (κ.val * (1 + TrivSqZeroExt.inr (ℓα + (e : k) * ℓμ))) * φ (TrivSqZeroExt.inr c₁) =
      φ ee.val * φ (κ.val * (1 + TrivSqZeroExt.inr ℓα)) * φ (TrivSqZeroExt.inr c₁) := by
    rw [← map_mul, ← map_mul, ← map_mul, hee]
    congr 1
    ext <;> simp <;> ring
  have hWt' : Wt.val * W0.val = Wi.val := by rw [← Units.val_mul, hWt]
  apply Units.ext
  simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  apply hY.mul_right_cancel
  linear_combination (-Uρ.val) * hi + (-(Uρ.val * Aρ)) * hWt' + Wt.val * hii +
    (Wt.val * Uc.val * Ac) * d1 + (Wt.val * Uc.val * A'c) * d2

end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

theorem exists_acts' {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) {O : Type} [CommRing O]
    [StarRing O] [Module O Dd.toPre.X] {oa : Dd.toPre.OAct O} (Y : Ray oa) {n : ℕ}
    (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left) (hv : ∀ a, IsInv Y.H (v a) (dd a))
    (inst : Algebra ℤ R) (D : @Derivation ℤ R R _ _ _ inst _ _) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D)
    (hb : IsBasic Y h) (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α) : ∃ σ', TActs Y h k α σ σ' := by
  obtain rfl : inst = Ring.toIntAlgebra R := Subsingleton.elim _ _
  exact heat_acts_on_terms R Dd O oa Y n v dd hv D h hb k α σ

end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

theorem prod_fam {G T : Type} [CommGroup G] (F : T → G) (p : Fin 4 → T) (e : ℕ) :
    ∏ j, F (p j) ^ DegPre.famε e j = F (p 0) ^ ((e : ℤ) - 1) * F (p 1) * (F (p 2))⁻¹ * F (p 3) := by
  simp [Fin.prod_univ_four, DegPre.famε]

end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

theorem mul_inv_mul_cancel_comm {G : Type} [CommGroup G] (a b c d x : G) (e : ℕ) :
    (a ^ ((e : ℤ) - 1) * b * c⁻¹ * d ^ (1 - (e : ℤ))) * (d ^ ((e : ℤ) - 1) * x * x⁻¹ * d) =
      a ^ ((e : ℤ) - 1) * b * c⁻¹ * d := by
  group

end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

set_option maxHeartbeats 1000000 in

theorem units_eval : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen → ∃ lam : ℕ → P.D.toPre.X → k, ∀ (mu α : P.D.toPre.X) (n : Fin m → ℕ) (ψ₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (K := PUnit) (fun _ => (P.D.toPre.c mu).left) fun _ => -1)) τ₀, GlobalTheory.LogKSChart.IsUnitPart P.D.toPre (bdParam k m d) gam mu n ψ₀ → IsUnitTau P.D.toPre (bdParam k m d) gam mu α τ₀ → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ ee : (DualNumber k)ˣ, (ee : DualNumber k) = 1 + TrivSqZeroExt.inr (lam e mu - ∑ i, ((e : k) * (n i : k) + (gam i mu α : k)) * MvPowerSeries.constantCoeff (q i)) → ∀ zz J, Good P.D.toPre.P.L zz J → (val ψ₀ (spMap ρ) zz J) ^ e * val τ₀ (spMap ρ) zz J * (val P.D.toPre.rig (spMap ρ) zz J) ^ e = gm (c' (mu)) zz _ (w.s (fun _ => J (c' (mu) ≫ π₂), fun _ => J (c' (mu) ≫ π₁))) ^ ((e : ℤ) - 1) * gm (c' (mu + α)) zz _ (w.s (fun _ => J (c' (mu + α) ≫ π₂), fun _ => J (c' (mu + α) ≫ π₁))) * (gm (c' (α)) zz _ (w.s (fun _ => J (c' (α) ≫ π₂), fun _ => J (c' (α) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) ^ (1 - (e : ℤ)) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn ee) * (val ψ₀ (spMap (constHom ρ)) zz J) ^ e * val τ₀ (spMap (constHom ρ)) zz J * (val P.D.toPre.rig (spMap (constHom ρ)) zz J) ^ e := by
  intro E _ _ _ H k _ _ m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B' _ π₁ π₂ c' hπ₁ hπ₂ hπ12 hc' w hw
  obtain ⟨κ, ℓ, hconn⟩ := GlobalTheory.T.heatOperator_symbolZero_eq_connection E H k m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B'
    π₁ π₂ c' hπ₁ hπ₂ hπ12 hc' w hw
  refine ⟨fun e mu => (e : k) * ℓ e mu, ?_⟩
  intro mu α n ψ₀ τ₀ hψ hτ
  obtain ⟨e₁, he₁⟩ := GlobalTheory.T.exists_bundleSection_unit_at_closedPoint_torusChart E H k m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B'
    π₁ π₂ c' hπ₁ hπ₂ hπ12 hc'
  obtain ⟨e₂, he₂⟩ := GlobalTheory.T.exists_shifted_section_div_monomial_over_chart E H k m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B'
    π₁ π₂ c' hπ₁ hπ₂ hπ12 hc' mu α n ψ₀ τ₀ hψ hτ
  refine ⟨max (max e₁ e₂) 1, fun e he ee hee zz J hJ => ?_⟩
  have he1 : 1 ≤ e := le_trans (le_max_right _ _) he
  have hle₁ : e₁ ≤ e := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) he
  have hle₂ : e₂ ≤ e := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) he
  obtain ⟨σ, hσu⟩ := he₁ e hle₁ mu α
  letI := H.starRing
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  obtain ⟨σ', hσσ'⟩ := exists_acts' P.D Y v' dd hdd _ D h hB e α σ
  obtain ⟨hN, hσ₁⟩ := he₂ e hle₂
  obtain ⟨σ₁, σ₁u, hS, hfac, hval⟩ := hσ₁ σ
  obtain ⟨σ₁', σ₁u', hS', hfac', hval'⟩ := hσ₁ σ'
  obtain ⟨σ₁u'', hT'', hval''⟩ := GlobalTheory.T.heatOperator_shift_div_monomial E H k m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B'
    π₁ π₂ c' hπ₁ hπ₂ hπ12 hc' e he1 mu α (fun i => ((e : ℤ) * n i + gam i mu α).toNat) σ σ' σ₁ σ₁u σ₁' σ₁u'
    hσσ' hS hS' hfac hfac'

  have pts := fun (a b : P.D.toPre.X) => famφB_pt P.D.toPre (spMap ρ) a b
  have pts' := fun (a b : P.D.toPre.X) => famφB_pt P.D.toPre (spMap (constHom ρ)) a b
  have hB' : ∀ a b : P.D.toPre.X, c' a ≫ B'.hom = c' b ≫ B'.hom := fun a b => by rw [(hc' a).1, (hc' b).1]
  have X0 : ∀ a b : P.D.toPre.X, c' a ≫ π₁ = (c' a ≫ π₁) ≫ P.D.toPre.famφB b 0 ∧
      c' a ≫ π₂ = (c' a ≫ π₂) ≫ P.D.toPre.famφB b 0 := fun a b =>
    ⟨by rw [(hc' a).2.1, (pts a b).1], by rw [(hc' a).2.2, (pts' a b).1]⟩
  have X1 : ∀ a b : P.D.toPre.X, c' (a + b) ≫ π₁ = (c' a ≫ π₁) ≫ P.D.toPre.famφB b 1 ∧
      c' (a + b) ≫ π₂ = (c' a ≫ π₂) ≫ P.D.toPre.famφB b 1 := fun a b =>
    ⟨by rw [(hc' _).2.1, (hc' a).2.1, (pts a b).2.1], by rw [(hc' _).2.2, (hc' a).2.2, (pts' a b).2.1]⟩
  have X2 : ∀ a b : P.D.toPre.X, c' b ≫ π₁ = (c' a ≫ π₁) ≫ P.D.toPre.famφB b 2 ∧
      c' b ≫ π₂ = (c' a ≫ π₂) ≫ P.D.toPre.famφB b 2 := fun a b =>
    ⟨by rw [(hc' _).2.1, (hc' a).2.1, (pts a b).2.2.1], by rw [(hc' _).2.2, (hc' a).2.2, (pts' a b).2.2.1]⟩
  have X3 : ∀ a b : P.D.toPre.X, c' 0 ≫ π₁ = (c' a ≫ π₁) ≫ P.D.toPre.famφB b 3 ∧
      c' 0 ≫ π₂ = (c' a ≫ π₂) ≫ P.D.toPre.famφB b 3 := fun a b =>
    ⟨by rw [(hc' _).2.1, (hc' a).2.1, (pts a b).2.2.2], by rw [(hc' _).2.2, (hc' a).2.2, (pts' a b).2.2.2]⟩
  have hi := hconn e he1 α σ σ' hσσ' _ (c' mu) ![c' mu, c' (mu + α), c' α, c' 0] (by
    intro j; fin_cases j
    · exact ⟨(X0 mu α).1, (X0 mu α).2, hB' _ _⟩
    · exact ⟨(X1 mu α).1, (X1 mu α).2, hB' _ _⟩
    · exact ⟨(X2 mu α).1, (X2 mu α).2, hB' _ _⟩
    · exact ⟨(X3 mu α).1, (X3 mu α).2, hB' _ _⟩) zz J hJ
  have hii := hconn e he1 (α + e • mu) σ₁u σ₁u'' hT'' _ (c' 0) ![c' 0, c' (α + e • mu), c' (α + e • mu), c' 0] (by
    intro j; fin_cases j
    · exact ⟨(X0 0 _).1, (X0 0 _).2, hB' _ _⟩
    · have h1 := X1 0 (α + e • mu)
      rw [zero_add] at h1
      exact ⟨h1.1, h1.2, hB' _ _⟩
    · exact ⟨(X2 0 _).1, (X2 0 _).2, hB' _ _⟩
    · exact ⟨(X3 0 _).1, (X3 0 _).2, hB' _ _⟩) zz J hJ

  have vρ := hval _ (spMap ρ) zz J hJ
  have vc := hval _ (spMap (constHom ρ)) zz J hJ
  have vc' := hval' _ (spMap (constHom ρ)) zz J hJ
  have v'' := hval'' _ (spMap (constHom ρ) ≫ (P.D.toPre.c 0).left) zz J hJ
  rw [← (hc' 0).2.1, ← (hc' mu).2.1] at vρ
  rw [← (hc' 0).2.2, ← (hc' mu).2.2] at vc vc'
  have hx0 : (spMap (constHom ρ) ≫ (P.D.toPre.c 0).left) ≫ P.D.toPre.P.A.hom = spMap (constHom ρ) := by
    rw [Category.assoc, Over.w (P.D.toPre.c 0)]; simp
  rw [hx0, gs_spMap, ← (hc' 0).2.2] at v''
  rw [(hc' mu).1, ← ev_apply, ← ev_apply] at hi
  rw [(hc' 0).1, ← ev_apply, ← ev_apply, v'', vρ, vc, vc'] at hii
  have hcH : ∀ r, constHom ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) := by
    intro r; simp [constHom, hρ, TrivSqZeroExt.algebraMap_eq_inl]
  set s : k := ∑ i, ((((e : ℤ) * n i + gam i mu α).toNat : ℕ) : k) * MvPowerSeries.constantCoeff (q i) with hs
  have hcst : constHom ρ (2 * (e : ChartRing k m d) * ∑ i, ((((e : ℤ) * n i + gam i mu α).toNat : ℕ) : ChartRing k m d) * q i) =
      TrivSqZeroExt.inl (2 * (e : k) * s) := by
    rw [hcH, hs]; congr 1
    rw [map_mul, map_mul, map_sum]
    simp only [map_mul, map_natCast, map_ofNat]
  rw [hcst, map_add, map_nsmul, nsmul_eq_mul] at hii

  have hee' : (ee : DualNumber k) = 1 + TrivSqZeroExt.inr ((e : k) * ℓ e mu - s) := by
    rw [hee, hs]
    congr 3
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have h0 := Int.toNat_of_nonneg (hN i)
    have h1 : ((((e : ℤ) * n i + gam i mu α).toNat : ℕ) : k) = ((((e : ℤ) * n i + gam i mu α) : ℤ) : k) := by
      rw [← Int.cast_natCast, h0]
    rw [h1]; push_cast; ring
  have hAc : IsUnit (sval σ (c' mu ≫ π₂) zz J) := by
    have := hσu zz J hJ
    rwa [← (hc' mu).2.2] at this
  rw [gm_unitOn, alg_eval (ev zz) e he1 (κ e) ee (ℓ e α) (ℓ e mu) s hee' _ _ _ _
    (gm (c' (mu)) zz _ (w.s (fun _ => J (c' (mu) ≫ π₂), fun _ => J (c' (mu) ≫ π₁))) ^ ((e : ℤ) - 1) *
      gm (c' (mu + α)) zz _ (w.s (fun _ => J (c' (mu + α) ≫ π₂), fun _ => J (c' (mu + α) ≫ π₁))) *
      (gm (c' (α)) zz _ (w.s (fun _ => J (c' (α) ≫ π₂), fun _ => J (c' (α) ≫ π₁))))⁻¹ *
      gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) ^ (1 - (e : ℤ)))
    _ _ _ hAc ?_ hi hii]
  · simp only [_root_.mul_assoc]
  · have e1 := prod_fam (fun x => gm x zz _ (w.s (fun _ => J (x ≫ π₂), fun _ => J (x ≫ π₁))))
      ![c' 0, c' (α + e • mu), c' (α + e • mu), c' 0] e
    have e2 := prod_fam (fun x => gm x zz _ (w.s (fun _ => J (x ≫ π₂), fun _ => J (x ≫ π₁))))
      ![c' mu, c' (mu + α), c' α, c' 0] e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] at e1 e2
    rw [e1, e2]
    exact mul_inv_mul_cancel_comm _ _ _ _ _ e

end GlobalTheory.UnitsEval
