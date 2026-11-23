import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineScalarTorusInvariantHeatOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjugateHeatOperatorPeriodShiftStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatDefect

theorem shiftEq_add {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {k : ℕ} {mu α : Q.X}
    {σ σ' σ'' : Q.SecB k α} {σ₁ σ₁' : Q.SecB k (α + k • mu)} {c₁ c₂ : R}
    (h0 : ShiftEq Q k mu α σ σ₁ 0 σ₁) (h1 : ShiftEq Q k mu α σ'' σ₁' c₁ σ₁)
    (h2 : ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J →
      sval σ'' x.left z J = sval σ' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom c₂) * sval σ x.left z J) :
    ShiftEq Q k mu α σ' σ₁' (c₁ + c₂) σ₁ := by
  intro u hu hc z J hJ
  have a := h1 u hu hc z J hJ
  have b := h0 u hu hc z J hJ
  have e := h2 _ (DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)) z J hJ
  have hz : (𝟙 (DegPre.BF Q (FractionRing R)).left) z ∈ (⊤ : (DegPre.BF Q (FractionRing R)).left.Opens) := trivial
  have g0 : gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom (0 : R)) = 0 := by
    rw [gs_eq _ z ⊤ hz]; simp only [Out.scal, map_zero]
  have gadd : gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom (c₁ + c₂)) =
      gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c₁) +
        gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c₂) := by
    rw [← gs_add _ z ⊤ hz]; simp only [Out.scal, map_add]
  rw [g0, zero_mul, add_zero] at b
  rw [a, e, gadd]
  linear_combination (-(gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c₂))) * b

end GlobalTheory.HeatDefect

theorem GlobalTheory.HeatDefect.defect_polynomial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∃ (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv m t gam hm ht D hD h hb
  have hA := fun mu => GlobalTheory.T.exists_conjugate_heatOperator_periodShift R Dd O oa Y n v dd hv m t gam hm ht D hD h hb mu
  choose h' w₁ π₁ π₁' hb' hΘ hu hrel using hA
  have hU := fun mu => GlobalTheory.T.exists_affine_scalar_torusInvariant_heatOperators R Dd.toPre O oa Y n v dd hv D h (h' mu) hb (hb' mu) (hΘ mu).symm (hu mu).symm
  choose ℓ π₂ π₂' hU using hU
  refine ⟨fun mu => w₁ mu + ℓ mu, fun mu => π₁ mu + π₂ mu, fun mu => π₁' mu + π₂' mu, ?_⟩
  intro k mu α σ σ' σ₁ σ₁' hk hs ht₀ ht₁
  obtain ⟨σ'', hσ'', hsh⟩ := hrel mu k α σ σ₁ σ₁' hk hs ht₁
  have key := GlobalTheory.HeatDefect.shiftEq_add hs hsh (hU mu k α σ σ' σ'' ht₀ hσ'')
  refine (congrArg (fun c => ShiftEq Dd.toPre k mu α σ' σ₁' c σ₁) ?_).mpr key
  simp only [AddMonoidHom.add_apply]
  ring
