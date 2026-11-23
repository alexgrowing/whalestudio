import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisibilityOnClosedFibreSpreadsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpansionScaledSectionCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpansionScaledSectionDivisibilityStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralLift

theorem dvd_of_specializes {V : Type} [CommRing V] {X : Scheme.{0}} (p : X ⟶ Sp V) {W : X.Opens} (a : Γ(X, W))
    {y z : X} (h : y ⤳ z) (hz : z ∈ W) (r : V) (hd : cst p z r ∣ gs (𝟙 X) z W a) : cst p y r ∣ gs (𝟙 X) y W a := by
  have hy : y ∈ W := h.mem_open W.isOpen hz
  have e₁ : ∀ (U : X.Opens) (hU : z ∈ U) (b : Γ(X, U)), (X.presheaf.stalkSpecializes h).hom (X.presheaf.germ U z hU b) =
      X.presheaf.germ U y (h.mem_open U.isOpen hU) b := fun U hU b => by
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  have k₁ : (X.presheaf.stalkSpecializes h).hom (gs (𝟙 X) z W a) = gs (𝟙 X) y W a := by
    rw [gs_eq _ z W hz, gs_eq _ y W hy]; exact e₁ _ _ _
  have k₂ : (X.presheaf.stalkSpecializes h).hom (cst p z r) = cst p y r := by
    rw [cst, cst, gs_eq _ z ⊤ trivial, gs_eq _ y ⊤ trivial]; exact e₁ _ _ _
  rw [← k₁, ← k₂]; exact map_dvd _ hd

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (q : ℕ), 1 ≤ q →
    ∀ (Φ : Fam D.toPre (FractionRing R) q) (f : ∀ α, D.toPre.SecB q α),
      (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) →
      ∃ σ : H0 U.LG.L q, ∀ e : ℕ, U.ExpandsAt e q σ f := by
  intro R _ _ _ hR D A G _ _ hG U q hq Φ f hf
  obtain ⟨s, ⟨r, hr, σ₁, f₁, -, hf₁, hE₁⟩, -⟩ := (U.expand q hq).2 Φ
  have h₁ : ∀ α, SecIsMul D.toPre.P.A.hom r (f₁ α) (f α) := fun α =>
    IntegralExpansion.secIsMul_of_secScal D.toPre.P.isLB _ (IntegralExpansion.prB_app_injective D.toPre) (hf α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing R))]; exact hf₁ α)
  have hcl := GlobalTheory.T.expansion_scaled_section_coordinates R hR.1 D A G U.toUnifPre q σ₁ f f₁ r h₁ hE₁
  have := hG.smooth
  have : Flat G.hom := inferInstance
  have hall : ∀ j, ∀ x ∈ (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (q : ℤ))).U j,
      cst G.hom x r ∣ gs (𝟙 G.left) x _ (σ₁.f j) := by
    intro j x hx
    refine GlobalTheory.T.divisibility_on_closed_fibre_spreads R hR.1 hR.2.1 G hG r hr _ _ x hx fun y hy ⟨z, hz, hyz⟩ => ?_
    obtain ⟨i, hi⟩ := exists_chart U.LG.isLB z
    have hz' : z ∈ (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (q : ℤ))).U (fun _ => i) :=
      Set.mem_iInter.2 fun _ => hi
    have hdz := hcl (fun _ => i) z hz' hz
    have hy' := hyz.mem_open (TopologicalSpace.Opens.isOpen _) hz'
    have hdy := dvd_of_specializes G.hom _ hyz hz' r hdz
    have hm : y ∈ (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (q : ℤ))).U j ⊓
        (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (q : ℤ))).U (fun _ => i) := ⟨hy, hy'⟩
    have e := congrArg (gs (𝟙 G.left) y _) (σ₁.compat j (fun _ => i))
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm] at e
    rw [e]
    exact Dvd.dvd.mul_left hdy _
  obtain ⟨σ, hσ⟩ := exists_div_sec G.hom hr σ₁ hall
  exact ⟨σ, GlobalTheory.T.expansion_scaled_section_divisibility R hR.1 D A G U.toUnifPre q σ σ₁ f f₁ r hr (fun j => hσ j) h₁ hE₁⟩

end GlobalTheory.IntegralLift
