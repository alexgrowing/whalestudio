import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedTorusInvariantHeatOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaugedTorusInvariantHeatOperatorStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.ConjGauge
open ReciprocityTheory.ChartRestriction.G.Semi

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  intro i j
  have e : (LB.LinComb L (Y := Y) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i j = 1 := by
    dsimp only [LB.LinComb]
    erw [Fintype.prod_empty]
    rfl
  show res _ (1 : Γ(Y, _)ˣ) = _ * res _ (1 : Γ(Y, _)ˣ)
  rw [map_one, map_one, e, _root_.one_mul]

theorem exists_pullSec {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (m : Y ⟶ X) (T : Y ⟶ Y) (k : ℕ)
    (τ : SecM m L k) : ∃ σ : SecM (T ≫ m) L k, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι),
      Good L z J → sval σ r z J = sval τ (r ≫ T) z J := by
  have hF : FormEq (K := Fin 1 ⊕ PEmpty.{1}) (Sum.elim (fun _ : Fin 1 => T ≫ m) PEmpty.elim)
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) PEmpty.elim) (K' := Fin 1) (fun _ => T ≫ m) (fun _ => (k : ℤ)) := by
    intro U _ h
    simp [Fintype.prod_sum_type]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF (pullMulSec τ T (LB.oneGen L (Y := Y)) (oneGen_isGen L))
  refine ⟨σ, fun Z r z J hJ => ?_⟩
  rw [hσ Z r z J hJ, sval_pullMulSec τ T _ _ r z hJ, val_one, Units.val_one, _root_.mul_one]

theorem conj_gauge : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → ∀ (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), e.IsGen → (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∃ h' : Heat Y.H Y.q.left Q.P.L dd ⇑D, IsBasic Y h' ∧ h'.Θ = h.Θ ∧ h'.u = h.u ∧ ∀ (k : ℕ) (τ τ' ρ ρ' : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ' r z J = sval τ' (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → h.Acts k τ τ' → h'.Acts k ρ ρ' := by
  intro R _ _ _ Q O _ _ _ oa Y n v dd hv D h hB x e β he hwt
  obtain ⟨h₁, hΘ₁, hu₁, hB₁, hA₁⟩ := GlobalTheory.T.exists_translated_torus_invariant_heat_operator R Q O oa Y n v dd hv D h hB x
  obtain ⟨h', hB', hΘ', hu', hA'⟩ := GlobalTheory.T.exists_gauged_torusInvariant_heatOperator R Q O oa Y n v dd hv D x h₁ hB₁ e β he hwt
  refine ⟨h', hB', hΘ'.trans hΘ₁, hu'.trans hu₁, fun k τ τ' ρ ρ' hρ hρ' hact => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_pullSec Q.P.L Q.P.isLB Y.q.left (𝟙 Y.H * (toUnit Y.H ≫ x)).left k τ
  obtain ⟨σ', hσ'⟩ := exists_pullSec Q.P.L Q.P.isLB Y.q.left (𝟙 Y.H * (toUnit Y.H ≫ x)).left k τ'
  exact hA' k σ σ' ρ ρ' (fun Z r z J hJ => by rw [hσ Z r z J hJ]; exact hρ Z r z J hJ)
    (fun Z r z J hJ => by rw [hσ' Z r z J hJ]; exact hρ' Z r z J hJ) (hA₁ k τ τ' σ σ' hσ hσ' hact)

end GlobalTheory.Heat.ConjGauge
