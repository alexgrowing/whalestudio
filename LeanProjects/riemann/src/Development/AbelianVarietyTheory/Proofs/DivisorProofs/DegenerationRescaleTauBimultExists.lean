import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleTrivialization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.RescaleBimult

variable {R : Type} [CommRing R] [IsDomain R]

theorem pt_add (D : DegPre R) (a b : D.X) :
    toUnit (TK R) ≫ D.c (a + b) = (toUnit (TK R) ≫ D.c a) * (toUnit (TK R) ≫ D.c b) := by
  rw [D.c_add]; exact MonObj.comp_mul _ _ _

theorem gm_unitOn_inj {u v : (FractionRing R)ˣ} (z : (TK R).left)
    (h : gm (𝟙 (TK R).left) z ⊤ (unitOn u) = gm (𝟙 (TK R).left) z ⊤ (unitOn v)) : u = v := by
  have hs : Subsingleton (TK R).left := (inferInstance : Subsingleton (PrimeSpectrum (FractionRing R)))
  have e : unitOn u = unitOn v := unit_ext fun x _ => by rw [Subsingleton.elim x z]; exact h
  exact Units.map_injective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1 e

theorem val_tau (D : DegPre R) (a b : D.X) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val (D.tau a b) (𝟙 _) z J = val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.psi b) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_cub3 (D : DegPre R) (a a' b : D.X) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c a') (toUnit (TK R) ≫ D.c b) := by
  refine (val_cub D.cub (𝟙 (TK R)) hJ _ _ _).trans ?_
  rw [Category.id_comp, Category.id_comp, Category.id_comp]

theorem exists_defect (D : DegPre R) (a a' b : D.X) : ∃ k : (FractionRing R)ˣ, ∀ (z : (TK R).left) J, Good D.P.L z J →
    val (D.psi (a + a' + b)) (𝟙 _) z J * val (D.psi a) (𝟙 _) z J * val (D.psi a') (𝟙 _) z J * val (D.psi b) (𝟙 _) z J *
      val D.rigK (𝟙 _) z J *
      cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c a') (toUnit (TK R) ≫ D.c b) =
      gm (𝟙 (TK R).left) z ⊤ (unitOn k) *
        (val (D.psi (a + a')) (𝟙 _) z J * val (D.psi (a + b)) (𝟙 _) z J * val (D.psi (a' + b)) (𝟙 _) z J) := by
  let t := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.psi (a + a' + b)) (D.psi a)) (D.psi a')) (D.psi b)) D.rigK)
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b))
  have ht : t.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (D.psi_gen _)) (D.psi_gen _))
    (D.psi_gen _)) (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)
  let t' := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (D.psi (a + a')) (D.psi (a + b))) (D.psi (a' + b))
  have ht' : t'.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (D.psi_gen _))
    (D.psi_gen _)
  obtain ⟨c, hc, H⟩ := DVR.TWM.exists_ratio (F := FractionRing R) D.P.isLB t ht t' ht' (fun U _ h => by
    refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl
      (prod_cub (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c a') (toUnit (TK R) ≫ D.c b) h))).trans ?_
    rw [← pt_add, ← pt_add, ← pt_add, ← pt_add]
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, zpow_neg, zpow_one]
    have e : (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TK R ⟶ D.P.A).left := rfl
    erw [e]
    simp only [ptK]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel)
  refine ⟨Units.mk0 c hc, fun z J hJ => ?_⟩
  have e := H _ (𝟙 _) z J hJ
  have e₁ : val t (𝟙 _) z J = val (D.psi (a + a' + b)) (𝟙 _) z J * val (D.psi a) (𝟙 _) z J *
      val (D.psi a') (𝟙 _) z J * val (D.psi b) (𝟙 _) z J * val D.rigK (𝟙 _) z J *
      cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c a') (toUnit (TK R) ≫ D.c b) :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (val_mul hJ _ _ _) rfl)) rfl)) rfl)) (val_cub3 D a a' b hJ))
  have e₂ : val t' (𝟙 _) z J = val (D.psi (a + a')) (𝟙 _) z J * val (D.psi (a + b)) (𝟙 _) z J *
      val (D.psi (a' + b)) (𝟙 _) z J :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)
  rw [← e₁, ← e₂]
  refine Units.ext (e.trans ?_)
  rw [Units.val_mul, ← gs_unit _ z ⊤ trivial]
  rfl

theorem exists_rescale_tauBimult : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R),
    ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).TauBimult := by
  intro R _ _ D
  choose F hF using exists_defect D
  let z₀ : (TK R).left := (⊥ : PrimeSpectrum (FractionRing R))
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z₀
  have C := isCub_cubV D.cub hJ₀
  have um : ∀ u v : (FractionRing R)ˣ, unitOn (u * v) = unitOn u * unitOn v :=
    fun u v => map_mul _ _ _
  have ui : ∀ u : (FractionRing R)ˣ, unitOn u⁻¹ = (unitOn u)⁻¹ := fun u => map_inv _ _
  have E := fun {z : (TK R).left} {p q : ((TK R).left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  obtain ⟨g, hg⟩ := GlobalTheory.symm_cubical_cocycle_isThirdDifference D.X (FractionRing R)ˣ F
    (fun a b c => gm_unitOn_inj z₀ (by
      have h₁ := E (hF a b c z₀ J₀ hJ₀)
      have h₂ := E (hF b a c z₀ J₀ hJ₀)
      rw [add_comm b a, C.s01] at h₂
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at h₁ h₂
      linear_combination (norm := abel) h₂ - h₁))
    (fun a b c => gm_unitOn_inj z₀ (by
      have h₁ := E (hF a b c z₀ J₀ hJ₀)
      have h₂ := E (hF a c b z₀ J₀ hJ₀)
      rw [add_comm c b, add_right_comm a c b, C.s12] at h₂
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at h₁ h₂
      linear_combination (norm := abel) h₂ - h₁))
    (fun x x' x'' y => gm_unitOn_inj z₀ (by
      have h₁ := E (hF (x + x') x'' y z₀ J₀ hJ₀)
      have h₂ := E (hF x x' y z₀ J₀ hJ₀)
      have h₃ := E (hF x (x' + x'') y z₀ J₀ hJ₀)
      have h₄ := E (hF x' x'' y z₀ J₀ hJ₀)
      have h₅ := E (C.coc (toUnit (TK R) ≫ D.c x) (toUnit (TK R) ≫ D.c x') (toUnit (TK R) ≫ D.c x'')
        (toUnit (TK R) ≫ D.c y))
      rw [← pt_add, ← pt_add] at h₅
      rw [← add_assoc x x' x''] at h₃
      rw [um, um, map_mul, map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at h₁ h₂ h₃ h₄ h₅ ⊢
      linear_combination (norm := abel) h₃ + h₄ - h₁ - h₂ + h₅))
  refine ⟨fun x => (g x)⁻¹, fun (a a' b : D.X) => corr_of_val D.P.isLB fun z J hJ => ?_⟩
  have hp : ∀ x : D.X, val ((GlobalTheory.PolDeg.rescale D fun x => (g x)⁻¹).psi x) (𝟙 _) z J =
      (gm (𝟙 (TK R).left) z ⊤ (unitOn (g x)))⁻¹ * val (D.psi x) (𝟙 _) z J := fun x =>
    (GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (by rw [ui, map_inv]; rfl)
  have ht : ∀ x y : D.X, val ((GlobalTheory.PolDeg.rescale D fun x => (g x)⁻¹).tau x y) (𝟙 _) z J =
      (gm (𝟙 (TK R).left) z ⊤ (unitOn (g (x + y))))⁻¹ * val (D.psi (x + y)) (𝟙 _) z J *
      ((gm (𝟙 (TK R).left) z ⊤ (unitOn (g x)))⁻¹ * val (D.psi x) (𝟙 _) z J)⁻¹ *
      ((gm (𝟙 (TK R).left) z ⊤ (unitOn (g y)))⁻¹ * val (D.psi y) (𝟙 _) z J)⁻¹ *
      (val D.rigK (𝟙 _) z J)⁻¹ := fun x y =>
    (val_tau (GlobalTheory.PolDeg.rescale D fun x => (g x)⁻¹) x y hJ).trans (congrArg₂ (· * ·) (congrArg₂ (· * ·)
      (congrArg₂ (· * ·) (hp (x + y)) (congrArg (·⁻¹) (hp x))) (congrArg (·⁻¹) (hp y))) rfl)
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (ht (a + a') b) (val_cub3 D a a' b hJ))).trans
    (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (ht a b) (ht a' b))).symm)
  have h₁ := E (hF a a' b z J hJ)
  have h₂ := congrArg (fun u => gm (𝟙 (TK R).left) z ⊤ (unitOn u)) (hg a a' b)
  simp only [um, map_mul] at h₂
  have h₃ := E h₂
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at h₁ h₃ ⊢
  linear_combination (norm := abel) h₁ + h₃

end GlobalTheory.RescaleBimult
