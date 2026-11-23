import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetrySecondDifferenceEqCubicalRatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauPeriodValNegCubicalRatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DefectHom

variable {R : Type} [CommRing R] [IsDomain R]

theorem c_zero (D : DegPre R) : D.c 0 = 1 := by
  have h : D.c (0 + 0) = D.c 0 * D.c 0 := D.c_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem c_neg (D : DegPre R) (a : D.X) : D.c (-a) = (D.c a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  have h : D.c (-a + a) = D.c (-a) * D.c a := D.c_add _ _
  rw [neg_add_cancel, c_zero] at h
  exact h.symm

theorem pt_neg (D : DegPre R) (a : D.X) : toUnit (TK R) ≫ D.c (-a) = (toUnit (TK R) ≫ D.c a)⁻¹ := by
  rw [c_neg, GrpObj.comp_inv]

theorem pt_add (D : DegPre R) (a b : D.X) :
    toUnit (TK R) ≫ D.c (a + b) = (toUnit (TK R) ≫ D.c a) * (toUnit (TK R) ≫ D.c b) := by
  rw [D.c_add, ← MonObj.comp_mul]; rfl

theorem neg_pt_left (D : DegPre R) (a : D.X) : ptK (D.c (-a)) = D.xK a ≫ (ι[D.P.A]).left := by
  show (toUnit (TK R) ≫ D.c (-a)).left = _
  rw [pt_neg, Hom.inv_def, Over.comp_left]

theorem exists_defect (D : DegPre R) (χ : D.X) : ∃ k : (FractionRing R)ˣ, ∀ (z : (TK R).left) J, Good D.P.L z J →
    val (D.psi (-χ)) (𝟙 _) z J * val D.sym (D.xK χ) z J =
      gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val (D.psi χ) (𝟙 _) z J := by
  let t := LB.mulGen D.P.L _ _ _ _ (D.psi (-χ)) (LB.pullGen D.P.L _ _ D.sym (D.xK χ))
  have ht : t.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)
  have hf : FormEq (Sum.elim (fun _ : PUnit => ptK (D.c (-χ))) (fun k => D.xK χ ≫ ![(ι[D.P.A]).left, 𝟙 D.P.A.left] k))
      (Sum.elim (fun _ => -1) ![1, -1]) (fun _ : PUnit => ptK (D.c χ)) (fun _ => -1) := by
    intro U _ h
    rw [Fintype.prod_sum_type, Fin.prod_univ_two, neg_pt_left]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id]
    simp only [zpow_neg, zpow_one]
    group
  obtain ⟨c, hc, H⟩ := DVR.TWM.exists_ratio (F := FractionRing R) D.P.isLB t ht (D.psi χ) (D.psi_gen χ) hf
  refine ⟨Units.mk0 c hc, fun z J hJ => ?_⟩
  have e := H _ (𝟙 _) z J hJ
  have e₁ : val t (𝟙 _) z J = val (D.psi (-χ)) (𝟙 _) z J * val D.sym (D.xK χ) z J := by
    refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans ?_))
    rw [Category.id_comp]
  rw [← e₁]
  refine Units.ext (e.trans ?_)
  rw [Units.val_mul, ← gs_unit _ z ⊤ trivial]
  rfl

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

theorem exists_evenDefect_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R),
    D.TauBimult → ∃ h : D.X → (FractionRing R)ˣ, (∀ a b, h (a + b) = h a * h b) ∧ EvenDefect D h := by
  intro R _ _ _ D hB
  choose h hh using exists_defect D
  refine ⟨h, fun a b => ?_, hh⟩
  let z : (TK R).left := (⊥ : PrimeSpectrum (FractionRing R))
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  refine gm_unitOn_inj z ?_
  have g1 := GlobalTheory.T.symmetry_secondDifference_eq_cubical_ratio R D (TK R) (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) z J hJ
  have g2 := GlobalTheory.T.tau_period_val_neg_cubical_ratio R D hB a b z J hJ
  rw [← pt_neg, ← pt_neg, ← pt_add] at g1
  rw [val_tau D a b hJ, val_tau D (-a) (-b) hJ, ← neg_add] at g2
  have e₀ := hh (a + b) z J hJ
  have e₁ := hh a z J hJ
  have e₂ := hh b z J hJ
  change val D.sym (D.xK (a + b)) z J * _ = val D.sym (D.xK a) z J * val D.sym (D.xK b) z J * _ at g1
  rw [show unitOn (h a * h b) = unitOn (h a) * unitOn (h b) from map_mul _ _ _, map_mul]
  generalize val D.sym (D.xK (a + b)) z J = s₀ at g1 e₀
  generalize val D.sym (D.xK a) z J = s₁ at g1 e₁
  generalize val D.sym (D.xK b) z J = s₂ at g1 e₂
  generalize gm (𝟙 (TK R).left) z ⊤ (unitOn (h (a + b))) = k₀ at e₀ ⊢
  generalize gm (𝟙 (TK R).left) z ⊤ (unitOn (h a)) = k₁ at e₁ ⊢
  generalize gm (𝟙 (TK R).left) z ⊤ (unitOn (h b)) = k₂ at e₂ ⊢
  apply Additive.ofMul.injective
  have E := fun {p q : ((TK R).left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₀ := E e₀; have a₁ := E e₁; have a₂ := E e₂; have b₁ := E g1; have b₂ := E g2
  simp only [ofMul_mul, ofMul_inv] at a₀ a₁ a₂ b₁ b₂ ⊢
  linear_combination (norm := abel) -a₀ + a₁ + a₂ + b₁ - b₂
end GlobalTheory.DefectHom
