import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LiftOUnique
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefUnit
open GlobalTheory.UT.CoefBasic

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem point_ext {X : Scheme.{0}} [X.IsSeparated] (x₁ x₂ : (TWM.TO hϖ hv).left ⟶ X)
    (h : (TWM.ιS hϖ hv).left ≫ x₁ = (TWM.ιS hϖ hv).left ≫ x₂) : x₁ = x₂ := by
  have hU : ValuativeCriterion.Uniqueness (terminal.from X) := IsSeparated.valuativeCriterion _
  let S : ValuativeCommSq (terminal.from X) :=
    { R := TWO.Ov v, K := F, i₁ := (TWM.ιS hϖ hv).left ≫ x₁, i₂ := terminal.from _,
      commSq := ⟨terminal.hom_ext _ _⟩ }
  have := (hU S).elim ⟨x₁, rfl, terminal.hom_ext _ _⟩ ⟨x₂, h.symm, terminal.hom_ext _ _⟩
  exact congrArg CommSq.LiftStruct.l this

theorem exists_ratio_nonneg {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((TWM.TO hϖ hv).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((TWM.TO hϖ hv).left ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht' : t'.IsGen) : ∃ x : F, 0 ≤ v x ∧ ∀ z J, Good L z J →
      (val t (TWM.ιS hϖ hv).left z J).val = cst (R := V) F z x * (val t' (TWM.ιS hϖ hv).left z J).val := by
  obtain ⟨s, hs⟩ := exists_sec hL h (Geo.Tor.genSec t ht)
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.TwistUnit.exists_ratio_local (R := TWO.Ov v) hL s t' ht'
  refine ⟨TWM.ιr (v := v) x₀, TWM.v_ιr x₀, fun z J hJ => ?_⟩
  have e := gs_pull (𝟙 _) (TWM.ιS hϖ hv).left z ⊤ trivial x₀
  rw [Category.id_comp] at e
  have e' := e.symm.trans (congrArg (gs (𝟙 _) z ⊤)
    (TWM.appTop_specMap (CommRingCat.ofHom (algebraMap (TWO.Ov v) F)) x₀))
  exact (sval_genSec t ht _ z hJ).symm.trans ((hs _ _ z J hJ).symm.trans
    ((hx₀ _ _ z J hJ).trans (congrArg (· * _) e')))

theorem exists_ratio_zero {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((TWM.TO hϖ hv).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((TWM.TO hϖ hv).left ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht' : t'.IsGen) : ∃ x : F, v x = 0 ∧ ∀ z J, Good L z J →
      (val t (TWM.ιS hϖ hv).left z J).val = cst (R := V) F z x * (val t' (TWM.ιS hϖ hv).left z J).val := by
  obtain ⟨x, hx, e⟩ := exists_ratio_nonneg hϖ hv hL h t ht t' ht'
  obtain ⟨y, hy, e'⟩ := exists_ratio_nonneg hϖ hv hL (fun U _ g => (h U g).symm) t' ht' t ht
  refine ⟨x, le_antisymm (TWO.le_zero_of_add_eq_zero_nonneg ?_ hy) hx, e⟩
  obtain ⟨z⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have a := e z J hJ
  rw [e' z J hJ, ← _root_.mul_assoc, cst_eq, cst_eq, ← map_mul] at a
  have b : cstH z (x * y) = 1 := by
    rw [← Units.mul_left_inj (val t (TWM.ιS hϖ hv).left z J), _root_.one_mul]; exact a.symm
  rw [← AddValuation.map_mul, cstH_inj z (b.trans (map_one _).symm), AddValuation.map_one]

theorem v_of_isCoef {D : DegData V (maximalIdeal V)} {k : ℕ} {g : GtPtF D.toPre F} {w : Frm D.toPre F k g.b}
    {χ : D.toPre.X} {l ω : ℚ} (hg : GenV hϖ hv (g.s χ) l) (hw : GenV hϖ hv w ω)
    (m : TWM.TO hϖ hv ⟶ D.toPre.P.A) (hm : TWM.ιS hϖ hv ≫ m = g.b)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)))
    (G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => m.left ≫ DegPre.famφB D.toPre χ i) (DegPre.famε k)))
    (hG₀ : G₀.IsGen) (x : F)
    (hs : ∀ z J, Good D.toPre.P.L z J → sval s (lift (𝟙 (TF (R := V) F)) g.b).left z J =
      cst (R := V) F z x * (val G₀ (TWM.ιS hϖ hv).left z J).val) :
    ∃ c, IsCoef k g w χ s c ∧ v c = v x + ((l + ω : ℚ) : WithTop ℚ) := by
  have hL := D.toPre.P.isLB
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  have : D.toPre.P.A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  obtain ⟨φ₁, h₁, t₁, ht₁, x₁, v₁, e₁⟩ := hg
  obtain ⟨φ₂, h₂, t₂, ht₂, x₂, v₂, e₂⟩ := hw
  have c₁ : TWM.ιS hϖ hv ≫ cP D.toPre _ χ = cP D.toPre _ χ := comp_cP D.toPre _ χ
  have c₂ : TWM.ιS hϖ hv ≫ (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A) = 1 := MonObj.comp_one _
  have c₃ : TWM.ιS hϖ hv ≫ (cP D.toPre _ χ * m) = cP D.toPre _ χ * g.b := by
    rw [MonObj.comp_mul, c₁, hm]
  obtain rfl : φ₁ = TWM.gtφO hϖ hv m χ := funext fun i => point_ext hϖ hv _ _ ((h₁ i).symm.trans (by
    fin_cases i
    exacts [congrArg (·.left) c₃.symm, congrArg (·.left) c₁.symm, congrArg (·.left) hm.symm,
      congrArg (·.left) c₂.symm]))
  obtain rfl : φ₂ = TWM.lineφO hϖ hv m := funext fun i => point_ext hϖ hv _ _ ((h₂ i).symm.trans (by
    fin_cases i
    exacts [congrArg (·.left) c₂.symm, congrArg (·.left) hm.symm]))
  obtain ⟨u, hu, eu⟩ := exists_ratio_zero hϖ hv hL (fun U _ h => by
      have p := SectionScalarValuation.prod_famB D.toPre m χ k h
      have q : (TWM.TO hϖ hv).hom ≫ eSec D.toPre.P.A = (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A).left := rfl
      have r : m * SectionScalarValuation.cQ D.toPre _ χ = cP D.toPre _ χ * m := mul_comm _ _
      have r' : SectionScalarValuation.cQ D.toPre (TWM.TO hϖ hv) χ = cP D.toPre _ χ := rfl
      rw [r, r'] at p
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [p, Fintype.prod_unique (_ : PUnit → U), q]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, TWM.gtφO, TWM.lineφO, DegPre.gtε, DegPre.lineε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ G₀ t₁) t₂)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hG₀ ht₁) ht₂)
    (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1)
      D.toPre.rig k) (TWM.TO hϖ hv).hom)
    (DVR.pullGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ D.toPre.rig_gen k) _)
  refine ⟨x * x₁ * x₂ * u, fun z J hJ => ?_, ?_⟩
  · have a := eu z J hJ
    rw [val_mul hJ, val_mul hJ, val_pull hJ, Over.w (TWM.ιS hϖ hv)] at a
    have b : val (GeneratorPullback.powGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1)
      D.toPre.rig k) (TF (R := V) F).hom z J = rigV D.toPre (TF (R := V) F).hom z J ^ k := map_pow _ _ _
    rw [b, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val] at a
    rw [hs z J hJ, e₁ z J hJ, e₂ z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination (-(cstH z x * cstH z x₁ * cstH z x₂)) * a
  · rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, hu, v₁, v₂, add_zero, add_assoc,
      WithTop.coe_add]

end

theorem exists_fam_coef_val : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (k : ℕ), 4 ≤ k → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b) l ω, w.IsGen → GtV hϖ hv g l → GenV hϖ hv w ω → ∀ a₀ : D.toPre.X, ∃ s : Fam D.toPre F k, NuGe D Q F v k s 0 ∧ (∀ β, (∀ z : D.toPre.X, β ≠ a₀ + k • z) → ∀ j, (s.s β).f j = 0) ∧ v (coef s g w a₀) = (((Q a₀ : ℚ) / k + l a₀ + ω : ℚ) : WithTop ℚ) := by
  intro hLL hT _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k hk g w l ω hw hg hω a₀
  obtain ⟨m, hm⟩ := TWM.exists_liftO hϖ hv g.b
  obtain ⟨σ, hσ, G₀, hG₀, x, hx, hs⟩ :=
    GlobalTheory.exists_integral_section_unit_at hLL.1 hT V ϖ hϖ D Q hQ F v hv k hk a₀ m
  rw [hm] at hs
  obtain ⟨c, hc, vc⟩ := v_of_isCoef hϖ hv (hg a₀) hω m hm σ G₀ hG₀ x hs
  obtain ⟨s₀, rfl, h₀⟩ := GlobalTheory.FamFree.exists_fam_single hLL.1.globalFns D.tau_bimult (by omega : 1 ≤ k) a₀ σ
  obtain ⟨ζ, hζ⟩ : ∃ ζ : F, v ζ = (((Q a₀ : ℚ) / k : ℚ) : WithTop ℚ) := by
    by_cases h : a₀ = 0
    · exact ⟨1, by rw [h, QForm.Q_zero hϖ D hQ, AddValuation.map_one]; simp⟩
    · have h1 := QForm.Q_pos hϖ D hQ h
      obtain ⟨ζ, -, e⟩ := exists_val_eq hv (r := (Q a₀ : ℚ) / k)
        (div_pos (by exact_mod_cast (by omega : (0 : ℤ) < Q a₀)) (by exact_mod_cast (by omega : 0 < k)))
      exact ⟨ζ, e⟩
  have hsm : Fam.IsSmul D.toPre F ζ s₀ (ζ • s₀) := (isSmul_iff _ _ _).2 rfl
  have hz : ∀ β, (∀ z : D.toPre.X, β ≠ a₀ + k • z) → ∀ j, ((ζ • s₀).s β).f j = 0 := fun β hβ j => by
    rw [hsm β j, h₀ β (fun mu e => hβ mu e.symm) j]; exact mul_zero _
  refine ⟨ζ • s₀, fun χ => ?_, hz, ?_⟩
  · by_cases h : ∃ z : D.toPre.X, χ = a₀ + k • z
    · obtain ⟨z, rfl⟩ := h
      have H := SectionScalarValuation.fe_move hϖ hQ hv k z a₀ (ζ • s₀) (hσ.smul hζ.ge (hsm a₀))
      have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      have e : 0 + (Q a₀ : ℚ) / k + ((k * Q z + QForm.bOf D.toPre Q z a₀ : ℤ) : ℚ) =
          0 + (Q (a₀ + k • z) : ℚ) / k := by
        rw [q_shift hϖ hQ a₀ z k]; push_cast; field_simp; ring
      rwa [e] at H
    · exact vge_of_zero (hz χ fun z e => h ⟨z, e⟩) _
  · have e : ζ • s₀ = (ζ - 1) • s₀ + s₀ := by rw [sub_smul, one_smul, sub_add_cancel]
    rw [e, ((coef_basic V D.toPre F k g).2.2 w hw).2.1, coef_eq hc, show (ζ - 1) * c + c = ζ * c by ring,
      AddValuation.map_mul, hζ, vc, hx, ← WithTop.coe_add, ← WithTop.coe_add, zero_add, add_assoc]

end GlobalTheory.UT.CoefUnit
end
