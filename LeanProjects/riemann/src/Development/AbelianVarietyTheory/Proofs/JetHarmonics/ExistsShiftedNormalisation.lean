import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValPowGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_shifted_normalisation (k : ℕ) (g : GtPtF D F) (z : D.X) (b' : TF (R := R) F ⟶ D.P.A)
    (hb : b' = g.b * cP D _ z)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (hw : w.IsGen) :
    ∃ w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b') (DegPre.lineε k)), w'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (x : Z) (J), Good D.P.L x J →
        val w' r x J = val (g.s z) r x J ^ k * (val (D.psi z) (r ≫ jFK (R := R) F) x J ^ k *
          val D.rigK (r ≫ jFK (R := R) F) x J ^ k) * val w r x J := by
  obtain ⟨w', hw', hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b') (ε' := DegPre.lineε k) (fun U _ h => by
      have a₁ : ∀ χ, jFK (R := R) F ≫ D.xK χ = (cP D (TF (R := R) F) χ).left := fun χ => (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two, hb, mul_comm g.b]
      show h (cP D _ z * g.b).left ^ ((k : ℤ) * (-1 : ℤ)) * h (cP D _ z).left ^ ((k : ℤ) * (1 : ℤ)) *
        h g.b.left ^ ((k : ℤ) * (1 : ℤ)) * h (1 : TF (R := R) F ⟶ D.P.A).left ^ ((k : ℤ) * (-1 : ℤ)) * _ *
        (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ))) =
        h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h (cP D _ z * g.b).left ^ (-(k : ℤ))
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (g.s z) k)
      (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi z) k)
        (GeneratorPullback.powGen D.P.L _ _ D.rigK k)) (jFK (R := R) F))) w)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (g.isGen z) k)
      (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.psi_gen z) k)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) k)) _)) hw)
  refine ⟨w', hw', fun Z r x J hJ => ?_⟩
  refine (hv Z r x J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (UUA.val_powGen' _ _ _ _ _) ((val_pull hJ _ _ _).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (UUA.val_powGen' _ _ _ _ _) (UUA.val_powGen' _ _ _ _ _)))))) rfl))

theorem phi_value_shift (hG : GlobalFnsSt) (k : ℕ) (g h g' : GtPtF D F) (z : D.X)
    (hι : GtPtF.IsIota z h) (ha : GtPtF.IsAdd g h g')
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k)))
    (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g'.b) (DegPre.lineε k)))
    (hw' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (x : Z) (J), Good D.P.L x J →
        val w' r x J = val (g.s z) r x J ^ k * (val (D.psi z) (r ≫ jFK (R := R) F) x J ^ k *
          val D.rigK (r ≫ jFK (R := R) F) x J ^ k) * val w r x J)
    (s : Fam D F k) (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (x : T.left) (J)
    (hJ : Good D.P.L x J) :
    sval (s.s (α + k • z)) (ρ ≫ DegPre.trPt D F g.b).left x J *
      (uVal D F k (α + k • z) g.b ρ x J *
        val (LB.mulGen D.P.L _ _ _ _ (g.s (α + k • z)) w) (ρ ≫ fst _ _).left x J).val =
    sval (s.s α) (ρ ≫ DegPre.trPt D F g'.b).left x J *
      (uVal D F k α g'.b ρ x J * val (LB.mulGen D.P.L _ _ _ _ (g'.s α) w') (ρ ≫ fst _ _).left x J).val := by
  have C : IsCub (th D x J) := isCub_cubV D.cub hJ
  have hh : h.b = cP D _ z := hι.1
  have hb : g'.b = g.b * cP D _ z := ha.1.trans (congrArg (g.b * ·) hh)
  obtain ⟨⟨u, hu, hc⟩, hv'⟩ := gen_fe (D := D) (F := F) hG k z α
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe z α u hu hc) _ (ρ ≫ DegPre.trPt D F g.b).left x J hJ
  have htr : (ρ ≫ DegPre.trPt D F g.b) ≫ DegPre.trPt D F (cP D _ z) = ρ ≫ DegPre.trPt D F g'.b := by
    rw [hb, Category.assoc]
    refine congrArg (ρ ≫ ·) ?_
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, tr_fst, tr_fst]
    · have e₁ : (DegPre.trPt D F g.b ≫ DegPre.trPt D F (cP D _ z)) ≫ DegPre.prB D F =
          DegPre.prB D F * (fst _ _ ≫ g.b) * (fst _ _ ≫ cP D _ z) := by
        rw [Category.assoc, tr_pr, MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst]
      have e₂ : DegPre.trPt D F (g.b * cP D _ z) ≫ DegPre.prB D F =
          DegPre.prB D F * (fst _ _ ≫ g.b) * (fst _ _ ≫ cP D _ z) := by
        rw [tr_pr, MonObj.comp_mul, _root_.mul_assoc]
      exact e₁.trans e₂.symm
  have hf : (ρ ≫ DegPre.trPt D F g.b) ≫ fst (TF (R := R) F) D.P.A = ρ ≫ fst _ _ := by
    rw [Category.assoc, tr_fst]
  have hp : (ρ ≫ DegPre.trPt D F g.b) ≫ DegPre.prB D F = (ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, Category.assoc]
  rw [hv' u hu hc _ (ρ ≫ DegPre.trPt D F g.b) x J hJ, trF_eq, ← Over.comp_left, htr, hf] at e
  rw [e, _root_.mul_assoc, ← Units.val_mul]
  refine congrArg₂ (· * ·) rfl (congrArg Units.val ?_)
  have u1 : uVal D F k α (cP D _ z) (ρ ≫ DegPre.trPt D F g.b) x J =
      hv (th D x J) k (cP D T α) (cP D T z) ((ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ g.b)) := by
    rw [uVal, hp, ← Category.assoc (ρ ≫ DegPre.trPt D F g.b), hf, comp_cP]; rfl
  have u2 : uVal D F k (α + k • z) g.b ρ x J =
      hv (th D x J) k (cP D T α * cP D T z ^ k) ((ρ ≫ fst _ _) ≫ g.b) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, cPoint_add, cPoint_nsmul, ← Category.assoc ρ]; rfl
  have u3 : uVal D F k α g'.b ρ x J =
      hv (th D x J) k (cP D T α) (cP D T z * ((ρ ≫ fst _ _) ≫ g.b)) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, ← Category.assoc ρ, hb, MonObj.comp_mul, comp_cP, mul_comm (cP D T z)]; rfl
  have hvc := UUA.hv_comp C k (cP D T α) (cP D T z) ((ρ ≫ fst _ _) ≫ g.b) (ρ ≫ DegPre.prB D F)
  have h8 : hv (th D x J) k (cP D T α) (cP D T z) ((ρ ≫ fst _ _) ≫ g.b) =
      cubN (th D x J) k (cP D T α) (cP D T z) ((ρ ≫ fst _ _) ≫ g.b) *
        (th D x J (cP D T α) ((ρ ≫ fst _ _) ≫ g.b) (cP D T z))⁻¹ := rfl
  have t1 := gt_nsmul (ρ ≫ fst _ _) hJ g α z k
  have t2 : val (g'.s α) (ρ ≫ fst _ _).left x J * th D x J (cP D T α) ((ρ ≫ fst _ _) ≫ g.b) (cP D T z) =
      val (g.s α) (ρ ≫ fst _ _).left x J * val (D.tau z α) ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) x J := by
    have e' := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub (ρ ≫ fst _ _) hJ _ _ _))).symm.trans
      ((val_corr hJ (ha.2 α) (ρ ≫ fst _ _).left).trans (val_mul hJ _ _ _))
    have e₂ : (ρ ≫ fst _ _) ≫ DegPre.cF D F α = cP D T α := comp_cP D _ α
    have e₃ : (ρ ≫ fst _ _) ≫ h.b = cP D T z := by rw [hh, comp_cP]
    rw [e₂, e₃] at e'
    exact e'.trans (congrArg₂ (· * ·) rfl ((val_corr hJ (hι.2 α) _).trans (val_pull hJ _ _ _)))
  rw [u1, u2, u3, val_famMult _ hJ, UUA.val_powGen', UUA.val_powGen', val_mul hJ, val_mul hJ, hw' _ _ x J hJ]
  apply Additive.ofMul.injective
  have a1 := congrArg Additive.ofMul hvc
  have a2 := congrArg Additive.ofMul h8
  have a3 := congrArg Additive.ofMul t1
  have a4 := congrArg Additive.ofMul t2
  simp only [ofMul_mul, ofMul_inv] at a1 a2 a3 a4 ⊢
  linear_combination (norm := abel) a1 + a2 + a3 - a4

end

theorem phiRel_of_qkEquiv : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, QkPt.Equiv D.toPre F p p' → ∀ w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k)), w.IsGen → ∃ w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p'.g.b) (DegPre.lineε k)), w'.IsGen ∧ ∀ s t : Fam D.toPre F k, PhiRel D.toPre F k p w s t ↔ PhiRel D.toPre F k p' w' s t := by
  intro hL V _ _ _ D F _ _ k _ p p' ⟨z, hy, h, hι, ha⟩ w hw
  have hG := hL.globalFns
  obtain ⟨w', hw', hv⟩ := exists_shifted_normalisation k p.g z p'.g.b
    (ha.1.trans (congrArg (p.g.b * ·) hι.1)) w hw
  refine ⟨w', hw', fun s t => ?_⟩
  rw [phiRel_iff hG p w hw, phiRel_iff hG p' w' hw']
  constructor
  · intro H α β hβ T ρ x J hJ
    rw [← phi_value_shift hG k p.g h p'.g z hι ha w w' hv s α T ρ x J hJ]
    exact H (α + k • z) β (by rw [← hβ, hy]; abel) T ρ x J hJ
  · intro H α β hβ T ρ x J hJ
    obtain ⟨α, rfl⟩ : ∃ α', α' + k • z = α := ⟨α - k • z, sub_add_cancel _ _⟩
    rw [phi_value_shift hG k p.g h p'.g z hι ha w w' hv s α T ρ x J hJ]
    exact H α β (by rw [← hβ, hy]; abel) T ρ x J hJ

end GlobalTheory
