import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QkShift

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h

theorem cubN_one_mul (k : ℕ) (b m x : A) :
    cubN θ k 1 (b * m) x * θ m b x ^ k = θ (m ^ k) (b ^ k) x * cubN θ k 1 b x * cubN θ k 1 m x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c₁ := h.coc (b ^ k * m ^ k) m b x
    have c₂ := h.coc (b ^ k) (m ^ k) m x
    have c₃ := h.coc (m ^ k * m) (b ^ k) b x
    rw [mul_comm m b] at c₁
    rw [h.s01 (b ^ k) (m ^ k), h.s01 (b ^ k) (m ^ k * m)] at c₂
    rw [mul_comm (m ^ k * m) (b ^ k), ← _root_.mul_assoc] at c₃
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [mul_pow b m k, pow_succ m, pow_succ b, pow_succ (θ m b x)]
    apply Additive.ofMul.injective
    have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
    have a₀ := E ih; have a₁ := E c₁; have a₂ := E c₂; have a₃ := E c₃
    simp only [ofMul_mul] at a₀ a₁ a₂ a₃ ⊢
    linear_combination (norm := abel) a₀ - a₁ + a₂ + a₃

theorem cub_shift (k : ℕ) (a m b x : A) (Sa Sm Sam Sq τ P w : U) (h₁ : Sam * cubN θ k a m b = Sa * Sm ^ k)
    (h₂ : Sq * θ a b m = Sa * τ) :
    cubN θ k a m (x * b) * (θ a (x * b) m)⁻¹ * (τ * P) *
        (cubN θ k (a * m ^ k) b x * (θ (a * m ^ k) x b)⁻¹ * (Sam * w)) =
      cubN θ k a (b * m) x * (θ a x (b * m))⁻¹ * (Sq * (w * P * Sm ^ k)) := by
  have e₁ := h.N_add k a m x b
  have e₂ := cubN_one_mul h k b m x
  have e₃ := h.N_split k (a * m ^ k) b x
  have e₄ := h.N_split k a (b * m) x
  have e₅ := h.N_split k a m x
  have e₆ := h.coc a (m ^ k) (b ^ k) x
  have e₇ := h.coc x b m a
  rw [h.s12 m x b] at e₁
  rw [← mul_pow, mul_comm m b] at e₆
  rw [h.s12 (x * b), h.s01 (x * b), h.s12 x b a, h.s01 x a b, h.s12 x (b * m), h.s01 x a, h.s12 b m a,
    h.s01 b a m] at e₇
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄; have a₅ := E e₅; have a₆ := E e₆
  have a₇ := E e₇; have c₁ := E h₁; have c₂ := E h₂
  simp only [ofMul_mul, ofMul_inv] at *
  linear_combination (norm := abel) a₁ - a₂ + a₃ - a₄ + a₅ + a₆ - a₇ + c₁ - c₂

end Alg

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem trPt_comp (m m' : TF (R := R) F ⟶ D.P.A) :
    DegPre.trPt D F m ≫ DegPre.trPt D F m' = DegPre.trPt D F (m * m') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, tr_fst, tr_fst]
  · refine Eq.trans ?_ (tr_pr D F (m * m')).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D F m')).trans ?_)
    rw [MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, MonObj.comp_mul, _root_.mul_assoc]

theorem exists_shift_gen (n : ℕ) (g : GtPtF D F) (z : D.X) (b' : TF (R := R) F ⟶ D.P.A)
    (hb : b' = g.b * cP D _ z)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε n))) (hw : w.IsGen) :
    ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b') (DegPre.lineε n)), w₂.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (y : Z) (J), Good D.P.L y J →
        val w₂ r y J = val w r y J *
          (val (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) (r ≫ jFK (R := R) F) y J *
            val (GeneratorPullback.powGen D.P.L _ _ D.rigK n) (r ≫ jFK (R := R) F) y J) * val (g.s z) r y J ^ n := by
  subst hb
  obtain ⟨w₂, h₂, v₂⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F (g.b * cP D _ z)) (ε' := DegPre.lineε n)
    (fun U _ h => by
      have a₁ : ∀ χ, jFK (R := R) F ≫ D.xK χ = (cP D (TF (R := R) F) χ).left := fun χ => (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h (1 : TF (R := R) F ⟶ D.P.A).left ^ (n : ℤ) * h g.b.left ^ (-(n : ℤ)) * _ *
        (h (cP D _ z * g.b).left ^ ((n : ℤ) * -1) * h (cP D _ z).left ^ ((n : ℤ) * 1) * h g.b.left ^ ((n : ℤ) * 1) *
          h (1 : TF (R := R) F ⟶ D.P.A).left ^ ((n : ℤ) * -1)) =
        h (1 : TF (R := R) F ⟶ D.P.A).left ^ (n : ℤ) * h (g.b * cP D _ z).left ^ (-(n : ℤ))
      rw [mul_comm g.b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ w (LB.pullGen D.P.L _ _
      (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) (GeneratorPullback.powGen D.P.L _ _ D.rigK n)) (jFK (R := R) F)))
      (GeneratorPullback.powGen D.P.L _ _ (g.s z) n))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hw (pullGen_isGen _ _ _ _
      (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.psi_gen z) n)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) n)) _)) (powGen_isGen _ _ _ _ (g.isGen z) n))
  refine ⟨w₂, h₂, fun Z r y J hJ => (v₂ Z r y J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (val_mul hJ _ _ _)))) ?_))⟩
  exact map_pow _ _ _

theorem qk_shift : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p q : QkPt D F n) (z : D.X) (h : GtPtF D F), q.y = p.y + n • z → GtPtF.IsIota z h → GtPtF.IsAdd p.g h q.g → ∀ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n)), w.IsGen → ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε n)), w₂.IsGen ∧ ∀ s s' : Fam D F n, PhiRel D F n p w s s' → PhiRel D F n q w₂ s s' := by
  intro hG R _ _ D _ F _ _ n _ p q z h hy hι hadd w hw
  have hh : h.b = cP D _ z := hι.1
  have hb : q.g.b = p.g.b * cP D _ z := hadd.1.trans (congrArg (p.g.b * ·) hh)
  obtain ⟨w₂, h₂, v₂⟩ := exists_shift_gen n p.g z q.g.b hb w hw
  refine ⟨w₂, h₂, fun s t H => ?_⟩
  rw [phiRel_iff hG p w hw] at H
  rw [phiRel_iff hG q w₂ h₂]
  intro α β hβ T ρ y J hJ
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  have e₁ := H (α + n • z) β (by rw [← hβ, hy]; abel) T ρ y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := F) hG n z α
  have e₄ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').1 (s.fe z α u' hu' hc') _
    (ρ ≫ DegPre.trPt D F p.g.b).left y J hJ
  rw [hv' u' hu' hc' _ (ρ ≫ DegPre.trPt D F p.g.b) y J hJ, trF_eq, ← Over.comp_left, Category.assoc, trPt_comp, ← hb,
    Category.assoc, tr_fst] at e₄
  rw [e₁, e₄, _root_.mul_assoc, ← Units.val_mul]
  congr 2
  have t₁ := gt_nsmul (ρ ≫ fst (TF (R := R) F) D.P.A) hJ p.g α z n
  have t₂ := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl
    (val_cub D.cub (ρ ≫ fst (TF (R := R) F) D.P.A) hJ _ _ _))).symm.trans
    ((val_corr hJ (hadd.2 α) (ρ ≫ fst (TF (R := R) F) D.P.A).left).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl ((val_corr hJ (hι.2 α) _).trans (val_pull hJ _ _ _)))))
  have c₁ : (ρ ≫ fst (TF (R := R) F) D.P.A) ≫ DegPre.cF D F α = cP D T α := comp_cP D _ α
  have c₂ : (ρ ≫ fst (TF (R := R) F) D.P.A) ≫ cP D _ z = cP D T z := comp_cP D _ z
  rw [hh, c₁, c₂] at t₂
  have key := cub_shift C n _ _ _ (ρ ≫ DegPre.prB D F) _ _ _ _ _
    (val (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) ((ρ ≫ fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) y J *
      val (GeneratorPullback.powGen D.P.L _ _ D.rigK n) ((ρ ≫ fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) y J)
    (val w (ρ ≫ fst (TF (R := R) F) D.P.A).left y J) t₁ t₂
  have d₁ : (ρ ≫ DegPre.trPt D F p.g.b) ≫ fst _ _ ≫ cP D _ z = cP D T z := by
    rw [← Category.assoc]; exact comp_cP D _ z
  have d₂ : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.prB D F =
      (ρ ≫ DegPre.prB D F) * ((ρ ≫ fst (TF (R := R) F) D.P.A) ≫ p.g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, Category.assoc]
  have d₃ : ρ ≫ fst _ _ ≫ q.g.b = ((ρ ≫ fst (TF (R := R) F) D.P.A) ≫ p.g.b) * cP D T z := by
    rw [← Category.assoc, hb, MonObj.comp_mul, c₂]
  rw [val_famMult _ hJ, val_mul hJ, val_mul hJ, v₂ _ _ y J hJ, uVal, uVal, uVal, d₁, d₂, d₃, cPoint_add, cPoint_nsmul,
    ← Category.assoc ρ]
  exact key

end GlobalTheory.QkShift
