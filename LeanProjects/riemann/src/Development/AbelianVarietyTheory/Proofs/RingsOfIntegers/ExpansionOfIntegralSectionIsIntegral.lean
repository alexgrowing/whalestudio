import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZeroOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PGAppEqZeroIff
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpInt

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

theorem secScal_sval {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have le : LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have e2 := congrArg (gs r z _) e
  exact ((gs_res r z _ hm _).trans (gs_pull r h z _ (le hm.2) _)).symm.trans (e2.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_res r z le_top hm _) (gs_res r z _ hm _))))

theorem gs_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (q : Z ⟶ Y) (z : Z)
    (a : R) : gs q z ⊤ (scal p a) = cst (q ≫ p) z a := gs_pull q p z ⊤ trivial _

section Mul

variable {R : Type} [CommRing R] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of R)} {L : LB Y}

theorem exists_secIsMul (a : R) (τ : LB.Sec L) : ∃ σ, SecIsMul p a σ τ :=
  ⟨SecOps.secScale (scal p a) τ, fun _ => rfl⟩

theorem secIsMul_trans {a b : R} {ρ σ τ : LB.Sec L} (h₁ : SecIsMul p a ρ σ) (h₂ : SecIsMul p b σ τ) :
    SecIsMul p (a * b) ρ τ := fun j => by
  rw [h₁ j, h₂ j, ← _root_.mul_assoc, scal, scal, scal, map_mul, map_mul]
  exact congrArg (· * τ.f j) (map_mul _ _ _).symm

theorem secIsMul_one (σ : LB.Sec L) : SecIsMul p 1 σ σ := fun j => by
  rw [scal, map_one, map_one, Out.resTop, map_one, _root_.one_mul]

theorem secIsMul_symm {u : Rˣ} {σ τ : LB.Sec L} (h : SecIsMul p (u⁻¹ : Rˣ).val σ τ) : SecIsMul p u.val τ σ := by
  obtain ⟨ρ, hρ⟩ := exists_secIsMul (p := p) u.val σ
  have h₁ := secIsMul_trans hρ h
  rw [Units.mul_inv] at h₁
  exact fun j => ((secIsMul_one (p := p) τ j).trans (h₁ j).symm).trans (hρ j)

end Mul

theorem generic_app_injective {V : Type} [CommRing V] [IsDomain V] (G : Over (Spec (CommRingCat.of V))) [Flat G.hom]
    (W : G.left.Opens) : Function.Injective ((pullback.fst G.hom (jK V)).app W).hom := by
  have : IsDominant (jK V) := isDominant_jK
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK V)
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK V)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback G.hom (jK V)).flip
  exact (pullback.fst G.hom (jK V)).app_injective W

theorem secIsMul_of_generic {V : Type} [CommRing V] [IsDomain V] (G : Over (Spec (CommRingCat.of V))) [Flat G.hom]
    {L : LB G.left} (hL : L.IsLB) (k : ℕ) (σ σ' : H0 L k)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)))) (r : V)
    (h : GeneratorPullback.SecScal L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK V)) 1)
    (h' : GeneratorPullback.SecScal L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ' (pullback.fst G.hom (jK V)) (scal (pullback.snd G.hom (jK V) ≫ jK V) r)) :
    SecIsMul G.hom r σ' σ := by
  obtain ⟨ρ, hρ⟩ := exists_secIsMul (p := G.hom) r σ
  refine fun j => Eq.trans (generic_app_injective G _ (fn_ext fun y hy => ?_)) (hρ j)
  obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : Unit => (𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left)
    (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hy 0)
  have ej : ∀ a : Fin 1, J ((𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left) = j a := fun a => by
    rw [Subsingleton.elim a 0]; exact e ()
  have e₁ := SectionScalarValuation.secScal_sval h (𝟙 _) y hJ
  have e₂ := secScal_sval h' (𝟙 _) y hJ
  rw [← e₁, sval_of σ _ y J j ej, sval_of σ' _ y J j ej, gs_scal, ← pullback.condition, ← Category.assoc] at e₂
  refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) _ y _ hy _).symm)
  exact e₂.trans (secIsMul_gs hρ _ y j hy).symm

theorem isUnit_cst {V : Type} [CommRing V] [IsDomain V] {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of (FractionRing V))) (z : Z) {r : V} (hr : r ≠ 0) : IsUnit (cst (q ≫ jK V) z r) := by
  have h : algebraMap V (FractionRing V) r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hr
  have e : cst (q ≫ jK V) z r = cst q z (algebraMap V (FractionRing V) r) := cst_comp _ _ _ _
  rw [e]
  exact IsUnit.of_mul_eq_one (cst q z (algebraMap V (FractionRing V) r)⁻¹)
    (by rw [← cst_mul, mul_inv_cancel₀ h, cst_one])

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (σ : H0 U.LG.L k) (s : U.SecK k), GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK V)) 1 → ∀ E : Fam D.toPre (FractionRing V) k, U.Expands k s E → ∃ g : ∀ α : D.toPre.X, D.toPre.SecB k α, (∀ e, U.ExpandsAt e k σ g) ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  intro V _ _ _ ϖ hϖ D A G _ _ U k σ s hs E hE
  obtain ⟨r, hr, σ₁, f₁, h₁, hf₁, hE₁⟩ := hE
  have := U.smooth
  have : Flat G.hom := inferInstance
  have hσ₁ : SecIsMul G.hom r σ₁ σ := secIsMul_of_generic G U.LG.isLB k σ σ₁ s r hs h₁
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  obtain ⟨σ₂, hσ₂⟩ := exists_secIsMul (p := G.hom) (u⁻¹ : Vˣ).val σ₁
  choose f₂ hf₂ using fun α => exists_secIsMul (p := D.toPre.P.A.hom) (u⁻¹ : Vˣ).val (f₁ α)
  have hE₂ : ∀ e, U.ExpandsAt e k σ₂ f₂ := fun e =>
    expandsAt_secIsMul V _ D A G U e k _ σ₁ σ₂ f₁ f₂ hσ₂ hf₂ (hE₁ e)
  have hσ : SecIsMul G.hom (ϖ ^ n) σ₂ σ := by
    have := secIsMul_trans hσ₂ hσ₁
    rwa [Units.inv_mul_cancel_left] at this
  have hg : ∀ α, ∃ g : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom (ϖ ^ n) (f₂ α) g := fun α => by
    cases n with
    | zero => exact ⟨f₂ α, by rw [pow_zero]; exact secIsMul_one _⟩
    | succ m =>
      exact (GlobalTheory.ExtDiv.main V ϖ hϖ D A G U m k α (f₂ α)).1 (WeightPf.weightIndep V _ D A G U m k σ₂ f₂
        ((GlobalTheory.ThickDiv.main V ϖ hϖ G _ σ₂ m).2 ⟨σ, hσ⟩) (hE₂ m) α)
  choose g hg using hg
  refine ⟨g, fun e => expandsAt_cancel_pow V ϖ hϖ D A G U e n k σ σ₂ g f₂ hσ hg (hE₂ _), fun α => ?_⟩
  refine SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_
  have e₁ := secScal_sval (hf₁ α) (𝟙 _) y hJ
  have e₂ : sval (f₁ α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J = _ *
      sval (g α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J :=
    secIsMul_gs (secIsMul_trans (secIsMul_symm (hf₂ α)) (hg α)) _ y _ (hJ.mem _ _)
  rw [Category.assoc, Over.w] at e₂
  rw [e₂, gs_scal] at e₁
  refine (IsUnit.mul_right_inj ?_).1 e₁
  have e₃ : 𝟙 _ ≫ (DegPre.BF D.toPre (FractionRing V)).hom =
      ((fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ jFK (R := V) (FractionRing V)) ≫ jK V := by
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
  rw [e₃]
  exact isUnit_cst _ y hr

end GlobalTheory.ExpInt
