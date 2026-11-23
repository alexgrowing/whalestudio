import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZeroOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralExpansion

section General

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ₁ : K → (Y' ⟶ X)}
  {ε₁ : K → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K' → (Y ⟶ X)} {ε₂ : K' → ℤ}

theorem sval_of_secScal {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have e := congrArg (gs r z _) (H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e))
  exact ((gs_res r z _ hm _).trans (gs_pull r h z
    (LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k))) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm.2 k) _)).symm.trans
    (e.trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _))))

theorem secIsMul_of_secScal (hL : L.IsLB) {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) {a : R}
    {s s' : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} (hinj : ∀ W : Y.Opens, Function.Injective (h.app W))
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s h 1) (H' : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s' h (scal (h ≫ p) a)) :
    SecIsMul p a s' s := by
  intro j
  refine hinj _ (fn_ext fun y hy => ?_)
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
  have hJ' : Good L y J := hJ
  have hy' : (𝟙 Y' ≫ h) y ∈ LB.wchart L φ₂ j := hy
  have m := hJ'.mem φ₂ (𝟙 Y' ≫ h)
  have e₁ := sval_scal H (𝟙 Y') y hJ'
  have e₂ := sval_of_secScal H' (𝟙 Y') y hJ'
  have e₃ : gs (𝟙 Y' ≫ h) y (LB.wchart L φ₂ j) (Out.resTop _ (scal p a)) = gs (𝟙 Y') y ⊤ (scal (h ≫ p) a) :=
    ((gs_res _ y le_top hy' _).trans (gs_pull _ p y ⊤ trivial _)).trans
      (((gs_pull _ (h ≫ p) y ⊤ trivial _).trans (by rw [Category.assoc])).symm)
  refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
  refine (sec_trans s' _ y hy' m).trans (Eq.trans ?_ ((gs_mul _ y _ hy' _ _).trans
    (congrArg₂ (· * ·) e₃ (sec_trans s _ y hy' m))).symm)
  exact (congrArg _ (e₂.trans (congrArg _ e₁))).trans (mul_left_comm _ _ _)

end General

theorem exists_secIsMul {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {M : LB Y}
    (a : R) (s : LB.Sec M) : ∃ s' : LB.Sec M, SecIsMul p a s' s :=
  ⟨SectionArithmetic.secCMul (V := ⊤) (fun _ => le_top) (scal p a) s, fun _ => rfl⟩

theorem SecIsMul.comp {R : Type} [CommRing R] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of R)} {M : LB Y}
    {a b : R} {s s' s'' : LB.Sec M} (h : SecIsMul p a s'' s') (h' : SecIsMul p b s' s) :
    SecIsMul p (a * b) s'' s := fun j => by
  rw [h j, h' j, ← _root_.mul_assoc]
  simp only [Out.resTop, scal, map_mul]

theorem prB_app_injective {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (W : D.P.A.left.Opens) :
    Function.Injective ((DegPre.prB D (FractionRing V)).left.app W) := by
  have := D.P.isAb.smooth
  have : Flat D.P.A.hom := inferInstance
  have e : (TF (R := V) (FractionRing V)).hom = jK V := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]; rfl
  have h := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  have : IsSchemeTheoreticallyDominant (TF (R := V) (FractionRing V)).hom := by rw [e]; exact h.2
  have : QuasiCompact (TF (R := V) (FractionRing V)).hom := by rw [e]; exact h.1
  exact (pullback.snd (TF (R := V) (FractionRing V)).hom D.P.A.hom).app_injective W

theorem exists_div_of_expandsAt {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G)
    (e k : ℕ) (σ : H0 U.LG.L k) (f f' : ∀ α : D.toPre.X, D.toPre.SecB k α)
    (hf : ∀ α, SecIsMul D.toPre.P.A.hom (ϖ ^ (e + 1)) (f' α) (f α)) (hE : U.ExpandsAt e k σ f') :
    ∃ τ : H0 U.LG.L k, SecIsMul G.hom (ϖ ^ (e + 1)) σ τ := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  refine (GlobalTheory.ThickDiv.main V ϖ hϖ G _ σ e).1 fun j => fn_ext fun y hy => ?_
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f' hE
  choose J hJ using fun ψ : (thickObj V (maximalIdeal V) e G).left ⟶ D.toPre.P.A.left =>
    exists_chart D.toPre.P.isLB (ψ y)
  have hJ' : Good D.toPre.P.L y J := hJ
  have H := (hS _ (𝟙 _) y J hJ').2 jL (Set.mem_iInter.1 hy 0)
  have hc : pGl U e ≫ D.toPre.P.A.hom = (thickObj V (maximalIdeal V) e G).hom ≫
      spMap (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1))) := Over.w (U.gt e).pG
  have h0 : cst (pGl U e ≫ D.toPre.P.A.hom) y (ϖ ^ (e + 1)) = 0 := by
    rw [hc, cst_comp, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.pow_mem_pow ((mem_maximalIdeal _).2 hϖ.not_isUnit) _), cst, map_zero]
    exact gs_zero _ _ _ trivial
  have hF : ∀ α, sval (f' α) (𝟙 _ ≫ pGl U e) y J = 0 := fun α => by
    rw [Category.id_comp]
    exact (secIsMul_gs (hf α) (pGl U e) y _ (hJ'.mem _ _)).trans (by rw [h0, zero_mul])
  simp only [hF, zero_mul, Finset.sum_const_zero, Units.mul_right_eq_zero] at H
  exact (gs_pull (𝟙 _) _ y _ hy _).trans (H.trans (gs_zero (𝟙 _) y _ hy).symm)

theorem main : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (q : ℕ), 1 ≤ q → ∀ (Φ : Fam D.toPre (FractionRing V) q) (f : ∀ α, D.toPre.SecB q α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α) (D.toPre.famφB α) (DegPre.famε q) (f α) (DegPre.prB D.toPre (FractionRing V)).left 1) → ∃ σ : H0 U.LG.L q, ∀ e : ℕ, U.ExpandsAt e q σ f := by
  intro _ V _ _ _ D A G _ _ U q hq Φ f hf
  obtain ⟨s, ⟨r, hr, σ₁, f₁, -, hf₁, hE₁⟩, -⟩ := (U.expand q hq).2 Φ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hr hϖ
  have h₁ : ∀ α, SecIsMul D.toPre.P.A.hom r (f₁ α) (f α) := fun α =>
    secIsMul_of_secScal D.toPre.P.isLB _ (prB_app_injective D.toPre) (hf α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing V))]; exact hf₁ α)
  obtain ⟨σ₂, hσ₂⟩ := exists_secIsMul G.hom (u : V) σ₁
  choose f₂ hf₂ using fun α => exists_secIsMul D.toPre.P.A.hom (u : V) (f₁ α)
  have hE₂ : ∀ e, U.ExpandsAt e q σ₂ f₂ := fun e =>
    expandsAt_secIsMul V _ D A G U.toUnifPre e q u σ₁ σ₂ f₁ f₂ hσ₂ hf₂ (hE₁ e)
  have h₂ : ∀ α, SecIsMul D.toPre.P.A.hom (ϖ ^ n) (f₂ α) (f α) := fun α => by
    rw [← hu, mul_comm]; exact SecIsMul.comp (hf₂ α) (h₁ α)
  obtain ⟨σ, hσ⟩ : ∃ σ : H0 U.LG.L q, SecIsMul G.hom (ϖ ^ n) σ₂ σ := by
    cases n with
    | zero => exact ⟨σ₂, fun j => by rw [pow_zero, scal, map_one, map_one, Out.resTop, map_one, _root_.one_mul]⟩
    | succ m => exact exists_div_of_expandsAt hϖ U.toUnifPre m q σ₂ f f₂ h₂ (hE₂ m)
  exact ⟨σ, fun e => expandsAt_cancel_pow V ϖ hϖ D A G U.toUnifPre e n q σ σ₂ f f₂ hσ h₂ (hE₂ (e + n))⟩

end GlobalTheory.IntegralExpansion
