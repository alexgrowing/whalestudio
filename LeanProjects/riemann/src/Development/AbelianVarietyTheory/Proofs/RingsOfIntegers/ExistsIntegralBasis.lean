import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullbackValuationInvarianceOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfEq

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullbackValuation

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

theorem exists_form {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
    {ϖ : V} (hϖ : Irreducible ϖ) (v : AddValuation F (WithTop ℚ))
    (hinj : Function.Injective (algebraMap V F)) (h0 : ∀ t, 0 ≤ v (algebraMap V F t)) (h1 : 0 < v (algebraMap V F ϖ))
    {n : ℕ} (b : Fin n → F) (hb : ∀ i, 0 ≤ v (b i)) (i₀ : Fin n) (hi₀ : b i₀ = 1) :
    ∃ l : Submodule.span V (Set.range b) →ₗ[V] V, IsUnit (l ⟨b i₀, Submodule.subset_span ⟨i₀, rfl⟩⟩) ∧
      ∀ x : Submodule.span V (Set.range b), 0 < v x.1 → ϖ ∣ l x := by
  have : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).2 hinj
  let N : Submodule V F := Submodule.span V (Set.range b)
  have : Module.Finite V N := Module.Finite.span_of_finite V (Set.finite_range b)
  have nn : ∀ x ∈ N, 0 ≤ v x := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hb i
    | zero => rw [AddValuation.map_zero]; exact le_top
    | add x y _ _ hx hy => exact v.map_le_add hx hy
    | smul r x _ hx => rw [Algebra.smul_def, AddValuation.map_mul]; exact add_nonneg (h0 r) hx
  let P : Submodule V N :=
    { carrier := {x | 0 < v x.1}
      add_mem' := fun hx hy => v.map_lt_add hx hy
      zero_mem' := by show 0 < v 0; rw [AddValuation.map_zero]; exact WithTop.top_pos
      smul_mem' := fun r x hx => by
        show 0 < v (r • x.1)
        rw [Algebra.smul_def, AddValuation.map_mul]; exact lt_of_lt_of_le hx (le_add_of_nonneg_left (h0 r)) }
  have hm : IsLocalRing.maximalIdeal V = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have tor : Module.IsTorsionBySet V (N ⧸ P) (IsLocalRing.maximalIdeal V) := by
    rintro x ⟨r, hr⟩
    obtain ⟨x, rfl⟩ := P.mkQ_surjective x
    rw [hm] at hr
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    refine (Submodule.Quotient.mk_eq_zero P).2 ?_
    show 0 < v ((s * ϖ) • x.1)
    rw [Algebra.smul_def, (algebraMap V F).map_mul, AddValuation.map_mul, AddValuation.map_mul]
    exact lt_of_lt_of_le h1 ((le_add_of_nonneg_left (h0 s)).trans (le_add_of_nonneg_right (nn _ x.2)))
  let _ := tor.module
  have := tor.isScalarTower (S := V)
  let _ := Ideal.Quotient.field (IsLocalRing.maximalIdeal V)
  let one : N := ⟨b i₀, Submodule.subset_span ⟨i₀, rfl⟩⟩
  have hne : P.mkQ one ≠ 0 := fun e => by
    have : 0 < v (b i₀) := (Submodule.Quotient.mk_eq_zero P).1 e
    rw [hi₀, AddValuation.map_one] at this
    exact lt_irrefl _ this
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (V ⧸ IsLocalRing.maximalIdeal V) hne
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (IsLocalRing.maximalIdeal V).mkQ
    ((f.restrictScalars V).comp P.mkQ) (IsLocalRing.maximalIdeal V).mkQ_surjective
  refine ⟨l, ?_, fun x hx => ?_⟩
  · by_contra hn
    exact hf ((LinearMap.congr_fun hl one).symm.trans ((Submodule.Quotient.mk_eq_zero _).2 hn))
  · have e : P.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero P).2 hx
    have : l x ∈ IsLocalRing.maximalIdeal V := (Submodule.Quotient.mk_eq_zero _).1
      ((LinearMap.congr_fun hl x).trans (by show f (P.mkQ x) = 0; rw [e, map_zero]))
    rw [hm] at this
    exact Ideal.mem_span_singleton.1 this

theorem val_reflect {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] (f : V →+* F)
    {ϖ : V} (hϖ : Irreducible ϖ) (v : AddValuation F (WithTop ℚ))
    (hinj : Function.Injective f) (h0 : ∀ t, 0 ≤ v (f t)) (h1 : 0 < v (f ϖ))
    {n m : ℕ} (M : Fin n → Fin m → V) (hM : ∀ t : Fin n → V, (∀ l, ϖ ∣ ∑ i, t i * M i l) → ∀ i, ϖ ∣ t i)
    (a : Fin n → F) (q : WithTop ℚ) (ha : ∀ l, q ≤ v (∑ i, a i * f (M i l))) (i : Fin n) : q ≤ v (a i) := by
  classical
  let _ : Algebra V F := f.toAlgebra
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun i => v (a i)) ⟨i, Finset.mem_univ _⟩
  refine le_trans ?_ (hmin i (Finset.mem_univ _))
  by_contra hlt
  rw [not_le] at hlt
  have hc : a i₀ ≠ 0 := fun h => by rw [h, AddValuation.map_zero] at hlt; exact not_top_lt hlt
  have hct : v (a i₀) ≠ ⊤ := ne_top_of_lt hlt
  have e₀ : ∀ x, v x = v (a i₀) + v ((a i₀)⁻¹ * x) := fun x => by
    rw [← AddValuation.map_mul, mul_inv_cancel_left₀ hc]
  have hb : ∀ j, 0 ≤ v ((a i₀)⁻¹ * a j) := fun j => by
    have := hmin j (Finset.mem_univ _)
    rw [e₀ (a j)] at this
    exact (WithTop.add_le_add_iff_left hct).1 ((add_zero _).le.trans this)
  obtain ⟨l, hl₁, hl₂⟩ := exists_form hϖ v hinj h0 h1 (fun j => (a i₀)⁻¹ * a j) hb i₀ (inv_mul_cancel₀ hc)
  have := hM (fun j => l ⟨(a i₀)⁻¹ * a j, Submodule.subset_span ⟨j, rfl⟩⟩) (fun k => by
    have e : ∑ j, l ⟨(a i₀)⁻¹ * a j, Submodule.subset_span ⟨j, rfl⟩⟩ * M j k =
        l (∑ j, M j k • ⟨(a i₀)⁻¹ * a j, Submodule.subset_span ⟨j, rfl⟩⟩) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, _root_.mul_comm]
    rw [e]
    refine hl₂ _ ?_
    have e' : ((∑ j, M j k • (⟨(a i₀)⁻¹ * a j, Submodule.subset_span ⟨j, rfl⟩⟩ :
        Submodule.span V (Set.range fun j => (a i₀)⁻¹ * a j)) : Submodule.span V (Set.range fun j => (a i₀)⁻¹ * a j)) : F) =
        (a i₀)⁻¹ * ∑ j, a j * f (M j k) := by
      rw [Submodule.coe_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        show f (M j k) * ((a i₀)⁻¹ * a j) = _
        ring
    rw [e']
    by_contra hn
    exact absurd ((hlt.trans_le (ha k)).trans_le ((e₀ _).le.trans (add_le_of_nonpos_right (not_lt.1 hn)))) (lt_irrefl _)) i₀
  exact hϖ.not_isUnit (isUnit_of_dvd_unit this hl₁)

def secComb {X : Scheme.{0}} {L : LB X} {n : ℕ} (c : Fin n → Γ(X, ⊤)) (t : Fin n → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (c i) * (t i).f j
  compat := fun i j => by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (SecOps.secScale (c l) (t l)).compat i j

theorem cst_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {Z : Scheme.{0}} (q : Z ⟶ Sp B) (z : Z) (a : A) :
    cst (q ≫ spMap f) z a = cst q z (f a) := by
  rw [cst, ← GlobalTheory.IntegralCoord.gs_appTop, GlobalTheory.IntegralCoord.specMap_appTop, Iso.inv_hom_id_apply, cst]

theorem cst_sum {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) {n : ℕ} (a : Fin n → V) :
    cst q z (∑ i, a i) = ∑ i, cst q z (a i) := by
  rw [cst, map_sum, gs_sum q z ⊤ trivial]; rfl

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

abbrev toF (V : Type) [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F] : V →+* F :=
  (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))

omit [IsDiscreteValuationRing V] in
theorem hom_TF (F : Type) [Field F] [Algebra (FractionRing V) F] :
    jFK (R := V) F ≫ jK V = Spec.map (CommRingCat.ofHom (toF V F)) := by
  show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

omit [IsDiscreteValuationRing V] in
theorem cst_prB (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (t : V) :
    cst ((r ≫ (DegPre.prB D F).left) ≫ D.P.A.hom) z t = cst (r ≫ (fst (TF (R := V) F) D.P.A).left) z (toF V F t) := by
  have e : (DegPre.prB D F).left ≫ D.P.A.hom = (fst (TF (R := V) F) D.P.A).left ≫ spMap (toF V F) := by
    rw [Over.w, spMap, ← hom_TF]
    exact (Over.w (fst (TF (R := V) F) D.P.A)).symm
  rw [Category.assoc, e, ← Category.assoc, cst_spMap]

omit [IsDiscreteValuationRing V] in
theorem gs_gF (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (x : F) :
    gs r z ⊤ (gF D F x) = cst (r ≫ (fst (TF (R := V) F) D.P.A).left) z x :=
  GlobalTheory.IntegralCoord.gs_appTop r (fst (TF (R := V) F) D.P.A).left z _

theorem exists_integral_basis (hT : TwistBaseChangeStatement) (D : DegPre V) (F : Type) [Field F]
    [Algebra (FractionRing V) F] (k : ℕ) (hk : 1 ≤ k) (α : D.X) :
    ∃ (m : ℕ) (b₀ : Fin m → D.SecB k α) (b : Fin m → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))),
      (∀ i (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) J, Good D.P.L z J →
        sval (b i) r z J = sval (b₀ i) (r ≫ (DegPre.prB D F).left) z J) ∧
      (∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)), ∃ a : Fin m → F,
        ∀ j, s.f j = ∑ i, DegPre.constBF D F (a i) _ * (b i).f j) ∧
      (∀ a a' : Fin m → F, (∀ (y : (DegPre.BF D F).left) J, Good D.P.L y J →
        ∑ i, cst (fst (TF (R := V) F) D.P.A).left y (a i) * sval (b₀ i) (DegPre.prB D F).left y J =
          ∑ i, cst (fst (TF (R := V) F) D.P.A).left y (a' i) * sval (b₀ i) (DegPre.prB D F).left y J) → a = a') ∧
      ∀ σ : D.SecB k α, ∃ c : Fin m → V, ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) J, Good D.P.L z J →
        sval σ r z J = ∑ i, cst (r ≫ D.P.A.hom) z (c i) * sval (b₀ i) r z J := by
  classical
  have hL := D.P.isLB
  obtain ⟨m, b₀, -, hb₀⟩ := hT V D k hk α
  have hb₁ : ∀ (R' : Type) [CommRing R'] (f : V →+* R') (t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of V)),
      t = Spec.map (CommRingCat.ofHom f) → IsSecBasis (T := Over.mk t) (A := D.P.A) _
        (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k) (b₀ i) (snd (Over.mk t) D.P.A).left) := by
    intro R' _ f t ht
    subst ht
    exact hb₀ R' f _ (fun i j => rfl)
  obtain ⟨b, hb, hbv⟩ := GlobalTheory.IntegralCoord.exists_basis_of_eq b₀ (hb₁ F (toF V F) _ (hom_TF F)) (DegPre.famφ D F α)
    (funext fun i => GC.famφ_eq D F α i)
  have huniq : ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)),
      ∃! a : Fin m → F, ∀ j, s.f j = ∑ i, DegPre.constBF D F (a i) _ * (b i).f j := by
    intro s
    obtain ⟨r, hr, hu⟩ := hb s
    have e : ∀ i, (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (r i)) = r i := fun i => Iso.hom_inv_id_apply _ _
    refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (r i), fun j => ?_, fun a ha => ?_⟩
    · refine (hr j).trans (Finset.sum_congr rfl fun i _ => ?_)
      simp only [DegPre.constBF, e]
    · have := hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i)) ha
      funext i
      rw [← this]
      exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of F)) (a i)).symm
  refine ⟨m, b₀, b, hbv, fun s => (huniq s).exists, fun a a' h => ?_, fun σ => ?_⟩
  · refine (huniq (secComb (fun i => gF D F (a i)) b)).unique (fun j => rfl) ?_
    refine GlobalTheory.IntegralCoord.lin_of_sval hL (fun i => gF D F (a' i)) b fun y J hJ => ?_
    rw [sval_lin (s := secComb (fun i => gF D F (a i)) b) (fun i => gF D F (a i)) b (fun j => rfl) (𝟙 _) y hJ]
    simp only [gs_gF, hbv _ _ _ y J hJ, Category.id_comp]
    exact h y J hJ
  · have hid := hb₁ V (RingHom.id V) (𝟙 _) (by simp)
    let T₀ : Over (Spec (CommRingCat.of V)) := Over.mk (𝟙 _)
    let g : D.P.A ⟶ T₀ ⊗ D.P.A := lift (Over.homMk D.P.A.hom (Category.comp_id _)) (𝟙 _)
    have g2 : g.left ≫ (snd T₀ D.P.A).left = 𝟙 _ := by
      rw [← Over.comp_left, lift_snd]; rfl
    have g1 : g.left ≫ (fst T₀ D.P.A).left = D.P.A.hom := by
      rw [← Over.comp_left, lift_fst]; rfl
    obtain ⟨c, hc, -⟩ := hid (DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k) σ (snd T₀ D.P.A).left)
    refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (c i), fun Z r z J hJ => ?_⟩
    have H := sval_lin (fun i => (fst T₀ D.P.A).left.appTop.hom (c i)) _ hc (r ≫ g.left) z hJ
    have g2' : (r ≫ g.left) ≫ (snd T₀ D.P.A).left = r := by rw [Category.assoc, g2, Category.comp_id]
    rw [sval_pullSec _ _ _ _ _ z hJ, g2'] at H
    rw [H]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sval_pullSec _ _ _ _ _ z hJ]
    refine congrArg₂ (· * ·) ?_ (congrArg (fun q => sval (b₀ i) q z J) g2')
    rw [GlobalTheory.IntegralCoord.gs_appTop, Category.assoc, g1, cst, Iso.hom_inv_id_apply]

theorem div_of_mulA (hL : Laws) (D : DegPre V) {ϖ : V} (hϖ : ϖ ≠ 0) (N : ℕ) (hN : 1 ≤ N) {k : ℕ} {χ : D.X}
    (σ : D.SecB k χ) (h : ∀ (x : D.P.A.left) J, Good D.P.L x J →
      cst D.P.A.hom x ϖ ∣ sval σ (mulA D.P.A N).left x J) :
    ∃ σ' : D.SecB k χ, ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) J, Good D.P.L z J →
      sval σ r z J = cst (r ≫ D.P.A.hom) z ϖ * sval σ' r z J := by
  have := D.P.isAb.smooth
  obtain ⟨-, hflat, hsurj, -⟩ := hL.mulN _ D.P N hN
  obtain ⟨σ', hσ'⟩ := exists_div_sec D.P.A.hom hϖ σ fun j y hy => by
    obtain ⟨x, rfl⟩ := (mulA D.P.A N).left.surjective y
    apply dvd_descend (mulA D.P.A N).left x
    choose J hJ using fun ψ : D.P.A.left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ x)
    rw [H1.cst_stalkMap, Over.w]
    exact (congrArg (cst D.P.A.hom x ϖ ∣ ·) ((gs_stalkMap _ x _ hy _).symm.trans
      (sec_trans σ (mulA D.P.A N).left x hy (Good.mem hJ _ _)))).mpr ((h x J hJ).mul_left _)
  refine ⟨σ', fun Z r z J hJ => ?_⟩
  have hm := hJ.mem (D.famφB χ) r
  exact (congrArg (gs r z _) (hσ' _)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_constFn D.P.A.hom _ r z hm ϖ) rfl))

theorem vge_reflect (hL : Laws) (hT : TwistBaseChangeStatement) {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v)
    {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O)
    (hw : TraceFormTwistIso D.toPre oa w0) (a : O) (N : ℕ) (hN : 1 ≤ N) (haa : a * star a = (N : O)) (haa' : star a * a = (N : O))
    (k : ℕ) (hk : 1 ≤ k) (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)) (hP : PullAl D F oa a k N s s')
    (χ : D.toPre.X) (q : ℚ) (hq : VGe D F v (k * N) (star a • χ) (s'.s (star a • χ)) q) :
    VGe D F v k χ (s.s χ) q := by
  classical
  have hLB := D.toPre.P.isLB
  obtain ⟨u, hu, hcu, hrel⟩ := hP.1 χ
  obtain ⟨m, ψ, δ, e, he, hF, ve⟩ := pullGen_one hL.globalFns D F oa w0 hw a N hN haa' k χ u hu hcu
  obtain ⟨n₁, b₀, b, hbv, hbs, hbu, hbV⟩ := exists_integral_basis hT D.toPre F k hk χ
  obtain ⟨n₂, c₀, -, -, -, hcu, hcV⟩ := exists_integral_basis hT D.toPre F (k * N) (Nat.mul_pos hk hN) (star a • χ)
  obtain ⟨x, hx⟩ := hbs (s.s χ)
  obtain ⟨n, a₀, τ, τF, hτ, hva, hsum⟩ := hq

  have hM : ∀ i, ∃ M : Fin n₂ → V, ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) J, Good D.toPre.P.L z J →
      sval (b₀ i) (r ≫ (oa.onB.act a).left) z J * (val e r z J).val =
        ∑ l, cst (r ≫ D.toPre.P.A.hom) z (M l) * sval (c₀ l) r z J := fun i => by
    obtain ⟨β, hβ⟩ := exists_sec hLB hF (pullMulSec (b₀ i) (oa.onB.act a).left e he)
    obtain ⟨M, hM⟩ := hcV β
    exact ⟨M, fun Z r z J hJ => ((hβ Z r z J hJ).trans (sval_pullMulSec _ _ _ he r z hJ)).symm.trans (hM Z r z J hJ)⟩
  choose M hM using hM
  choose P hP' using fun i => hcV (τ i)
  have a₁ : (aF D F oa a).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left :=
    congrArg (fun q => q.left) (lift_fst (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))
  have a₂ : (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ (oa.onB.act a).left :=
    congrArg (fun q => q.left) (lift_snd (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))
  have cp : ∀ (y : (DegPre.BF D.toPre F).left) (t : V),
      cst ((DegPre.prB D.toPre F).left ≫ D.toPre.P.A.hom) y t =
        cst (fst (TF (R := V) F) D.toPre.P.A).left y (toF V F t) := fun y t => by
    have := cst_prB D.toPre F (𝟙 _) y t
    rwa [Category.id_comp, Category.id_comp] at this

  have coord : (fun l => ∑ i, x i * toF V F (M i l)) = fun l => ∑ i, a₀ i * toF V F (P i l) := by
    refine hcu _ _ fun y J hJ => ?_
    have e₁ := (secRel_iff hLB _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ
    have e₂ := sval_lin (fun i => gF D.toPre F (x i)) b hx (𝟙 _ ≫ (aF D F oa a).left) y hJ
    have e₃ := sval_lin (fun i => gF D.toPre F (a₀ i)) τF hsum (𝟙 _) y hJ
    rw [e₂, e₃, ve _ _ y J hJ, Finset.sum_mul] at e₁
    simp only [gs_gF, hbv _ _ _ y J hJ, H1.sval_scal (hτ _) _ y hJ, Category.id_comp, a₁, a₂, _root_.mul_assoc,
      hM _ _ _ y J hJ, hP' _ _ _ y J hJ, cp] at e₁
    simp only [cst_sum, H1.cst_mul, Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc] at e₁ ⊢
    rw [Finset.sum_comm, ← e₁, Finset.sum_comm]
  have hinj : Function.Injective (toF V F) := (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _)
  have h0 : ∀ t, 0 ≤ v (toF V F t) := GC.v_alg_nonneg hϖ hv
  have h1 : 0 < v (toF V F ϖ) := by
    have := hv (algebraMap V (FractionRing V) ϖ) 1 ⟨1, by simp⟩
    exact lt_of_lt_of_eq (by exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)) this.symm
  have hm : oa.onB.act (star a) ≫ oa.onB.act a = mulA D.toPre.P.A N := by
    rw [← oa.onB.map_mul, haa, ← _root_.mul_one (N : O), act_nsmul, oa.onB.map_one]
  refine ⟨n₁, x, b₀, b, fun i => secScal_of_sval hLB fun y J hJ => (hbv i _ (𝟙 _) y J hJ).symm, ?_, hx⟩
  refine val_reflect (toF V F) hϖ v hinj h0 h1 M (fun t ht => ?_) x _ (fun l => ?_)
  · let σ : D.toPre.SecB k χ :=
      secComb (fun i => D.toPre.P.A.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom (t i))) b₀
    have hσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) J, Good D.toPre.P.L z J →
        sval σ r z J = ∑ i, cst (r ≫ D.toPre.P.A.hom) z (t i) * sval (b₀ i) r z J := fun Z r z J hJ =>
      (sval_lin (s := σ) _ b₀ (fun j => rfl) r z hJ).trans (Finset.sum_congr rfl fun i _ =>
        congrArg₂ (· * ·) (GlobalTheory.IntegralCoord.gs_appTop r D.toPre.P.A.hom z _) rfl)
    obtain ⟨σ', hσ'⟩ := div_of_mulA hL D.toPre hϖ.ne_zero N hN σ fun y J hJ => by
      rw [← Units.dvd_mul_right (u := val e (oa.onB.act (star a)).left y J), hσ _ _ y J hJ, ← hm, Over.comp_left,
        Finset.sum_mul]
      simp only [_root_.mul_assoc, hM _ _ _ y J hJ, Category.assoc, Over.w, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.dvd_sum fun l _ => ?_
      obtain ⟨w, hw⟩ := ht l
      simp only [← _root_.mul_assoc, ← H1.cst_mul]
      rw [← Finset.sum_mul, ← cst_sum, hw, H1.cst_mul, _root_.mul_assoc]
      exact dvd_mul_right _ _
    obtain ⟨w, hw'⟩ := hbV σ'
    have key := hbu (fun i => toF V F (t i)) (fun i => toF V F (ϖ * w i)) fun y J hJ => by
      have e₁ := hσ' _ (DegPre.prB D.toPre F).left y J hJ
      rw [hσ _ _ y J hJ, hw' _ _ y J hJ, Finset.mul_sum] at e₁
      simp only [← _root_.mul_assoc, ← H1.cst_mul, cp] at e₁
      simpa only [map_mul] using e₁
    exact fun i => ⟨w i, hinj (congrFun key i)⟩
  · rw [congrFun coord l]
    refine v.map_le_sum fun i _ => ?_
    rw [AddValuation.map_mul]
    calc ((q : ℚ) : WithTop ℚ) = ((q : ℚ) : WithTop ℚ) + 0 := (add_zero _).symm
      _ ≤ _ := add_le_add (hva i) (h0 _)

theorem main : Laws → TwistBaseChangeStatement → PullbackValuationInvariance := by
  intro hL hT V _ _ _ ϖ hϖ D Q hQ F _ _ v hv O _ _ _ oa w0 hw a N hN haa haa' k hk s s' hP r
  refine ⟨pullback_valuation_forward_of (pullGen_of hL.globalFns) (QuadraticAlgebraValuation.qAl_of hL) V ϖ hϖ D Q hQ F v hv O oa w0 hw a N hN haa haa' k hk
    s s' hP r, fun h χ => ?_⟩
  have hQa : (Q (star a • χ) : ℚ) / ((k * N : ℕ) : ℚ) = (Q χ : ℚ) / k := by
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hN)
    rw [QuadraticAlgebraValuation.qAl_of hL V ϖ hϖ D Q hQ O oa a N haa haa' χ]
    push_cast
    field_simp
  have h₁ := h (star a • χ)
  rw [hQa] at h₁
  exact vge_reflect hL hT hϖ D F v hv oa w0 hw a N hN haa haa' k hk s s' hP χ _ h₁

end GlobalTheory.PullbackValuation
