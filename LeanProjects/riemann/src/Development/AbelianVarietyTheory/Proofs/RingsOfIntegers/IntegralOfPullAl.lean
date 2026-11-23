import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullIntegral

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_of_secScal {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ₁ : K → (Y' ⟶ X)}
    {ε₁ : K → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K' → (Y ⟶ X)} {ε₂ : K' → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)} (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c)
    (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have e := congrArg (gs r z _) (H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e))
  exact ((gs_res r z _ hm _).trans (gs_pull r h z
    (LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k))) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm.2 k) _)).symm.trans
    (e.trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top hm _) (gs_res r z _ hm _))))

theorem sec_ext_of_inj {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y' ⟶ Y) (hp : ∀ U, Function.Injective (p.app U).hom) {s s' : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, Good L y J → sval s (𝟙 _ ≫ p) y J = sval s' (𝟙 _ ≫ p) y J) (j : K → L.ι) : s.f j = s'.f j := by
  refine hp _ (fn_ext fun y hy => ?_)
  choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
  have hy' : (𝟙 Y' ≫ p) y ∈ LB.wchart L φ j := hy
  refine (gs_pull (𝟙 _) p y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) p y _ hy _).symm)
  exact (sec_trans s _ y hy' (Good.mem hI φ _)).trans ((congrArg _ (h y I hI)).trans
    (sec_trans s' _ y hy' (Good.mem hI φ _)).symm)

variable {V : Type} [CommRing V] [IsDomain V]

theorem prB_app_injective (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (U : D.P.A.left.Opens) :
    Function.Injective ((DegPre.prB D F).left.app U).hom := by
  have := D.P.isAb.smooth
  have := GC.isDominant_jFR (V := V) F
  have h₁ := IsSchemeTheoreticallyDominant.of_isDominant (DegPre.jFR (R := V) F)
  have hf : Flat D.P.A.hom := inferInstance
  have hq : QuasiCompact (DegPre.jFR (R := V) F) := by
    generalize DegPre.jFR (R := V) F = q
    exact quasiCompact_of_compactSpace q
  have h₂ := IsSchemeTheoreticallyDominant.pullbackSnd (DegPre.jFR (R := V) F) D.P.A.hom
  have h₃ : QuasiCompact (pullback.snd (DegPre.jFR (R := V) F) D.P.A.hom) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback _ _) hq
  exact (pullback.snd (DegPre.jFR (R := V) F) D.P.A.hom).app_injective U

variable [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)} {F : Type} [Field F]
  [Algebra (FractionRing V) F] {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

set_option maxHeartbeats 800000 in

theorem pull_val_eq (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (N k : ℕ) (χ : D.toPre.X)
    (X : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, (oa.onB.act a).left]
      ![((1 * (N + 1) : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (hX : X.IsGen)
    (nX : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ X (eSec D.toPre.P.A))
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (1 * (N + 1 - 1))))
    (u₁ : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (hu₁ : u₁.IsGen)
    (n₁ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u₁ (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k (N + 1)))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N + 1 - 1))) (jFK (R := V) F)))
    {z : (DegPre.BF D.toPre F).left} {J} (hJ : Good D.toPre.P.L z J) :
    val u (𝟙 _) z J = val X (DegPre.prB D.toPre F).left z J ^ k *
      val (LB.pullGen D.toPre.P.L _ _ u₁ (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left)
        (DegPre.prB D.toPre F).left z J := by
  obtain ⟨s, hs, vs⟩ := exists_gen D.toPre.P.isLB (K' := Fin 3)
    (φ' := ![(𝟙 D.toPre.P.A : D.toPre.P.A ⟶ D.toPre.P.A).left, (oa.onB.act a).left,
      (1 : D.toPre.P.A ⟶ D.toPre.P.A).left]) (ε' := ![(N + 1 : ℕ), -1, -(N : ℤ)]) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 2) (K' := PUnit) (U := U) _ (Fin.prod_univ_two _)
        (prod_neg _ _ (ppow _ _ N (c := h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left)
          ((Fintype.prod_unique _).trans (zpow_one _))))).trans ?_
      rw [Fin.prod_univ_three]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, Sum.elim_inl, Matrix.cons_val, Over.id_left,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ X (LB.invGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _
      (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig D.toPre.P.A.hom) N)))
    (mulGen_isGen _ _ _ _ _ _ _ hX (invGen_isGen _ _ _ _
      (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) _)))
  have vs' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → val s r z J =
      val X r z J * (val (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1) D.toPre.rig
        (r ≫ D.toPre.P.A.hom) z J ^ N)⁻¹ :=
    fun Z r z J hJ => by rw [vs Z r z J hJ, val_mul hJ, val_inv, val_pow, val_pull hJ]
  have s₁ : ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.toPre.P.L z J →
      val s (1 : T ⟶ D.toPre.P.A).left z J = 1 := fun T z J hJ => by
    have e := val_corr hJ nX T.hom
    rw [val_pull hJ] at e
    have e' : val X (1 : T ⟶ D.toPre.P.A).left z J = val (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A)
        (ε := fun _ => 1) D.toPre.rig T.hom z J ^ N := e.trans ((val_pow _ _ _ _ _).trans (by simp))
    rw [vs' _ _ z J hJ, Over.w (1 : T ⟶ D.toPre.P.A), e', mul_inv_cancel]
  have H := pull_val hG oa a N k χ u₁ hu₁ n₁ s hs s₁ u hu hc (𝟙 _) hJ
  have e₁ : val D.toPre.rigK ((fst (TF (R := V) F) D.toPre.P.A).left ≫ jFK (R := V) F) z J =
      val (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1) D.toPre.rig
        ((DegPre.prB D.toPre F).left ≫ D.toPre.P.A.hom) z J :=
    (val_pull hJ _ _ _).trans (congrArg (fun q => val _ q z J) ((Category.assoc _ _ _).trans
      ((Over.w (fst (TF (R := V) F) D.toPre.P.A)).trans (Over.w (DegPre.prB D.toPre F)).symm)))
  have e₂ := val_ros u₁ (DegPre.prB D.toPre F) hJ (cP D.toPre _ χ) (𝟙 D.toPre.P.A)
  rw [comp_cP, Category.comp_id] at e₂
  rw [Category.id_comp, Category.id_comp, e₁, vs' _ _ z J hJ, ← e₂] at H
  refine H.trans ?_
  rw [mul_pow, inv_pow, ← pow_mul, mul_comm N k, mul_right_comm, inv_mul_cancel_right]
  rfl

set_option maxHeartbeats 800000 in

theorem integral_of_pullAl (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (N : ℕ) (hN : 0 < N)
    (X : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, (oa.onB.act a).left]
      ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (hX : X.IsGen)
    (nX : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ X (eSec D.toPre.P.A))
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (1 * (N - 1))))
    (u₁ : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (hu₁ : u₁.IsGen)
    (n₁ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u₁ (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (k : ℕ) (s : Fam D.toPre F k) (s'' : Fam D.toPre F (k * N)) (hP : PullAl D F oa a k N s s'') (c : V)
    (f'' : ∀ α : D.toPre.X, D.toPre.SecB (k * N) α) (f : ∀ α : D.toPre.X, D.toPre.SecB k α)
    (hf : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α)
      (DegPre.famε k) (f α) (DegPre.prB D.toPre F).left (scal (DegPre.BF D.toPre F).hom c))
    (hf'' : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε (k * N)) (s''.s α) (D.toPre.famφB α)
      (DegPre.famε (k * N)) (f'' α) (DegPre.prB D.toPre F).left (scal (DegPre.BF D.toPre F).hom c)) :
    (∀ (χ : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      sval (f'' (star a • χ)) r z J = sval (f χ) (r ≫ (oa.onB.act a).left) z J * (val X r z J ^ k *
        val (LB.pullGen D.toPre.P.L _ _ u₁ (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left) r z J).val) ∧
    ∀ β : D.toPre.X, (∀ χ, β ≠ star a • χ) → ∀ j, (f'' β).f j = 0 := by
  obtain ⟨N, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have inj := prB_app_injective D.toPre F
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, hc, hrel⟩ := hP.1 χ
    let g := oa.onB.act a
    let g' := oa.onB.act (star a)
    let x : D.toPre.P.A ⟶ D.toPre.P.A := 𝟙 _
    have cf : cP D.toPre D.toPre.P.A (star a • χ) = cP D.toPre D.toPre.P.A χ ≫ g' := by
      rw [cP, oa.c_lin, ← Category.assoc]; rfl
    have he := mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ hX k)
      (pullGen_isGen _ _ _ _ hu₁ (lift (cP D.toPre D.toPre.P.A χ) x).left)
    obtain ⟨σ, hσ⟩ := exists_sec D.toPre.P.isLB (φ' := D.toPre.famφB (star a • χ)) (ε' := DegPre.famε (k * (N + 1)))
      (fun U _ h => by
        refine (prod_sum₂ (K := Fin 4) (K' := Fin 2 ⊕ Fin 6) (U := U) _ (Fin.prod_univ_four _)
          (prod_sum₂ (K := Fin 2) (K' := Fin 6) (U := U) _ (ppow _ _ k (Fin.prod_univ_two _))
            (prod_ros g' g (cP D.toPre _ χ) x h))).trans ?_
        have a₁ : D.toPre.famφB (star a • χ) 1 = ((cP D.toPre D.toPre.P.A χ ≫ g') * x).left := congrArg (fun q => q.left)
          ((mul_comm x (cP D.toPre D.toPre.P.A (star a • χ))).trans (by rw [cf]))
        have a₂ : D.toPre.famφB (star a • χ) 2 = (cP D.toPre D.toPre.P.A χ ≫ g').left := congrArg (fun q => q.left) cf
        have a₃ : g.left ≫ D.toPre.famφB χ 1 = (cP D.toPre D.toPre.P.A χ * (x ≫ g)).left := congrArg (fun q => q.left)
          ((MonObj.comp_mul g x (cP D.toPre D.toPre.P.A χ)).trans
            (by rw [comp_cP, mul_comm, Category.comp_id, Category.id_comp]))
        have a₄ : g.left ≫ D.toPre.famφB χ 2 = (cP D.toPre D.toPre.P.A χ).left :=
          congrArg (fun q => q.left) (comp_cP D.toPre g χ)
        have a₅ : g.left ≫ D.toPre.famφB χ 3 = (1 : D.toPre.P.A ⟶ D.toPre.P.A).left :=
          congrArg (fun q : D.toPre.P.A ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) g)
        have a₆ : g.left ≫ D.toPre.famφB χ 0 = g.left := Category.comp_id _
        have a₇ : D.toPre.famφB (star a • χ) 0 = x.left := rfl
        have a₈ : D.toPre.famφB (star a • χ) 3 = (1 : D.toPre.P.A ⟶ D.toPre.P.A).left := rfl
        have a₉ : x ≫ g = g := Category.id_comp _
        have a₀ : 𝟙 D.toPre.P.A.left = x.left := rfl
        rw [Fin.prod_univ_four]
        simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₀]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, DegPre.famε, Matrix.cons_val]
        push_cast
        module)
      (pullMulSec (f χ) g.left _ he)
    have hσ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
        sval σ r z J = sval (f χ) (r ≫ (oa.onB.act a).left) z J * (val X r z J ^ k *
          val (LB.pullGen D.toPre.P.L _ _ u₁ (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left)
            r z J).val := fun Z r z J hJ => by
      rw [hσ Z r z J hJ, sval_pullMulSec _ _ _ _ _ z hJ, val_mul hJ, val_pow]; rfl
    have a₁ : (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ (oa.onB.act a).left :=
      congrArg (fun q => q.left) (lift_snd (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))
    have E := sec_ext_of_inj D.toPre.P.isLB _ inj (s := f'' (star a • χ)) (s' := σ) fun y J hJ => by
      have e₁ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ
      have e₂ := sval_of_secScal (hf χ) (aF D F oa a).left y hJ
      have e₃ : gs (aF D F oa a).left y ⊤ (scal (DegPre.BF D.toPre F).hom c) =
          gs (𝟙 _) y ⊤ (scal (DegPre.BF D.toPre F).hom c) :=
        (gs_pull _ (DegPre.BF D.toPre F).hom y ⊤ trivial _).trans (Eq.trans (by rw [Over.w, Category.id_comp])
          (gs_pull _ (DegPre.BF D.toPre F).hom y ⊤ trivial _).symm)
      rw [a₁, e₃] at e₂
      rw [Category.id_comp, pull_val_eq hG oa a N k χ X hX nX u₁ hu₁ n₁ u hu hc hJ] at e₁
      rw [sval_of_secScal (hf'' _) (𝟙 _) y hJ, hσ' _ _ y J hJ, Category.id_comp, e₁, e₂, _root_.mul_assoc]
    intro Z r z J hJ
    exact (congrArg (gs r z _) (E _)).trans (hσ' Z r z J hJ)
  · refine inj _ ((fn_ext fun y hy => ?_).trans (map_zero _).symm)
    choose I hI using fun χ : (DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ y)
    have hy' : (𝟙 _ ≫ (DegPre.prB D.toPre F).left) y ∈ LB.wchart D.toPre.P.L (D.toPre.famφB β) j := hy
    have e : sval (s''.s β) (𝟙 _) y I = 0 :=
      (congrArg (gs _ y _) (hP.2 β hβ _)).trans (gs_zero _ y _ (Good.mem hI _ _))
    have e' := sval_of_secScal (hf'' β) (𝟙 _) y hI
    rw [e, mul_zero] at e'
    refine (gs_pull (𝟙 _) _ y _ hy _).trans ((sec_trans (f'' β) _ y hy' (Good.mem hI _ _)).trans ?_)
    exact (congrArg _ e').trans ((mul_zero _).trans (gs_zero _ y _ hy).symm)

end GlobalTheory.PullIntegral

namespace GlobalTheory.PullIntegral

theorem main : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])), X.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ X (eSec P.D.toPre.P.A)) (GeneratorPullback.powGen P.D.toPre.P.L _ _ P.D.toPre.rig (1 * (N - 1))) → ∀ uR : LB.Gen (LB.LinComb P.D.toPre.P.L (rosatiφ P.D.toPre.P.A (P.oD.onB.act (star a)) (P.oD.onB.act a)) rosatiε), uR.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ uR (zero2 P.D.toPre.P.A)) (LB.oneGen P.D.toPre.P.L) → ∀ (k : ℕ) (F : Fam P.D.toPre (FractionRing V) k) (F'' : Fam P.D.toPre (FractionRing V) (k * N)), PullAl P.D (FractionRing V) P.oD a k N F F'' → ∀ (c : V) (f'' : ∀ α : P.D.toPre.X, P.D.toPre.SecB (k * N) α) (f : ∀ α : P.D.toPre.X, P.D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre (FractionRing V) α) (DegPre.famε (k)) (F.s α) (P.D.toPre.famφB α) (DegPre.famε (k)) (f α) (DegPre.prB P.D.toPre (FractionRing V)).left (scal (DegPre.BF P.D.toPre (FractionRing V)).hom c)) → (∀ α, GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre (FractionRing V) α) (DegPre.famε (k * N)) (F''.s α) (P.D.toPre.famφB α) (DegPre.famε (k * N)) (f'' α) (DegPre.prB P.D.toPre (FractionRing V)).left (scal (DegPre.BF P.D.toPre (FractionRing V)).hom c)) → ((∀ (χ : P.D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ P.D.toPre.P.A.left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → Geo.Tor.sval (f'' (star a • χ)) r z J = Geo.Tor.sval (f χ) (r ≫ (P.oD.onB.act a).left) z J * (Geo.Tor.val X r z J ^ k * Geo.Tor.val (LB.pullGen P.D.toPre.P.L _ _ uR (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c χ) (𝟙 P.D.toPre.P.A)).left) r z J).val) ∧ ∀ β : P.D.toPre.X, (∀ χ, β ≠ star a • χ) → ∀ j, (f'' β).f j = 0) := by
  intro hG V _ _ _ E _ _ _ H t P a N _ hN
  letI := H.starRing
  intro X hX nX uR huR nR k F F'' hP c f'' f hf hf''
  exact integral_of_pullAl hG P.oD a N hN X hX nX uR huR nR k F F'' hP c f'' f hf hf''

end GlobalTheory.PullIntegral
