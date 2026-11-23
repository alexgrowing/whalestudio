import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section
namespace GlobalTheory.USep.TauPullB

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] {ρ : V →+* V₁} {Q : DegPre V} {D : DegPre V₁}

theorem exists_moved (p : IsPullDeg ρ Q D) (τ₀ : GlobalTheory.UChart.Gens Q) (hτ : ∀ a b, (τ₀ a b).IsGen) :
    ∃ τ₁ : GlobalTheory.UChart.Gens D, (∀ a b, (τ₁ a b).IsGen) ∧ ∀ (a b : D.X) (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z)
      (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (J' : (Z ⟶ D.P.A.left) → D.P.L.ι), Good Q.P.L z J → Good D.P.L z J' →
      val (τ₀ (p.xe a) (p.xe b)) (r ≫ spMap ρ) z J =
        (ArcPull.om p.w z J J' (r ≫ (D.c (a + b)).left))⁻¹ * ArcPull.om p.w z J J' (r ≫ (D.c a).left) *
          ArcPull.om p.w z J J' (r ≫ (D.c b).left) * (ArcPull.om p.w z J J' (r ≫ (D.c 0).left))⁻¹ *
          val (τ₁ a b) r z J' := by
  have key : ∀ a b : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(D.c (a + b)).left, (D.c a).left, (D.c b).left, (D.c 0).left] ![-1, 1, 1, -1]), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J J', Good Q.P.L z J → Good D.P.L z J' →
      val (τ₀ (p.xe a) (p.xe b)) (r ≫ spMap ρ) z J =
        (ArcPull.om p.w z J J' (r ≫ (D.c (a + b)).left))⁻¹ * ArcPull.om p.w z J J' (r ≫ (D.c a).left) *
          ArcPull.om p.w z J J' (r ≫ (D.c b).left) * (ArcPull.om p.w z J J' (r ≫ (D.c 0).left))⁻¹ *
          val t r z J' := by
    intro a b
    have hψ : ∀ k : Fin 4, (![(D.c (a + b)).left, (D.c a).left, (D.c b).left, (D.c 0).left] k) ≫
        (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)) =
        spMap ρ ≫ (![(Q.c (p.xe a + p.xe b)).left, (Q.c (p.xe a)).left, (Q.c (p.xe b)).left, (Q.c 0).left] k) := by
      intro k
      fin_cases k
      · simpa [map_add] using p.c_pr (a + b)
      · simpa using p.c_pr a
      · simpa using p.c_pr b
      · simpa [map_zero] using p.c_pr 0
    obtain ⟨t, ht, hv⟩ := ArcPull.exists_down_om p.w_gen Q.P.isLB D.P.isLB (spMap ρ) hψ (τ₀ (p.xe a) (p.xe b))
      (hτ _ _)
    refine ⟨t, ht, fun Z r z J J' hJ hJ' => ?_⟩
    rw [hv Z r z J J' hJ hJ']
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
  choose τ₁ h₁ h₂ using key
  exact ⟨τ₁, h₁, fun a b => h₂ a b⟩

end GlobalTheory.USep.TauPullB

noncomputable section
namespace GlobalTheory.USep.TauPullB

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] {ρ : V →+* V₁} {Q : DegPre V} {D : DegPre V₁}

theorem c_zero (D : DegPre V₁) : D.c 0 = 1 := by
  have h := D.c_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xK_zero (D : DegPre V₁) : (1 : TK V₁ ⟶ D.P.A).left = (toUnit (TK V₁)).left ≫ (D.c 0).left := by
  rw [c_zero, ← Over.comp_left, MonObj.comp_one]

end GlobalTheory.USep.TauPullB

noncomputable section
namespace GlobalTheory.USep.TauPullB

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] {ρ : V →+* V₁} {Q : DegPre V} {D : DegPre V₁}

theorem tauIn_moved (hρ : Function.Injective ρ) (p : IsPullDeg ρ Q D) (τ₀ : GlobalTheory.UChart.Gens Q) (τ₁ : GlobalTheory.UChart.Gens D)
    (h₁ : ∀ a b, (τ₁ a b).IsGen) (hmv : ∀ (a b : D.X) (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z)
      (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (J' : (Z ⟶ D.P.A.left) → D.P.L.ι), Good Q.P.L z J → Good D.P.L z J' →
      val (τ₀ (p.xe a) (p.xe b)) (r ≫ spMap ρ) z J =
        (ArcPull.om p.w z J J' (r ≫ (D.c (a + b)).left))⁻¹ * ArcPull.om p.w z J J' (r ≫ (D.c a).left) *
          ArcPull.om p.w z J J' (r ≫ (D.c b).left) * (ArcPull.om p.w z J J' (r ≫ (D.c 0).left))⁻¹ *
          val (τ₁ a b) r z J') {N : ℕ} (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ Q.X)
    (ε₁ : Fin N → LinearMap.BilinForm ℤ D.X) (hε : ∀ k a b, ε₁ k a b = ε k (p.xe a) (p.xe b))
    (hT : GlobalTheory.UChart.TauIn Q τ₀ s ε) : GlobalTheory.UChart.TauIn D τ₁ (fun k => ρ (s k)) ε₁ := by
  intro a b
  obtain ⟨-, k, hk, hv⟩ := hT (p.xe a) (p.xe b)
  refine ⟨h₁ a b, Units.map (ArcPull.fracMap hρ).toMonoidHom k, ?_, fun z J' hJ' => ?_⟩
  · rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, hk, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀, ArcPull.fracMap_algebraMap, hε]
  · choose J hJ using fun χ : (TK V₁).left ⟶ Q.P.A.left => exists_chart Q.P.isLB (χ z)
    have hJ : Good Q.P.L z J := hJ
    have hcorr : LB.Gen.Corr Q.P.L _ _ _ _ (Q.tau (p.xe a) (p.xe b))
        (DVR.scaleGen (unitOn k) (LB.pullGen Q.P.L _ _ (τ₀ (p.xe a) (p.xe b)) (toUnit (TK V)).left)) :=
      corr_of_val Q.P.isLB fun y I hI => by
        rw [hv y I hI, TauTwist.val_scale _ _ _ hI, val_pull hI, Category.id_comp]; rfl
    have e1 := ArcPull.tau_val p (ArcPull.genMap hρ) (𝟙 _) (ArcPull.fracMap_sq hρ) hJ hJ' a b
    have e2 := val_corr hJ hcorr (ArcPull.genMap hρ)
    rw [TauTwist.val_scale _ _ _ hJ, val_pull hJ] at e2
    have e3 : ArcPull.genMap hρ ≫ (toUnit (TK V)).left = (toUnit (TK V₁)).left ≫ spMap ρ :=
      (ArcPull.fracMap_sq hρ).symm.trans (Category.id_comp _)
    rw [e3, hmv a b _ (toUnit (TK V₁)).left z J J' hJ hJ'] at e2
    have e4 : TauTwist.unitAt (ArcPull.genMap hρ) z k =
        TauTwist.unitAt (𝟙 _) z (Units.map (ArcPull.fracMap hρ).toMonoidHom k) :=
      (congrArg (fun q => TauTwist.unitAt q z k) (Category.id_comp (ArcPull.genMap hρ)).symm).trans
        (TauTwist.unitAt_spMap _ _ _ _)
    have o : ∀ x : D.X, 𝟙 _ ≫ D.xK x = (toUnit (TK V₁)).left ≫ (D.c x).left := fun x => by
      rw [Category.id_comp]; rfl
    rw [o, o, o, Category.id_comp, xK_zero] at e1
    rw [e4] at e2
    have e := e1.symm.trans e2
    rw [← TauTwist.unitAt_apply]
    generalize (ArcPull.om p.w z J J' ((toUnit (TK V₁)).left ≫ (D.c (a + b)).left))⁻¹ *
      ArcPull.om p.w z J J' ((toUnit (TK V₁)).left ≫ (D.c a).left) *
      ArcPull.om p.w z J J' ((toUnit (TK V₁)).left ≫ (D.c b).left) *
      (ArcPull.om p.w z J J' ((toUnit (TK V₁)).left ≫ (D.c 0).left))⁻¹ = O at e
    rw [mul_left_comm] at e
    exact mul_left_cancel e

end GlobalTheory.USep.TauPullB

noncomputable section
namespace GlobalTheory.USep.TauPullB

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] {ρ : V →+* V₁} {Q : DegPre V} {D : DegPre V₁}

def trGen {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ} (h : φ = φ')
    (t : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ' ε) := h ▸ t

theorem trGen_isGen {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) : (trGen h t).IsGen := by
  subst h; exact ht

theorem val_trGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (trGen h t) r z J = val t r z J := by
  subst h; rfl

theorem fromBase_moved (p : IsPullDeg ρ Q D) (τ₀ : GlobalTheory.UChart.Gens Q) (τ₁ : GlobalTheory.UChart.Gens D)
    (h₁ : ∀ a b, (τ₁ a b).IsGen) (hmv : ∀ (a b : D.X) (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z)
      (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (J' : (Z ⟶ D.P.A.left) → D.P.L.ι), Good Q.P.L z J → Good D.P.L z J' →
      val (τ₀ (p.xe a) (p.xe b)) (r ≫ spMap ρ) z J =
        (ArcPull.om p.w z J J' (r ≫ (D.c (a + b)).left))⁻¹ * ArcPull.om p.w z J J' (r ≫ (D.c a).left) *
          ArcPull.om p.w z J J' (r ≫ (D.c b).left) * (ArcPull.om p.w z J J' (r ≫ (D.c 0).left))⁻¹ *
          val (τ₁ a b) r z J') (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V)
    (hF : GlobalTheory.UChart.FromBase Q τ₀ ib) : GlobalTheory.UChart.FromBase D τ₁ (ρ.comp ib) := by
  obtain ⟨B₀, iG, M₀, c₀, σ, β, w, hB₀, hM₀, hgp, hw, hc, hσ, hval⟩ := hF
  have key : ∀ (x y : Q.X) (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) (JQ : (Z ⟶ Q.P.A.left) → Q.P.L.ι)
      (J₀ : (Z ⟶ B₀.left) → M₀.ι), Good Q.P.L z JQ → Good M₀ z J₀ →
      val (σ x y) (r ≫ spMap ib) z J₀ = (ArcPull.om w z J₀ JQ (r ≫ GlobalTheory.UChart.cpt Q (x + y)))⁻¹ *
        ArcPull.om w z J₀ JQ (r ≫ GlobalTheory.UChart.cpt Q x) * ArcPull.om w z J₀ JQ (r ≫ GlobalTheory.UChart.cpt Q y) *
        (ArcPull.om w z J₀ JQ (r ≫ GlobalTheory.UChart.cpt Q 0))⁻¹ * val (τ₀ x y) r z JQ := by
    intro x y
    have hψ : ∀ k : Fin 4, (![GlobalTheory.UChart.cpt Q (x + y), GlobalTheory.UChart.cpt Q x, GlobalTheory.UChart.cpt Q y,
        GlobalTheory.UChart.cpt Q 0] k) ≫ β = spMap ib ≫ (![c₀ (x + y), c₀ x, c₀ y, c₀ 0] k) := by
      intro k; fin_cases k <;> exact hc _
    obtain ⟨g, -, hvg⟩ := ArcPull.exists_down_om hw hM₀ Q.P.isLB (spMap ib) hψ (σ x y) (hσ x y)
    have hcor : LB.Gen.Corr Q.P.L _ _ _ _ (τ₀ x y) g := corr_of_val Q.P.isLB fun y' I hI => by
      choose I₀ hI₀ using fun χ : Sp V ⟶ B₀.left => exists_chart hM₀ (χ y')
      have e1 := hval x y y' I I₀ hI hI₀
      have e2 := hvg _ (𝟙 _) y' I₀ I hI₀ hI
      simp only [Category.id_comp, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one] at e2
      have hg : ∀ t : Q.X, gm (GlobalTheory.UChart.cpt Q t) y' _ (w.s (fun _ => I₀ (GlobalTheory.UChart.cpt Q t ≫ β), I (GlobalTheory.UChart.cpt Q t))) =
          ArcPull.om w y' I₀ I (GlobalTheory.UChart.cpt Q t) := fun t => rfl
      simp only [hg] at e1
      show val (τ₀ x y) (𝟙 (Sp V)) y' I = val g (𝟙 (Sp V)) y' I
      rw [e1]
      erw [e2]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    intro Z r z JQ J₀ hJQ hJ₀
    rw [hvg Z r z J₀ JQ hJ₀ hJQ, ← val_corr hJQ hcor r]
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
  obtain ⟨w₂, hT⟩ := exists_comp Q.P.isLB w p.w ((isGen_iff w).1 hw) ((isGen_iff p.w).1 p.w_gen) hM₀ D.P.isLB
  have hw₂ : w₂.IsGen :=
    (isGen_iff w₂).2 (hT.pgen_comp Q.P.isLB ((isGen_iff w).1 hw) ((isGen_iff p.w).1 p.w_gen))
  have hφ : ∀ a b : D.X, ![c₀ (p.xe a + p.xe b), c₀ (p.xe a), c₀ (p.xe b), c₀ 0] =
      ![c₀ (p.xe (a + b)), c₀ (p.xe a), c₀ (p.xe b), c₀ (p.xe 0)] := fun a b => by rw [map_add, map_zero]
  have ec : ∀ t : D.X, GlobalTheory.UChart.cpt D t ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)) =
      spMap ρ ≫ GlobalTheory.UChart.cpt Q (p.xe t) := fun t => p.c_pr t
  refine ⟨B₀, iG, M₀, fun a => c₀ (p.xe a), fun a b => trGen (hφ a b) (σ (p.xe a) (p.xe b)),
    (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)) ≫ β, w₂, hB₀, hM₀, ?_, hw₂, ?_,
    fun a b => trGen_isGen _ (hσ _ _), ?_⟩
  · rw [spMap_comp]; exact (pull_grp p).comp hgp
  · intro a
    rw [spMap_comp, ← Category.assoc, ec, Category.assoc, hc, Category.assoc]
  · intro a b zz J J₀ hJ hJ₀
    choose JQ hJQ using fun χ : Sp V₁ ⟶ Q.P.A.left => exists_chart Q.P.isLB (χ zz)
    have hJQ : Good Q.P.L zz JQ := hJQ
    have tri : ∀ (t : D.X) (t' : Q.X), GlobalTheory.UChart.cpt D t ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)) =
        spMap ρ ≫ GlobalTheory.UChart.cpt Q t' →
        gm (GlobalTheory.UChart.cpt D t) zz _ (w₂.s (fun _ => J₀ (GlobalTheory.UChart.cpt D t ≫
          (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)) ≫ β), J (GlobalTheory.UChart.cpt D t))) =
          ArcPull.om w zz J₀ JQ (spMap ρ ≫ GlobalTheory.UChart.cpt Q t') * ArcPull.om p.w zz JQ J ((D.c t).left) := by
      intro t t' e
      have := hT _ (GlobalTheory.UChart.cpt D t) zz (J₀ (GlobalTheory.UChart.cpt D t ≫
        (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)) ≫ β))
        (JQ (GlobalTheory.UChart.cpt D t ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)))) (J (GlobalTheory.UChart.cpt D t))
        (hJ₀ _) (hJQ _) (hJ _)
      refine this.trans ?_
      simp only [ArcPull.om]
      rw [← e]
      simp only [Category.assoc]
      rfl
    have m := hmv a b _ (𝟙 _) zz JQ J hJQ hJ
    have k := key (p.xe a) (p.xe b) _ (spMap ρ) zz JQ J₀ hJQ hJ₀
    simp only [Category.id_comp] at m
    rw [tri (a + b) (p.xe a + p.xe b) (by rw [← map_add]; exact ec _), tri a _ (ec a), tri b _ (ec b),
      tri 0 0 (by rw [ec, map_zero]), val_trGen, spMap_comp, k, m]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end GlobalTheory.USep.TauPullB

noncomputable section
namespace GlobalTheory.USep

open GlobalTheory.USep.TauPullB in

theorem tauIn_fromBase_pull : ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁), Function.Injective ρ → ∀ (Q : DegPre V) (D : DegPre V₁) (p : IsPullDeg ρ Q D) (τ₀ : GlobalTheory.UChart.Gens Q) (N : ℕ) (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ Q.X) (ε₁ : Fin N → LinearMap.BilinForm ℤ D.X), (∀ k a b, ε₁ k a b = ε k (p.xe a) (p.xe b)) → GlobalTheory.UChart.TauIn Q τ₀ s ε → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V), GlobalTheory.UChart.FromBase Q τ₀ ib → ∃ τ₁ : GlobalTheory.UChart.Gens D, GlobalTheory.UChart.TauIn D τ₁ (fun k => ρ (s k)) ε₁ ∧ GlobalTheory.UChart.FromBase D τ₁ (ρ.comp ib) := by
  intro V V₁ _ _ _ _ ρ hρ Q D p τ₀ N s ε ε₁ hε hT W₀ _ ib hF
  obtain ⟨τ₁, h₁, hmv⟩ := exists_moved p τ₀ fun a b => (hT a b).1
  exact ⟨τ₁, tauIn_moved hρ p τ₀ τ₁ h₁ hmv s ε ε₁ hε hT, fromBase_moved p τ₀ τ₁ h₁ hmv W₀ ib hF⟩

end GlobalTheory.USep
