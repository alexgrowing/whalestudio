import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CorrOfValFieldExtension

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiRelationDescent

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

def chartPullComb {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) :
    ChartPull ((LB.LinComb L φ ε).pull h) (LB.LinComb L (fun k => h ≫ φ k) ε) (𝟙 Y') :=
  have le : ∀ J : PUnit → K → L.ι, ((LB.LinComb L φ ε).pull h).U J ≤
      LB.wchart L (fun k => h ≫ φ k) (J PUnit.unit) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hy) k
  { idx := fun J => J PUnit.unit
    le := le
    g := fun y J J' hj hj' => by
      refine (gm_pull_g (LB.LinComb L φ ε) h (𝟙 Y') y J J' hj hj').trans
        ((gm_linComb L φ ε (𝟙 Y' ≫ h) y _ _ (mem_pull.1 hj) (mem_pull.1 hj')).trans
          (Eq.trans ?_ (gm_linComb L (fun k => h ≫ φ k) ε (𝟙 Y') y _ _ (le J hj) (le J' hj')).symm))
      simp only [Category.assoc] }

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]
  (oa : D.OAct O) (w : O)

abbrev mor : Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  ![(padd D.P.A (𝟙 _) (oa.onB.act w)).left, 𝟙 D.P.A.left, (oa.onB.act w).left, (toUnit D.P.A ≫ η[D.P.A]).left]

theorem prod_mor {T : Over (Sp R)} (x : T ⟶ D.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 4, h (x.left ≫ mor oa w k) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) k =
      h (x * (x ≫ oa.onB.act w)).left * (h x.left ^ 2)⁻¹ * (h (x ≫ oa.onB.act w).left)⁻¹ *
        h (1 : T ⟶ D.P.A).left ^ 2 := by
  have a₀ : x ≫ padd D.P.A (𝟙 _) (oa.onB.act w) = x * (x ≫ oa.onB.act w) :=
    (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])
  have a₁ : x ≫ toUnit D.P.A ≫ η[D.P.A] = 1 := MonObj.comp_one (M := D.P.A) x
  rw [Fin.prod_univ_four]
  show h (x ≫ padd D.P.A (𝟙 _) (oa.onB.act w)).left ^ (1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (-2 : ℤ) *
    h (x ≫ oa.onB.act w).left ^ (-1 : ℤ) * h (x ≫ toUnit D.P.A ≫ η[D.P.A]).left ^ (2 : ℤ) = _
  rw [a₀, a₁, Category.comp_id]
  simp only [zpow_neg, zpow_ofNat, pow_one]

theorem prod_mor_one {T : Over (Sp R)} {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 4, h ((1 : T ⟶ D.P.A).left ≫ mor oa w k) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) k = 1 := by
  have := oa.onB.hom w
  rw [prod_mor, MonObj.one_comp, _root_.mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
  abel

theorem exists_normalised (u : LB.Gen (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2])) (hu : u.IsGen) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2]), t.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (eSec D.P.A)) (LB.oneGen D.P.L) := by
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := mor oa w) (ε' := ![1, -2, -1, 2])
    (fun V _ k => by
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _
        (c := ∏ i, k (mor oa w i) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) i) rfl
        (prod_neg _ _ (prod_mor_one oa w (T := D.P.A) k))) ?_
      simp)
    (LB.mulGen D.P.L _ _ _ _ u (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u (1 : D.P.A ⟶ D.P.A).left)))
    (mulGen_isGen _ _ _ _ _ _ _ hu (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hu _)))
  refine ⟨t, ht, corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e : eSec D.P.A ≫ (1 : D.P.A ⟶ D.P.A).left = eSec D.P.A :=
    (congrArg (fun q => q.left) (MonObj.comp_one (M := D.P.A) η[D.P.A])).trans (Category.id_comp _)
  rw [val_pull hJ, val_one, Category.id_comp, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, e, mul_inv_cancel]

end

end GlobalTheory.PsiRelationDescent

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull GlobalTheory.PsiRelationDescent in

theorem psi_relation_descend_field : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oa : D.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oa.onB.act a).left) → ∀ w : O, TraceFormTwistIso D' oa' w → TraceFormTwistIso D oa w := by
  intro hG K₀ K _ _ i D D' hD O _ _ _ _ oa oa' hx ho w ⟨u', hu', u₀', hy'⟩
  have gp := pull_grp hD
  have hφ : Function.Injective i := i.injective
  have i₁ : (𝟙 D'.P.A : D'.P.A ⟶ _).left ≫ PsiEvenPull.proj hD =
      PsiEvenPull.proj hD ≫ (𝟙 D.P.A : D.P.A ⟶ _).left :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have i₂ : (toUnit D'.P.A ≫ η[D'.P.A]).left ≫ PsiEvenPull.proj hD =
      PsiEvenPull.proj hD ≫ (toUnit D.P.A ≫ η[D.P.A]).left := by
    show (D'.P.A.hom ≫ eSec D'.P.A) ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ D.P.A.hom ≫ eSec D.P.A
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hD.he).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) gp.1.w.symm).trans (Category.assoc _ _ _))))
  have hψ : ∀ k, mor oa' w k ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ mor oa w k := fun k => by
    fin_cases k
    exacts [mul_push gp _ i₁ (ho w), i₁, ho w, i₂]
  obtain ⟨s, hs, -⟩ := exists_up_om ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (mor oa' w)
    (fun k => PsiEvenPull.proj hD ≫ mor oa w k) _ hψ u' hu'
  obtain ⟨u₁, hu₁⟩ := (lb_gen_iso_descend_field K₀ K i _ _ D.P.A.hom D'.P.A.hom (PsiEvenPull.proj hD)
    D.P.isAb.smooth D.P.isAb.proper D.P.isAb.geomConnected gp.1).1 (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2])
    (LB.isLB_linComb D.P.isLB _ _) ⟨_, GtBaseChange.genPull_isGen (chartPullComb D.P.L (mor oa w) _ _) hs⟩
  obtain ⟨u, hu, u₀⟩ := exists_normalised oa w u₁ hu₁
  obtain ⟨t, ht, vt⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB (φ' := mor oa' w) (PsiEvenPull.proj hD) hψ u hu
  have tu := gen_unique D'.P.isLB D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2 ht hu'
    fun y J' hJ' => by
      obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
      have o₁ : (1 : 𝟙_ (Over (Sp K)) ⟶ D'.P.A).left = eSec D'.P.A := Category.id_comp _
      have e := vt _ (1 : 𝟙_ (Over (Sp K)) ⟶ D'.P.A).left y J J' hJ hJ'
      rw [prod_mor_one, _root_.one_mul, o₁, hD.he] at e
      have e₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ u₀ (specOf i)).trans (val_one _))
      have e₂ := (val_pull hJ' _ _ _).symm.trans ((val_corr hJ' u₀' (𝟙 _)).trans (val_one _))
      rw [Category.id_comp] at e₂
      exact e.symm.trans (e₁.trans e₂.symm)
  refine ⟨u, hu, u₀, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hD.xe.surjective y
  refine corr_of_val_field_extension _ _ (fracMap hφ) _ _ D.P.isLB _ _ _ _ _ _ _ _ fun z J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := (TK K).left) z
  have sq := fracMap_sq hφ
  have hh : (TK K).hom ≫ spMap i = genMap hφ ≫ (TK K₀).hom := (Category.id_comp _).symm.trans sq
  have e := val_corr hJ' (hy' x) (𝟙 _)
  have v := vt _ (cP D' (TK K) x).left z J J' hJ hJ'
  rw [prod_mor, cPoint_proj hD _ hh, ← TorusExt.cPoint_smul oa', ← cPoint_add, tu _ _ z J' hJ'] at v
  have c₀ : ∀ x, (cP D' (TK K) x).left = D'.xK x := fun _ => rfl
  have c₁ : ∀ x, (cP D (TK K₀) x).left = D.xK x := fun _ => rfl
  simp only [c₀, c₁] at v
  rw [val_mul hJ', val_mul hJ', val_pull hJ', Category.id_comp] at e
  show val (LB.mulGen D.P.L _ _ _ _ (D.tau (hD.xe x) (w • hD.xe x)) (LB.pullGen D.P.L _ _ u (D.xK (hD.xe x))))
    (genMap hφ) z J = val (LB.mulGen D.P.L _ _ _ _ (D.psi (hD.xe x)) D.rigK) (genMap hφ) z J
  have hJ₀ : Good (Z := (TK K).left) D.P.L z J := hJ
  rw [val_mul hJ₀, val_mul hJ₀, val_pull hJ₀, v, ← hx, tau_val hD _ _ sq hJ₀ hJ', psi_val hD _ _ sq hJ₀ hJ',
    rig_val hD _ _ sq hJ₀ hJ']
  simp only [Category.id_comp]
  have e' := congrArg Additive.ofMul e
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory
