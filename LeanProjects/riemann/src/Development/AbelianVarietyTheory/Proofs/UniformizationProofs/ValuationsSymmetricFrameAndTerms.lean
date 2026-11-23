import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LiftOUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTermsStatement
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
namespace GlobalTheory.UT.TxVal
open TWM TWO

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

def cstHom (z : (TF (R := V) F).left) : F →+* (TF (R := V) F).left.presheaf.stalk z :=
  ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem cst_eq_hom (z : (TF (R := V) F).left) (x : F) : cst F z x = cstHom (V := V) z x := by
  rw [cst, gs_eq _ z ⊤ trivial]; rfl

theorem gs_iota (z : (TF (R := V) F).left) (a : Γ((TO hϖ hv).left, ⊤)) :
    gs ((ιS hϖ hv).left ≫ 𝟙 _) z ⊤ a = cstHom (V := V) z (ιr (v := v) a) := by
  rw [Category.comp_id, gs_eq _ z ⊤ trivial]
  exact congrArg ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z trivial).hom
    (appTop_specMap (CommRingCat.ofHom (algebraMap (Ov v) F)) a)

theorem iota_inj {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of V)) [IsSeparated p] :
    Function.Injective fun q : (TO hϖ hv).left ⟶ X => (ιS hϖ hv).left ≫ q := by
  intro x₁ x₂ h
  have hU : ValuativeCriterion.Uniqueness (p ≫ terminal.from _) := IsSeparated.valuativeCriterion _
  let S : ValuativeCommSq (p ≫ terminal.from _) :=
    { R := Ov v, K := F, i₁ := Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x₁,
      i₂ := terminal.from _,
      commSq := ⟨terminal.hom_ext _ _⟩ }
  have := (hU S).elim ⟨x₁, rfl, terminal.hom_ext _ _⟩ ⟨x₂, h.symm, terminal.hom_ext _ _⟩
  exact congrArg CommSq.LiftStruct.l this

variable {hϖ hv} {X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → ((TF (R := V) F).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((TF (R := V) F).left ⟶ X)} {ε' : K' → ℤ}

theorem genV_mul {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} {r r' : ℚ}
    (h : GenV hϖ hv t r) (h' : GenV hϖ hv t' r') : GenV hϖ hv (LB.mulGen L _ _ _ _ t t') (r + r') := by
  obtain ⟨φ₀, e, t₀, g, x, vx, hx⟩ := h
  obtain ⟨φ₀', e', t₀', g', x', vx', hx'⟩ := h'
  refine ⟨Sum.elim φ₀ φ₀', by rintro (i | i); exacts [e i, e' i], LB.mulGen L _ _ _ _ t₀ t₀',
    mulGen_isGen _ _ _ _ _ _ _ g g', x * x', by rw [AddValuation.map_mul, vx, vx', WithTop.coe_add], fun z J hJ => ?_⟩
  rw [val_mul hJ, val_mul hJ, Units.val_mul, Units.val_mul, hx z J hJ, hx' z J hJ, cst_eq_hom, cst_eq_hom, cst_eq_hom,
    map_mul]
  ring

theorem genV_pull {Y : Scheme.{0}} {ψ : K → (Y ⟶ X)} (u : LB.Gen (LB.LinComb L ψ ε)) (hu : u.IsGen)
    (b : (TF (R := V) F).left ⟶ Y) (m : (TO hϖ hv).left ⟶ Y) (hm : (ιS hϖ hv).left ≫ m = b) :
    GenV hϖ hv (LB.pullGen L ψ ε u b) 0 := by
  refine ⟨fun i => m ≫ ψ i, fun i => by rw [← Category.assoc, hm], LB.pullGen L ψ ε u m, pullGen_isGen _ _ _ _ hu _, 1,
    by rw [AddValuation.map_one]; rfl, fun z J hJ => ?_⟩
  rw [val_pull hJ, val_pull hJ, Category.id_comp, hm, cst_eq_hom, map_one, _root_.one_mul]

theorem genV_unique (hL : L.IsLB) (p : X ⟶ Spec (CommRingCat.of V)) [IsSeparated p] (hF : FormEq φ ε φ' ε')
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (hval : ∀ z J, Good L z J → val t (𝟙 _) z J = val t' (𝟙 _) z J) {r r' : ℚ}
    (h : GenV hϖ hv t r) (h' : GenV hϖ hv t' r') : r = r' := by
  obtain ⟨φ₀, e, t₀, g, x, vx, hx⟩ := h
  obtain ⟨φ₀', e', t₀', g', x', vx', hx'⟩ := h'
  have hF₀ : FormEq φ₀ ε φ₀' ε' := fun U _ k => by
    have hi := iota_inj hϖ hv p
    have := hF U (Function.extend (fun q : (TO hϖ hv).left ⟶ X => (ιS hϖ hv).left ≫ q) k 1)
    simpa only [e, e', hi.extend_apply] using this
  have hsurj : Function.Surjective (Scheme.Hom.appTop (𝟙 (TO hϖ hv).left)).hom := fun x => ⟨x, by simp⟩
  have hu := mulGen_isGen _ _ _ _ _ _ _ g (invGen_isGen _ _ _ _ g')
  have hf : ∀ (U : Type) [CommGroup U] (k : ((TO hϖ hv).left ⟶ X) → U),
      ∏ i, k (Sum.elim φ₀ φ₀' i) ^ Sum.elim ε (fun i => - ε' i) i = 1 := fun U _ k => by
    refine (prod_sum₂ (K := K) (K' := K') (U := U) _ (hF₀ U k) (prod_neg _ _ rfl)).trans (mul_inv_cancel _)
  obtain ⟨a, ha⟩ := H1.exists_const L hL (𝟙 _) hsurj _ hu hf
  obtain ⟨a', ha'⟩ := H1.exists_const L hL (𝟙 _) hsurj _ (invGen_isGen _ _ _ _ hu)
    (fun U _ k => (prod_neg _ _ (hf U k)).trans inv_one)
  let z₀ : (TF (R := V) F).left := (default : Spec (CommRingCat.of F))
  choose J hJ using fun χ : (TF (R := V) F).left ⟶ X => exists_chart hL (χ z₀)
  have hG : Good L z₀ J := hJ
  have h₁ := ha _ (ιS hϖ hv).left z₀ J hG
  have h₂ := ha' _ (ιS hϖ hv).left z₀ J hG
  rw [gs_iota] at h₁ h₂
  have hinj : Function.Injective (cstHom (V := V) z₀) := (cstHom (V := V) z₀).injective
  have k2 : ιr (v := v) a * ιr (v := v) a' = 1 := by
    apply hinj
    rw [map_mul, map_one, ← h₁, ← h₂, val_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have va : v (ιr (v := v) a) = 0 := by
    have e : v (ιr (v := v) a) + v (ιr (v := v) a') = 0 := by rw [← AddValuation.map_mul, k2, AddValuation.map_one]
    exact le_antisymm (le_zero_of_add_eq_zero_nonneg e (v_ιr a')) (v_ιr a)
  have k1 : x * ιr (v := v) a = x' := by
    apply hinj
    have e₁ := hx z₀ J hG
    have e₂ := hx' z₀ J hG
    rw [hval z₀ J hG, e₂, cst_eq_hom, cst_eq_hom] at e₁
    rw [val_mul hG, val_inv] at h₁
    apply (val t₀' (ιS hϖ hv).left z₀ J).isUnit.mul_right_cancel
    rw [map_mul, ← h₁, e₁, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel_right]
  have k3 := congrArg v k1
  rw [AddValuation.map_mul, va, vx, vx', add_zero] at k3
  exact_mod_cast k3

end

theorem exists_nu {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (hm : MulPullSt) (D : DegPre R) (N : ℕ) :
    ∃ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(𝟙 D.P.A ^ (N + 1)).left, (𝟙 D.P.A ^ N).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left]
      ![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1]), Normd ν := by
  obtain ⟨α, hα⟩ := hm _ D.P N
  obtain ⟨β, hβ⟩ := hm _ D.P (N + 1)
  let δ := LB.mulGen D.P.L _ _ _ _ α (LB.invGen D.P.L _ _ β)
  have hδ : δ.IsGen := mulGen_isGen _ _ _ _ _ _ _ hα (invGen_isGen _ _ _ _ hβ)
  let o : D.P.A ⟶ D.P.A := 1
  have op : ∀ n : ℕ, o.left ≫ (mulA D.P.A n).left = o.left := fun n =>
    congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (show o ≫ 𝟙 D.P.A ^ n = o from
      (map_pow (preHom o) _ n).trans (by
        show (o ≫ 𝟙 _) ^ n = o
        rw [Category.comp_id, one_pow]))
  obtain ⟨ν, hν, vν⟩ := exists_gen D.P.isLB
    (φ' := ![(𝟙 D.P.A ^ (N + 1)).left, (𝟙 D.P.A ^ N).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left])
    (ε' := ![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1]) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_four,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, op, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, o]
      push_cast
      module)
    (LB.mulGen D.P.L _ _ _ _ δ (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ δ o.left)))
    (mulGen_isGen _ _ _ _ _ _ _ hδ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hδ _)))
  refine ⟨ν, hν, corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e : eSec D.P.A ≫ o.left = eSec D.P.A :=
    congrArg (fun q : 𝟙_ _ ⟶ D.P.A => q.left) (show η[D.P.A] ≫ o = η[D.P.A] by simp [o, Hom.one_def])
  rw [val_pull hJ, Category.id_comp, vν _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, e, mul_inv_cancel, val_one]

theorem nsmul_b {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {m : ℕ} {g g' : GtPtF D F} (h : GtPtF.IsNsmul m g g') : g'.b = g.b ^ m := by
  obtain ⟨gs, g₀, gst, rfl⟩ := h
  have : ∀ i : Fin (m + 1), (gs i).b = g.b ^ (i : ℕ) := fun i => by
    induction i using Fin.induction with
    | zero => exact ((isZero_iff _).1 g₀).1.trans (pow_zero _).symm
    | succ i ih => rw [((isAdd_iff _ _ _).1 (gst i)).1, ih, Fin.val_succ, pow_succ, Fin.val_castSucc]
  exact this (Fin.last m)

theorem comp_pow_left {S : Scheme.{0}} {A T : Over S} [GrpObj A] (b : T ⟶ A) (n : ℕ) :
    b.left ≫ (𝟙 A ^ n).left = (b ^ n).left :=
  congrArg (fun q : T ⟶ A => q.left) (show b ≫ 𝟙 A ^ n = b ^ n from
    (map_pow (preHom b) _ n).trans (by
      show (b ≫ 𝟙 _) ^ n = _
      rw [Category.comp_id]))

theorem comp_one_left {S : Scheme.{0}} {A T : Over S} [GrpObj A] (b : T ⟶ A) :
    b.left ≫ (1 : A ⟶ A).left = (1 : T ⟶ A).left :=
  congrArg (fun q : T ⟶ A => q.left) (MonObj.comp_one (M := A) b)

theorem prod_line {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (b : TF (R := R) F ⟶ D.P.A) (k : ℕ) {U : Type} [CommGroup U] (h : ((TF (R := R) F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.lineφ D F b i) ^ DegPre.lineε k i =
      h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h b.left ^ (-(k : ℤ)) := by
  rw [Fin.prod_univ_two]; rfl

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => (∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) w, TXFrame N p w → GenV hϖ hv w ((Q p.y : ℚ) / N)) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (p : QkPt D.toPre F (m ^ 2)) w, TXFrame (m ^ 2) p w → ∀ (g' : GtPtF D.toPre F), GtPtF.IsNsmul m p.g g' → ∀ (κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ m) (m ^ 2) 1)), Normd κ → ∀ w' : Frm D.toPre F 1 g'.b, w'.IsGen → (∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J * val κ p.g.b.left z J = val w' (𝟙 _) z J) → GenV hϖ hv w' ((Q p.y : ℚ) / (m ^ 2 : ℕ)) ∧ GtV hϖ hv g' (fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / m) ∧ ∀ ϑ : Fam D.toPre F 1, NuGe D Q F v 1 ϑ 0 → ∀ χ, (((Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ) : ℚ) : WithTop ℚ) ≤ v (coef ϑ g' w' χ) := by
  intro hLL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv
  have CV := GlobalTheory.T.valuations_torusPoints_frames_familyTerms hLL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv
  have hL := D.toPre.P.isLB
  have part1 : ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) w, TXFrame N p w → GenV hϖ hv w ((Q p.y : ℚ) / N) := by
    intro N hN p w hw
    obtain ⟨r, hr, -⟩ := (CV p.g).2.1 N w hw.1
    obtain ⟨ν, hν⟩ := exists_nu hLL.1.mulPull D.toPre N
    obtain ⟨m, hm⟩ := exists_liftO hϖ hv p.g.b
    have hg := (CV p.g).2.2.2.2.1 N hN p p.y
    have e := genV_unique hL D.toPre.P.A.hom (fun U _ h => by
        refine (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (prod_line p.g.b N h) (prod_line p.g.b N h)).trans
          (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_gt p.g.b p.y h) rfl).symm)
        simp only [Sum.elim_inr, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          comp_pow_left, comp_one_left, Category.comp_id, cPoint_y]
        rw [pow_succ]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
        module)
      (fun z J hJ => by
        rw [val_mul hJ, val_mul hJ, val_pull hJ, Category.id_comp, ← sq]
        exact hw.2.1 ν hν z J hJ)
      (genV_mul hr hr) (genV_mul hg (genV_pull ν hν.1 p.g.b.left m.left (congrArg (fun q => q.left) hm)))
    beta_reduce at e
    rw [← QForm.two_Q_eq hϖ D hQ] at e
    have : r = (Q p.y : ℚ) / N := by
      push_cast at e
      linear_combination e / 2
    exact this ▸ hr
  refine ⟨part1, fun m hm p w hw g' hg' κ hκ w' hw' hval => ?_⟩
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have A₁ : GenV hϖ hv w' ((Q p.y : ℚ) / (m ^ 2 : ℕ)) := by
    obtain ⟨r, hr, -⟩ := (CV g').2.1 1 w' hw'
    obtain ⟨b, hb⟩ := exists_liftO hϖ hv p.g.b
    have e := genV_unique hL D.toPre.P.A.hom (fun U _ h => by
        refine (prod_sum₂ (K := Fin 2) (K' := Fin 3) (U := U) _ (prod_line p.g.b (m ^ 2) h) rfl).trans
          (Eq.trans ?_ (prod_line g'.b 1 h).symm)
        simp only [Sum.elim_inr, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          comp_pow_left, comp_one_left, Category.comp_id, nsmul_b hg']
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow]
        module)
      (fun z J hJ => by
        rw [val_mul hJ, val_pull hJ, Category.id_comp]
        exact hval z J hJ)
      (genV_mul (part1 _ hm2 p w hw) (genV_pull κ hκ.1 p.g.b.left b.left (congrArg (fun q => q.left) hb))) hr
    rw [add_zero] at e
    exact e ▸ hr
  have A₂ : GtV hϖ hv g' (fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / m) := by
    have hg := (CV p.g).2.2.2.2.1 _ hm2 p
    obtain ⟨gs, g₀, gst, rfl⟩ := hg'
    have all : ∀ i : Fin (m + 1), GtV hϖ hv (gs i)
        (fun χ => (i : ℕ) * ((QForm.bOf D.toPre Q p.y χ : ℚ) / (m ^ 2 : ℕ))) := fun i => by
      induction i using Fin.induction with
      | zero =>
        obtain ⟨l, hl, ul⟩ := (CV (gs 0)).1
        obtain ⟨zb, zv⟩ := (isZero_iff _).1 g₀
        have hadd : (gs 0).IsAdd (gs 0) (gs 0) := (isAdd_iff _ _ _).2 ⟨by rw [zb, _root_.mul_one], fun χ y J hJ => by
          have C : IsCub (th D.toPre (T := TF (R := V) F) y J) := isCub_cubV D.toPre.cub hJ
          rw [zv χ y J hJ, zb, C.face₃]⟩
        have l0 : l = 0 := add_eq_left.1 (ul (l + l) ((CV (gs 0)).2.2.2.1 _ _ _ _ hadd hl hl))
        subst l0
        intro χ
        simpa using hl χ
      | succ i ih =>
        have := (CV (gs i.castSucc)).2.2.2.1 _ _ _ _ (gst i) ih hg
        intro χ
        have t := this χ
        simp only [Pi.add_apply, Fin.val_castSucc] at t
        rw [Fin.val_succ]
        convert t using 1
        push_cast
        ring
    intro χ
    have t := all (Fin.last m) χ
    rw [Fin.val_last] at t
    convert t using 1
    push_cast
    field_simp
  refine ⟨A₁, A₂, fun ϑ hϑ χ => ?_⟩
  have t := ((CV g').2.2.2.2.2.2 1 le_rfl w' ϑ hw').2 _ _ _ A₂ A₁ hϑ χ
  have q₁ : QForm.bOf D.toPre Q (m • χ) p.y = m * QForm.bOf D.toPre Q p.y χ := by
    rw [QForm.bOf_comm D (Q := Q), ← QForm.bHom_apply hϖ D hQ, map_nsmul, QForm.bHom_apply, nsmul_eq_mul]
  have q₂ : 2 * Q (m • χ) = m * m * (2 * Q χ) := by
    rw [QForm.two_Q_eq hϖ D hQ, QForm.two_Q_eq hϖ D hQ, ← QForm.bHom_apply hϖ D hQ, ← QForm.bHom_apply hϖ D hQ,
      map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, nsmul_eq_mul, _root_.mul_assoc]
  have q₃ : Q (m • χ + p.y) = m * m * Q χ + m * QForm.bOf D.toPre Q p.y χ + Q p.y := by
    rw [← q₁]
    unfold QForm.bOf
    linarith
  convert t using 2
  rw [q₃]
  push_cast
  field_simp
  ring

end GlobalTheory.UT.TxVal
end
