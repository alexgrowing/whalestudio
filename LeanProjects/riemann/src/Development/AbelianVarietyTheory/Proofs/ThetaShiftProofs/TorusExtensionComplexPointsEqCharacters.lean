import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.TorusExtChar

open CubeValues SymmetricSemicharacter FrameValue

theorem fn_ext_val {U : (Sp ℂ).Opens} {a b : Γ(Sp ℂ, U)}
    (h : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ U → valAt' (𝟙 (Sp ℂ)) U a = valAt' (𝟙 (Sp ℂ)) U b) : a = b := by
  by_cases hU : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ U
  · have e := h hU
    obtain rfl : U = ⊤ := top_le_iff.1 hU
    rw [valAt', valAt', dif_pos hU, dif_pos hU, valAt, valAt] at e
    have e' := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 e
    have r : ∀ a : Γ(Sp ℂ, ⊤), ((𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ).appLE ⊤ ⊤ hU).hom a = a := fun a =>
      congrArg (fun q => q.hom a) ((Sp ℂ).presheaf.map_id (Opposite.op ⊤))
    exact (r a).symm.trans (Eq.trans e' (r b))
  · refine fn_ext fun x hx => (hU fun y _ => ?_).elim
    obtain rfl : x = y := Subsingleton.elim (α := PrimeSpectrum ℂ) x y
    exact hx

theorem exists_unit_val (U : (Sp ℂ).Opens) (c : ℂ) (hc : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ U → c ≠ 0) :
    ∃ a : Γ(Sp ℂ, U)ˣ, ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ U → valAt' (𝟙 (Sp ℂ)) U a.val = c := by
  by_cases hU : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ U
  · have v := fun a => (valueRules _ (𝟙 (Sp ℂ))).2.2.2.2.2 (𝟙 _) (Category.id_comp _) U a hU
    obtain ⟨e, he⟩ := (valueRules _ (𝟙 (Sp ℂ))).2.1 U hU
    have m : constFn (𝟙 (Sp ℂ)) U c * constFn (𝟙 (Sp ℂ)) U c⁻¹ = 1 := fn_ext_val fun _ => by
      rw [he, he, map_mul, ← he, ← he, v, v, map_one, mul_inv_cancel₀ (hc hU)]
    exact ⟨Units.mkOfMulEqOne _ _ m, fun _ => v c⟩
  · exact ⟨1, fun h => (hU h).elim⟩

section Gen

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Sp ℂ ⟶ A.left)} {ε : K → ℤ} {φ' : K' → (Sp ℂ ⟶ A.left)} {ε' : K' → ℤ}

theorem corr_of_genVal (hL : L.IsLB) {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (ht : t.IsGen) (ht' : t'.IsGen) {z : K → Fin g → ℂ} {z' : K' → Fin g → ℂ}
    (hz : IsLift u φ (𝟙 _) z) (hz' : IsLift u φ' (𝟙 _) z')
    (hs : ∀ f : (Fin g → ℂ) → ℂˣ, ∏ k, f (z k) ^ ε k = ∏ k, f (z' k) ^ ε' k)
    (h : genVal u hL t (𝟙 _) z = genVal u hL t' (𝟙 _) z') : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  refine Units.ext (fn_ext_val fun h₃ => ?_)
  obtain ⟨h₁, h₂⟩ := (le_preimage_inf _ _ _).1 h₃
  refine (val_res _ valueRules inf_le_left h₃ _).trans (Eq.trans ?_ (val_res _ valueRules inf_le_right h₃ _).symm)
  refine (valAt'_gen hL ht hz h₁).trans (Eq.trans ?_ (valAt'_gen hL ht' hz' h₂).symm)
  rw [h]
  congr 1
  obtain ⟨J, hJ, e⟩ := exists_good L hL (default : PrimeSpectrum ℂ) (Sum.elim φ φ') (Sum.elim j j') (by
    rintro (a | a) (b | b) e
    exacts [c₁ a b e, c₃ a b e, (c₃ b a e.symm).symm, c₂ a b e]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 (h₁ trivial) a, Set.mem_iInter.1 (h₂ trivial) a])
  have := congrArg (Units.coeHom ℂ) (hs fun w => Units.mk0 _ (u.fr_ne (J (u.ex w).left) w
    (((valueRules _ (u.ex w).left).1 _).2 (hJ _))))
  simp only [map_prod, map_zpow, Units.coeHom_apply, Units.val_mk0] at this
  have a : ∀ k, J (u.ex (z k)).left = j k := fun k => by
    rw [← hz k, Category.id_comp]; exact e (.inl k)
  have a' : ∀ k, J (u.ex (z' k)).left = j' k := fun k => by
    rw [← hz' k, Category.id_comp]; exact e (.inr k)
  simpa only [frameProd, a, a'] using this

theorem eq_of_genVal (hL : L.IsLB) {t t' : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    {z : K → Fin g → ℂ} (hz : IsLift u φ (𝟙 _) z)
    (h : genVal u hL t (𝟙 _) z = genVal u hL t' (𝟙 _) z) : t = t' := by
  have : t.s = t'.s := funext fun j => Units.ext (fn_ext_val fun h₁ =>
    (valAt'_gen hL ht hz h₁).trans (Eq.trans (by rw [h]) (valAt'_gen hL ht' hz h₁).symm))
  obtain ⟨s⟩ := t
  obtain ⟨s'⟩ := t'
  exact congrArg LB.Gen.mk this

theorem exists_genVal (hL : L.IsLB) (ε : K → ℤ) {z : K → Fin g → ℂ} (hz : IsLift u φ (𝟙 _) z) {c : ℂ} (hc : c ≠ 0) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ genVal u hL t (𝟙 _) z = c := by
  choose s hs using fun j : K → L.ι => exists_unit_val (L.wchart φ j) (c * frameProd u ε z j)
    fun hj => mul_ne_zero hc (frameProd_ne_zero hz ε hj)
  refine ⟨⟨s⟩, fun j j' => Units.ext (fn_ext_val fun h₃ => ?_), ?_⟩
  · obtain ⟨hj, hj'⟩ := (le_preimage_inf _ _ _).1 h₃
    have e₂ := val_linComb (𝟙 _) valueRules L φ ε j j' hj hj'
    have e₃ : frameProd u ε z j = valAt' (𝟙 _) (L.wchart φ j ⊓ L.wchart φ j') ((L.LinComb φ ε).g j j').val *
        frameProd u ε z j' := by
      refine Eq.trans ?_ (congrArg (· * _) e₂).symm
      simp only [frameProd]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [u.fr_compat (j k) (j' k) (z k) ((le_preimage_inf _ _ _).2 ⟨(hz.le_iff j).1 hj k, (hz.le_iff j').1 hj' k⟩),
        mul_zpow, hz k]
    refine ((val_res _ valueRules inf_le_left h₃ _).trans (hs j hj)).trans (Eq.trans ?_
      ((val_unit_mul _ valueRules h₃ _ _).trans (congrArg (_ * ·)
        ((val_res _ valueRules inf_le_right h₃ _).trans (hs j' hj')))).symm)
    rw [e₃]
    exact mul_left_comm _ _ _
  · have h := le_wchart_chartAt hL φ (𝟙 _)
    exact (congrArg (· / _) (hs _ h)).trans (mul_div_cancel_right₀ _ (frameProd_ne_zero hz ε h))

end Gen

theorem exists_log {X : Type} [AddCommGroup X] [Module.Free ℤ X] (v : X → ℂ) (h₀ : ∀ x, v x ≠ 0)
    (h : ∀ x y, v (x + y) = v x * v y) : ∃ lam : X →+ ℂ, ∀ x, v x = eTwoPi (lam x) := by
  let w : X →+ Additive ℂˣ := AddMonoidHom.mk' (fun x => Additive.ofMul (Units.mk0 _ (h₀ x)))
    fun x y => congrArg Additive.ofMul (Units.ext (h x y))
  let e : ℂ →+ Additive ℂˣ := AddMonoidHom.mk' (fun x => Additive.ofMul (Units.mk0 (eTwoPi x) (Complex.exp_ne_zero _)))
    fun x y => congrArg Additive.ofMul (Units.ext (by simp [eTwoPi, mul_add, Complex.exp_add]))
  have he : Function.Surjective e.toIntLinearMap := fun a =>
    ⟨Complex.log a.toMul.val / (2 * Real.pi * Complex.I), congrArg Additive.ofMul (Units.ext (by
      show Complex.exp _ = _
      rw [mul_div_cancel₀ _ Complex.two_pi_I_ne_zero, Complex.exp_log a.toMul.ne_zero]
      rfl))⟩
  obtain ⟨l, hl⟩ := Module.projective_lifting_property e.toIntLinearMap w.toIntLinearMap he
  exact ⟨l.toAddMonoidHom, fun x => (congrArg (fun q => (Additive.toMul (q x)).val) hl).symm⟩

section Points

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

theorem TF_hom : (Out.TF (R := ℂ) ℂ).hom = 𝟙 (Sp ℂ) := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  exact Spec.map_id _

variable {D : Out.DegPre ℂ} {g : ℕ} (u : HolUnif D.P.A D.P.L g)

abbrev pt (z : Fin g → ℂ) : Out.TF (R := ℂ) ℂ ⟶ D.P.A := toUnit _ ≫ u.ex z

theorem toUnit_left {B : Over (Sp ℂ)} (x : 𝟙_ (Over (Sp ℂ)) ⟶ B) :
    (show Sp ℂ ⟶ _ from (toUnit (Out.TF (R := ℂ) ℂ) ≫ x).left) = x.left := by
  show (Out.TF (R := ℂ) ℂ).hom ≫ x.left = _
  rw [TF_hom]
  exact Category.id_comp _

variable {u} {ct : D.X →+ (Fin g → ℂ)}

theorem isLift_gt (hc : ∀ x, u.ex (ct x) = D.c x) (z : Fin g → ℂ) (x : D.X) :
    IsLift u (Y := Sp ℂ) (Out.DegPre.gtφ D ℂ (pt u z) x) (𝟙 _) ![ct x + z, ct x, z, 0] := fun k => by
  refine (Category.id_comp _).trans (Eq.trans ?_ (toUnit_left _))
  fin_cases k
  · refine congrArg (fun q => q.left) (?_ : padd D.P.A (toUnit _ ≫ D.c x) (pt u z) = pt u (ct x + z))
    rw [pt, pt, u.ex_add, hc, MonObj.comp_mul]
    rfl
  · exact congrArg (fun q => (toUnit (Out.TF (R := ℂ) ℂ) ≫ q).left) (hc x).symm
  · rfl
  · refine congrArg (fun q => (toUnit (Out.TF (R := ℂ) ℂ) ≫ q).left) (?_ : η[D.P.A] = u.ex 0)
    rw [ex_zero, Hom.one_def]; simp

theorem lift_left (hc : ∀ x, u.ex (ct x) = D.c x) (z : Fin g → ℂ) (x x' : D.X) :
    (show Sp ℂ ⟶ _ from (lift (Out.DegPre.cF D ℂ x) (lift (Out.DegPre.cF D ℂ x') (pt u z))).left) =
      (pt3 u ![ct x, ct x', z]).left := by
  have e : lift (Out.DegPre.cF D ℂ x) (lift (Out.DegPre.cF D ℂ x') (pt u z)) = toUnit _ ≫ pt3 u ![ct x, ct x', z] := by
    simp [pt3, comp_lift, hc]
  exact (congrArg (fun q => q.left) e).trans (toUnit_left _)

theorem isLift_mult (hc : ∀ x, u.ex (ct x) = D.c x) (z : Fin g → ℂ) (x x' : D.X) :
    IsLift u (Y := Sp ℂ) (Sum.elim (Out.DegPre.gtφ D ℂ (pt u z) (x + x'))
      (fun k => (lift (Out.DegPre.cF D ℂ x) (lift (Out.DegPre.cF D ℂ x') (pt u z))).left ≫ thφ D.P.A (x3 D.P.A) k))
      (𝟙 _) (Sum.elim ![ct (x + x') + z, ct (x + x'), z, 0] (cubeLift ![ct x, ct x', z])) := by
  rintro (k | k)
  · exact isLift_gt hc z _ k
  · exact (Category.id_comp _).trans ((congrArg (· ≫ _) (lift_left hc z x x')).trans (isLift_cube u _ k))

theorem isLift_mult' (hc : ∀ x, u.ex (ct x) = D.c x) (z : Fin g → ℂ) (x x' : D.X) :
    IsLift u (Y := Sp ℂ) (Sum.elim (Out.DegPre.gtφ D ℂ (pt u z) x) (Out.DegPre.gtφ D ℂ (pt u z) x'))
      (𝟙 _) (Sum.elim ![ct x + z, ct x, z, 0] ![ct x' + z, ct x', z, 0]) := by
  rintro (k | k)
  exacts [isLift_gt hc z _ k, isLift_gt hc z _ k]

theorem prod_mult (a b z : Fin g → ℂ) (f : (Fin g → ℂ) → ℂˣ) :
    ∏ k, f (Sum.elim ![a + b + z, a + b, z, 0] (cubeLift ![a, b, z]) k) ^ Sum.elim Out.DegPre.gtε thε k =
      ∏ k, f (Sum.elim ![a + z, a, z, 0] ![b + z, b, z, 0] k) ^ Sum.elim Out.DegPre.gtε Out.DegPre.gtε k := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  refine (congrArg (_ * ·) (prod_thK fun I => f (∑ i ∈ I, ![a, b, z] i))).trans ?_
  simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val, Fin.prod_univ_four, Out.DegPre.gtε,
    zpow_neg, zpow_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem genVal_mult {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (hc : ∀ x, u.ex (ct x) = D.c x)
    (z : Fin g → ℂ) (x x' : D.X) (t : LB.Gen (LB.LinComb D.P.L (Out.DegPre.gtφ D ℂ (pt u z) (x + x')) Out.DegPre.gtε)) :
    genVal u D.P.isLB (Y := Sp ℂ) (LB.mulGen D.P.L _ _ _ _ t
      (Out.DegPre.cubAt D ℂ (Out.DegPre.cF D ℂ x) (Out.DegPre.cF D ℂ x') (pt u z))) (𝟙 _)
      (Sum.elim ![ct (x + x') + z, ct (x + x'), z, 0] (cubeLift ![ct x, ct x', z])) =
      genVal u D.P.isLB (Y := Sp ℂ) t (𝟙 _) ![ct (x + x') + z, ct (x + x'), z, 0] := by
  refine (genVal_mul D.P.isLB _ _ _ _).trans ((congrArg₂ (· * ·) rfl ?_).trans (_root_.mul_one _))
  refine (genVal_pull D.P.isLB _ _ _ _).trans ?_
  refine Eq.trans ?_ (genVal_cube_of_face D.P.isLB h D.cub.t D.cub.isGen (D.cub.face 0) ![ct x, ct x', z])
  exact congrArg (fun q => genVal u D.P.isLB (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t q (cubeLift ![ct x, ct x', z]))
    ((Category.id_comp _).trans (lift_left hc z x x'))

theorem mult_iff {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (hc : ∀ x, u.ex (ct x) = D.c x)
    (z : Fin g → ℂ) (s : ∀ x, LB.Gen (LB.LinComb D.P.L (Out.DegPre.gtφ D ℂ (pt u z) x) Out.DegPre.gtε))
    (hs : ∀ x, (s x).IsGen) (x x' : D.X) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (s (x + x'))
      (Out.DegPre.cubAt D ℂ (Out.DegPre.cF D ℂ x) (Out.DegPre.cF D ℂ x') (pt u z)))
      (LB.mulGen D.P.L _ _ _ _ (s x) (s x')) ↔
    genVal u D.P.isLB (Y := Sp ℂ) (s (x + x')) (𝟙 _) ![ct (x + x') + z, ct (x + x'), z, 0] =
      genVal u D.P.isLB (Y := Sp ℂ) (s x) (𝟙 _) ![ct x + z, ct x, z, 0] *
        genVal u D.P.isLB (Y := Sp ℂ) (s x') (𝟙 _) ![ct x' + z, ct x', z, 0] := by
  have a := genVal_mult h hc z x x' (s (x + x'))
  have b : genVal u D.P.isLB (Y := Sp ℂ) (LB.mulGen D.P.L _ _ _ _ (s x) (s x')) (𝟙 _)
      (Sum.elim ![ct x + z, ct x, z, 0] ![ct x' + z, ct x', z, 0]) =
      genVal u D.P.isLB (Y := Sp ℂ) (s x) (𝟙 _) ![ct x + z, ct x, z, 0] *
        genVal u D.P.isLB (Y := Sp ℂ) (s x') (𝟙 _) ![ct x' + z, ct x', z, 0] := genVal_mul D.P.isLB _ _ _ _
  have p := prod_mult (ct x) (ct x') z
  rw [← map_add] at p
  have g₁ := DVR.mulGen_isGen _ _ _ _ _ _ _ (hs (x + x')) (DVR.pullGen_isGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
    D.cub.isGen (lift (Out.DegPre.cF D ℂ x) (lift (Out.DegPre.cF D ℂ x') (pt u z))).left)
  have g₂ := DVR.mulGen_isGen _ _ _ _ _ _ _ (hs x) (hs x')
  exact ⟨fun hm => a.symm.trans ((genVal_corr D.P.isLB hm (isLift_mult hc z x x') (isLift_mult' hc z x x') p).trans b),
    fun e => corr_of_genVal D.P.isLB g₁ g₂ (isLift_mult hc z x x') (isLift_mult' hc z x x') p
      (a.trans (e.trans b.symm))⟩

theorem eq_pt {b : Out.TF (R := ℂ) ℂ ⟶ D.P.A} {z : Fin g → ℂ} (hb : (show Sp ℂ ⟶ _ from b.left) = (u.ex z).left) :
    b = pt u z := Over.OverMorphism.ext (hb.trans (toUnit_left _).symm)

end Points

theorem points_eq_characters : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g : ℕ) (u : HolUnif D.P.A D.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (ct : D.X →+ (Fin g → ℂ)), u.IsAH Hm χ → u.IsRig D.rig → (∀ x, u.ex (ct x) = D.c x) → ∀ z : Fin g → ℂ, (∀ lam : D.X →+ ℂ, ∃! p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex z).left ∧ ∀ x, FrameValue.genVal u D.P.isLB (p.s x) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![ct x + z, ct x, z, 0] = eTwoPi (lam x)) ∧ ∀ p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex z).left → ∃ lam : D.X →+ ℂ, ∀ x, FrameValue.genVal u D.P.isLB (p.s x) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![ct x + z, ct x, z, 0] = eTwoPi (lam x) := by
  intro _ _ D g u Hm χ ct h _ hc z
  refine ⟨fun lam => ?_, ?_⟩
  · choose s hs hv using fun x => exists_genVal D.P.isLB Out.DegPre.gtε (isLift_gt hc z x)
      (c := eTwoPi (lam x)) (Complex.exp_ne_zero _)
    refine ⟨⟨pt u z, s, hs, ?_, fun x x' => ?_⟩, ⟨toUnit_left _, hv⟩, ?_⟩
    · refine corr_of_genVal D.P.isLB (hs 0) (fun i j => (map_one _).trans ?_) (isLift_gt hc z 0) (z' := PEmpty.elim)
        (fun k => k.elim) (fun f => ?_) ((hv 0).trans (Eq.trans ?_ (genVal_one D.P.isLB _ _).symm))
      · exact ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
      · simp [Fin.prod_univ_four, Out.DegPre.gtε]
      · simp [eTwoPi]
    · refine (mult_iff h hc z s hs x x').2 ((hv _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (hv x) (hv x')).symm))
      simp [eTwoPi, mul_add, Complex.exp_add]
    · rintro ⟨b, s', hs', h₀, hm⟩ ⟨hb, hv'⟩
      obtain rfl : b = pt u z := eq_pt hb
      obtain rfl : s' = s := funext fun x => eq_of_genVal D.P.isLB (hs' x) (hs x) (isLift_gt hc z x)
        ((hv' x).trans (hv x).symm)
      rfl
  · rintro ⟨b, s, hs, h₀, hm⟩ hb
    obtain rfl : b = pt u z := eq_pt hb
    exact exists_log _ (fun x => genVal_ne_zero D.P.isLB _ (isLift_gt hc z x))
      fun x x' => (mult_iff h hc z s hs x x').1 (hm x x')

end GlobalTheory.TorusExtChar
