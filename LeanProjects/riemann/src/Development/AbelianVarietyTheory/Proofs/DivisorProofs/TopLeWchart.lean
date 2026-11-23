import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigValD
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanGauge

def trV {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι) (n : ℤ) : A :=
  valR y (L.U a ⊓ L.U b) ((L.g a b) ^ n).val

def pickJ {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) (i : Fin 4) : Ix :=
  jf (Classical.epsilon fun i' => φs i' = φs i)

theorem pickJ_congr {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) {i₁ i₂ : Fin 4}
    (h : φs i₁ = φs i₂) : pickJ φs jf i₁ = pickJ φs jf i₂ := by
  unfold pickJ; rw [h]

theorem pickJ_spec {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) (i : Fin 4) :
    ∃ i', φs i' = φs i ∧ pickJ φs jf i = jf i' :=
  ⟨_, Classical.epsilon_spec (p := fun i' => φs i' = φs i) ⟨i, rfl⟩, rfl⟩

theorem trV_add {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n m : ℤ) : trV L y a b n * trV L y a b m = trV L y a b (n + m) := by
  unfold trV
  rw [zpow_add, Units.val_mul, GlobalTheory.ZH.CrdCalc.valR_mul y _ h]

theorem isUnit_trV {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n : ℤ) : IsUnit (trV L y a b n) := by
  unfold trV
  rw [GlobalTheory.ZH.CrdCalc.valR_eq y _ h]
  exact (Units.isUnit _).map _

theorem top_le_wchart {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (h : ∀ k, ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ L.U (j k)) : ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j :=
  fun q _ => Set.mem_iInter.2 fun k => h k (x := q) trivial

theorem wchart_top_le {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j) (k : K) : ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ L.U (j k) :=
  fun q _ => Set.mem_iInter.1 (h (x := q) trivial) k

theorem trV_zero {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) : trV L y a b 0 = 1 := by
  unfold trV
  rw [zpow_zero, Units.val_one, GlobalTheory.ZH.CrdCalc.valR_eq y _ h, map_one]

theorem trV_pow {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n : ℤ) (m : ℕ) : trV L y a b n ^ m = trV L y a b (n * m) := by
  unfold trV
  rw [GlobalTheory.ZH.CrdCalc.valR_eq y _ h, GlobalTheory.ZH.CrdCalc.valR_eq y _ h, ← map_pow, ← Units.val_pow_eq_pow_val, ← zpow_natCast,
    ← zpow_mul]

end GlobalTheory.MBLow.TanGauge

namespace GlobalTheory.MBLow.TanGauge

theorem gl_corr : ∀ {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')),
    LB.Gen.Corr L φ ε φ' ε' t t' → ∀ (j : K → L.ι) (j' : K' → L.ι), LB.Coh L φ j → LB.Coh L φ' j' →
    (∀ k k', φ k = φ' k' → j k = j' k') → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ' j' →
    valR y (LB.wchart L φ j) (t.s j).val = valR y (LB.wchart L φ' j') (t'.s j').val := by
  intro X Y L K K' _ _ φ ε φ' ε' t t' hc j j' hj hj' hx A _ y h h'
  have hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') := fun q hq => ⟨h hq, h' hq⟩
  have e := congrArg Units.val (hc j j' hj hj' hx)
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ j) hh (t.s j).val
  have e2 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ' j') hh (t'.s j').val
  refine e1.symm.trans (Eq.trans ?_ e2)
  exact congrArg (valR y _) e

theorem gl_pullGen : ∀ {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (j : K → L.ι) {A : Type} [CommRing A] (y : Sp A ⟶ Z),
    ⊤ ≤ (y ≫ h) ⁻¹ᵁ LB.wchart L φ j →
    valR y (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε c h).s j).val = valR (y ≫ h) (LB.wchart L φ j) (c.s j).val := by
  intro X Y Z L K _ φ ε c h j A _ y hy
  have hy' : ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j :=
    top_le_wchart L _ _ _ fun k => by rw [← Category.assoc]; exact wchart_top_le L _ _ _ hy k
  have e := GlobalTheory.ZH.CrdCalc.valR_res y ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
    LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j) hy' (pullU h _ (c.s j)).val
  refine e.trans ?_
  exact GlobalTheory.ZH.EvCrd.valR_comp y h (LB.wchart L φ j) (fun q hq => hy hq) _

theorem gl_gtφT_pull : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T T' : Over (Sp R)) (h : T'.left ⟶ T.left),
    h ≫ T.hom = T'.hom → ∀ (b : T ⟶ D.P.A) (b' : T' ⟶ D.P.A), b'.left = h ≫ b.left → ∀ (α : D.X) (i : Fin 4),
    DegPre.gtφT D T' b' α i = h ≫ DegPre.gtφT D T b α i := by
  intro R _ _ D T T' h hh b b' hb α i
  have hb' : b' = Over.homMk h hh ≫ b := by
    ext; simpa using hb
  subst hb'
  fin_cases i
  · change (padd D.P.A (DegPre.cT D T' α) (Over.homMk h hh ≫ b)).left = (Over.homMk h hh : T' ⟶ T).left ≫
      (padd D.P.A (DegPre.cT D T α) b).left
    rw [← Over.comp_left]; congr 1; simp [padd, comp_lift_assoc, DegPre.cT]
  · change (toUnit T' ≫ D.c α).left = (Over.homMk h hh : T' ⟶ T).left ≫ (toUnit T ≫ D.c α).left
    rw [← Over.comp_left]; congr 1; simp
  · show (Over.homMk h hh ≫ b).left = h ≫ b.left
    simp
  · change (toUnit T' ≫ η[D.P.A]).left = (Over.homMk h hh : T' ⟶ T).left ≫ (toUnit T ≫ η[D.P.A]).left
    rw [← Over.comp_left]; congr 1; simp

theorem gl_gtφT_famφB : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Sp R)) (b : T ⟶ D.P.A) (α : D.X) (i : Fin 4),
    DegPre.gtφT D T b α i = b.left ≫ D.famφB α (![1, 2, 0, 3] i) := by
  intro R _ _ D T b α i
  have pc : ∀ (x y : T ⟶ D.P.A), padd D.P.A x y = padd D.P.A y x := fun x y => by
    show x * y = y * x
    exact mul_comm x y
  fin_cases i
  · change (padd D.P.A (DegPre.cT D T α) b).left = b.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    rw [← Over.comp_left, pc]; congr 1; simp [padd, comp_lift_assoc, DegPre.cT]
  · change (toUnit T ≫ D.c α).left = b.left ≫ (toUnit D.P.A ≫ D.c α).left
    rw [← Over.comp_left]; congr 1; simp
  · exact (Category.comp_id _).symm
  · change (toUnit T ≫ η[D.P.A]).left = b.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left
    rw [← Over.comp_left]; congr 1; simp

theorem gl_prB : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (α : D.X) (i : Fin 4),
    DegPre.famφ D C α i = (DegPre.prB D C).left ≫ D.famφB α i := by
  intro R _ _ D C _ _ α i
  fin_cases i
  · exact (Category.comp_id _).symm
  · change (padd D.P.A (DegPre.prB D C) (toUnit _ ≫ D.c α)).left =
      (DegPre.prB D C).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    rw [← Over.comp_left]; congr 1; simp [padd, comp_lift_assoc]
  · change (toUnit _ ≫ D.c α).left = (DegPre.prB D C).left ≫ (toUnit D.P.A ≫ D.c α).left
    rw [← Over.comp_left]; congr 1; simp
  · change (toUnit _ ≫ η[D.P.A]).left = (DegPre.prB D C).left ≫ (toUnit D.P.A ≫ η[D.P.A]).left
    rw [← Over.comp_left]; congr 1; simp

theorem gl_prB' : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (b : TE R C ⟶ D.P.A),
    (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ≫ (DegPre.prB D C).left =
      b.left := by
  intro R _ _ D C _ _ b
  rw [← Over.comp_left, lift_snd]

theorem gl_famφ : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (b : TE R C ⟶ D.P.A) (α : D.X) (i : Fin 4),
    (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ≫ DegPre.famφ D C α i =
      b.left ≫ D.famφB α i := by
  intro R _ _ D C _ _ b α i
  rw [gl_prB D C α i, ← Category.assoc, gl_prB' D C b]

theorem gl_scal : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (b : TE R C ⟶ D.P.A) (c : C),
    valR (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ⊤
      (scal (fst (TF (R := R) C) D.P.A).left c) = TrivSqZeroExt.inl c := by
  intro R _ _ D C _ _ b c
  have hq : (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ≫
      (fst (TF (R := R) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h := GlobalTheory.ZH.FormCount.valR_scal (algebraMap C (DualNumber C)) _ _ hq ⊤ (fun _ _ => trivial) c
  have e : resTop ⊤ (scal (fst (TF (R := R) C) D.P.A).left c) = scal (fst (TF (R := R) C) D.P.A).left c := by
    simp [resTop]
  rw [e] at h
  rw [h, TrivSqZeroExt.algebraMap_eq_inl]

theorem gl_tan : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (gm₀ : GtPt D (epsR R)), GtTan gm₀ →
    redE R ≫ gm₀.b.left = eSec D.P.A := by
  intro R _ _ D gm₀ hT
  obtain ⟨o, ⟨hb, -⟩, h1, -⟩ := hT
  rw [← h1, hb]
  have hw := Over.w (toUnit (baseOver (Sp R)))
  have e : (toUnit (baseOver (Sp R))).left = 𝟙 _ := by simpa using hw
  simp only [DegPre.zeroT, Over.comp_left, e, Category.id_comp]
  rfl

theorem gl_TF : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    (TF (R := R) C).hom = spMap (toF R C) := by
  intro R _ _ C _ _
  simp only [TF, jFK, jK, Over.mk_hom, spMap, toF, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem gl_redE : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    redE C ≫ spMap (dualMap (toF R C)) = spMap (toF R C) ≫ redE R := by
  intro R _ _ C _ _
  simp only [redE, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun z => ?_
  simp [dualMap, toF]

theorem gl_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    spMap (dualMap (toF R C)) ≫ (epsR R).hom = (TE R C).hom := by
  intro R _ _ C _ _
  simp only [TE, epsR, Over.mk_hom, gl_TF, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun z => ?_
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, toF, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.MBLow.TanGauge

end
