import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ExistsChartComplexPoint
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

noncomputable section
namespace GlobalTheory.GtAnModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArcPts GlobalTheory.ToricData GlobalTheory.ToricDict GlobalTheory.HostModel Out.Inh Out.InhTate

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

variable (l) in

def splitArc : letI := H.starRing; AnArc (𝓞 E) :=
  letI := H.starRing
  { gB := 0
    abelian₂ := ⊥
    discrete := inferInstance
    full := Subsingleton.elim _ _
    Hm := 0
    Hm_herm := Matrix.isHermitian_zero
    Hm_pos := fun z hz => absurd (Subsingleton.elim _ _) hz
    Ef := 0
    Ef_eq := fun l m => by simp [hermForm]
    Ef_bij := ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
    chi := fun _ => 1
    chi_norm := fun _ => norm_one
    chi_add := fun l m => by simp [hermForm]
    chi_neg := fun _ => rfl
    F := { toFun := fun _ => 0
           map_one' := Subsingleton.elim _ _
           map_mul' := fun _ _ => Subsingleton.elim _ _
           map_zero' := rfl
           map_add' := fun _ _ => Subsingleton.elim _ _ }
    F_mem := fun a l _ => Subsingleton.elim (α := Fin 0 → ℂ) _ _
    F_adj := fun a z w => by simp [hermForm]
    X := 𝓞 E
    ct := 0
    ct_smul := fun _ _ => Subsingleton.elim _ _
    T := 0
    T_symm := fun _ _ => rfl
    T_adj := fun _ _ _ => rfl
    psi := fun _ => 1
    psi_neg := fun _ => rfl
    psi_add := fun _ _ => by simp
    be := arcForm l
    be_symm := fun y z => congrArg ((2 * l.M' : ℤ) * ·) (trForm_symm H y z)
    be_pos := fun y hy => mul_pos (mul_pos two_pos (Int.natCast_pos.2 (LevelExist.M'_pos l))) (trForm_pos H hy)
    be_adj := fun a y z => congrArg ((2 * l.M' : ℤ) * ·) (trForm_adj H a y z)
    be_even := fun y => ⟨l.M' * trForm H y y, mul_assoc _ _ _⟩ }

instance : letI := H.starRing; IsEmpty (Fin (splitArc l).gB) := inferInstanceAs (IsEmpty (Fin 0))

theorem isTangent_zero (v : epsR ℂ ⟶ (zeroPolAV (Sp ℂ)).A) : IsTangent v := by
  have h : v.left = spMap (algebraMap ℂ (DualNumber ℂ)) := (Category.comp_id _).symm.trans (Over.w v)
  have h' : η[(zeroPolAV (Sp ℂ)).A].left = 𝟙 (Sp ℂ) :=
    (Category.comp_id _).symm.trans (Over.w η[(zeroPolAV (Sp ℂ)).A])
  unfold IsTangent
  rw [h, h']
  refine (Spec.map_comp _ _).symm.trans ?_
  exact Spec.map_id _

theorem isDiff_zero {O : Type} [CommRing O] [StarRing O] (A : AnArc O) [IsEmpty (Fin A.gB)] (w : Fin A.gB → ℂ)
    (v : epsR ℂ ⟶ (zeroPolAV (Sp ℂ)).A) : (zeroUnif A).IsDiff w v := by
  intro U h f
  have hv : v.left ≫ 𝟙 (Sp ℂ) = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w v
  obtain rfl : w = 0 := Subsingleton.elim _ _
  rw [map_zero]
  have hf : f = constFn (𝟙 (Sp ℂ)) U (valAt' (𝟙 (Sp ℂ)) U f) := by
    refine ComplexPoints.eq_of_valAt'_eq (𝟙 (Sp ℂ)) _ _ _ fun x hx hU => ?_
    obtain rfl : x = 𝟙 _ := (Category.comp_id _).symm.trans hx
    exact (valAt'_constFn _ _ (Category.comp_id _) _ _ hU).symm
  have e := GlobalTheory.Points.valR_constFn_of_over (𝟙 (Sp ℂ)) (algebraMap ℂ (DualNumber ℂ)) v.left hv U h (valAt' (𝟙 (Sp ℂ)) U f)
  have e' := (congrArg (valR v.left U) hf).trans e
  unfold valR at e'
  rw [dif_pos h] at e'
  exact (congrArg TrivSqZeroExt.snd e').trans rfl

variable (c : Coeff l) (bF : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

def model : letI := H.starRing; GtAn (arcIn c ℂ bF) :=
  letI := H.starRing
  let d := dict (splitArc l) (fun _ => 1) (fun _ => by simp [splitArc]) (polar_one_smul ℂ)
  { star_eq := rfl
    A := splitArc l
    ε := LinearEquiv.refl _ _
    be_eq := fun _ _ => rfl
    gB_eq := rfl
    u := zeroUnif (splitArc l)
    lam := rfl
    ah := d.isAH
    rig := d.isRig
    tan := ⟨fun v _ => ⟨0, isDiff_zero _ _ _, fun _ _ => Subsingleton.elim _ _⟩,
      fun w => ⟨toUnit _, ⟨isTangent_zero _, isDiff_zero _ _ _⟩, fun _ _ => toUnit_unique _ _⟩⟩
    pow := fun n => by
      have hθ : ∀ θ, (zeroUnif (splitArc l)).IsThetaFn (splitArc l).Hm (fun m => (splitArc l).chi ⟨m.1, m.2⟩) n θ :=
        fun θ => ⟨(mem_Theta (splitArc l) n 0 θ).1, fun m z => by
          have := (mem_Theta (splitArc l) n 0 θ).2 ⟨m.1, m.2⟩ z
          rw [map_zero, AnArc.H_zero_left, mul_zero, Complex.exp_zero, _root_.mul_one] at this
          exact this⟩
      have key : ∀ s θ, (zeroUnif (splitArc l)).IsFnPow n s θ ↔
          valAt' (𝟙 (Sp ℂ)) _ (s.f fun _ => PUnit.unit) = θ 0 := fun s θ =>
        ⟨fun h => (h (fun _ => PUnit.unit) 0 (wchart_triv _ _).ge).trans (by simp [zeroUnif]), fun h j z _ => by
          obtain rfl : z = 0 := Subsingleton.elim (α := Fin 0 → ℂ) _ _
          exact h.trans (by simp [zeroUnif])⟩
      refine ⟨fun s => ⟨fun _ => _, ⟨hθ _, (key _ _).2 rfl⟩, fun θ h => funext fun z => ?_⟩, fun θ _ => ?_⟩
      · obtain rfl : z = 0 := Subsingleton.elim (α := Fin 0 → ℂ) _ _
        exact ((key _ _).1 h.2).symm
      · have hc : ∀ i, valAt' (𝟙 (Sp ℂ)) ((lbPow (zeroPolAV (Sp ℂ)).L n).U i) (constFn (𝟙 (Sp ℂ)) _ (θ 0)) = θ 0 :=
          fun i => valAt'_constFn _ _ (Category.comp_id _) _ _ (wchart_triv _ _).ge
        refine ⟨⟨fun i => constFn (𝟙 (Sp ℂ)) _ (θ 0), fun i i' => ?_⟩, (key _ _).2 (hc _), ?_⟩
        · obtain rfl : i = i' := funext fun _ => rfl
          erw [linComb_triv_g]
          exact (_root_.one_mul _).symm
        · rintro ⟨f, hf⟩ h
          congr 1
          funext i
          refine ComplexPoints.eq_of_valAt'_eq (𝟙 (Sp ℂ)) _ _ _ fun x hx _ => ?_
          obtain rfl : x = 𝟙 _ := (Category.comp_id _).symm.trans hx
          exact ((key _ _).1 h).trans (hc _).symm
    act := fun _ _ => toUnit_unique _ _
    ct := fun _ => toUnit_unique _ _
    psi := fun x => by
      refine (congrArg₂ (· / ·) (d.psi_val x _ le_top) (frameProd_zeroUnif (splitArc l) _ _ _)).trans ?_
      change (1 : ℂ) * (1 : ℂ)⁻¹ / 1 = 1
      simp
    ex0 := d.ex₀
    ex0_b := d.ex₀_b_left
    arcDict_expZero_section := fun v x => by
      refine (congrArg₂ (· / ·) (valAt'_gv_unitOn _ (wchart_triv _ _).ge) (frameProd_zeroUnif (splitArc l) _ _ _)).trans ?_
      exact div_one _ }

end Model

example : letI := host.starRing
    letI : Algebra (FractionRing ℂ) ℂ := (FractionRing.algEquiv ℂ ℂ).toRingHom.toAlgebra
    Nonempty (GtAn (arcIn (coeff (level host 5 (by norm_num))) ℂ (coeff _).F.val.toRingHom)) := by
  letI : Algebra (FractionRing ℂ) ℂ := (FractionRing.algEquiv ℂ ℂ).toRingHom.toAlgebra
  haveI : IsScalarTower ℂ (FractionRing ℂ) ℂ :=
    IsScalarTower.of_algebraMap_eq fun x => ((FractionRing.algEquiv ℂ ℂ).commutes x).symm
  exact ⟨model _ _⟩

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
  {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  [Algebra (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn a)

open FrameValue

include Λ in

theorem isScalarTower : IsScalarTower ℂ (FractionRing ℂ) ℂ := by
  have h : Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ = 𝟙 (Sp ℂ) :=
    (Over.w (Λ.ex0 0).b).symm.trans ((congrArg (· ≫ a.D₀.P.A.hom) (Λ.ex0_b 0)).trans (Over.w (Λ.u.ex _)))
  rw [← Spec.map_comp, ← Spec.map_id] at h
  have h' := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  exact IsScalarTower.of_algebraMap_eq' h'.symm

theorem ex_zero : Λ.u.ex 0 = η[a.D₀.P.A] := by
  rw [(Λ.u.ker 0).2 (zero_mem _), Hom.one_def, toUnit_unit, Category.id_comp]

theorem isLift_fam (z : Fin Λ.A.gB → ℂ) (α : Λ.A.X) :
    IsLift Λ.u (a.D₀.famφB (Λ.ε α)) (Λ.u.ex z).left ![z, z + Λ.A.ct α, Λ.A.ct α, 0] := fun k => by
  have h : ∀ p : 𝟙_ (Over (Sp ℂ)) ⟶ a.D₀.P.A, Λ.u.ex z ≫ toUnit a.D₀.P.A ≫ p = p := fun p => by
    rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  fin_cases k
  · exact Category.comp_id _
  · change (Λ.u.ex z ≫ (𝟙 a.D₀.P.A * toUnit _ ≫ a.D₀.c (Λ.ε α))).left = (Λ.u.ex (z + Λ.A.ct α)).left
    rw [MonObj.comp_mul, h, Category.comp_id, Λ.u.ex_add, Λ.ct]
  · change (Λ.u.ex z ≫ toUnit _ ≫ a.D₀.c (Λ.ε α)).left = (Λ.u.ex (Λ.A.ct α)).left
    rw [h, Λ.ct]
  · change (Λ.u.ex z ≫ toUnit _ ≫ η[a.D₀.P.A]).left = (Λ.u.ex 0).left
    rw [h, ex_zero]

theorem fn_mem_Theta (j : ℕ) (α : Λ.A.X) (s : a.D₀.SecB j (Λ.ε α)) : Λ.fn j α s ∈ Λ.A.Theta j α := by
  refine ⟨?_, fun m z => ?_⟩
  · have := differentiable_secVal (u := Λ.u) a.D₀.P.isLB s (𝟙 _) (q := id) differentiable_id
      (z := fun z => ![z, z + Λ.A.ct α, Λ.A.ct α, 0]) (fun k => by fin_cases k <;> simp <;> fun_prop)
      (fun w => by rw [id, Category.comp_id]; exact isLift_fam Λ w α)
    simp only [id, Category.comp_id] at this
    exact this
  · let m' : Λ.u.Λ := ⟨m, Λ.lam.ge m.2⟩
    have e₁ : Λ.u.ex (z + m) = Λ.u.ex z := by rw [Λ.u.ex_add, (Λ.u.ker m).2 m'.2, _root_.mul_one]
    have e₂ : ![z + m, z + m + Λ.A.ct α, Λ.A.ct α, 0] = fun k => ![z, z + Λ.A.ct α, Λ.A.ct α, 0] k +
        ((![m', m', 0, 0] : Fin 4 → Λ.u.Λ) k : Fin Λ.A.gB → ℂ) := by
      funext k
      fin_cases k <;> simp [m'] <;> abel
    rw [GtAn.fn, GtAn.fn, e₁, e₂, secVal_add_period _ Λ.ah s (isLift_fam Λ z α)]
    congr 1
    have n := Λ.A.ah_ne_zero m z
    simp only [Fin.prod_univ_four, Out.DegPre.famε, Matrix.cons_val, ahFactor_zero a.D₀.P.isLB Λ.ah]
    change Λ.A.ah m z ^ ((j : ℤ) - 1) * Λ.A.ah m (z + Λ.A.ct α) ^ (1 : ℤ) * _ * _ = _
    rw [AnArc.ah_add, zpow_sub₀ n]
    simp
    field_simp

theorem analyticTorusPoint_base_eq_holUnif_ex (v : Λ.A.V) : (Λ.ex0 v).b = toUnit _ ≫ Λ.u.ex v.2 := by
  haveI := isScalarTower Λ
  exact Over.OverMorphism.ext ((Λ.ex0_b v).trans (toUnit_TF_comp_left _).symm)

theorem isLift_gt (v : Λ.A.V) (x : Λ.A.X) :
    IsLift Λ.u (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 v).b (Λ.ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
      ![Λ.A.ct x + v.2, Λ.A.ct x, v.2, 0] := fun k => by
  haveI := isScalarTower Λ
  refine (Category.id_comp _).trans ?_
  fin_cases k
  · refine Eq.trans ?_ (toUnit_TF_comp_left _)
    change (toUnit _ ≫ a.D₀.c (Λ.ε x) * (Λ.ex0 v).b).left = (toUnit _ ≫ Λ.u.ex (Λ.A.ct x + v.2)).left
    rw [analyticTorusPoint_base_eq_holUnif_ex, Λ.u.ex_add, MonObj.comp_mul, Λ.ct]
  · exact (toUnit_TF_comp_left _).trans (congrArg (·.left) (Λ.ct x).symm)
  · exact Λ.ex0_b v
  · exact (toUnit_TF_comp_left _).trans (congrArg (·.left) (ex_zero Λ).symm)

theorem corr_of_genVal {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Sp ℂ ⟶ A.left)} {ε : K → ℤ} {φ' : K' → (Sp ℂ ⟶ A.left)}
    {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen)
    {z : K → Fin g → ℂ} {z' : K' → Fin g → ℂ} (hz : IsLift u φ (𝟙 _) z) (hz' : IsLift u φ' (𝟙 _) z')
    (hs : ∀ f : (Fin g → ℂ) → ℂˣ, ∏ k, f (z k) ^ ε k = ∏ k, f (z' k) ^ ε' k)
    (h : genVal u hL t (𝟙 _) z = genVal u hL t' (𝟙 _) z') : LB.Gen.Corr L φ ε φ' ε' t t' := by
  classical
  intro j j' c₁ c₂ c₃
  refine Units.ext (ComplexPoints.eq_of_valAt'_eq (𝟙 (Sp ℂ)) _ _ _ fun x hx hW => ?_)
  obtain rfl : x = 𝟙 _ := (Category.comp_id _).symm.trans hx
  have h₁ : ⊤ ≤ 𝟙 (Sp ℂ) ⁻¹ᵁ L.wchart φ j := hW.trans inf_le_left
  have h₂ : ⊤ ≤ 𝟙 (Sp ℂ) ⁻¹ᵁ L.wchart φ' j' := hW.trans inf_le_right
  refine (valAt'_res _ inf_le_left _ hW).trans (Eq.trans ?_ (valAt'_res _ inf_le_right _ hW).symm)
  rw [valAt'_gen hL ht hz h₁, valAt'_gen hL ht' hz' h₂, h]
  congr 1
  have hφ : ∀ k, φ k = (u.ex (z k)).left := fun k => (Category.id_comp _).symm.trans (hz k)
  have hφ' : ∀ k, φ' k = (u.ex (z' k)).left := fun k => (Category.id_comp _).symm.trans (hz' k)
  let idx : (Sp ℂ ⟶ A.left) → L.ι := fun p =>
    if h : ∃ k, φ k = p then j h.choose else if h : ∃ k, φ' k = p then j' h.choose else chartAt hL p
  have i₁ : ∀ k, idx (φ k) = j k := fun k => by
    have e : ∃ k', φ k' = φ k := ⟨k, rfl⟩
    simp only [idx, dif_pos e]
    exact c₁ _ _ e.choose_spec
  have i₂ : ∀ k, idx (φ' k) = j' k := fun k => by
    have e : ∃ k', φ' k' = φ' k := ⟨k, rfl⟩
    by_cases e' : ∃ k', φ k' = φ' k
    · simp only [idx, dif_pos e']
      exact c₃ _ _ e'.choose_spec
    · simp only [idx, dif_neg e', dif_pos e]
      exact c₂ _ _ e.choose_spec
  have hi : ∀ w, u.fr (idx (u.ex w).left) w ≠ 0 := fun w => u.fr_ne _ _ (by
    by_cases e : ∃ k, φ k = (u.ex w).left
    · obtain ⟨k, hk⟩ := e
      rw [← hk, i₁, hφ]; exact (hz.le_iff j).1 h₁ k
    · by_cases e' : ∃ k, φ' k = (u.ex w).left
      · obtain ⟨k, hk⟩ := e'
        rw [← hk, i₂, hφ']; exact (hz'.le_iff j').1 h₂ k
      · simp only [idx, dif_neg e, dif_neg e']
        exact le_chartAt hL _)
  have := congrArg (Units.coeHom ℂ) (hs fun w => Units.mk0 _ (hi w))
  simp only [map_prod, map_zpow, Units.coeHom_apply, Units.val_mk0, ← hφ, ← hφ', i₁, i₂] at this
  exact this

theorem genVal_mul_of {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g} {hL : L.IsLB}
    {Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ A.left)} {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} {z' : K' → Fin g → ℂ} {p q : ℂ} (h : genVal u hL t y z = p)
    (h' : genVal u hL t' y z' = q) : genVal u hL (LB.mulGen L φ ε φ' ε' t t') y (Sum.elim z z') = p * q :=
  (genVal_mul hL t t' y _).trans (congrArg₂ (· * ·) h h')

theorem genVal_inv_of {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g} {hL : L.IsLB}
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} {p : ℂ} (h : genVal u hL t y z = p) :
    genVal u hL (LB.invGen L φ ε t) y z = p⁻¹ :=
  (genVal_inv hL t y _).trans (congrArg (·⁻¹) h)

theorem genVal_pull_of {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g} {hL : L.IsLB}
    {Y Y' : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {f : Y' ⟶ Y} {y : Sp ℂ ⟶ Y'} {y' : Sp ℂ ⟶ Y} (e : y ≫ f = y') {z : K → Fin g → ℂ} {p : ℂ}
    (h : genVal u hL t y' z = p) : genVal u hL (LB.pullGen L φ ε t f) y z = p :=
  (genVal_pull hL t f y z).trans (e ▸ h)

theorem genVal_shift (v : Λ.A.V) (z : Fin Λ.A.gB → ℂ) (m : Λ.A.abelian₂) (hv : v.2 = z + m) (x : Λ.A.X) :
    IsLift Λ.u (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 v).b (Λ.ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
      ![Λ.A.ct x + z, Λ.A.ct x, z, 0] ∧
    genVal Λ.u a.D₀.P.isLB ((Λ.ex0 v).s (Λ.ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![Λ.A.ct x + z, Λ.A.ct x, z, 0] =
      eTwoPi (v.1 x + Λ.A.H (Λ.A.ct x) m / (2 * Complex.I)) := by
  let m' : Λ.u.Λ := ⟨m, Λ.lam.ge m.2⟩
  have e₂ : ![Λ.A.ct x + v.2, Λ.A.ct x, v.2, 0] = fun k => ![Λ.A.ct x + z, Λ.A.ct x, z, 0] k +
      ((![m', 0, m', 0] : Fin 4 → Λ.u.Λ) k : Fin Λ.A.gB → ℂ) := by
    funext k
    fin_cases k <;> simp [m', hv, add_assoc]
  have hz : IsLift Λ.u (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 v).b (Λ.ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
      ![Λ.A.ct x + z, Λ.A.ct x, z, 0] := fun k => by
    refine (isLift_gt Λ v x k).trans ?_
    rw [e₂]
    beta_reduce
    rw [Λ.u.ex_add, (Λ.u.ker _).2 (Subtype.prop _), _root_.mul_one]
  refine ⟨hz, ?_⟩
  have h := Λ.arcDict_expZero_section v x
  rw [e₂] at h
  have h' := (genVal_add_period a.D₀.P.isLB Λ.ah _ hz _).symm.trans h
  simp only [Fin.prod_univ_four, Out.DegPre.gtε, Matrix.cons_val, ahFactor_zero a.D₀.P.isLB Λ.ah] at h'
  change Λ.A.ah m (Λ.A.ct x + z) ^ (-1 : ℤ) * _ * Λ.A.ah m z ^ (1 : ℤ) * _ * _ = _ at h'
  have n := Λ.A.ah_ne_zero m z
  have e₃ : eTwoPi (Λ.A.H (Λ.A.ct x) m / (2 * Complex.I)) = Complex.exp (Real.pi * Λ.A.H (Λ.A.ct x) m) := by
    have := AnArc.e_neg_div (-Λ.A.H (Λ.A.ct x) m)
    simpa [neg_div] using this
  rw [add_comm (Λ.A.ct x) z, AnArc.ah_add] at h'
  rw [AnArc.e_add, e₃, ← h', add_comm (Λ.A.ct x) z]
  simp
  field_simp
  rfl

theorem isZero_iff (v : Λ.A.V) : (Λ.ex0 v).IsZero ↔ ∃ la : Λ.A.La, la.y = 0 ∧ v = Λ.A.P0 la := by
  haveI := isScalarTower Λ
  constructor
  · rintro ⟨hb, hs⟩
    have h0 : Λ.u.ex v.2 = 1 := Over.OverMorphism.ext ((Λ.ex0_b v).symm.trans ((congrArg (·.left) hb).trans
      ((toUnit_TF_comp_left _).trans (by rw [Hom.one_def, toUnit_unit, Category.id_comp]))))
    let m : Λ.A.abelian₂ := ⟨v.2, Λ.lam.le ((Λ.u.ker _).1 h0)⟩
    let w : Λ.A.V := v - Λ.A.P0 (AnArc.La.mk 0 0 m)
    obtain ⟨n, hn⟩ := (expChar_eq_one_iff w.1).1 (MonoidHom.ext fun x => Units.ext (by
      obtain ⟨hz, h⟩ := genVal_shift Λ v 0 m (zero_add _).symm x.toAdd
      have := genVal_corr a.D₀.P.isLB (hs _) hz (z' := PEmpty.elim) (fun k => k.elim)
        (fun f => by simp [Fin.prod_univ_four, Out.DegPre.gtε])
      have e := h.symm.trans (this.trans (genVal_one (u := Λ.u) _ _ _))
      change eTwoPi (w.1 x.toAdd) = 1
      simpa [w] using e))
    refine ⟨AnArc.La.mk 0 n m, rfl, Prod.ext (AddMonoidHom.ext fun x => ?_) (by simp [m])⟩
    have := hn x
    simp [w] at this
    simp [← this]
  · rintro ⟨la, hy, rfl⟩
    have hv : (Λ.A.P0 la).2 = 0 + la.l := by simp [hy]
    refine ⟨by rw [analyticTorusPoint_base_eq_holUnif_ex, hv, zero_add, (Λ.u.ker _).2 (Λ.lam.ge la.l.2), Hom.one_def, toUnit_unit, Category.id_comp], fun x => ?_⟩
    obtain ⟨x, rfl⟩ := Λ.ε.surjective x
    obtain ⟨hz, h⟩ := genVal_shift Λ _ 0 la.l hv x
    refine corr_of_genVal (u := Λ.u) a.D₀.P.isLB ((Λ.ex0 _).isGen _) (fun i j => ?_) hz
      (z' := PEmpty.elim) (fun k => k.elim) (fun f => ?_) ?_
    · exact (map_one _).trans ((_root_.mul_one _).symm.trans (congrArg₂ (· * ·) rfl (map_one _).symm))
    · simp [Fin.prod_univ_four, Out.DegPre.gtε]
    · exact h.trans (Eq.trans (by simp [hy]) (genVal_one (u := Λ.u) _ _ _).symm)

theorem isIota (la : Λ.A.La) : Out.GtPtF.IsIota (Λ.ε la.y) (Λ.ex0 (Λ.A.P0 la)) := by
  haveI := isScalarTower Λ
  refine ⟨by rw [analyticTorusPoint_base_eq_holUnif_ex, AnArc.degeneratingTori_basePeriodMap_snd, Λ.u.ex_add, (Λ.u.ker _).2 (Λ.lam.ge la.l.2), _root_.mul_one, Λ.ct], fun x => ?_⟩
  obtain ⟨x, rfl⟩ := Λ.ε.surjective x
  obtain ⟨hz, h⟩ := genVal_shift Λ _ _ la.l (Λ.A.degeneratingTori_basePeriodMap_snd la) x
  have hc : ∀ y : Λ.A.X, 𝟙 (Sp ℂ) ≫ Out.jFK (R := ℂ) ℂ ≫ a.D₀.xK (Λ.ε y) = (Λ.u.ex (Λ.A.ct y)).left := fun y => by
    rw [Category.id_comp, Λ.ct]
    change Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ ≫ _ = _
    rw [← Category.assoc, jFK_comp_jK_complex, Category.id_comp]
  refine corr_of_genVal (u := Λ.u) a.D₀.P.isLB ((Λ.ex0 _).isGen _) ?_ hz
    (z' := Sum.elim (Sum.elim (Sum.elim (fun _ => Λ.A.ct (la.y + x)) (fun _ => Λ.A.ct la.y)) (fun _ => Λ.A.ct x))
      (fun _ => 0)) ?_ (fun f => ?_) ?_
  · exact DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (a.D₀.psi_gen _) (DVR.invGen_isGen _ _ _ _ (a.D₀.psi_gen _)))
      (DVR.invGen_isGen _ _ _ _ (a.D₀.psi_gen _)))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ a.D₀.rig_gen _))) _
  · rintro (((k | k) | k) | k)
    · exact (by rw [map_add]; rfl : _ = 𝟙 (Sp ℂ) ≫ Out.jFK (R := ℂ) ℂ ≫ a.D₀.xK (Λ.ε (la.y + x))).trans (hc _)
    · exact hc _
    · exact hc _
    · change 𝟙 (Sp ℂ) ≫ Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ ≫ eSec a.D₀.P.A = (Λ.u.ex 0).left
      rw [Category.id_comp, ← Category.assoc, jFK_comp_jK_complex, Category.id_comp, ex_zero]
      rfl
  · simp [Fin.prod_univ_four, Out.DegPre.gtε, Fintype.prod_sum_type, add_comm]
    ac_rfl
  · have h1 := Λ.psi (la.y + x)
    rw [map_add Λ.ε] at h1
    have hr := genVal_pull_of (f := (toUnit (Out.TK ℂ)).left) (y := Out.jFK (R := ℂ) ℂ) jFK_comp_jK_complex
      (genVal_rig a.D₀.P.isLB Λ.rig)
    have h2 := genVal_pull_of (Category.id_comp (Out.jFK (R := ℂ) ℂ)) (genVal_mul_of (genVal_mul_of
      (genVal_mul_of h1 (genVal_inv_of (Λ.psi la.y))) (genVal_inv_of (Λ.psi x))) (genVal_inv_of hr))
    refine h.trans (Eq.trans ?_ h2.symm)
    have n1 := (Λ.A.psi la.y).ne_zero
    have n2 := (Λ.A.psi x).ne_zero
    simp [Λ.A.psi_add, AnArc.e_add]
    field_simp

theorem isAdd (v v' : Λ.A.V) : (Λ.ex0 v).IsAdd (Λ.ex0 v') (Λ.ex0 (v + v')) := by
  haveI := isScalarTower Λ
  refine ⟨by rw [analyticTorusPoint_base_eq_holUnif_ex, analyticTorusPoint_base_eq_holUnif_ex, analyticTorusPoint_base_eq_holUnif_ex, Prod.snd_add, Λ.u.ex_add, MonObj.comp_mul]; rfl, fun x => ?_⟩
  obtain ⟨x, rfl⟩ := Λ.ε.surjective x
  have hp : 𝟙 (Sp ℂ) ≫ (lift (Out.DegPre.cF a.D₀ ℂ (Λ.ε x)) (lift (Λ.ex0 v).b (Λ.ex0 v').b)).left =
      (CubeValues.pt3 Λ.u ![Λ.A.ct x, v.2, v'.2]).left := by
    rw [Category.id_comp, analyticTorusPoint_base_eq_holUnif_ex, analyticTorusPoint_base_eq_holUnif_ex, Out.DegPre.cF, ← Λ.ct, ← comp_lift, ← comp_lift]
    exact toUnit_TF_comp_left _
  refine corr_of_genVal (u := Λ.u) a.D₀.P.isLB
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ((Λ.ex0 _).isGen _) (DVR.pullGen_isGen _ _ _ _ a.D₀.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ((Λ.ex0 _).isGen _) ((Λ.ex0 _).isGen _))
    (z := Sum.elim ![Λ.A.ct x + (v + v').2, Λ.A.ct x, (v + v').2, 0] (cubeLift ![Λ.A.ct x, v.2, v'.2]))
    (z' := Sum.elim ![Λ.A.ct x + v.2, Λ.A.ct x, v.2, 0] ![Λ.A.ct x + v'.2, Λ.A.ct x, v'.2, 0]) ?_ ?_ (fun f => ?_) ?_
  · rintro (k | k)
    · exact isLift_gt Λ _ x k
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hp).trans (isLift_cube Λ.u _ k))
  · rintro (k | k)
    · exact isLift_gt Λ _ x k
    · exact isLift_gt Λ _ x k
  · erw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    erw [show ∏ I : thK, f (cubeLift ![Λ.A.ct x, v.2, v'.2] I) ^ thε I = _ from
      prod_thK fun I => f (∑ a ∈ I, ![Λ.A.ct x, v.2, v'.2] a)]
    simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val, Fin.prod_univ_four,
      Out.DegPre.gtε, zpow_neg, zpow_one, Prod.snd_add, add_assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have h1 := genVal_mul_of (Λ.arcDict_expZero_section (v + v') x) (genVal_pull_of hp
      (genVal_cube_of_face a.D₀.P.isLB Λ.ah _ a.D₀.cub.isGen (a.D₀.cub.face 0) _))
    have h2 := genVal_mul_of (Λ.arcDict_expZero_section v x) (Λ.arcDict_expZero_section v' x)
    refine h1.trans (Eq.trans ?_ h2.symm)
    simp [AnArc.e_add]

theorem analyticTorusPoint_surjective : Function.Surjective Λ.ex0 := by
  haveI := isScalarTower Λ
  intro g
  obtain ⟨z, hz⟩ := Λ.u.ex_onto (Over.homMk (show Sp ℂ ⟶ _ from g.b.left) ((Over.w g.b).trans jFK_comp_jK_complex))
  have hb : ∀ w : Λ.A.X →+ ℂ, (Λ.ex0 (w, z)).b = g.b := fun w =>
    Over.OverMorphism.ext ((Λ.ex0_b _).trans (congrArg (·.left) hz))
  have hl : ∀ x, IsLift Λ.u (Out.DegPre.gtφ a.D₀ ℂ g.b (Λ.ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
      ![Λ.A.ct x + z, Λ.A.ct x, z, 0] := fun x => hb 0 ▸ isLift_gt Λ (0, z) x
  let t : Multiplicative Λ.A.X →* ℂˣ := MonoidHom.mk'
    (fun x => Units.mk0 _ (genVal_ne_zero a.D₀.P.isLB (g.s (Λ.ε x.toAdd)) (hl x.toAdd))) fun x' y' => Units.ext (by
      let x := x'.toAdd
      let y := y'.toAdd
      have hp : 𝟙 (Sp ℂ) ≫ (lift (Out.DegPre.cF a.D₀ ℂ (Λ.ε x)) (lift (Out.DegPre.cF a.D₀ ℂ (Λ.ε y)) g.b)).left =
          (CubeValues.pt3 Λ.u ![Λ.A.ct x, Λ.A.ct y, z]).left := by
        rw [Category.id_comp, ← hb 0, analyticTorusPoint_base_eq_holUnif_ex, Out.DegPre.cF, Out.DegPre.cF, ← Λ.ct, ← Λ.ct, ← comp_lift, ← comp_lift]
        exact toUnit_TF_comp_left _
      have hm := g.mult (Λ.ε x) (Λ.ε y)
      rw [← map_add Λ.ε] at hm
      have h0 := genVal_corr (u := Λ.u) a.D₀.P.isLB hm (y := 𝟙 (Sp ℂ))
        (z := Sum.elim ![Λ.A.ct (x + y) + z, Λ.A.ct (x + y), z, 0] (cubeLift ![Λ.A.ct x, Λ.A.ct y, z]))
        (z' := Sum.elim ![Λ.A.ct x + z, Λ.A.ct x, z, 0] ![Λ.A.ct y + z, Λ.A.ct y, z, 0])
        (by
          rintro (k | k)
          · exact hl _ k
          · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hp).trans (isLift_cube Λ.u _ k)))
        (by
          rintro (k | k)
          · exact hl _ k
          · exact hl _ k)
        (fun f => by
          erw [Fintype.prod_sum_type, Fintype.prod_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr]
          erw [show ∏ I : thK, f (cubeLift ![Λ.A.ct x, Λ.A.ct y, z] I) ^ thε I = _ from
            prod_thK fun I => f (∑ a ∈ I, ![Λ.A.ct x, Λ.A.ct y, z] a)]
          simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val, Fin.prod_univ_four,
            Out.DegPre.gtε, zpow_neg, zpow_one, map_add]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel)
      have h1 := genVal_mul_of (rfl : genVal Λ.u a.D₀.P.isLB (g.s (Λ.ε (x + y))) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
        ![Λ.A.ct (x + y) + z, Λ.A.ct (x + y), z, 0] = _) (genVal_pull_of hp
        (genVal_cube_of_face a.D₀.P.isLB Λ.ah _ a.D₀.cub.isGen (a.D₀.cub.face 0) _))
      have h2 := genVal_mul_of (rfl : genVal Λ.u a.D₀.P.isLB (g.s (Λ.ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
        ![Λ.A.ct x + z, Λ.A.ct x, z, 0] = _) (rfl : genVal Λ.u a.D₀.P.isLB (g.s (Λ.ε y))
        (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![Λ.A.ct y + z, Λ.A.ct y, z, 0] = _)
      exact (_root_.mul_one _).symm.trans (h1.symm.trans (h0.trans h2)))
  obtain ⟨w, hw⟩ := expChar_surjective t
  refine ⟨(w, z), TorusExt.gt_ext (hb w) fun x => ?_⟩
  obtain ⟨x, rfl⟩ := Λ.ε.surjective x
  exact corr_of_genVal (u := Λ.u) a.D₀.P.isLB ((Λ.ex0 _).isGen _) (g.isGen _) (isLift_gt Λ (w, z) x) (hl x)
    (fun _ => rfl) ((Λ.arcDict_expZero_section _ x).trans (congrArg Units.val (DFunLike.congr_fun hw (Multiplicative.ofAdd x))))

theorem rep_iff (k : ℕ) (p : Out.QkPt a.D₀ (FractionRing ℂ) k) (la : Λ.A.La) :
    Λ.Rep k p la ↔ ∃ q : Out.QkPt a.D₀ ℂ k, QkExt (algebraMap _ ℂ) p q ∧ q.y = Λ.ε la.y ∧
      q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 la) := by
  obtain ⟨q, hq, hu⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ)
    (RingHom.ext fun _ => rfl) p
  exact ⟨fun h => ⟨q, hq, h q hq⟩, fun ⟨q', hq', h⟩ q'' hq'' => (hu _ hq'').trans (hu _ hq').symm ▸ h⟩

end General

section Bridge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b}

open FrameValue

theorem gtAct (Λ : letI := H.starRing; GtAn a) (r : 𝓞 E) (v : letI := H.starRing; Λ.A.V) :
    letI := H.starRing; GtAct a.oa r (Λ.ex0 v) (Λ.ex0 (Λ.A.actV r v)) := by
  letI := H.starRing
  refine ⟨by rw [analyticTorusPoint_base_eq_holUnif_ex, analyticTorusPoint_base_eq_holUnif_ex, AnArc.actV_snd, Λ.act, Category.assoc], fun w hw h₀ x => ?_⟩
  obtain ⟨x, rfl⟩ := Λ.ε.surjective x
  have hp : 𝟙 (Sp ℂ) ≫ (lift (Out.DegPre.cF a.D₀ ℂ (Λ.ε x)) (Λ.ex0 v).b).left =
      (lift (Λ.u.ex (Λ.A.ct x)) (Λ.u.ex v.2)).left := by
    rw [Category.id_comp, analyticTorusPoint_base_eq_holUnif_ex, Out.DegPre.cF, ← Λ.ct, ← comp_lift]
    exact toUnit_TF_comp_left _
  rw [← map_smul Λ.ε]
  refine corr_of_genVal (u := Λ.u) a.D₀.P.isLB
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ((Λ.ex0 _).isGen _) (DVR.pullGen_isGen _ _ _ _ hw _)) ((Λ.ex0 _).isGen _)
    (z := Sum.elim ![Λ.A.ct (star r • x) + v.2, Λ.A.ct (star r • x), v.2, 0]
      (rosatiLift (Λ.A.F (star r)) (Λ.A.F r) (Λ.A.ct x) v.2)) ?_ (isLift_gt Λ _ x) (fun f => ?_) ?_
  · rintro (k | k)
    · exact isLift_gt Λ _ _ k
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hp).trans
        (isLift_rosati (Λ.act (star r)) (Λ.act r) _ _ k))
  · erw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, Fin.prod_univ_six, rosatiLift, Out.rosatiε,
      Out.DegPre.gtε, Matrix.cons_val, zpow_neg, zpow_one, Λ.A.ct_smul, AnArc.actV_snd]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have h1 := genVal_mul_of (Λ.arcDict_expZero_section v (star r • x)) (genVal_pull_of hp
      ((genVal_rosati a.D₀.P.isLB Λ.ah (Λ.act (star r)) (Λ.act r) w hw h₀).2 _ _))
    exact h1.trans ((_root_.mul_one _).trans (Λ.arcDict_expZero_section (Λ.A.actV r v) x).symm)

def toDict (Λ : letI := H.starRing; GtAn a) : letI := H.starRing; GtDict a.D₀ a.oa :=
  letI := H.starRing
  { A := Λ.A
    eX := Λ.ε
    u := Λ.u
    lam_eq := Λ.lam
    isAH := Λ.ah
    isRig := Λ.rig
    ex_act := Λ.act
    ex_ct := Λ.ct
    psi_val := fun x j hj => by
      have hz : IsLift Λ.u (fun _ : PUnit => Out.ptK (a.D₀.c (Λ.ε x))) (Out.jFK (R := ℂ) ℂ) fun _ => Λ.A.ct x :=
        fun _ => by
          rw [Λ.ct]
          change Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ ≫ _ = _
          rw [← Category.assoc, jFK_comp_jK_complex, Category.id_comp]
      refine (valAt'_gen a.D₀.P.isLB (a.D₀.psi_gen _) hz ((hz.le_iff j).2 fun _ => hj)).trans ?_
      rw [Λ.psi, FrameValue.frameProd, Fintype.prod_unique, zpow_neg, zpow_one]
    ex₀ := Λ.ex0
    ex₀_b := analyticTorusPoint_base_eq_holUnif_ex Λ
    chi_val := fun v x j hj =>
      (valAt'_gen a.D₀.P.isLB ((Λ.ex0 v).isGen _) (isLift_gt Λ v x) hj).trans (congrArg (· * _) (Λ.arcDict_expZero_section v x))
    add := isAdd Λ
    onto := analyticTorusPoint_surjective Λ
    lin := gtAct Λ
    ker := isZero_iff Λ
    iota := isIota Λ }

theorem exists_rep (Λ : letI := H.starRing; GtAn a) (k : ℕ) [NeZero k] (p : Out.QkPt a.D₀ (FractionRing ℂ) k) :
    letI := H.starRing; ∃ la, Λ.Rep k p la := by
  letI := H.starRing
  obtain ⟨q, hq, -⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ)
    (RingHom.ext fun _ => rfl) p
  obtain ⟨la, rfl⟩ := (toDict Λ).qk_surjective k q
  exact ⟨la, (rep_iff Λ k p la).2 ⟨_, hq, rfl, rfl⟩⟩

theorem rep_unique (Λ : letI := H.starRing; GtAn a) (k : ℕ) [NeZero k] (p : Out.QkPt a.D₀ (FractionRing ℂ) k) :
    letI := H.starRing; ∀ la la', Λ.Rep k p la → Λ.Rep k p la' → ∃ m, la' = la + k • m := by
  letI := H.starRing
  intro la la' h h'
  obtain ⟨q, hq, hy, hg⟩ := (rep_iff Λ k p la).1 h
  obtain ⟨hy', hg'⟩ := h' q hq
  have e : (toDict Λ).qk k la' = (toDict Λ).qk k la := TorusExt.qk_ext (hy'.symm.trans hy) (hg'.symm.trans hg)
  refine ((toDict Λ).qk_equiv_iff k la la').1 ?_
  rw [e]
  have := (toDict Λ).qk_equiv_add k la 0
  rw [smul_zero] at this
  erw [_root_.add_zero] at this
  exact this

end Bridge

section Test

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
  [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

theorem rep_eta (v : HypLattice H) : letI := H.starRing
    (model c c.F.val.toRingHom).Rep l.M ((arcIn c ℂ c.F.val.toRingHom).eta v)
      (AnArc.La.mk (A := splitArc l) v.1 (ConjDual.toDual H v.2).toAddMonoidHom 0) := by
  letI := H.starRing
  let ζ : ℂˣ := Units.mk0 (zeta l.M) (Complex.exp_ne_zero _)
  have h : (ζ : ℂ) = algebraMap (FractionRing ℂ) ℂ (arcRoot c ℂ c.F.val.toRingHom (Nat.dvd_lcm_left l.M l.A)) :=
    IsScalarTower.algebraMap_apply ℂ (FractionRing ℂ) ℂ _
  have hζ : ζ ^ l.M = 1 := Units.ext ((Units.val_pow_eq_pow_val _ _).trans
    (isPrimitiveRoot_zeta (lt_of_lt_of_le three_pos l.three_le)).pow_eq_one)
  intro q hq
  obtain rfl := (qkExt_qkPt ℂ (isPrimitiveRoot_arcRoot c ℂ c.F.val.toRingHom (Nat.dvd_lcm_left l.M l.A)).pow_eq_one
    (algebraMap (FractionRing ℂ) ℂ) (RingHom.ext fun _ => rfl) hζ h v q).1 hq
  refine ⟨rfl, congrArg (pt _ ℂ) (MonoidHom.ext fun x => Units.ext ?_)⟩
  change ((ζ ^ ConjDual.toDual H v.2 x.toAdd : ℂˣ) : ℂ) =
    eTwoPi ((l.M : ℂ)⁻¹ * (0 + (ConjDual.toDual H v.2 x.toAdd : ℤ) - (splitArc l).H 0 0 / (2 * Complex.I)))
  rw [Units.val_zpow_eq_zpow_val, AnArc.H_zero_left, zero_div, sub_zero, zero_add, AnArc.e_mul_intCast]
  rfl

example : letI := H.starRing
    ¬ (model c c.F.val.toRingHom).Rep l.M ((arcIn c ℂ c.F.val.toRingHom).eta ((1, 0) : HypLattice H)) 0 := by
  letI := H.starRing
  intro h
  obtain ⟨q, hq, hy, -⟩ := (rep_iff _ _ _ _).1 h
  exact one_ne_zero (α := 𝓞 E) (hq.1.symm.trans hy)

end Test

end GlobalTheory.GtAnModel
