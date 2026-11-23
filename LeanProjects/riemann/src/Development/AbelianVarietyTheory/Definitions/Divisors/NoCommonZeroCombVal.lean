import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff TensorProduct

namespace GlobalTheory

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ}

namespace CxPts

variable {A B : LB Y} {y : CxPts p σ} {U W : Y.Opens}

variable (p σ) in

def gv (B : LB Y) (i j : B.ι) : CxPts p σ → ℂ := ev p σ (B.U i ⊓ B.U j) (B.g i j).val

def pick (hB : B.IsLB) (y : CxPts p σ) : B.ι := (exists_mem_ptsIn hB.cover y).choose

theorem mem_pick (hB : B.IsLB) (y : CxPts p σ) : y ∈ ptsIn p σ (B.U (pick hB y)) := (exists_mem_ptsIn hB.cover y).choose_spec

theorem ev_one (h : y ∈ ptsIn p σ U) : ev p σ U 1 y = 1 := by
  rw [ev_eq h, map_one]

theorem ev_inv (h : y ∈ ptsIn p σ U) (u : Γ(Y, U)ˣ) :
    ev p σ U (u⁻¹).val y = (ev p σ U u.val y)⁻¹ := by
  rw [ev_eq h, ev_eq h]
  exact map_units_inv (evHom h) u

theorem gv_ne_zero {i j : B.ι} (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B.U j)) :
    gv p σ B i j y ≠ 0 := ev_ne_zero (mem_ptsIn_inf.2 ⟨hi, hj⟩) (B.g i j).isUnit

private theorem ev_res_units_val_eq {U₁ W₁ : Y.Opens} (e : W₁ ≤ U₁) (h : y ∈ ptsIn p σ W₁)
    (u : Γ(Y, U₁)ˣ) : ev p σ W₁ (Semi.res e u).val y = ev p σ U₁ u.val y :=
  ev_res e h u.val

theorem gv_self (hB : B.IsLB) {i : B.ι} (hi : y ∈ ptsIn p σ (B.U i)) : gv p σ B i i y = 1 := by
  have e := congrArg (fun u => ev p σ _ (Units.val u) y) (hB.2 i)
  simp only [Units.val_one] at e
  rw [ev_res_units_val_eq, ev_one] at e
  · exact e
  all_goals simp [hi]

theorem gv_mul (hB : B.IsLB) {i j l : B.ι} (hi : y ∈ ptsIn p σ (B.U i))
    (hj : y ∈ ptsIn p σ (B.U j)) (hl : y ∈ ptsIn p σ (B.U l)) :
    gv p σ B i j y * gv p σ B j l y = gv p σ B i l y := by
  have e := congrArg (fun u => ev p σ _ (Units.val u) y) (hB.3 i j l)
  simp only [Units.val_mul, ev_mul] at e
  rw [ev_res_units_val_eq, ev_res_units_val_eq, ev_res_units_val_eq] at e
  · exact e
  all_goals simp [hi, hj, hl]

theorem gv_tens {c c' : (tens A B).ι} (h : y ∈ ptsIn p σ ((tens A B).U c))
    (h' : y ∈ ptsIn p σ ((tens A B).U c')) :
    gv p σ (tens A B) c c' y = gv p σ A c.1 c'.1 y * gv p σ B c.2 c'.2 y := by
  have e := mem_ptsIn_inf.1 h
  have e' := mem_ptsIn_inf.1 h'
  simp only [gv, CechPic.tens, Units.val_mul, ev_mul]
  rw [ev_res_units_val_eq, ev_res_units_val_eq]
  all_goals simp_all

theorem gv_dual {i j : B.ι} (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B.U j)) :
    gv p σ (dual B) i j y = (gv p σ B i j y)⁻¹ := ev_inv (mem_ptsIn_inf.2 ⟨hi, hj⟩) _

theorem ev_iso_rel {w : LB.Iso A B} (hw : w.IsGen) {a a' : A.ι} {b b' : B.ι}
    (ha : y ∈ ptsIn p σ (A.U a)) (ha' : y ∈ ptsIn p σ (A.U a')) (hb : y ∈ ptsIn p σ (B.U b))
    (hb' : y ∈ ptsIn p σ (B.U b')) :
    ev p σ _ (w.s (b, a)).val y * gv p σ A a a' y =
      gv p σ B b b' y * ev p σ _ (w.s (b', a')).val y := by
  have hy : y ∈ ptsIn p σ (B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a')) := by simp [ha, ha', hb, hb']
  have hw' : Semi.res (V := B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a')) inf_le_left (w.s (b, a)) =
      (Semi.res (V := B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a'))
          (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (B.g b b') *
        (Semi.res (V := B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a'))
          (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (A.g a a'))⁻¹) *
        Semi.res (V := B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a')) inf_le_right (w.s (b', a')) :=
    hw (b, a) (b', a')
  have e := congrArg (fun u => ev p σ (B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a')) (Units.val u) y) hw'
  simp only [Units.val_mul, ev_mul] at e
  rw [ev_inv hy, ev_res_units_val_eq _ hy, ev_res_units_val_eq _ hy] at e
  have h₁ : ev p σ (B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a'))
      (Semi.res (V := B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a')) inf_le_left (w.s (b, a))).val y =
      ev p σ ((B.div A).U (b, a)) (w.s (b, a)).val y := ev_res_units_val_eq _ hy _
  have h₂ : ev p σ (B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a'))
      (Semi.res (V := B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a')) inf_le_right (w.s (b', a'))).val y =
      ev p σ ((B.div A).U (b', a')) (w.s (b', a')).val y := ev_res_units_val_eq _ hy _
  have hA : ev p σ (A.U a ⊓ A.U a') (A.g a a').val y ≠ 0 := gv_ne_zero ha ha'
  unfold gv
  rw [← h₁, ← h₂, e]
  field_simp

theorem ev_iso_ne_zero (w : LB.Iso A B) {a : A.ι} {b : B.ι} (ha : y ∈ ptsIn p σ (A.U a))
    (hb : y ∈ ptsIn p σ (B.U b)) : ev p σ _ (w.s (b, a)).val y ≠ 0 := ev_ne_zero (mem_ptsIn_inf.2 ⟨hb, ha⟩) (w.s (b, a)).isUnit

section Pull

variable {k' : Type} [CommRing k'] {Y' : Scheme.{0}} {p' : Y' ⟶ Sp k'} {σ' : k' →+* ℂ}
  {κ : Type} [Fintype κ] {f : κ → (Y' ⟶ Y)} {z : CxPts p' σ'} {m : κ → CxPts p σ}

theorem mem_of_mem_linComb (hm : ∀ a, (m a).1 = z.1 ≫ f a) {ε : κ → ℤ} {j : κ → B.ι}
    (h : z ∈ ptsIn p' σ' ((LB.LinComb B f ε).U j)) (a : κ) : m a ∈ ptsIn p σ (B.U (j a)) := by
  rw [mem_ptsIn] at h ⊢
  rw [hm a]
  have h₁ : z.1 (IsLocalRing.closedPoint ℂ) ∈ ⋂ c, ⇑(f c) ⁻¹' (B.U (j c) : Set Y) := h
  exact Set.mem_iInter.1 h₁ a

private theorem ev_units_val_eq_evHom {V₁ : Y.Opens} {y₁ : CxPts p σ} (h : y₁ ∈ ptsIn p σ V₁)
    (u : Γ(Y, V₁)ˣ) :
    ev p σ V₁ u.val y₁ = ((Units.map (evHom h).toMonoidHom u : ℂˣ) : ℂ) := by
  rw [ev_eq h]
  rfl

private theorem pullU_val' {Y₁ : Scheme.{0}} (g : Y₁ ⟶ Y) (W₁ : Y.Opens) (u : Γ(Y, W₁)ˣ) :
    (pullU g W₁ u).val = (g.app W₁).hom u.val :=
  rfl

private theorem ev_app_pullback_eq_ev {k₁ : Type} [CommRing k₁] {Y₁ : Scheme.{0}} {p₁ : Y₁ ⟶ Sp k₁}
    {σ₁ : k₁ →+* ℂ} (g : Y₁ ⟶ Y) {W₁ : Y.Opens} {z₁ : CxPts p₁ σ₁} {y₁ : CxPts p σ}
    (hm : y₁.1 = z₁.1 ≫ g) (a : Γ(Y, W₁)) :
    ev p₁ σ₁ (g ⁻¹ᵁ W₁) ((g.app W₁).hom a) z₁ = ev p σ W₁ a y₁ := by
  simp only [ev, valR]
  rw [hm]
  by_cases h : ⊤ ≤ (z₁.1 ≫ g) ⁻¹ᵁ W₁
  · have h' : ⊤ ≤ z₁.1 ⁻¹ᵁ (g ⁻¹ᵁ W₁) := h
    rw [dif_pos h, dif_pos h', Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ z₁.1 ⁻¹ᵁ (g ⁻¹ᵁ W₁) := h
    rw [dif_neg h, dif_neg h']

theorem gv_linComb (hm : ∀ a, (m a).1 = z.1 ≫ f a) {ε : κ → ℤ} {j j' : κ → B.ι}
    (h : z ∈ ptsIn p' σ' ((LB.LinComb B f ε).U j)) (h' : z ∈ ptsIn p' σ' ((LB.LinComb B f ε).U j')) :
    gv p' σ' (LB.LinComb B f ε) j j' z = ∏ a, gv p σ B (j a) (j' a) (m a) ^ ε a := by
  have hz : z ∈ ptsIn p' σ' (B.wchart f j ⊓ B.wchart f j') := mem_ptsIn_inf.2 ⟨h, h'⟩
  simp only [gv, LB.LinComb]
  rw [ev_units_val_eq_evHom hz, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val, ← ev_units_val_eq_evHom hz]
  congr 1
  exact (ev_res_units_val_eq _ hz _).trans (ev_app_pullback_eq_ev (W₁ := B.U (j a) ⊓ B.U (j' a)) (f a) (hm a) _)

end Pull

theorem mem_pow_iff {n : ℤ} {j : PUnit → B.ι} :
    y ∈ ptsIn p σ ((LB.LinComb B (fun _ => 𝟙 Y) fun _ => n).U j) ↔
      y ∈ ptsIn p σ (B.U (j PUnit.unit)) := by
  constructor
  · intro h
    exact mem_of_mem_linComb (m := fun _ => y) (fun _ => (Category.comp_id _).symm) h PUnit.unit
  · intro h
    rw [mem_ptsIn] at h ⊢
    exact Set.mem_iInter.2 fun _ => h

theorem gv_pow {n : ℤ} {j j' : PUnit → B.ι} (h : y ∈ ptsIn p σ (B.U (j PUnit.unit)))
    (h' : y ∈ ptsIn p σ (B.U (j' PUnit.unit))) :
    gv p σ (LB.LinComb B (fun _ => 𝟙 Y) fun _ => n) j j' y =
      gv p σ B (j PUnit.unit) (j' PUnit.unit) y ^ n := by
  rw [gv_linComb (m := fun _ => y) (fun _ => (Category.comp_id _).symm) (mem_pow_iff.2 h)
    (mem_pow_iff.2 h')]
  simp

section Ratio

variable {D : ℕ} {U' U'' : Y.Opens} {η : FormsOn p D U} {η' : FormsOn p D U'}
  {η'' : FormsOn p D U''}

variable (σ) in

def rv (hη : IsFrame η) (hη' : IsFrame η') : CxPts p σ → ℂ := ev p σ (U ⊓ U') (hη.ratio hη').val

theorem rv_ne_zero (hη : IsFrame η) (hη' : IsFrame η') (h : y ∈ ptsIn p σ U)
    (h' : y ∈ ptsIn p σ U') : rv σ hη hη' y ≠ 0 := ev_ne_zero (mem_ptsIn_inf.2 ⟨h, h'⟩) (Units.isUnit _)

theorem rv_mul (hη : IsFrame η) (hη' : IsFrame η') (hη'' : IsFrame η'') (h : y ∈ ptsIn p σ U)
    (h' : y ∈ ptsIn p σ U') (h'' : y ∈ ptsIn p σ U'') :
    rv σ hη hη' y * rv σ hη' hη'' y = rv σ hη hη'' y := by
  have e := congrArg (fun u => ev p σ (U ⊓ U' ⊓ U'') (Units.val u) y)
    (hη.res_ratio_mul hη' hη'' (V := U ⊓ U' ⊓ U'')
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
  simp only [Units.val_mul, ev_mul] at e
  rw [ev_res_units_val_eq, ev_res_units_val_eq, ev_res_units_val_eq] at e
  · exact e
  all_goals simp [h, h', h'']

theorem gv_canon [SmoothOfRelativeDimension D p] (K : CanonLB p D) (a b : K.bundle.ι) :
    gv p σ K.bundle a b = rv σ (K.isFrame a) (K.isFrame b) := by
  funext y
  show ev p σ _ (K.bundle.g a b).val y = ev p σ _ ((K.isFrame a).ratio (K.isFrame b)).val y
  rw [K.g_eq_ratio a b]

theorem rv_chart (c c' : AlgChart p σ D) (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) :
    rv σ c.isFrame c'.isFrame y = transDet c.e c'.e y := c.ev_ratio c' hy hy'

end Ratio

variable (p σ B) in

def fibSec : Submodule ℂ (B.ι → CxPts p σ → ℂ) where
  carrier := {s | (∀ i j y, y ∈ ptsIn p σ (B.U i) → y ∈ ptsIn p σ (B.U j) →
    s i y = gv p σ B i j y * s j y) ∧ ∀ i y, y ∉ ptsIn p σ (B.U i) → s i y = 0}
  zero_mem' := ⟨fun _ _ _ _ _ => (mul_zero _).symm, fun _ _ _ => rfl⟩
  add_mem' {s t} hs ht := ⟨fun i j y hi hj => by
    simp only [Pi.add_apply, hs.1 i j y hi hj, ht.1 i j y hi hj, mul_add],
    fun i y h => by simp only [Pi.add_apply, hs.2 i y h, ht.2 i y h, add_zero]⟩
  smul_mem' c s hs := ⟨fun i j y hi hj => by
    simp only [Pi.smul_apply, hs.1 i j y hi hj, smul_eq_mul, mul_left_comm],
    fun i y h => by simp only [Pi.smul_apply, hs.2 i y h, smul_zero]⟩

variable (p σ) in

def secVal : B.Sec →+ (B.ι → CxPts p σ → ℂ) where
  toFun s i := ev p σ (B.U i) (s.f i)
  map_zero' := funext₂ fun i y => by
    by_cases h : y ∈ ptsIn p σ (B.U i)
    · exact (ev_eq h _).trans (map_zero _)
    · exact ev_of_notMem h _
  map_add' s t := funext₂ fun i y => ev_add _ _ y

theorem secVal_apply (s : B.Sec) (i : B.ι) : secVal p σ s i = ev p σ (B.U i) (s.f i) := rfl

theorem secVal_mem (s : B.Sec) : secVal p σ s ∈ fibSec p σ B := by
  refine ⟨fun i j y hi hj => ?_, fun i y h => ev_of_notMem h _⟩
  have hij : y ∈ ptsIn p σ (B.U i ⊓ B.U j) := mem_ptsIn_inf.2 ⟨hi, hj⟩
  have e := congrArg (fun f => ev p σ _ f y) (s.2 i j)
  simp only [ev_mul] at e
  rw [ev_res inf_le_left hij, ev_res inf_le_right hij] at e
  exact e

theorem secVal_smul (a : k) (s : B.Sec) : secVal p σ (algX p ⊤ a • s) = σ a • secVal p σ s := by
  funext i y
  show ev p σ (B.U i) ((algX p ⊤ a • s).f i) y = σ a * ev p σ (B.U i) (s.f i) y
  by_cases h : y ∈ ptsIn p σ (B.U i)
  · have e : (algX p ⊤ a • s).f i = resG Y le_top (algX p ⊤ a) * s.f i := rfl
    rw [e, ev_mul, ev_res le_top h, ev_algX mem_ptsIn_top a]
  · rw [ev_of_notMem h, ev_of_notMem h, mul_zero]

theorem secVal_ne_zero_iff (s : B.Sec) {i : B.ι} (hi : y ∈ ptsIn p σ (B.U i)) :
    secVal p σ s i y ≠ 0 ↔ y ∈ ptsIn p σ (nonzeroLocus s) := by
  have key : ∀ l, y ∈ ptsIn p σ (B.U l) → (secVal p σ s l y ≠ 0 ↔ secVal p σ s i y ≠ 0) :=
    fun l hl => by rw [(secVal_mem s).1 i l y hi hl, mul_ne_zero_iff, and_iff_right (gv_ne_zero hi hl)]
  rw [nonzeroLocus, mem_ptsIn, Opens.mem_iSup]
  constructor
  · intro h
    exact ⟨i, mem_ptsIn.1 ((mem_ptsIn_basicOpen hi _).2 h)⟩
  · rintro ⟨l, hl⟩
    have hl' : y ∈ ptsIn p σ (Y.basicOpen (s.f l)) := mem_ptsIn.2 hl
    have hlU : y ∈ ptsIn p σ (B.U l) := ptsIn_mono (Y.basicOpen_le _) hl'
    exact (key l hlU).1 ((mem_ptsIn_basicOpen hlU _).1 hl')

def secTens (s : A.ι → CxPts p σ → ℂ) (t : B.ι → CxPts p σ → ℂ) :
    (tens A B).ι → CxPts p σ → ℂ := fun c y => s c.1 y * t c.2 y

theorem secTens_mem {s : A.ι → CxPts p σ → ℂ} {t : B.ι → CxPts p σ → ℂ} (hs : s ∈ fibSec p σ A)
    (ht : t ∈ fibSec p σ B) : secTens s t ∈ fibSec p σ (tens A B) := by
  refine ⟨fun c c' y h h' => ?_, fun c y h => ?_⟩
  · have e := mem_ptsIn_inf.1 h
    have e' := mem_ptsIn_inf.1 h'
    simp only [secTens]
    rw [gv_tens h h', hs.1 _ _ y e.1 e'.1, ht.1 _ _ y e.2 e'.2]
    ring
  · simp only [secTens]
    by_cases ha : y ∈ ptsIn p σ (A.U c.1)
    · have hb : y ∉ ptsIn p σ (B.U c.2) := fun hb => h (mem_ptsIn_inf.2 ⟨ha, hb⟩)
      rw [ht.2 _ y hb, mul_zero]
    · rw [hs.2 _ y ha, zero_mul]

end CxPts

open CxPts

abbrev secModuleBase (p : Y ⟶ Sp k) (B : LB Y) : Module k B.Sec := Module.compHom B.Sec (algX p ⊤)

def SecC (p : Y ⟶ Sp k) (σ : k →+* ℂ) (B : LB Y) : Type :=
  letI := σ.toAlgebra
  letI := secModuleBase p B
  ℂ ⊗[k] B.Sec

namespace SecC

variable {B : LB Y}

instance : AddCommGroup (SecC p σ B) :=
  letI := σ.toAlgebra
  letI := secModuleBase p B
  (inferInstance : AddCommGroup (ℂ ⊗[k] B.Sec))

instance : Module ℂ (SecC p σ B) :=
  letI := σ.toAlgebra
  letI := secModuleBase p B
  (inferInstance : Module ℂ (ℂ ⊗[k] B.Sec))

variable (p σ) in

def of : B.Sec →+ SecC p σ B :=
  letI := σ.toAlgebra
  letI := secModuleBase p B
  (TensorProduct.mk k ℂ B.Sec 1).toAddMonoidHom

theorem of_smul (a : k) (s : B.Sec) : of p σ (algX p ⊤ a • s) = σ a • of p σ s := by
  letI := σ.toAlgebra
  letI := secModuleBase p B
  show (1 : ℂ) ⊗ₜ[k] (a • s) = σ a • ((1 : ℂ) ⊗ₜ[k] s)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul,
    mul_one]
  rfl

theorem span_range_of : Submodule.span ℂ (range (of p σ : B.Sec → _)) = ⊤ := by
  letI := σ.toAlgebra
  letI := secModuleBase p B
  refine eq_top_iff.2 fun x _ => ?_
  refine TensorProduct.induction_on (motive := fun x : ℂ ⊗[k] B.Sec =>
    @id (SecC p σ B) x ∈ Submodule.span ℂ (range (of p σ : B.Sec → SecC p σ B))) x ?_ ?_ ?_
  · exact zero_mem _
  · intro c s
    have e : @id (SecC p σ B) (c ⊗ₜ[k] s) = c • of p σ s := by
      show c ⊗ₜ[k] s = c • ((1 : ℂ) ⊗ₜ[k] s)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨s, rfl⟩)
  · intro x y hx hy
    exact add_mem hx hy

def lift {E : Type*} [AddCommGroup E] [Module ℂ E] (φ : B.Sec →+ E)
    (h : ∀ a s, φ (algX p ⊤ a • s) = σ a • φ s) : SecC p σ B →ₗ[ℂ] E :=
  letI := σ.toAlgebra
  letI := secModuleBase p B
  letI : Module k E := Module.compHom E σ
  haveI : IsScalarTower k ℂ E := ⟨fun a c x => mul_smul (σ a) c x⟩
  LinearMap.liftBaseChange ℂ ({ φ with map_smul' := h } : B.Sec →ₗ[k] E)

@[simp] theorem lift_of {E : Type*} [AddCommGroup E] [Module ℂ E] (φ : B.Sec →+ E)
    (h : ∀ a s, φ (algX p ⊤ a • s) = σ a • φ s) (s : B.Sec) : lift φ h (of p σ s) = φ s := by
  letI := σ.toAlgebra
  letI := secModuleBase p B
  letI : Module k E := Module.compHom E σ
  haveI : IsScalarTower k ℂ E := ⟨fun a c x => mul_smul (σ a) c x⟩
  show LinearMap.liftBaseChange ℂ _ ((1 : ℂ) ⊗ₜ[k] s) = φ s
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  rfl

def val : SecC p σ B →ₗ[ℂ] (B.ι → CxPts p σ → ℂ) := lift (secVal p σ) secVal_smul

@[simp] theorem val_of (s : B.Sec) : val (of p σ s) = secVal p σ s := lift_of _ _ s

theorem val_mem_of {M : Submodule ℂ (B.ι → CxPts p σ → ℂ)} (h : ∀ s, secVal p σ s ∈ M)
    (x : SecC p σ B) : val x ∈ M := by
  have hle : Submodule.span ℂ (range (of p σ : B.Sec → SecC p σ B)) ≤ M.comap val :=
    Submodule.span_le.2 (by
      rintro _ ⟨s, rfl⟩
      show val (of p σ s) ∈ M
      rw [val_of]
      exact h s)
  exact hle (by rw [span_range_of]; exact Submodule.mem_top)

theorem val_mem (x : SecC p σ B) : val x ∈ fibSec p σ B := val_mem_of secVal_mem x

end SecC

structure Weight (p : Y ⟶ Sp k) (σ : k →+* ℂ) (B : LB Y) where

  isLB : B.IsLB

  φ : B.ι → CxPts p σ → ℝ

  trans : ∀ i j y, y ∈ ptsIn p σ (B.U i) → y ∈ ptsIn p σ (B.U j) →
    φ j y = φ i y - Real.log (‖gv p σ B i j y‖ ^ 2)

theorem log_normSq_mul {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.log (‖a * b‖ ^ 2) = Real.log (‖a‖ ^ 2) + Real.log (‖b‖ ^ 2) := by
  rw [norm_mul, mul_pow, Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.2 ha))
    (pow_ne_zero 2 (norm_ne_zero_iff.2 hb))]

theorem log_normSq_zpow (a : ℂ) (n : ℤ) : Real.log (‖a ^ n‖ ^ 2) = n * Real.log (‖a‖ ^ 2) := by
  have e : ‖a ^ n‖ ^ 2 = (‖a‖ ^ 2) ^ n := by
    rw [norm_zpow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [e, Real.log_zpow]

theorem normSq_mul_exp {u : ℂ} (hu : u ≠ 0) (s : ℂ) (φ : ℝ) :
    ‖u * s‖ ^ 2 * Real.exp (-(φ + Real.log (‖u‖ ^ 2))) = ‖s‖ ^ 2 * Real.exp (-φ) := by
  have hu' : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.2 hu) 2
  rw [norm_mul, mul_pow, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hu']
  field_simp

namespace Weight

variable {A B : LB Y} (φ : Weight p σ B) {y : CxPts p σ} {s : B.ι → CxPts p σ → ℂ}

def nsq (s : B.ι → CxPts p σ → ℂ) (y : CxPts p σ) : ℝ :=
  ‖s (pick φ.isLB y) y‖ ^ 2 * Real.exp (-φ.φ (pick φ.isLB y) y)

theorem nsq_eq (hs : s ∈ fibSec p σ B) {i : B.ι} (hi : y ∈ ptsIn p σ (B.U i)) :
    φ.nsq s y = ‖s i y‖ ^ 2 * Real.exp (-φ.φ i y) := by
  have hp := mem_pick φ.isLB y
  have e := normSq_mul_exp (gv_ne_zero hp hi) (s i y)
    (φ.φ (pick φ.isLB y) y - Real.log (‖gv p σ B (pick φ.isLB y) i y‖ ^ 2))
  rw [sub_add_cancel] at e
  unfold nsq
  rw [hs.1 _ i y hp hi, φ.trans _ i y hp hi]
  exact e

theorem nsq_nonneg (s : B.ι → CxPts p σ → ℂ) (y : CxPts p σ) : 0 ≤ φ.nsq s y := by
  unfold nsq
  positivity

def addFn (u : CxPts p σ → ℝ) : Weight p σ B where
  isLB := φ.isLB
  φ i y := φ.φ i y + u y
  trans i j y hi hj := by rw [φ.trans i j y hi hj]; ring

theorem nsq_addFn (u : CxPts p σ → ℝ) (s : B.ι → CxPts p σ → ℂ) (y : CxPts p σ) :
    (φ.addFn u).nsq s y = φ.nsq s y * Real.exp (-u y) := by
  simp only [nsq, addFn, neg_add, Real.exp_add]
  ring

def tens (ψ : Weight p σ A) (φ : Weight p σ B) : Weight p σ (tens A B) where
  isLB := isLB_tens ψ.isLB φ.isLB
  φ c y := ψ.φ c.1 y + φ.φ c.2 y
  trans c c' y h h' := by
    have e := mem_ptsIn_inf.1 h
    have e' := mem_ptsIn_inf.1 h'
    rw [gv_tens h h', log_normSq_mul (gv_ne_zero e.1 e'.1) (gv_ne_zero e.2 e'.2),
      ψ.trans _ _ y e.1 e'.1, φ.trans _ _ y e.2 e'.2]
    ring

theorem nsq_tens (ψ : Weight p σ A) {t : A.ι → CxPts p σ → ℂ} (ht : t ∈ fibSec p σ A)
    (hs : s ∈ fibSec p σ B) (y : CxPts p σ) :
    (ψ.tens φ).nsq (secTens t s) y = ψ.nsq t y * φ.nsq s y := by
  have hp := mem_pick (ψ.tens φ).isLB y
  have e := mem_ptsIn_inf.1 hp
  rw [(ψ.tens φ).nsq_eq (secTens_mem ht hs) hp, ψ.nsq_eq ht e.1, φ.nsq_eq hs e.2]
  simp only [secTens, Weight.tens, norm_mul, mul_pow, neg_add, Real.exp_add]
  ring

def dual : Weight p σ (dual B) where
  isLB := isLB_dual φ.isLB
  φ i y := -φ.φ i y
  trans i j y hi hj := by
    rw [gv_dual (B := B) hi hj, φ.trans i j y hi hj, norm_inv, inv_pow, Real.log_inv]
    ring

def linComb {k' : Type} [CommRing k'] {Y' : Scheme.{0}} {p' : Y' ⟶ Sp k'} {σ' : k' →+* ℂ}
    {κ : Type} [Fintype κ] (f : κ → (Y' ⟶ Y)) (ε : κ → ℤ) (m : κ → CxPts p' σ' → CxPts p σ)
    (hm : ∀ a z, (m a z).1 = z.1 ≫ f a) : Weight p' σ' (LB.LinComb B f ε) where
  isLB := Semi.LB.isLB_linComb φ.isLB _ _
  φ j z := ∑ a, ε a * φ.φ (j a) (m a z)
  trans j j' z h h' := by
    have e := mem_of_mem_linComb (hm · z) h
    have e' := mem_of_mem_linComb (hm · z) h'
    rw [gv_linComb (hm · z) h h', log_normSq_prod_zpow _ fun a => gv_ne_zero (e a) (e' a),
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [φ.trans _ _ _ (e a) (e' a), mul_sub]

def zpow (n : ℤ) : Weight p σ (LB.LinComb B (K := PUnit) (fun _ => 𝟙 Y) fun _ => n) :=
  φ.linComb _ _ (fun _ => id) fun _ _ => (Category.comp_id _).symm

abbrev pow (n : ℕ) : Weight p σ (lbPow B n) := φ.zpow n

theorem zpow_φ (n : ℤ) (j : PUnit → B.ι) (y : CxPts p σ) :
    (φ.zpow n).φ j y = n * φ.φ (j PUnit.unit) y := by
  simp [Weight.zpow, Weight.linComb]

def pull {Y' : Scheme.{0}} {p' : Y' ⟶ Sp k} (f : Y' ⟶ Y) (hf : f ≫ p = p') :
    Weight p' σ (B.pull f) :=
  φ.linComb _ _ (fun _ => PtsOver.map f hf _) fun _ _ => rfl

theorem pull_φ {Y' : Scheme.{0}} {p' : Y' ⟶ Sp k} (f : Y' ⟶ Y) (hf : f ≫ p = p')
    (j : PUnit → B.ι) (z : CxPts p' σ) :
    (φ.pull f hf).φ j z = φ.φ (j PUnit.unit) (PtsOver.map f hf _ z) := by
  simp [Weight.pull, Weight.linComb]

def ofPairs (hA : A.IsLB) (hB : B.IsLB) (ψ : A.ι → B.ι → CxPts p σ → ℝ)
    (h : ∀ a a' b b' y, y ∈ ptsIn p σ (A.U a) → y ∈ ptsIn p σ (A.U a') → y ∈ ptsIn p σ (B.U b) →
      y ∈ ptsIn p σ (B.U b') → ψ a' b' y = ψ a b y - Real.log (‖gv p σ A a a' y‖ ^ 2)) :
    Weight p σ A :=
  ⟨hA, fun a y => ψ a (pick hB y) y, fun a a' y ha ha' =>
    h a a' _ _ y ha ha' (mem_pick hB y) (mem_pick hB y)⟩

theorem ofPairs_φ {hA : A.IsLB} {hB : B.IsLB} {ψ : A.ι → B.ι → CxPts p σ → ℝ} {h} {a : A.ι}
    {b : B.ι} (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    (ofPairs hA hB ψ h).φ a y = ψ a b y := by
  show ψ a (pick hB y) y = ψ a b y
  have e := h a a (pick hB y) b y ha ha (mem_pick hB y) hb
  rw [gv_self hA ha, norm_one, one_pow, Real.log_one, sub_zero] at e
  exact e.symm

def cancel (hA : A.IsLB) (χ : Weight p σ (CechPic.tens A B)) (φ : Weight p σ B) : Weight p σ A :=
  ofPairs hA φ.isLB (fun a b y => χ.φ (a, b) y - φ.φ b y) fun a a' b b' y ha ha' hb hb' => by
    have e : y ∈ ptsIn p σ ((CechPic.tens A B).U (a, b)) := mem_ptsIn_inf.2 ⟨ha, hb⟩
    have e' : y ∈ ptsIn p σ ((CechPic.tens A B).U (a', b')) := mem_ptsIn_inf.2 ⟨ha', hb'⟩
    rw [χ.trans _ _ y e e', φ.trans b b' y hb hb', gv_tens e e',
      log_normSq_mul (gv_ne_zero ha ha') (gv_ne_zero hb hb')]
    ring

def ofIso (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) : Weight p σ A :=
  ofPairs hA φ.isLB (fun a b y => φ.φ b y + Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2))
    fun a a' b b' y ha ha' hb hb' => by
    have e := (log_normSq_mul (ev_iso_ne_zero w hb ha) (gv_ne_zero hb hb')).symm.trans
      ((congrArg (fun z => Real.log (‖z‖ ^ 2)) (ev_iso_rel hw hb hb' ha ha')).trans
        (log_normSq_mul (gv_ne_zero ha ha') (ev_iso_ne_zero w hb' ha')))
    rw [φ.trans b b' y hb hb']
    linarith

def IsConj {σ' : k →+* ℂ} (φ : Weight p σ B) (φ' : Weight p σ' B) : Prop :=
  ∀ i (y : CxPts p σ) (y' : CxPts p σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 →
    y ∈ ptsIn p σ (B.U i) → φ'.φ i y' = φ.φ i y

section FS

variable {α : Type*} [Fintype α] {e : α → B.ι → CxPts p σ → ℂ}

def NoCommonZero (e : α → B.ι → CxPts p σ → ℂ) : Prop :=
  ∀ i, ∀ y ∈ ptsIn p σ (B.U i), ∃ a, e a i y ≠ 0

theorem NoCommonZero.sum_pos (h : NoCommonZero e) {i : B.ι} (hi : y ∈ ptsIn p σ (B.U i)) :
    0 < ∑ a, ‖e a i y‖ ^ 2 := by
  obtain ⟨a, ha⟩ := h i y hi
  exact Finset.sum_pos' (fun b _ => by positivity)
    ⟨a, Finset.mem_univ _, pow_pos (norm_pos_iff.2 ha) 2⟩

def fs (hB : B.IsLB) (e : α → B.ι → CxPts p σ → ℂ) (he : ∀ a, e a ∈ fibSec p σ B)
    (h : NoCommonZero e) : Weight p σ B where
  isLB := hB
  φ i y := Real.log (∑ a, ‖e a i y‖ ^ 2)
  trans i j y hi hj := by
    have := gv_ne_zero hi hj
    simp only [fun a => (he a).1 i j y hi hj, norm_mul, mul_pow, ← Finset.mul_sum]
    rw [Real.log_mul (by positivity) (h.sum_pos hj).ne']
    ring

theorem nsq_fs {hB : B.IsLB} {he : ∀ a, e a ∈ fibSec p σ B} {h : NoCommonZero e}
    (hs : s ∈ fibSec p σ B) {i : B.ι} (hi : y ∈ ptsIn p σ (B.U i)) :
    (fs hB e he h).nsq s y = ‖s i y‖ ^ 2 / ∑ a, ‖e a i y‖ ^ 2 := by
  rw [nsq_eq _ hs hi]
  simp only [fs]
  rw [Real.exp_neg, Real.exp_log (h.sum_pos hi), div_eq_mul_inv]

theorem nsq_fs_le {hB : B.IsLB} {he : ∀ a, e a ∈ fibSec p σ B} {h : NoCommonZero e} (c : α → ℂ)
    (y : CxPts p σ) : (fs hB e he h).nsq (∑ a, c a • e a) y ≤ ∑ a, ‖c a‖ ^ 2 := by
  have hi := mem_pick hB y
  have hpos := h.sum_pos hi
  simp only [nsq, fs]
  rw [Real.exp_neg, Real.exp_log hpos, ← div_eq_mul_inv, div_le_iff₀ hpos]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc ‖∑ a, c a * e a (pick hB y) y‖ ^ 2 ≤ (∑ a, ‖c a‖ * ‖e a (pick hB y) y‖) ^ 2 := by
        gcongr
        exact (norm_sum_le _ _).trans_eq (by simp [norm_mul])
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem sum_nsq_fs {hB : B.IsLB} {he : ∀ a, e a ∈ fibSec p σ B} {h : NoCommonZero e}
    (y : CxPts p σ) : ∑ a, (fs hB e he h).nsq (e a) y = 1 := by
  have hpos := h.sum_pos (mem_pick hB y)
  simp only [nsq, fs]
  rw [← Finset.sum_mul, Real.exp_neg, Real.exp_log hpos, mul_inv_cancel₀ hpos.ne']

variable [DecidableEq α]

variable (p σ) in

def combVal (b : α → B.Sec) (M : Matrix α α ℂ) (a : α) : B.ι → CxPts p σ → ℂ :=
  ∑ j, M j a • secVal p σ (b j)

omit [DecidableEq α] in

theorem combVal_eq (b : α → B.Sec) (M : Matrix α α ℂ) (a : α) :
    combVal p σ b M a = SecC.val (∑ j, M j a • SecC.of p σ (b j)) := by
  simp only [combVal, map_sum, map_smul, SecC.val_of]

theorem noCommonZero_combVal {b : α → B.Sec} (hb : ⨆ j, nonzeroLocus (b j) = ⊤)
    {M : Matrix α α ℂ} (hM : M.det ≠ 0) : NoCommonZero (combVal p σ b M) := by
  intro i y hi
  have hy : y ∈ ptsIn p σ (⨆ j, nonzeroLocus (b j)) := by rw [hb]; exact mem_ptsIn_top
  rw [mem_ptsIn, Opens.mem_iSup] at hy
  obtain ⟨j, hj⟩ := hy
  have hj' : secVal p σ (b j) i y ≠ 0 := (secVal_ne_zero_iff (b j) hi).2 (mem_ptsIn.2 hj)
  by_contra hcon
  push_neg at hcon
  have hv : Matrix.vecMul (fun l => secVal p σ (b l) i y) M = 0 := by
    funext a
    rw [Pi.zero_apply, ← hcon a]
    simp [combVal, Matrix.vecMul, dotProduct, Finset.sum_apply, mul_comm]
  exact hj' (congrFun (Matrix.eq_zero_of_vecMul_eq_zero hM hv) j)

variable (p σ) in

def fsBasis (hB : B.IsLB) (b : α → B.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (M : Matrix α α ℂ)
    (hM : M.det ≠ 0) : Weight p σ B :=
  fs hB (combVal p σ b M) (fun a => combVal_eq (p := p) (σ := σ) b M a ▸ SecC.val_mem _)
    (noCommonZero_combVal hb hM)

theorem fsBasis_φ (hB : B.IsLB) (b : α → B.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤)
    (M : Matrix α α ℂ) (hM : M.det ≠ 0) (i : B.ι) (y : CxPts p σ) :
    (fsBasis p σ hB b hb M hM).φ i y =
      Real.log (∑ a, ‖∑ j, M j a * valR y.1 (B.U i) ((b j).f i)‖ ^ 2) := by
  simp [fsBasis, fs, combVal, Finset.sum_apply, secVal_apply, ev]

end FS

end Weight

end GlobalTheory
