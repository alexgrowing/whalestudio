import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2

variable {F : Type} [Field F] [NumberField F]

variable (F) in

def Cell : Set (G1 F) := {g | IsUnit (g 1 0)}
theorem inv_mem_cell {g : G1 F} (h : g ∈ Cell F) : g⁻¹ ∈ Cell F := by
  change IsUnit ((g⁻¹).1 1 0)
  rw [specialLinear_inv_val]; exact IsUnit.neg h
theorem nmwn_val (b₁ b₂ : A F) (a : (A F)ˣ) : (nU b₁ * mD a * wW F * nU b₂).1 =
    !![-(b₁ * ((a⁻¹ : (A F)ˣ) : A F)), a - b₁ * ((a⁻¹ : (A F)ˣ) : A F) * b₂;
      -((a⁻¹ : (A F)ˣ) : A F), -(((a⁻¹ : (A F)ˣ) : A F) * b₂)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
theorem nmwn_mem_cell (b₁ b₂ : A F) (a : (A F)ˣ) : nU b₁ * mD a * wW F * nU b₂ ∈ Cell F := by
  change IsUnit ((nU b₁ * mD a * wW F * nU b₂).1 1 0)
  rw [nmwn_val]; exact (a⁻¹).isUnit.neg

theorem cell_normal (g : G1 F) (c : (A F)ˣ) (hc : g 1 0 = c) :
    g = nU (g 0 0 * ((c⁻¹ : (A F)ˣ) : A F)) * mD (-c⁻¹) * wW F * nU (((c⁻¹ : (A F)ˣ) : A F) * g 1 1) := by
  have hd := specialLinear_det_entries g
  have hu := c.mul_inv
  rw [hc] at hd
  refine Subtype.ext ?_
  rw [nmwn_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [hc]
  linear_combination (-((c⁻¹ : (A F)ˣ) : A F)) * hd - g 0 1 * hu
theorem nmwn_unique {b₁ b₂ b₁' b₂' : A F} {a a' : (A F)ˣ}
    (h : nU b₁ * mD a * wW F * nU b₂ = nU b₁' * mD a' * wW F * nU b₂') : b₁ = b₁' ∧ a = a' ∧ b₂ = b₂' := by
  have h' := congrArg Subtype.val h
  rw [nmwn_val, nmwn_val] at h'
  have h10 := congrFun (congrFun h' 1) 0
  have h00 := congrFun (congrFun h' 0) 0
  have h11 := congrFun (congrFun h' 1) 1
  simp at h10 h00 h11
  obtain rfl : a = a' := Units.ext h10
  exact ⟨(Units.mul_left_inj _).1 h00, rfl, (Units.mul_right_inj _).1 h11⟩
theorem mem_cell_iff (g : G1 F) : g ∈ Cell F ↔ ∃ b₁ a b₂, g = nU b₁ * mD a * wW F * nU b₂ :=
  ⟨fun h => ⟨_, _, _, cell_normal g (IsUnit.unit h) rfl⟩, by rintro ⟨b₁, a, b₂, rfl⟩; exact nmwn_mem_cell _ _ _⟩

theorem lmn_normal (g : G1 F) (a : (A F)ˣ) (ha : g 0 0 = a) :
    g = nL (g 1 0 * ((a⁻¹ : (A F)ˣ) : A F)) * mD a * nU (((a⁻¹ : (A F)ˣ) : A F) * g 0 1) := by
  have hd := specialLinear_det_entries g
  have hu := a.mul_inv
  rw [ha] at hd
  apply specialLinear_ext_entries <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha]
  linear_combination ((a⁻¹ : (A F)ˣ) : A F) * hd - g 1 1 * hu

theorem upper_normal (g : G1 F) (h : g 1 0 = 0) : ∃ b a, g = nU b * mD a := by
  have hd := specialLinear_det_entries g
  rw [h, mul_zero, sub_zero] at hd
  refine ⟨g 0 1 * g 0 0, ⟨g 0 0, g 1 1, hd, by rw [mul_comm, hd]⟩, ?_⟩
  apply specialLinear_ext_entries <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h]
  rw [mul_assoc, hd, mul_one]

variable (F) in

def p1 : A F →+* InfiniteAdeleRing F := RingHom.fst _ _
variable (F) in

def p2 : A F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _

def pv (v : HeightOneSpectrum (𝓞 F)) : A F →+* v.adicCompletion F :=
  (RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F) v).comp (RingHom.snd _ _)
theorem adeleInfiniteComponent_apply (x : A F) : p1 F x = x.1 := rfl
theorem adele_ext_components (x : A F) : p2 F x = x.2 := rfl
theorem pv_apply (v : HeightOneSpectrum (𝓞 F)) (x : A F) : pv v x = x.2 v := rfl
theorem a_ext {x y : A F} (h1 : p1 F x = p1 F y) (h2 : ∀ v, pv v x = pv v y) : x = y := Prod.ext h1 (FiniteAdeleRing.ext F h2)
theorem isUnit_adele_iff (x : A F) :
    IsUnit x ↔ (∀ w, x.1 w ≠ 0) ∧ (∀ v, x.2 v ≠ 0) ∧ ∀ᶠ v in cofinite, Valued.v (x.2 v) = 1 := by
  rw [← FiniteAdeleRing.isUnit_iff]
  refine Iff.trans (Prod.isUnit_iff (x := (x : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))) (and_congr_left fun _ => ?_)
  exact (Pi.isUnit_iff (M := fun w : InfinitePlace F => w.Completion)).trans (forall_congr' fun _ => isUnit_iff_ne_zero)

private theorem map_eq_one_iff' {R : Type} [CommRing R] (f : A F →+* R) (g : G1 F) :
    Matrix.SpecialLinearGroup.map f g = 1 ↔ ∀ i j, f (g i j) = f ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) := by
  have e : ∀ i j, f ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) = (1 : Matrix (Fin 2) (Fin 2) R) i j := fun i j => by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  simp only [e]
  exact ⟨fun h i j => congrFun (congrFun (congrArg Subtype.val h) i) j, fun h => Subtype.ext (Matrix.ext h)⟩
theorem infOne_iff (g : G1 F) : InfOne g ↔ Matrix.SpecialLinearGroup.map (p1 F) g = 1 := (map_eq_one_iff' (p1 F) g).symm
theorem at_iff (v : HeightOneSpectrum (𝓞 F)) (g : G1 F) :
    At v g ↔ InfOne g ∧ ∀ v' ≠ v, Matrix.SpecialLinearGroup.map (pv v') g = 1 :=
  and_congr_right fun _ => forall₂_congr fun v' _ => (map_eq_one_iff' (pv v') g).symm
theorem InfOne.one : InfOne (1 : G1 F) := fun _ _ => rfl
theorem InfOne.mul {g h : G1 F} (hg : InfOne g) (hh : InfOne h) : InfOne (g * h) := by
  rw [infOne_iff] at *; rw [map_mul, hg, hh, mul_one]
theorem InfOne.inv {g : G1 F} (hg : InfOne g) : InfOne g⁻¹ := by rw [infOne_iff] at *; rw [map_inv, hg, inv_one]
theorem At.one (v : HeightOneSpectrum (𝓞 F)) : At v (1 : G1 F) := ⟨InfOne.one, fun _ _ _ _ => rfl⟩
theorem At.mul {v : HeightOneSpectrum (𝓞 F)} {g h : G1 F} (hg : At v g) (hh : At v h) : At v (g * h) := by
  rw [at_iff] at *; exact ⟨hg.1.mul hh.1, fun v' hv => by rw [map_mul, hg.2 v' hv, hh.2 v' hv, mul_one]⟩
theorem At.inv {v : HeightOneSpectrum (𝓞 F)} {g : G1 F} (hg : At v g) : At v g⁻¹ := by
  rw [at_iff] at *; exact ⟨hg.1.inv, fun v' hv => by rw [map_inv, hg.2 v' hv, inv_one]⟩
theorem IntAt.one (v : HeightOneSpectrum (𝓞 F)) : IntAt v (1 : G1 F) := fun i j => by
  change pv v ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) ∈ _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]
theorem IntAt.mul {v : HeightOneSpectrum (𝓞 F)} {g h : G1 F} (hg : IntAt v g) (hh : IntAt v h) : IntAt v (g * h) := fun i j => by
  change pv v ((g * h) i j) ∈ _
  rw [specialLinear_mul_entry, map_add, map_mul, map_mul]
  exact add_mem (mul_mem (hg i 0) (hh 0 j)) (mul_mem (hg i 1) (hh 1 j))
theorem IntAt.inv {v : HeightOneSpectrum (𝓞 F)} {g : G1 F} (hg : IntAt v g) : IntAt v g⁻¹ := fun i j => by
  change pv v ((g⁻¹).1 i j) ∈ _
  rw [specialLinear_inv_val]
  fin_cases i <;> fin_cases j
  exacts [hg 1 1, neg_mem (hg 0 1), neg_mem (hg 1 0), hg 0 0]
theorem eventually_intAt (g : G1 F) : ∀ᶠ v in cofinite, IntAt v g :=
  eventually_all.2 fun i => eventually_all.2 fun j => (g i j).2.2
theorem infOrth_iff (g : G1 F) : InfOrth g ↔ g.1.map (p1 F) * (g.1.map (p1 F))ᵀ = 1 := by
  rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_one (p1 F) (map_zero _) (map_one _), ← Matrix.ext_iff]
  rfl
theorem InfOne.infOrth {g : G1 F} (hg : InfOne g) : InfOrth g := by
  have : g.1.map (p1 F) = 1 := congrArg Subtype.val ((infOne_iff g).1 hg)
  rw [infOrth_iff, this]; simp
theorem InfOrth.one : InfOrth (1 : G1 F) := InfOne.one.infOrth
theorem InfOrth.mul {g h : G1 F} (hg : InfOrth g) (hh : InfOrth h) : InfOrth (g * h) := by
  rw [infOrth_iff] at *
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (h.1.map _), hh, Matrix.one_mul, hg]
theorem InfOrth.inv {g : G1 F} (hg : InfOrth g) : InfOrth g⁻¹ := by
  rw [infOrth_iff] at *
  have h1 : (g⁻¹).1.map (p1 F) * g.1.map (p1 F) = 1 := by
    rw [← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    exact Matrix.map_one (p1 F) (map_zero _) (map_one _)
  have h2 : (g⁻¹).1.map (p1 F) = (g.1.map (p1 F))ᵀ := by
    rw [← Matrix.mul_one ((g⁻¹).1.map _), ← hg, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [h2, Matrix.transpose_transpose, ← h2, h1]
variable (F) in

def KG : Subgroup (G1 F) where
  carrier := KK F
  one_mem' := ⟨InfOrth.one, IntAt.one⟩
  mul_mem' hg hh := ⟨hg.1.mul hh.1, fun v => (hg.2 v).mul (hh.2 v)⟩
  inv_mem' hg := ⟨hg.1.inv, fun v => (hg.2 v).inv⟩
theorem mem_KG {g : G1 F} : g ∈ KG F ↔ g ∈ KK F := Iff.rfl
theorem wW_mem_KK : wW F ∈ KK F := by
  refine ⟨fun i j => ?_, fun v i j => ?_⟩
  · have : (wW F).1 * (wW F).1ᵀ = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [this]
  · change pv v ((wW F).1 i j) ∈ _
    fin_cases i <;> fin_cases j <;> simp

def sv (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : A F :=
  (0, ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    rw [Pi.single_eq_of_ne hw]; exact zero_mem _⟩)
@[simp] theorem finiteProjection_single_same (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : p1 F (sv v x) = 0 := rfl
@[simp] theorem pv_sv (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : pv v (sv v x) = x :=
  Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x
theorem pv_sv_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : v.adicCompletion F) : pv w (sv v x) = 0 :=
  Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) h x
theorem sv_mul_left (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (b : A F) : sv v x * b = sv v (x * pv v b) :=
  a_ext (by simp) fun w => by
    by_cases h : w = v
    · subst h; simp
    · simp [pv_sv_of_ne h]
theorem sv_mul (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) : sv v x * sv v y = sv v (x * y) := by
  rw [sv_mul_left, pv_sv]
theorem sv_add (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) : sv v (x + y) = sv v x + sv v y :=
  a_ext (by simp) fun w => by
    by_cases h : w = v
    · subst h; simp
    · simp [pv_sv_of_ne h]
theorem eq_sv {v : HeightOneSpectrum (𝓞 F)} {b : A F} (h1 : b.1 = 0) (h2 : ∀ w ≠ v, b.2 w = 0) : b = sv v (b.2 v) :=
  a_ext h1 fun w => by
    by_cases h : w = v
    · subst h; exact (pv_sv _ _).symm
    · rw [pv_sv_of_ne h]; exact h2 w h
variable (F) in

def eInf : A F := (1, 0)
theorem eInf_idem : eInf F * eInf F = eInf F := Prod.ext (mul_one _) (mul_zero _)
theorem eInf_mul (b : A F) : eInf F * b = (b.1, 0) := Prod.ext (one_mul _) (zero_mul _)
theorem one_sub_eInf_mul (b : A F) : (1 - eInf F) * b = (0, b.2) :=
  Prod.ext (by change (1 - 1) * b.1 = 0; simp) (by change (1 - 0) * b.2 = b.2; simp)

def cut (e : A F) (he : e * e = e) : G1 F →* G1 F where
  toFun g := ⟨!![e * g 0 0 + (1 - e), e * g 0 1; e * g 1 0, e * g 1 1 + (1 - e)], by
    rw [Matrix.det_fin_two_of]
    linear_combination (g 0 0 * g 1 1 - g 0 1 * g 1 0 - g 0 0 - g 1 1 + 1) * he + e * specialLinear_det_entries g⟩
  map_one' := by apply specialLinear_ext_entries <;> simp
  map_mul' g h := by
    apply specialLinear_ext_entries <;> refine Eq.trans ?_ (specialLinear_mul_entry _ _ _ _).symm <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-(g 0 0 * h 0 0 + g 0 1 * h 1 0 - g 0 0 - h 0 0 + 1)) * he
    · linear_combination (-(g 0 0 * h 0 1 + g 0 1 * h 1 1 - h 0 1 - g 0 1)) * he
    · linear_combination (-(g 1 0 * h 0 0 + g 1 1 * h 1 0 - g 1 0 - h 1 0)) * he
    · linear_combination (-(g 1 0 * h 0 1 + g 1 1 * h 1 1 - g 1 1 - h 1 1 + 1)) * he
theorem cut_val (e : A F) (he : e * e = e) (g : G1 F) :
    (cut e he g).1 = !![e * g 0 0 + (1 - e), e * g 0 1; e * g 1 0, e * g 1 1 + (1 - e)] := rfl
theorem cut_nU (e : A F) (he : e * e = e) (b : A F) : cut e he (nU b) = nU (e * b) := by apply specialLinear_ext_entries <;> simp [cut_val]
theorem cut_nL (e : A F) (he : e * e = e) (b : A F) : cut e he (nL b) = nL (e * b) := by apply specialLinear_ext_entries <;> simp [cut_val]

def Lev (r : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ)) : AddSubgroup (A F) where
  carrier := {x | x.1 = 0 ∧ ∀ v, Valued.v (x.2 v) ≤ r v}
  zero_mem' := ⟨rfl, fun v => by change Valued.v (pv v 0) ≤ _; simp⟩
  add_mem' {x y} hx hy := ⟨by change p1 F (x + y) = 0; rw [map_add, adeleInfiniteComponent_apply, adeleInfiniteComponent_apply, hx.1, hy.1, add_zero],
    fun v => by change Valued.v (pv v (x + y)) ≤ _; rw [map_add]; exact Valuation.map_add_le _ (hx.2 v) (hy.2 v)⟩
  neg_mem' {x} hx := ⟨by change p1 F (-x) = 0; rw [map_neg, adeleInfiniteComponent_apply, hx.1, neg_zero],
    fun v => by change Valued.v (pv v (-x)) ≤ _; rw [map_neg, Valuation.map_neg]; exact hx.2 v⟩
theorem mem_Lev {r : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ)} {x : A F} :
    x ∈ Lev r ↔ x.1 = 0 ∧ ∀ v, Valued.v (x.2 v) ≤ r v := Iff.rfl

def IsLev (r : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ)) : Prop :=
  (∀ v, r v ≠ 0) ∧ (∀ v, r v ≤ 1) ∧ ∀ᶠ v in cofinite, r v = 1

def InLev (r : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ)) (g : G1 F) : Prop :=
  ∀ i j, g i j - (1 : Matrix (Fin 2) (Fin 2) (A F)) i j ∈ Lev r

end UpperTheory.ConvolutionTheory.R2

end
