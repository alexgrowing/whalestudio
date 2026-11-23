import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical

open MeasureTheory Matrix
open scoped Pointwise

namespace GlobalTheory.UnipChange

section Shear

variable {k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k]
  {ι : Type} [Fintype ι]

end Shear

section Linear

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]

open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in
private theorem map_mul_left_eq_smul' (a : F) (ha : a ≠ 0) :
    Measure.map (fun x => a * x) ν = distribHaarChar F (Units.mk0 a ha)⁻¹ • ν := by
  have hf : (fun x : F => a * x) = fun x => Units.mk0 a ha • x := by
    funext x; simp [Units.smul_def]
  ext s hs
  rw [Measure.map_apply (by rw [hf]; exact (continuous_const_smul _).measurable) hs, hf,
    Set.preimage_smul, ← distribHaarChar_mul ν]
  rw [Measure.coe_nnreal_smul_apply]

open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in
private theorem map_diagonal_mulVec_pi (D : κ → F) (hD : ∀ i, D i ≠ 0) :
    Measure.map (diagonal D).mulVec (Measure.pi fun _ : κ => ν)
      = (∏ i, distribHaarChar F (Units.mk0 (D i) (hD i))⁻¹) • Measure.pi fun _ : κ => ν := by
  have hfun : (diagonal D).mulVec = fun x i => (fun y => D i * y) (x i) := by
    funext x i; simp [mulVec_diagonal]
  haveI : ∀ i, SigmaFinite (Measure.map (fun y => D i * y) ν) := fun i => by
    rw [map_mul_left_eq_smul' ν (D i) (hD i)]; infer_instance
  rw [hfun, Measure.pi_map_pi (f := fun i y => D i * y)
    (fun i => (continuous_const.mul continuous_id).aemeasurable)]
  simp_rw [map_mul_left_eq_smul' ν _ (hD _)]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi, ENNReal.coe_finset_prod,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => Measure.coe_nnreal_smul_apply _ _ _

open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in
private theorem measurePreserving_transvection_mulVec (t : TransvectionStruct κ F) :
    MeasurePreserving t.toMatrix.mulVec (Measure.pi fun _ : κ => ν)
      (Measure.pi fun _ : κ => ν) := by
  let p : κ → Prop := fun i => i ≠ t.i
  let α : Type := { x // p x }
  let β : Type := { x // ¬p x }
  let g : (α → F) → (β → F) → β → F := fun a b => (fun _ => t.c * a ⟨t.j, t.hij.symm⟩) + b
  let G : (α → F) × (β → F) → (α → F) × (β → F) := fun q => (id q.1, g q.1 q.2)
  let e : (κ → F) ≃ᵐ (α → F) × (β → F) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : κ => F) p
  have hmv : t.toMatrix.mulVec = e.symm ∘ G ∘ e := by
    cases t with | mk i j hij c =>
    ext f k
    by_cases h : i = k
    · subst h
      simp [e, G, g, p, TransvectionStruct.toMatrix, transvection, mulVec, dotProduct,
        add_mul, Finset.sum_add_distrib, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd, Matrix.single, ite_and, Matrix.one_apply, ite_mul]
      ring
    · simp [e, G, g, p, TransvectionStruct.toMatrix, transvection, mulVec, dotProduct,
        add_mul, Finset.sum_add_distrib, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd, h, Matrix.single, ite_and, Ne.symm h, Matrix.one_apply,
        ite_mul]
  rw [hmv]
  have hA : MeasurePreserving e (Measure.pi fun _ : κ => ν)
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : κ => ν) p
  have hB : MeasurePreserving G ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν))
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν)) := by
    have hg : Measurable (Function.uncurry g) := by
      refine Measurable.add ?_ measurable_snd
      exact measurable_pi_lambda _ fun _ =>
        ((measurable_pi_apply _).comp measurable_fst).const_mul _
    exact (MeasurePreserving.id _).skew_product hg
      (Filter.Eventually.of_forall fun a => map_add_left_eq_self _ _)
  exact ((hA.symm e).comp hB).comp hA

open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in

theorem _root_.GlobalTheory.UnipChange.smul_map_mulVec_pi (M : Matrix κ κ F) (u : Fˣ)
    (hu : (u : F) = M.det) :
    (distribHaarChar F u : ENNReal) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν)
      = Measure.pi fun _ : κ => ν := by
  have hmeas : ∀ N : Matrix κ κ F, Measurable N.mulVec := fun N =>
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have key : ∀ u : Fˣ, (u : F) = M.det → Measure.map M.mulVec (Measure.pi fun _ : κ => ν)
      = distribHaarChar F u⁻¹ • Measure.pi fun _ : κ => ν := by
    refine diagonal_transvection_induction_of_det_ne_zero (fun N : Matrix κ κ F => ∀ u : Fˣ,
      (u : F) = N.det → Measure.map N.mulVec (Measure.pi fun _ : κ => ν)
        = distribHaarChar F u⁻¹ • Measure.pi fun _ : κ => ν) M
      (hu ▸ u.ne_zero) ?_ ?_ ?_
    · intro D hD u hu
      have hD' : ∀ i, D i ≠ 0 := fun i => by
        rw [det_diagonal] at hD
        exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
      rw [map_diagonal_mulVec_pi ν D hD']
      have hu' : u = ∏ i, Units.mk0 (D i) (hD' i) := by
        ext
        rw [hu, det_diagonal, Units.coe_prod]
        rfl
      rw [hu', ← Finset.prod_inv_distrib, map_prod]
    · intro t u hu
      have hu' : u = 1 := by
        ext
        rw [hu, TransvectionStruct.det, Units.val_one]
      rw [hu', inv_one, map_one, one_smul]
      exact (measurePreserving_transvection_mulVec ν t).map_eq
    · intro A B hA hB hPA hPB u hu
      have hcomp : (A * B).mulVec = A.mulVec ∘ B.mulVec :=
        funext fun x => (mulVec_mulVec x A B).symm
      have hu' : u = Units.mk0 _ hA * Units.mk0 _ hB := by
        ext
        simp [hu, det_mul]
      rw [hcomp, ← Measure.map_map (hmeas A) (hmeas B), hPB (Units.mk0 _ hB) rfl,
        Measure.map_smul, hPA (Units.mk0 _ hA) rfl, smul_smul, hu', _root_.mul_inv_rev, map_mul,
        mul_comm]
  rw [key u hu]
  ext s hs
  rw [Measure.smul_apply, Measure.coe_nnreal_smul_apply, smul_eq_mul, ← mul_assoc,
    ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one, one_mul]

end Linear

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointRadical

section Algebra

variable {k : Type} [Field k] {r : ℕ} {b : Fin r → ℕ}

variable (k b) in

def filt (t : ℕ) : Submodule k (Matrix (Fin r) (Fin r) k) where
  carrier := {X | ∀ i j, ¬ b i + t ≤ b j → X i j = 0}
  add_mem' := by
    intro X Y hX hY i j h
    simp [hX i j h, hY i j h]
  zero_mem' := by intro i j _; rfl
  smul_mem' := by
    intro c X hX i j h
    simp [hX i j h]

theorem mul_mem_filt {s t : ℕ} {X Y : Matrix (Fin r) (Fin r) k} (hX : X ∈ filt k b s)
    (hY : Y ∈ filt k b t) : X * Y ∈ filt k b (s + t) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : b i + s ≤ b l
  · rw [hY l j (by omega), mul_zero]
  · rw [hX i l hl, zero_mul]

theorem mem_filt_zero {X : Matrix (Fin r) (Fin r) k} (h : X.BlockTriangular b) : X ∈ filt k b 0 :=
  fun _ _ hij => h (by omega)

theorem mem_filt_one {X : Matrix (Fin r) (Fin r) k} (h : X ∈ lieRadical k b) : X ∈ filt k b 1 :=
  fun i j hij => h i j (by omega)

theorem pow_mem_filt {X : Matrix (Fin r) (Fin r) k} (h : X ∈ filt k b 1) (n : ℕ) :
    X ^ n ∈ filt k b n := by
  induction n with
  | zero => rw [pow_zero]; exact mem_filt_zero Matrix.blockTriangular_one
  | succ n ih => rw [pow_succ]; exact mul_mem_filt ih h

theorem pow_eq_zero {X : Matrix (Fin r) (Fin r) k} (h : X ∈ filt k b 1) :
    X ^ (Finset.univ.sup b + 1) = 0 := by
  ext i j
  refine pow_mem_filt h _ i j ?_
  have := Finset.le_sup (f := b) (Finset.mem_univ j)
  omega

def unip (X : lieRadical k b) : radical k b :=
  ⟨⟨1 + X, ∑ i ∈ Finset.range (Finset.univ.sup b + 1), (-(X : Matrix (Fin r) (Fin r) k)) ^ i,
    by
      rw [← sub_neg_eq_add, mul_neg_geom_sum, pow_eq_zero (neg_mem (mem_filt_one X.2)), sub_zero],
    by
      rw [← sub_neg_eq_add, geom_sum_mul_neg, pow_eq_zero (neg_mem (mem_filt_one X.2)), sub_zero]⟩,
    by
      show (1 + X : Matrix (Fin r) (Fin r) k) - 1 ∈ lieRadical k b
      simp⟩

def lg (n : radical k b) : lieRadical k b :=
  ⟨((n : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) - 1, n.2⟩

theorem lg_unip (X : lieRadical k b) : lg (unip X) = X := by
  apply Subtype.ext
  simp [lg, unip]

theorem unip_lg (n : radical k b) : unip (lg n) = n := by
  apply Subtype.ext
  apply Units.ext
  simp [lg, unip]

abbrev Pos (b : Fin r → ℕ) : Type := {p : Fin r × Fin r // b p.1 < b p.2}

variable (k b) in

def coord : lieRadical k b ≃ₗ[k] (Pos b → k) where
  toFun X p := (X : Matrix (Fin r) (Fin r) k) p.1.1 p.1.2
  invFun x := ⟨Matrix.of fun i j => if h : b i < b j then x ⟨(i, j), h⟩ else 0, fun i j h => by simp [h]⟩
  map_add' X Y := rfl
  map_smul' c X := rfl
  left_inv X := by
    apply Subtype.ext
    ext i j
    by_cases h : b i < b j
    · simp [h]
    · simp [h, X.2 i j h]
  right_inv x := by
    funext p
    simp [p.2]

theorem mem_filt_of_map (L : lieRadical k b ≃ₗ[k] lieRadical k b)
    (hL : ∀ t (X : lieRadical k b), X.1 ∈ filt k b t → (L X).1 ∈ filt k b t)
    (t : ℕ) (X : lieRadical k b) (hX : (L X).1 ∈ filt k b t) : X.1 ∈ filt k b t := by
  set U := (filt k b t).comap (lieRadical k b).subtype with hU
  have h1 : U.map (L : lieRadical k b →ₗ[k] lieRadical k b) = U := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨Y, hY, rfl⟩
      exact hL t Y hY
    · exact LinearEquiv.finrank_map_eq L U
  have h2 : L X ∈ U := hX
  rw [← h1] at h2
  obtain ⟨Y, hY, e⟩ := h2
  have : Y = X := L.injective e
  exact this ▸ hY

end Algebra

section Top

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]
  {r : ℕ} {b : Fin r → ℕ}

theorem continuous_lg_val :
    Continuous fun n : radical k b => (lg n : Matrix (Fin r) (Fin r) k) :=
  (Units.continuous_val.comp continuous_subtype_val).sub continuous_const

theorem continuous_coord_symm_val :
    Continuous fun x : Pos b → k => ((coord k b).symm x : Matrix (Fin r) (Fin r) k) := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun x : Pos b → k => if h : b i < b j then x ⟨(i, j), h⟩ else 0
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

variable (k b) in

def chart : (Pos b → k) ≃ₜ radical k b where
  toFun x := unip ((coord k b).symm x)
  invFun n := coord k b (lg n)
  left_inv x := by simp [lg_unip]
  right_inv n := by simp [unip_lg]
  continuous_toFun := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact continuous_const.add continuous_coord_symm_val
    · show Continuous fun x : Pos b → k => ∑ i ∈ Finset.range (Finset.univ.sup b + 1),
        (-((coord k b).symm x : Matrix (Fin r) (Fin r) k)) ^ i
      exact continuous_finset_sum _ fun i _ => (continuous_coord_symm_val (k := k) (b := b)).neg.pow i
  continuous_invFun := continuous_pi fun p => continuous_lg_val.matrix_elem _ _

theorem continuous_linear {ι : Type} [Fintype ι] (L : (ι → k) →ₗ[k] ι → k) : Continuous L := by
  classical
  have : (L : (ι → k) → ι → k) = (LinearMap.toMatrix' L).mulVec := by
    funext x
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rw [this]
  exact continuous_const.matrix_mulVec continuous_id

theorem factor (L : lieRadical k b ≃ₗ[k] lieRadical k b)
    (hL : ∀ t (X : lieRadical k b), X.1 ∈ filt k b t → (L X).1 ∈ filt k b t)
    (f : radical k b → radical k b) (hf : Continuous f)
    (hd : ∀ t n n', (lg n - lg n').1 ∈ filt k b t →
      ((lg (f n) - L (lg n)) - (lg (f n') - L (lg n'))).1 ∈ filt k b (t + 1)) :
    ∃ (L' : (Pos b → k) ≃ₗ[k] Pos b → k) (g : (Pos b → k) → Pos b → k),
      LinearMap.det (L' : (Pos b → k) →ₗ[k] Pos b → k)
        = LinearMap.det (L : lieRadical k b →ₗ[k] lieRadical k b) ∧ Continuous g ∧
      (∀ x y i, (∀ j : Pos b, b j.1.2 - b j.1.1 < b i.1.2 - b i.1.1 → x j = y j) → g x i = g y i) ∧
      f ∘ chart k b = chart k b ∘ L' ∘ fun x => x + g x := by
  set L' : (Pos b → k) ≃ₗ[k] Pos b → k := ((coord k b).symm.trans L).trans (coord k b) with hL'
  refine ⟨L', fun x => L'.symm ((chart k b).symm (f (chart k b x))) - x, ?_, ?_, ?_, ?_⟩
  · exact LinearMap.det_conj (L : lieRadical k b →ₗ[k] lieRadical k b) (coord k b)
  · exact ((continuous_linear (L'.symm : (Pos b → k) →ₗ[k] Pos b → k)).comp
      ((chart k b).symm.continuous.comp (hf.comp (chart k b).continuous))).sub continuous_id
  · intro x y i hxy
    have h1 : (lg (chart k b x) - lg (chart k b y)).1 ∈ filt k b (b i.1.2 - b i.1.1) := by
      intro p q hpq
      by_cases h : b p < b q
      · have := hxy ⟨(p, q), h⟩ (by simp only; omega)
        show ((lg (unip _) - lg (unip _) : lieRadical k b) : Matrix (Fin r) (Fin r) k) p q = 0
        rw [lg_unip, lg_unip]
        simp [coord, h, this]
      · exact (lg (chart k b x) - lg (chart k b y)).2 p q h
    have h2 := mem_filt_of_map L hL (b i.1.2 - b i.1.1 + 1)
      ((L.symm (lg (f (chart k b x))) - lg (chart k b x))
        - (L.symm (lg (f (chart k b y))) - lg (chart k b y)))
      (by simpa only [map_sub, LinearEquiv.apply_symm_apply] using hd _ _ _ h1) i.1.1 i.1.2
      (by have := i.2; omega)
    have h3 : ∀ z, L'.symm ((chart k b).symm (f (chart k b z))) - z
        = coord k b (L.symm (lg (f (chart k b z))) - lg (chart k b z)) := by
      intro z
      have e : coord k b (lg (chart k b z)) = z := (chart k b).symm_apply_apply z
      rw [map_sub, e]
      congr 1
      show L'.symm (coord k b (lg (f (chart k b z)))) = _
      simp [hL']
    rw [← sub_eq_zero]
    simp only [h3]
    exact h2
  · funext x
    simp

end Top

end GlobalTheory.UnipChange
