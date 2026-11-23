import Mathlib
import Formalism.PeriodIntegrals.ScMuExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp

noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

section Lin

variable {n r : ℕ}

theorem spanLt_mono (e : Fin r → Fin n → ℂ) {a b : ℕ} (h : a ≤ b) : spanLt e a ≤ spanLt e b := by
  unfold spanLt
  exact Submodule.span_mono (Set.image_mono fun b (hb : b.1 < a) => lt_of_lt_of_le hb h)

theorem mulVec_eq_sub_add (g : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    g *ᵥ x = (g - 1) *ᵥ x + x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]

theorem sub_mem_spanLt {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ spanLt e a) : (g - 1) *ᵥ x ∈ spanLt e a := by
  have key : spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin (g - 1)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    exact spanLt_mono e (le_of_lt hb) (hg.1 b)
  exact key hx

theorem mem_spanLt_of_inS {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ spanLt e a) : g *ᵥ x ∈ spanLt e a := by
  rw [mulVec_eq_sub_add g x]
  exact Submodule.add_mem _ (sub_mem_spanLt hg a hx) hx

theorem inv_preserves {W : Submodule ℂ (Fin n → ℂ)} {g g' : Matrix (Fin n) (Fin n) ℂ} (h1 : g' * g = 1)
    (hW : ∀ x ∈ W, g *ᵥ x ∈ W) : ∀ x ∈ W, g' *ᵥ x ∈ W := by
  let f : W →ₗ[ℂ] W := (Matrix.mulVecLin g).restrict (fun x hx => hW x hx)
  have hf : Function.Injective f := by
    intro a b hab
    have h2 : g *ᵥ (a : Fin n → ℂ) = g *ᵥ (b : Fin n → ℂ) := congrArg Subtype.val hab
    have h3 := congrArg (fun y => g' *ᵥ y) h2
    simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h3
    exact Subtype.ext h3
  have hs : Function.Surjective f := LinearMap.injective_iff_surjective.mp hf
  intro x hx
  obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
  have hy' : g *ᵥ (y : Fin n → ℂ) = x := congrArg Subtype.val hy
  rw [← hy', Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  exact y.2

theorem mul_sub_one_mulVec (g g' : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    (g * g' - 1) *ᵥ x = g *ᵥ ((g' - 1) *ᵥ x) + (g - 1) *ᵥ x := by
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, mul_sub, mul_one,
    Matrix.one_mulVec] <;> abel

theorem inv_sub_one_mulVec {g g' : Matrix (Fin n) (Fin n) ℂ} (h1 : g' * g = 1) (x : Fin n → ℂ) :
    (g' - 1) *ᵥ x = -(g' *ᵥ ((g - 1) *ᵥ x)) := by
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec,
    neg_sub]

theorem inS_one (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : InS e z 1 := by
  unfold InS
  refine ⟨fun a => ?_, ?_⟩ <;> simp

theorem inS_mul {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (hg' : InS e z g') : InS e z (g * g') := by
  refine ⟨fun a => ?_, ?_⟩
  · rw [mul_sub_one_mulVec]
    exact Submodule.add_mem _ (mem_spanLt_of_inS hg _ (hg'.1 a)) (hg.1 a)
  · rw [mul_sub_one_mulVec]
    exact Submodule.add_mem _ (mem_spanLt_of_inS hg _ hg'.2) hg.2

theorem inS_inv {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (h1 : g' * g = 1) : InS e z g' := by
  have hp : ∀ (a : ℕ), ∀ x ∈ spanLt e a, g' *ᵥ x ∈ spanLt e a := fun a =>
    inv_preserves h1 (fun x hx => mem_spanLt_of_inS hg a hx)
  refine ⟨fun a => ?_, ?_⟩
  · rw [inv_sub_one_mulVec h1]
    exact Submodule.neg_mem _ (hp _ _ (hg.1 a))
  · rw [inv_sub_one_mulVec h1]
    exact Submodule.neg_mem _ (hp _ _ hg.2)

theorem inN_one (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : InN ε e z 1 := by
  unfold InN
  exact ⟨inS_one e z, fun y _ => by simp⟩

theorem inN_mul {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InN ε e z g) (hg' : InN ε e z g') : InN ε e z (g * g') := by
  refine ⟨inS_mul hg.1 hg'.1, fun y hy => ?_⟩
  rw [mul_sub_one_mulVec]
  exact Submodule.add_mem _ (mem_spanLt_of_inS hg.1 _ (hg'.2 y hy)) (hg.2 y hy)

theorem inN_inv {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InN ε e z g) (h1 : g' * g = 1) : InN ε e z g' := by
  refine ⟨inS_inv hg.1 h1, fun y hy => ?_⟩
  rw [inv_sub_one_mulVec h1]
  exact Submodule.neg_mem _
    (inv_preserves h1 (fun x hx => mem_spanLt_of_inS hg.1 r hx) _ (hg.2 y hy))

theorem isClosed_sub_mem (x : Fin n → ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ x ∈ W} := by
  have hc : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => (g - 1) *ᵥ x :=
    (continuous_id.sub continuous_const).matrix_mulVec continuous_const
  exact W.closed_of_finiteDimensional.preimage hc

theorem isClosed_inN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} := by
  have h1 : {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} =
      ((⋂ a : Fin r, {g | (g - 1) *ᵥ e a ∈ spanLt e a.1}) ∩ {g | (g - 1) *ᵥ z ∈ spanLt e r}) ∩
        ⋂ y ∈ {y : Fin n → ℂ | ∀ a, hJ ε (e a) y = 0}, {g | (g - 1) *ᵥ y ∈ spanLt e r} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, InN, InS]
  rw [h1]
  exact ((isClosed_iInter fun a => isClosed_sub_mem _ _).inter (isClosed_sub_mem _ _)).inter
    (isClosed_biInter fun y _ => isClosed_sub_mem _ _)

theorem hJ_mulVec {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g)
    (x y : Fin n → ℂ) : hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  unfold hJ
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg']

theorem fix_span {W : Set (Fin n → ℂ)} {g : Matrix (Fin n) (Fin n) ℂ} (hW : ∀ x ∈ W, g *ᵥ x = x) :
    ∀ x ∈ Submodule.span ℂ W, g *ᵥ x = x := by
  intro x hx
  have hle : Submodule.span ℂ W ≤ LinearMap.ker (Matrix.mulVecLin g - LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    simp [hW y hy]
  have hx' := hle hx
  simpa [sub_eq_zero] using hx'

theorem conj_sub_one {h x h' : Matrix (Fin n) (Fin n) ℂ} (hh : h * h' = 1) :
    h * x * h' - 1 = h * (x - 1) * h' := by
  rw [mul_sub, sub_mul, mul_one, hh]

theorem inN_conj {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ}
    {h h' x : Matrix (Fin n) (Fin n) ℂ} (hU : Formalism.REAL.inUJ ε h) (hh : h * h' = 1) (hh' : h' * h = 1)
    (he : ∀ a, h *ᵥ e a = e a) (hz : h *ᵥ z = z) (hx : InN ε e z x) : InN ε e z (h * x * h') := by
  have hfix : ∀ (a : ℕ), ∀ v ∈ spanLt e a, h *ᵥ v = v := fun a =>
    fix_span (fun v hv => by obtain ⟨b, _, rfl⟩ := hv; exact he b)
  have h'e : ∀ v, h *ᵥ v = v → h' *ᵥ v = v := fun v hv => by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, hh', Matrix.one_mulVec]
  have key : ∀ v, (h * x * h' - 1) *ᵥ v = h *ᵥ ((x - 1) *ᵥ (h' *ᵥ v)) := fun v => by
    rw [conj_sub_one hh]
    simp only [Matrix.mulVec_mulVec, mul_assoc]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, h'e _ (he a), hfix a.1 _ (hx.1.1 a)]
    exact hx.1.1 a
  · rw [key, h'e _ hz, hfix r _ hx.1.2]
    exact hx.1.2
  · have hy' : ∀ a, hJ ε (e a) (h' *ᵥ y) = 0 := fun a => by
      rw [← hJ_mulVec hU, he a, Matrix.mulVec_mulVec, hh, Matrix.one_mulVec]
      exact hy a
    rw [key, hfix r _ (hx.2 _ hy')]
    exact hx.2 _ hy'

end Lin

section Inst

variable (I : Formalism.MainNotions.S.AutInst)

theorem uMat_mul {n : ℕ} {ε : Fin n → Bool} (g h : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat (g * h) = Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat h := rfl

theorem uMat_one {n : ℕ} {ε : Fin n → Bool} : Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel, uMat_one]

theorem uMat_mul_inv {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel, uMat_one]

theorem uMat_inUJ {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Formalism.REAL.inUJ ε (Formalism.MainNotions.S.uMat g) := g.2

theorem continuous_uMat_apply (v : NumberField.InfinitePlace I.F) :
    Continuous fun s : I.Ginf => Formalism.MainNotions.S.uMat (s v) := (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)

variable {r : ℕ}

def NSub (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Subgroup I.Ginf where
  carrier := Ninf I e z
  one_mem' := fun v => by
    show InN _ _ _ (Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ (I.ε v)))
    rw [uMat_one]; exact inN_one _ _ _
  mul_mem' := fun {a b} ha hb v => by
    show InN _ _ _ (Formalism.MainNotions.S.uMat (a v * b v))
    rw [uMat_mul]; exact inN_mul (ha v) (hb v)
  inv_mem' := fun {a} ha v => by
    show InN _ _ _ (Formalism.MainNotions.S.uMat ((a v)⁻¹))
    exact inN_inv (ha v) (uMat_inv_mul (a v))

def HSub (S : Set (Fin I.n → I.E)) : Subgroup I.Ginf where
  carrier := Hset I S
  one_mem' := fun v x _ => by
    show Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ (I.ε v)) *ᵥ _ = _
    rw [uMat_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb v x hx => by
    show Formalism.MainNotions.S.uMat (a v * b v) *ᵥ _ = _
    rw [uMat_mul, ← Matrix.mulVec_mulVec, hb v x hx, ha v x hx]
  inv_mem' := fun {a} ha v x hx => by
    show Formalism.MainNotions.S.uMat ((a v)⁻¹) *ᵥ _ = _
    conv_lhs => rw [← ha v x hx]
    rw [Matrix.mulVec_mulVec, uMat_inv_mul, Matrix.one_mulVec]

theorem isClosed_Ninf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : IsClosed (Ninf I e z) := by
  have h1 : Ninf I e z = ⋂ v, (fun s : I.Ginf => Formalism.MainNotions.S.uMat (s v)) ⁻¹'
      {g | InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) g} := by
    ext s
    simp only [Ninf, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h1]
  exact isClosed_iInter fun v => (isClosed_inN _ _ _).preimage (continuous_uMat_apply I v)

theorem isClosed_Hset (S : Set (Fin I.n → I.E)) : IsClosed (Hset I S) := by
  have h1 : Hset I S = ⋂ v, ⋂ x ∈ S, {s : I.Ginf | Formalism.MainNotions.S.uMat (s v) *ᵥ rv I v x = rv I v x} := by
    ext s
    simp only [Hset, Set.mem_setOf_eq, Set.mem_iInter]
  rw [h1]
  refine isClosed_iInter fun v => isClosed_biInter fun x _ => ?_
  exact isClosed_eq ((continuous_uMat_apply I v).matrix_mulVec continuous_const) continuous_const

theorem measure_subFacts : SubFacts := by
  intro I r e f z
  refine ⟨NSub I e z, HSub I (frameSet I e f z), rfl, rfl, isClosed_Ninf I e z, isClosed_Hset I _, ?_⟩
  intro h hh x hx
  have hh' : h ∈ Hset I (frameSet I e f z) := hh
  have hx' : x ∈ Ninf I e z := hx
  show ∀ v, InN _ _ _ (Formalism.MainNotions.S.uMat ((h * x * h⁻¹) v))
  intro v
  show InN _ _ _ (Formalism.MainNotions.S.uMat (h v * x v * (h v)⁻¹))
  rw [uMat_mul, uMat_mul]
  exact inN_conj (uMat_inUJ _) (uMat_mul_inv _) (uMat_inv_mul _)
    (fun a => hh' v _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_range_self a))))
    (hh' v _ (Set.mem_union_right _ rfl)) (hx' v)

end Inst

end PI.ScMuExists.UnitaryGroupMassFormula
