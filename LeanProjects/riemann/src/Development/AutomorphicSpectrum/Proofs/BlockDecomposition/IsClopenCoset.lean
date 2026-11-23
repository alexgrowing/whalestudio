import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {d : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

variable (k d) in

@[ext] structure COSub where

  sub : AddSubgroup (Fin d → k)
  isOpen : IsOpen (sub : Set (Fin d → k))
  isCompact : IsCompact (sub : Set (Fin d → k))

def gHom (g : GL (Fin d) k) : (Fin d → k) →+ (Fin d → k) :=
  (Matrix.mulVecLin (g : Matrix (Fin d) (Fin d) k)).toAddMonoidHom

theorem gHom_apply (g : GL (Fin d) k) (y : Fin d → k) : gHom g y = (g : Matrix (Fin d) (Fin d) k).mulVec y := rfl

def COSub.act (L : COSub k d) (g : GL (Fin d) k) : COSub k d where
  sub := L.sub.comap (gHom g⁻¹)
  isOpen := L.isOpen.preimage (glHomeo g).symm.continuous
  isCompact := (glHomeo g).symm.isCompact_preimage.2 L.isCompact

theorem COSub.mem_act {L : COSub k d} {g : GL (Fin d) k} {y : Fin d → k} :
    y ∈ (L.act g).sub ↔ ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y ∈ L.sub := Iff.rfl

theorem COSub.mulVec_mem_act {L : COSub k d} (g : GL (Fin d) k) {y : Fin d → k} :
    (g : Matrix (Fin d) (Fin d) k).mulVec y ∈ (L.act g).sub ↔ y ∈ L.sub := by
  rw [COSub.mem_act, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem COSub.act_one (L : COSub k d) : L.act 1 = L := by
  ext y
  simp [COSub.mem_act]

theorem COSub.act_act (L : COSub k d) (g h : GL (Fin d) k) : (L.act g).act h = L.act (h * g) := by
  ext y
  simp only [COSub.mem_act, mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev]

theorem COSub.act_mono {L L' : COSub k d} (h : L'.sub ≤ L.sub) (g : GL (Fin d) k) :
    (L'.act g).sub ≤ (L.act g).sub := fun _ hy => h hy

def lat0 : COSub k d where
  sub :=
    { carrier := {y | ∀ i, ValuativeRel.valuation k (y i) ≤ 1}
      add_mem' := fun ha hb i => by
        rw [Pi.add_apply]
        exact (Valuation.map_add _ _ _).trans (max_le (ha i) (hb i))
      zero_mem' := fun i => by simp
      neg_mem' := fun ha i => by
        rw [Pi.neg_apply, Valuation.map_neg]
        exact ha i }
  isOpen := by
    have e : {y : Fin d → k | ∀ i, ValuativeRel.valuation k (y i) ≤ 1} = Set.univ.pi fun _ => cball (1 : kˣ) := by
      ext y
      simp [cball, Set.mem_pi]
    show IsOpen {y : Fin d → k | ∀ i, ValuativeRel.valuation k (y i) ≤ 1}
    rw [e]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball 1
  isCompact := by
    have e : {y : Fin d → k | ∀ i, ValuativeRel.valuation k (y i) ≤ 1} = Set.univ.pi fun _ => cball (1 : kˣ) := by
      ext y
      simp [cball, Set.mem_pi]
    show IsCompact {y : Fin d → k | ∀ i, ValuativeRel.valuation k (y i) ≤ 1}
    rw [e]
    exact isCompact_univ_pi fun _ => isCompact_cball 1

def latZ (z : GL (Fin d) k) (r : ℤ) : COSub k d := lat0.act (z ^ r)

def IsReps (L' L : COSub k d) (S : Finset (Fin d → k)) : Prop :=
  (∀ s ∈ S, s ∈ L.sub) ∧ ∀ y ∈ L.sub, ∃! s, s ∈ S ∧ y - s ∈ L'.sub

theorem isClopen_coset (L : COSub k d) (c : Fin d → k) : IsClopen {y | y - c ∈ L.sub} :=
  ⟨L.isCompact.isClosed.preimage (continuous_id.sub continuous_const),
    L.isOpen.preimage (continuous_id.sub continuous_const)⟩

open Classical in

def ind (L : COSub k d) (c : Fin d → k) (a : V) : SchF k d V :=
  ⟨fun y => if y - c ∈ L.sub then a else 0, by
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, ?_⟩
    · by_cases hx : x - c ∈ L.sub
      · filter_upwards [(isClopen_coset L c).isOpen.mem_nhds hx] with y hy
        have hy' : y - c ∈ L.sub := hy
        rw [if_pos hx, if_pos hy']
      · filter_upwards [(isClopen_coset L c).compl.isOpen.mem_nhds hx] with y hy
        have hy' : y - c ∉ L.sub := hy
        rw [if_neg hx, if_neg hy']
    · refine HasCompactSupport.intro (L.isCompact.image (continuous_add_right c)) fun x hx => ?_
      rw [if_neg]
      intro h
      exact hx ⟨x - c, h, by simp⟩⟩

open Classical in
theorem ind_apply (L : COSub k d) (c y : Fin d → k) (a : V) :
    (ind L c a).1 y = if y - c ∈ L.sub then a else 0 := rfl

theorem ind_add_mem (L : COSub k d) (x : Fin d → k) {l : Fin d → k} (hl : l ∈ L.sub) (a : V) :
    ind L (x + l) a = ind L x a := by
  refine Subtype.ext (funext fun y => ?_)
  rw [ind_apply, ind_apply]
  have : y - (x + l) ∈ L.sub ↔ y - x ∈ L.sub := by
    have e : y - (x + l) = y - x - l := by abel
    rw [e]
    exact ⟨fun h => by simpa using L.sub.add_mem h hl, fun h => L.sub.sub_mem h hl⟩
  by_cases h : y - x ∈ L.sub
  · rw [if_pos h, if_pos (this.2 h)]
  · rw [if_neg h, if_neg (mt this.1 h)]

theorem ind_add (L : COSub k d) (c : Fin d → k) (a b : V) : ind L c (a + b) = ind L c a + ind L c b := by
  refine Subtype.ext (funext fun y => ?_)
  show (ind L c (a + b)).1 y = (ind L c a).1 y + (ind L c b).1 y
  simp only [ind_apply]
  split_ifs <;> simp

theorem ind_smul (L : COSub k d) (c : Fin d → k) (t : ℂ) (a : V) : ind L c (t • a) = t • ind L c a := by
  refine Subtype.ext (funext fun y => ?_)
  show (ind L c (t • a)).1 y = t • (ind L c a).1 y
  simp only [ind_apply]
  split_ifs <;> simp

theorem shiftF_ind (L : COSub k d) (x c : Fin d → k) (a : V) : shiftF x (ind L c a) = ind L (c - x) a := by
  refine Subtype.ext (funext fun y => ?_)
  rw [shiftF_apply, ind_apply, ind_apply]
  have e : y + x - c = y - (c - x) := by abel
  rw [e]

theorem actF_ind (X : Representation ℂ (GL (Fin d) k) V) (g : GL (Fin d) k) (L : COSub k d) (c : Fin d → k) (a : V) :
    actF X g (ind L c a) = ind (L.act g) ((g : Matrix (Fin d) (Fin d) k).mulVec c) (X g a) := by
  refine Subtype.ext (funext fun y => ?_)
  rw [actF_apply, ind_apply, ind_apply]
  have e : ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec (y - (g : Matrix (Fin d) (Fin d) k).mulVec c) =
      ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y - c := by
    rw [mulVec_sub, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have h : (y - (g : Matrix (Fin d) (Fin d) k).mulVec c ∈ (L.act g).sub) ↔
      ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y - c ∈ L.sub := by
    rw [COSub.mem_act, e]
  by_cases hc : ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y - c ∈ L.sub
  · rw [if_pos hc, if_pos (h.2 hc)]
  · rw [if_neg hc, if_neg (mt h.1 hc), map_zero]

def mL (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (a : V) (a' : V') : ℂ :=
  B (ind L x a) (ind L 0 a')

theorem B_ind_ind (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ)
    (hT : ∀ x f f', B (shiftF x f) (shiftF x f') = B f f') (L : COSub k d) (c c' : Fin d → k) (a : V) (a' : V') :
    B (ind L c a) (ind L c' a') = mL B L (c - c') a a' := by
  rw [mL, ← hT c' (ind L c a) (ind L c' a'), shiftF_ind, shiftF_ind, sub_self]

theorem mL_act (X : Representation ℂ (GL (Fin d) k) V) (Y : Representation ℂ (GL (Fin d) k) V')
    (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ)
    (hG : ∀ g f f', B (actF X g f) (actF Y g f') = B f f') (g : GL (Fin d) k) (L : COSub k d) (x : Fin d → k)
    (a : V) (a' : V') :
    mL B (L.act g) ((g : Matrix (Fin d) (Fin d) k).mulVec x) (X g a) (Y g a') = mL B L x a a' := by
  rw [mL, mL, ← hG g (ind L x a) (ind L 0 a'), actF_ind, actF_ind, mulVec_zero]

theorem mL_add_mem (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) {l : Fin d → k}
    (hl : l ∈ L.sub) (a : V) (a' : V') : mL B L (x + l) a a' = mL B L x a a' := by
  rw [mL, mL, ind_add_mem L x hl]

theorem mL_add_left (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (a b : V) (a' : V') :
    mL B L x (a + b) a' = mL B L x a a' + mL B L x b a' := by
  simp [mL, ind_add]

theorem mL_add_right (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (a : V) (a' b' : V') :
    mL B L x a (a' + b') = mL B L x a a' + mL B L x a b' := by
  simp [mL, ind_add]

theorem mL_smul_left (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (t : ℂ) (a : V) (a' : V') :
    mL B L x (t • a) a' = t * mL B L x a a' := by
  simp [mL, ind_smul]

theorem mL_smul_right (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (a : V) (t : ℂ) (a' : V') :
    mL B L x a (t • a') = t * mL B L x a a' := by
  simp [mL, ind_smul]

def Refines (F : COSub k d → (Fin d → k) → ℂ) : Prop :=
  ∀ (L' L : COSub k d) (S : Finset (Fin d → k)), L'.sub ≤ L.sub → IsReps L' L S → ∀ x,
    (S.card : ℂ) * F L x = ∑ s ∈ S, F L' (x + s)

end GlobalTheory.CompanionTheory.BZCore

end
