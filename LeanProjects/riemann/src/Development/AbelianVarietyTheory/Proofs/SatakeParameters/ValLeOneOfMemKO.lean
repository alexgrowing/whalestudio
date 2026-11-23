import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll

noncomputable section

namespace GlobalTheory.BlockType

open GlobalTheory.SplitWeil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le_one_of_mem_KO {n : Type} [Fintype n] [DecidableEq n] {h : GL n k} (hh : h ∈ KO k n) (a b : n) :
    valuation k (h.val a b) ≤ 1 := by
  obtain ⟨g, rfl⟩ := hh
  exact (g.val a b).2

theorem val_col_lt {n : Type} [Fintype n] [DecidableEq n] {h g : GL n k} (hh : h ∈ KO k n) (b : n)
    (hg : ∀ c, valuation k ((g.val - 1) c b) < 1) (a : n) : valuation k ((h.val * (g.val - 1)) a b) < 1 := by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_lt _ one_ne_zero fun c _ => by
    rw [map_mul]; exact Right.mul_lt_one_of_le_of_lt (val_le_one_of_mem_KO hh a c) (hg c)

variable (k) in

def blockGrp (r t : ℕ) : Subgroup (GL (Fin (r + t)) k) where
  carrier := {h | h ∈ KO k (Fin (r + t)) ∧
    ∀ (a : Fin (r + t)) (j : Fin r), valuation k ((h.val - 1) a (Fin.castAdd t j)) < 1}
  one_mem' := ⟨(KO k _).one_mem, fun a j => by simp⟩
  mul_mem' := by
    rintro h g ⟨hh, h1⟩ ⟨hg, g1⟩
    refine ⟨(KO k _).mul_mem hh hg, fun a j => ?_⟩
    have e : ((h * g).val - 1) = h.val * (g.val - 1) + (h.val - 1) := by
      simp only [Units.val_mul, Matrix.mul_sub, Matrix.mul_one]; abel
    rw [e, Matrix.add_apply]
    exact Valuation.map_add_lt _ (val_col_lt hh _ (fun c => g1 c j) a) (h1 a j)
  inv_mem' := by
    rintro h ⟨hh, h1⟩
    refine ⟨(KO k _).inv_mem hh, fun a j => ?_⟩
    have e : ((h⁻¹ : GL (Fin (r + t)) k).val - 1) = -((h⁻¹ : GL (Fin (r + t)) k).val * (h.val - 1)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]; abel
    rw [e, Matrix.neg_apply, Valuation.map_neg]
    exact val_col_lt ((KO k _).inv_mem hh) _ (fun c => h1 c j) a

open Classical in

def blockChar {r t : ℕ} (χ : kˣ →* ℂˣ) (h : GL (Fin (r + t)) k) : ℂ :=
  if hd : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det = 0 then 0 else (χ (Units.mk0 _ hd) : ℂ)

theorem blockChar_eq {r t : ℕ} (χ : kˣ →* ℂˣ) (h : GL (Fin (r + t)) k) (u : kˣ)
    (hu : (u : k) = (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) : blockChar χ h = χ u := by
  have hd : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ≠ 0 := hu ▸ u.ne_zero
  rw [blockChar, dif_neg hd]
  congr 2
  ext; simp [hu]

theorem mem_blockGrp {r t : ℕ} {h : GL (Fin (r + t)) k} (hK : h ∈ KO k (Fin (r + t)))
    (h1 : ∀ (i : Fin t) (j : Fin r), valuation k (h.val (Fin.natAdd r i) (Fin.castAdd t j)) < 1)
    (h2 : ∀ i j : Fin r, valuation k (h.val (Fin.castAdd t i) (Fin.castAdd t j) - if i = j then 1 else 0) < 1) :
    h ∈ blockGrp k r t := by
  refine ⟨hK, fun a j => ?_⟩
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a
  · have := h2 i j
    simpa [Matrix.sub_apply, Matrix.one_apply, Fin.castAdd_inj] using this
  · have := h1 i j
    have hne : Fin.natAdd r i ≠ Fin.castAdd t j := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    simpa [Matrix.sub_apply, Matrix.one_apply, hne] using this

theorem isBlockVec_of {r t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (χ : kˣ →* ℂˣ)
    (π : Representation ℂ (GL (Fin (r + t)) k) W) (v : W)
    (hv : ∀ h ∈ blockGrp k r t, π h v = blockChar χ h • v) : GlobalTheory.SplitRead.IsBlockVec χ π v := by
  intro h hK h1 h2 u hu
  rw [hv h (mem_blockGrp hK h1 h2), blockChar_eq χ h u hu]

theorem kOne_le_blockGrp (r t : ℕ) : KOne k (Fin (r + t)) ≤ blockGrp k r t := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨⟨g, rfl⟩, fun a j => ?_⟩
  have hg' : ∀ a b, IsLocalRing.residue 𝒪[k] (g.val a b) = (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝓀[k]) a b := by
    intro a b
    have := congrArg (fun x : GL (Fin (r + t)) 𝓀[k] => x.val a b) hg
    simpa using this
  have hm : g.val a (Fin.castAdd t j) - (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) a (Fin.castAdd t j) ∈ 𝓂[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hg']
    by_cases e : a = Fin.castAdd t j <;> simp [Matrix.one_apply, e]
  have := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp ((IsLocalRing.mem_maximalIdeal _).1 hm)
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g).val - 1) a (Fin.castAdd t j) =
      ((g.val a (Fin.castAdd t j) - (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) a (Fin.castAdd t j) : 𝒪[k]) : k) := by
    by_cases e : a = Fin.castAdd t j <;> simp [Matrix.one_apply, e] <;> rfl
  rw [e]; exact this

theorem blockChar_kOne {r t : ℕ} (χ : kˣ →* ℂˣ) (hχ : IsTame χ) {h : GL (Fin (r + t)) k}
    (hh : h ∈ KOne k (Fin (r + t))) : blockChar χ h = 1 := by
  obtain ⟨g, hg, rfl⟩ := hh
  have hg' : (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).map (IsLocalRing.residue 𝒪[k]) = 1 := by
    have := congrArg (fun x : GL (Fin (r + t)) 𝓀[k] => x.val) hg
    ext a b
    have h2 := congrArg (fun M : Matrix (Fin (r + t)) (Fin (r + t)) 𝓀[k] => M (Fin.natAdd r a) (Fin.natAdd r b)) this
    simpa [Matrix.one_apply, Fin.natAdd_inj] using h2
  have hm : (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1 ∈ 𝓂[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, RingHom.map_det, RingHom.mapMatrix_apply, hg', Matrix.det_one, map_one, sub_self]
  have hv := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp ((IsLocalRing.mem_maximalIdeal _).1 hm)
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
      (((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) := by
    rw [show ((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : k) =
      algebraMap 𝒪[k] k (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det from rfl, RingHom.map_det]
    rfl
  have hne : (((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) ≠ 0 := by
    intro h0
    have : (((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1 : 𝒪[k]) : k) = -1 := by
      push_cast; rw [h0]; ring
    rw [this, Valuation.map_neg, map_one] at hv
    exact lt_irrefl _ hv
  rw [blockChar_eq χ _ (Units.mk0 _ hne) e.symm, hχ (Units.mk0 _ hne) (by simpa using hv)]
  simp

end GlobalTheory.BlockType
