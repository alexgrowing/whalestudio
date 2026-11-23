import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ParabolicFundamentalDomain

noncomputable section

namespace PI.IwaMeasEx.PD

open Matrix Formalism.L2.S.S7.WittLeviSubgroups

section Gen

variable {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin n)

def RelM (g Fm : Matrix (Fin n) (Fin n) R) (T : Matrix ι ι R) : Prop :=
  g * Fm = Fm * T.submatrix e.symm e.symm

def cols (Fm : Matrix (Fin n) (Fin n) R) (r : ι) : Fin n → R := fun i => Fm i (e r)

variable {e}

theorem coord_zero {Fm Fi : Matrix (Fin n) (Fin n) R} (hF : Fi * Fm = 1) (S : Set ι) {u : Fin n → R}
    (hu : u ∈ Submodule.span R (cols e Fm '' S)) (s : ι) (hs : s ∉ S) : (Fi *ᵥ u) (e s) = 0 := by
  have hle : Submodule.span R (cols e Fm '' S) ≤
      LinearMap.ker ((LinearMap.proj (e s)).comp (Matrix.toLin' Fi)) := by
    rw [Submodule.span_le]
    rintro _ ⟨r, hr, rfl⟩
    have hrs : e r ≠ e s := fun h' => hs (e.injective h' ▸ hr)
    have h1 : (Fi *ᵥ cols e Fm r) (e s) = (Fi * Fm) (e s) (e r) := by
      simp only [Matrix.mulVec, dotProduct, cols, Matrix.mul_apply]
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.proj_apply, h1,
      hF, Matrix.one_apply_ne (Ne.symm hrs)]
  have := hle hu
  rwa [LinearMap.mem_ker, LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.proj_apply] at this

theorem entry_zero {Fm Fi : Matrix (Fin n) (Fin n) R} (hF : Fi * Fm = 1) (S : Set ι) {g : GL (Fin n) R}
    (hg : g ∈ Formalism.UG.stabGL (Submodule.span R (cols e Fm '' S))) (s r : ι) (hr : r ∈ S) (hs : s ∉ S) :
    (Fi * (g : Matrix (Fin n) (Fin n) R) * Fm) (e s) (e r) = 0 := by
  have hu : (g : Matrix (Fin n) (Fin n) R) *ᵥ cols e Fm r ∈ Submodule.span R (cols e Fm '' S) :=
    (hg _).1 (Submodule.subset_span ⟨r, hr, rfl⟩)
  have h1 := coord_zero hF S hu s hs
  rw [Matrix.mulVec_mulVec] at h1
  rw [← h1]
  simp only [Matrix.mulVec, dotProduct, cols, Matrix.mul_apply]

variable (lev : ι → ℕ)

def BLo (T : Matrix ι ι R) : Prop := ∀ s r, lev r < lev s → T s r = 0

def BHi (T : Matrix ι ι R) : Prop := ∀ s r, lev s < lev r → T s r = 0

def BUn (T : Matrix ι ι R) : Prop := BLo lev T ∧ ∀ s r, lev s = lev r → T s r = if s = r then 1 else 0

def bd (T : Matrix ι ι R) : Matrix ι ι R := fun s r => if lev s = lev r then T s r else 0

theorem bd_mul {T Ti : Matrix ι ι R} (hT : BLo lev T) (hTi : BLo lev Ti) (h : T * Ti = 1) :
    bd lev T * bd lev Ti = 1 := by
  ext s r
  rw [Matrix.mul_apply]
  by_cases hl : lev s = lev r
  · rw [← h, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [bd]
    by_cases h1 : lev s = lev t
    · rw [if_pos h1, if_pos (show lev t = lev r by omega)]
    · rw [if_neg h1, zero_mul]
      rcases Nat.lt_or_ge (lev t) (lev s) with h2 | h2
      · rw [hT s t h2, zero_mul]
      · rw [hTi t r (by omega), mul_zero]
  · have hsr : s ≠ r := fun h' => hl (by rw [h'])
    rw [Matrix.one_apply_ne hsr]
    refine Finset.sum_eq_zero fun t _ => ?_
    simp only [bd]
    by_cases h1 : lev s = lev t
    · rw [if_neg (show ¬ lev t = lev r by omega), mul_zero]
    · rw [if_neg h1, zero_mul]

end Gen

section Form

variable {R : Type} [CommRing R] [StarRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (lev : ι → ℕ) (a : ℕ)

def AntiLev (W : Matrix ι ι R) : Prop := ∀ q r, W q r ≠ 0 → lev q + lev r = 2 * a

def RowProp (W : Matrix ι ι R) : Prop :=
  ∀ s, a < lev s → ∃ t, lev t + lev s = 2 * a ∧ lev t < a ∧ ∀ q, W t q = if q = s then 1 else 0

def PBT (T : Matrix ι ι R) : Prop := ∀ s r, lev r < a → lev r < lev s → T s r = 0

end Form

end PI.IwaMeasEx.PD

end
