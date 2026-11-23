import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFinite
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows
open scoped ContDiff

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CutOff

section Row

variable {R : Type} [CommRing R] {k : ℕ}

def eRow (R : Type) [CommRing R] (k : ℕ) : Fin k → R := fun c => if (c : ℕ) + 1 = k then 1 else 0

def lastEnt (r : Fin k → R) : R := ∑ c : Fin k, if (c : ℕ) + 1 = k then r c else 0

def lastRowM (A : Matrix (Fin k) (Fin k) R) : Fin k → R := fun c => ∑ i : Fin k, if (i : ℕ) + 1 = k then A i c else 0

def rowM (r : Fin k → R) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun i c => if (i : ℕ) + 1 = k then r c else (1 : Matrix (Fin k) (Fin k) R) i c

def rowI (r : Fin k → R) : Fin k → R :=
  fun c => if (c : ℕ) + 1 = k then Ring.inverse (lastEnt r) else -(r c * Ring.inverse (lastEnt r))

theorem rowM_apply_last (r : Fin k → R) (i c : Fin k) (h : (i : ℕ) + 1 = k) : rowM r i c = r c := by
  simp [rowM, h]

theorem rowM_apply_ne (r : Fin k → R) (i c : Fin k) (h : (i : ℕ) + 1 ≠ k) :
    rowM r i c = (1 : Matrix (Fin k) (Fin k) R) i c := by
  simp [rowM, h]

theorem lastEnt_eq (r : Fin k → R) (l : Fin k) (hl : (l : ℕ) + 1 = k) : lastEnt r = r l := by
  rw [lastEnt, Finset.sum_eq_single l]
  · simp [hl]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by omega))
  · simp

theorem rowM_mul_rowM (r t : Fin k → R) (l : Fin k) (hl : (l : ℕ) + 1 = k) (i c : Fin k) :
    (rowM r * rowM t) i c = if (i : ℕ) + 1 = k then
      (if (c : ℕ) + 1 = k then r l * t c else r c + r l * t c) else rowM t i c := by
  have hlast : ∀ j : Fin k, (j : ℕ) + 1 = k → j = l := fun j hj => Fin.ext (by omega)
  by_cases hi : (i : ℕ) + 1 = k
  · rw [if_pos hi, Matrix.mul_apply]
    have e : ∀ j, rowM r i j * rowM t j c =
        r j * (if j = l then t c else (1 : Matrix (Fin k) (Fin k) R) j c) := fun j => by
      rw [rowM_apply_last r i j hi]
      by_cases hj : j = l
      · subst hj; rw [rowM_apply_last t _ c hl, if_pos rfl]
      · rw [rowM_apply_ne t j c (fun h => hj (hlast j h)), if_neg hj]
    simp only [e]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
    have e2 : ∀ j ∈ Finset.univ.erase l, r j * (if j = l then t c else (1 : Matrix (Fin k) (Fin k) R) j c) =
        if j = c then r j else 0 := fun j hj => by
      rw [if_neg (Finset.ne_of_mem_erase hj), Matrix.one_apply]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl e2, if_pos rfl, Finset.sum_ite_eq' ]
    by_cases hc : (c : ℕ) + 1 = k
    · have : c = l := hlast c hc
      subst this
      simp [hc]
    · have : c ≠ l := fun h => hc (h ▸ hl)
      simp [hc, this, add_comm]
  · rw [if_neg hi, Matrix.mul_apply]
    simp only [rowM_apply_ne r i _ hi, Matrix.one_apply]
    simp

variable {r : Fin k → R}

theorem rowM_mul_rowI (h : IsUnit (lastEnt r)) : rowM r * rowM (rowI r) = 1 := by
  ext i c
  by_cases hk : ∃ l : Fin k, (l : ℕ) + 1 = k
  · obtain ⟨l, hl⟩ := hk
    have hu : r l * Ring.inverse (r l) = 1 := by
      rw [← lastEnt_eq r l hl] at *
      exact Ring.mul_inverse_cancel _ h
    rw [rowM_mul_rowM _ _ l hl]
    have e : Ring.inverse (lastEnt r) = Ring.inverse (r l) := by rw [lastEnt_eq r l hl]
    by_cases hi : (i : ℕ) + 1 = k
    · have hil : i = l := Fin.ext (by omega)
      subst hil
      by_cases hc : (c : ℕ) + 1 = k
      · have hcl : c = i := Fin.ext (by omega)
        subst hcl
        simp only [if_pos hl, rowI, e, Matrix.one_apply, if_true]
        exact hu
      · have hcl : i ≠ c := fun h => hc (h ▸ hl)
        simp only [if_pos hl, if_neg hc, rowI, e, Matrix.one_apply, if_neg hcl]
        linear_combination (- r c) * hu
    · rw [if_neg hi, rowM_apply_ne _ _ _ hi]
  · exact absurd ⟨⟨k - 1, by have := i.2; omega⟩, by have := i.2; simp; omega⟩ hk

theorem rowI_mul_rowM (h : IsUnit (lastEnt r)) : rowM (rowI r) * rowM r = 1 := by
  ext i c
  by_cases hk : ∃ l : Fin k, (l : ℕ) + 1 = k
  · obtain ⟨l, hl⟩ := hk
    have hu : r l * Ring.inverse (r l) = 1 := by
      rw [← lastEnt_eq r l hl] at *
      exact Ring.mul_inverse_cancel _ h
    rw [rowM_mul_rowM _ _ l hl]
    have e : Ring.inverse (lastEnt r) = Ring.inverse (r l) := by rw [lastEnt_eq r l hl]
    have el : rowI r l = Ring.inverse (r l) := by simp [rowI, hl, e]
    by_cases hi : (i : ℕ) + 1 = k
    · have hil : i = l := Fin.ext (by omega)
      subst hil
      by_cases hc : (c : ℕ) + 1 = k
      · have hcl : c = i := Fin.ext (by omega)
        subst hcl
        simp only [if_pos hl, el, Matrix.one_apply, if_true]
        linear_combination hu
      · have hcl : i ≠ c := fun h => hc (h ▸ hl)
        simp only [if_pos hl, if_neg hc, el, Matrix.one_apply, if_neg hcl]
        simp only [rowI, if_neg hc, e]
        ring
    · rw [if_neg hi, rowM_apply_ne _ _ _ hi]
  · exact absurd ⟨⟨k - 1, by have := i.2; omega⟩, by have := i.2; simp; omega⟩ hk

open Classical in

def rowGL (r : Fin k → R) : GL (Fin k) R :=
  if h : IsUnit (lastEnt r) then ⟨rowM r, rowM (rowI r), rowM_mul_rowI h, rowI_mul_rowM h⟩ else 1

theorem rowGL_val (h : IsUnit (lastEnt r)) : (rowGL r).val = rowM r := by
  simp [rowGL, h]

theorem rowGL_inv_val (h : IsUnit (lastEnt r)) : ((rowGL r)⁻¹).val = rowM (rowI r) := by
  simp [rowGL, h]

theorem lastEnt_eRow (hk : 1 ≤ k) : lastEnt (eRow R k) = 1 := by
  rw [lastEnt_eq _ ⟨k - 1, by omega⟩ (by simp; omega)]
  simp [eRow]; omega

theorem rowM_eRow : rowM (eRow R k) = 1 := by
  ext i c
  by_cases hi : (i : ℕ) + 1 = k
  · rw [rowM_apply_last _ _ _ hi, eRow, Matrix.one_apply]
    by_cases hc : (c : ℕ) + 1 = k
    · rw [if_pos hc, if_pos (Fin.ext (by omega))]
    · rw [if_neg hc, if_neg (fun h : i = c => hc (h ▸ hi))]
  · rw [rowM_apply_ne _ _ _ hi]

theorem rowGL_eRow (hk : 1 ≤ k) : rowGL (eRow R k) = 1 := by
  by_cases h : IsUnit (lastEnt (eRow R k))
  · exact Units.ext ((rowGL_val h).trans rowM_eRow)
  · simp [rowGL, h]

theorem lastRow_mul_rowGL_inv (A : GL (Fin k) R) (h : IsUnit (lastEnt r)) (hA : lastRowM A.val = r) :
    Mir (k - 1) (A * (rowGL r)⁻¹) := by
  intro i j hij
  have hi : (i : ℕ) + 1 = k := by have := i.2; have := j.2; omega
  have e1 : ∀ m, A.val i m = rowM r i m := fun m => by
    rw [rowM_apply_last _ _ _ hi, ← hA, lastRowM, Finset.sum_eq_single i]
    · rw [if_pos hi]
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext (by omega))
    · simp
  have e2 : (A * (rowGL r)⁻¹).val i j = (rowM r * rowM (rowI r)) i j := by
    rw [Units.val_mul, rowGL_inv_val h, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [e1]
  rw [e2, rowM_mul_rowI h]

end Row

section Adelic

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def latS (S : Finset (Pl E)) (B : ∀ w : Pl E, AddSubgroup (w.adicCompletion E)) : AddSubgroup (Af E) where
  carrier := {a | (∀ w, w ∉ S → pLoc E w a ∈ Formalism.UG.Ov E w) ∧ ∀ w ∈ S, pLoc E w a ∈ B w}
  add_mem' := fun {a b} ha hb => ⟨fun w hw => by
      rw [map_add]; exact add_mem (ha.1 w hw) (hb.1 w hw), fun w hw => by
      rw [map_add]; exact add_mem (ha.2 w hw) (hb.2 w hw)⟩
  zero_mem' := ⟨fun w _ => by rw [map_zero]; exact zero_mem _, fun w _ => by rw [map_zero]; exact zero_mem _⟩
  neg_mem' := fun {a} ha => ⟨fun w hw => by
      rw [map_neg]; exact neg_mem (ha.1 w hw), fun w hw => by
      rw [map_neg]; exact neg_mem (ha.2 w hw)⟩

variable (E k) in

def nuFin : Measure (Fin k → Af E) := Measure.pi fun _ => GroundTheory.Global.finiteAdeleMeasure E

def boxL (L : Set (Af E)) (c : Fin k → Af E) : Set (Fin k → Af E) := {f | ∀ i, f i - c i ∈ L}

variable [IsTotallyComplex E]

variable (E k) in

def nuInf : Measure (Fin k → Cinf E) :=
  (Measure.pi fun _ => GroundTheory.Global.infiniteAdeleMeasure E).map fun y i => (infEq E).symm (y i)

def glue (S : Finset (Pl E)) (a : GL (Fin k) (Cinf E)) (u : ∀ w : Pl E, GL (Fin k) (w.adicCompletion E)) : GA E k :=
  (S.toList.map fun w => fl k w (u w)).prod * infGL E k a

def sOf (S : Finset (Pl E)) (y : Fin k → Ad E) : GA E k :=
  glue S (rowGL fun i => pInf E (y i)) fun w => rowGL fun i => pLoc E w (pFin E (y i))

def etaOf (b : (Fin k → Cinf E) → ℝ) (L : Set (Af E)) (y : Fin k → Ad E) : ℝ :=
  b (fun i => pInf E (y i)) * (boxL L (eRow (Af E) k)).indicator (fun _ => 1) fun i => pFin E (y i)

end Adelic

end GlobalTheory.CompanionTheory.CutOff
end
