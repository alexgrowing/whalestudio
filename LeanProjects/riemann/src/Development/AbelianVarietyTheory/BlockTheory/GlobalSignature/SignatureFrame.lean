import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalRingCardinality.DataCD

open MeasureTheory Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SignatureFrame

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

structure SignFrame {n : ℕ} (ε : Fin n → Bool) (P Q : ℕ) where

  e : Fin P ⊕ Fin Q ≃ Fin n
  pos : ∀ i, ε (e (Sum.inl i)) = true
  neg : ∀ j, ε (e (Sum.inr j)) = false

variable {n P Q : ℕ} {ε : Fin n → Bool}

theorem SignFrame.reindex_J (F : SignFrame ε P Q) :
    Matrix.reindex F.e F.e (Formalism.UG.Jpq P Q) = Jm ε := by
  ext a b
  obtain ⟨x, rfl⟩ := F.e.surjective a
  obtain ⟨y, rfl⟩ := F.e.surjective b
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Formalism.UG.Jpq, Jm, Matrix.diagonal_apply, Matrix.one_apply, F.pos, F.neg]
  split_ifs <;> simp

def SignFrame.unitsMap (F : SignFrame ε P Q) :
    GL (Fin P ⊕ Fin Q) ℂ →* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  Units.map (Matrix.reindexAlgEquiv ℂ ℂ F.e).toMulEquiv.toMonoidHom

theorem SignFrame.unitsMap_val (F : SignFrame ε P Q) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    (F.unitsMap g : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.reindex F.e F.e (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := rfl

theorem SignFrame.inUJ_reindex (F : SignFrame ε P Q)
    (m : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    inUJ ε (Matrix.reindex F.e F.e m) ↔
      Formalism.UG.cT (starRingEnd ℂ) m * Formalism.UG.Jpq P Q * m = Formalism.UG.Jpq P Q := by
  unfold inUJ
  rw [← F.reindex_J]
  have h : Formalism.UG.cT (starRingEnd ℂ) m = mᴴ := by
    ext i j; simp [Formalism.UG.cT]
  rw [h]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  exact (Matrix.reindex F.e F.e).injective.eq_iff (a := mᴴ * Formalism.UG.Jpq P Q * m) (b := Formalism.UG.Jpq P Q)

def SignFrame.toDiag (F : SignFrame ε P Q) (g : UpqT P Q) : UJ ε :=
  let g' : Formalism.UG.Upq P Q := g
  ⟨F.unitsMap g'.1, (F.inUJ_reindex _).2 g'.2⟩

theorem SignFrame.umat_toDiag (F : SignFrame ε P Q) (g : UpqT P Q) :
    umat (F.toDiag g) = Matrix.reindex F.e F.e (UpqT.mat g) := rfl

theorem SignFrame.continuous_toDiag (F : SignFrame ε P Q) : Continuous F.toDiag := by
  refine Continuous.subtype_mk ?_ _
  refine Continuous.comp (g := F.unitsMap) ?_ continuous_subtype_val
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_reindex F.e F.e

theorem SignFrame.measurable_toDiag (F : SignFrame ε P Q) : Measurable F.toDiag := by
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  exact F.continuous_toDiag.measurable

theorem SignFrame.toDiag_mul (F : SignFrame ε P Q) (g h : UpqT P Q) :
    F.toDiag (g * h) = F.toDiag g * F.toDiag h :=
  Subtype.ext (map_mul F.unitsMap _ _)

theorem SignFrame.bijective_toDiag (F : SignFrame ε P Q) : Function.Bijective F.toDiag := by
  constructor
  · intro g h hgh
    have h1 : umat (F.toDiag g) = umat (F.toDiag h) := by rw [hgh]
    rw [F.umat_toDiag, F.umat_toDiag] at h1
    exact Subtype.ext (Units.ext ((Matrix.reindex F.e F.e).injective h1))
  · intro a
    let u : GL (Fin P ⊕ Fin Q) ℂ :=
      Units.map (Matrix.reindexAlgEquiv ℂ ℂ F.e.symm).toMulEquiv.toMonoidHom a.1
    have hu : Matrix.reindex F.e F.e (u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) = umat a :=
      (Matrix.reindex F.e F.e).apply_symm_apply (umat a)
    have hmem : u ∈ Formalism.UG.Upq P Q := (F.inUJ_reindex _).1 (by rw [hu]; exact a.2)
    exact ⟨(⟨u, hmem⟩ : Formalism.UG.Upq P Q), Subtype.ext (Units.ext hu)⟩

def cdMeasure (c : CDHaar) (F : SignFrame ε P Q) : Measure (UJ ε) :=
  Measure.map F.toDiag (c.cd P Q)

theorem cdMeasure_apply (c : CDHaar) (F : SignFrame ε P Q) {A : Set (UJ ε)} (hA : MeasurableSet A) :
    cdMeasure c F A = c.cd P Q (F.toDiag ⁻¹' A) :=
  Measure.map_apply F.measurable_toDiag hA

def SignFrame.mulEquiv (F : SignFrame ε P Q) : UpqT P Q ≃* UJ ε :=
  { Equiv.ofBijective F.toDiag F.bijective_toDiag with map_mul' := F.toDiag_mul }

theorem SignFrame.continuous_symm (F : SignFrame ε P Q) : Continuous F.mulEquiv.symm := by
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ →* GL (Fin P ⊕ Fin Q) ℂ :=
    Units.map (Matrix.reindexAlgEquiv ℂ ℂ F.e.symm).toMulEquiv.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ (continuous_id.matrix_reindex F.e.symm F.e.symm)
  have h : ∀ a : UJ ε, (F.mulEquiv.symm a : Formalism.UG.Upq P Q).1 = u a.1 := by
    intro a
    obtain ⟨g, rfl⟩ := F.mulEquiv.surjective a
    rw [MulEquiv.symm_apply_apply]
    exact Units.ext ((Matrix.reindex F.e F.e).symm_apply_apply _).symm
  refine continuous_induced_rng.2 ?_
  have : (Subtype.val ∘ fun a : UJ ε => (F.mulEquiv.symm a : Formalism.UG.Upq P Q)) = fun a => u a.1 :=
    funext h
  exact this ▸ hu.comp continuous_subtype_val

theorem cdMeasure_isHaar (c : CDHaar) (F : SignFrame ε P Q) : (cdMeasure c F).IsHaarMeasure := by
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI := c.haar P Q
  exact F.mulEquiv.isHaarMeasure_map (c.cd P Q) F.continuous_toDiag F.continuous_symm

def dimV {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  (∏ a : Fin n, ∏ b ∈ Ioi a, (lam a - lam b)) /
    ∏ a : Fin n, ∏ b ∈ Ioi a, (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))

theorem dimV_eq_fdegHC {n : ℕ} {lam : Fin n → ℝ} (h : StrictAnti lam) : dimV lam = fdegHC lam := by
  unfold dimV fdegHC
  simp only [Finset.filter_lt_eq_Ioi]
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b hb => ?_
  rw [abs_of_pos (sub_pos.2 (h (Finset.mem_Ioi.1 hb)))]

def HCFormalDegree : Prop :=
  ∀ (c : CDHaar) (n P Q : ℕ) (ε : Fin n → Bool) (F : SignFrame ε P Q) (lam : Fin n → ℝ),
    IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∀ w : H, w ≠ 0 → fdegOf (cdMeasure c F) σ w = dimV lam

theorem exists_signFrame (ε : Fin n → Bool) :
    Nonempty (SignFrame ε (Fintype.card {a // ε a = true}) (Fintype.card {a // ¬ ε a = true})) := by
  refine ⟨⟨(Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
    (Equiv.sumCompl fun a => ε a = true), fun i => ?_, fun j => ?_⟩⟩
  · simpa using ((Fintype.equivFin {a // ε a = true}).symm i).2
  · simpa using ((Fintype.equivFin {a // ¬ ε a = true}).symm j).2

example (x y : ℝ) : dimV ![x, y] = x - y := by
  simp [dimV, Fin.prod_univ_succ]

example (x y z : ℝ) : dimV ![x, y, z] = (x - y) * (x - z) * (y - z) / 2 := by
  simp [dimV, Fin.prod_univ_succ, Fin.prod_Ioi_zero, Fin.prod_Ioi_succ]
  norm_num

end GlobalTheory.IndefiniteRowSideFullHecke.SignatureFrame
