import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.FixK
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.MirabolicVectors.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCosetRepsOpenInCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardCosetRepsEqRelIndexStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCharacterSeparatingLatticeStatement
import Mathlib

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel

namespace PositivityTheory.RgUd.Form.LeviSmoothness.stab

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ann (ψ : AddChar k Circle) {n : ℕ} (A : AddSubgroup (Fin n → k)) : AddSubgroup (Fin n → k) where
  carrier := {η | ∀ a ∈ A, ψ (η ⬝ᵥ a) = 1}
  add_mem' {x y} hx hy a ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [add_dotProduct, AddChar.map_add_eq_mul, hx a ha, hy a ha, one_mul]
  zero_mem' a _ := by simp
  neg_mem' {x} hx a ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [neg_dotProduct, AddChar.map_neg_eq_inv, hx a ha, inv_one]

def ball (n : ℕ) (s : kˣ) : AddSubgroup (Fin n → k) where
  carrier := {x | ∀ i, valuation k (x i) ≤ valuation k (s : k)}
  add_mem' {a b} ha hb i := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply] at *
    exact Valuation.map_add_le _ (ha i) (hb i)
  zero_mem' i := by simp
  neg_mem' {a} ha i := by
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, Valuation.map_neg] at *
    exact ha i

def pre {n : ℕ} (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) : AddSubgroup (Fin n → k) :=
  A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom

def IsTr {X : Type} [AddCommGroup X] (A L : AddSubgroup X) (T : Finset X) : Prop :=
  (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L

theorem ann_anti {ψ : AddChar k Circle} {n : ℕ} {A A' : AddSubgroup (Fin n → k)} (h : A ≤ A') : ann ψ A' ≤ ann ψ A :=
  fun _ hη a ha => hη a (h ha)

section
variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V}

theorem avg_conj (hψ : Continuous ψ) (hπ : IsSmooth π) (g : GL (Fin (m + 1)) k) (ξ : Fin (m + 1) → k)
    {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v : V) :
    π (blkAt k (m + 1) N (by omega) g) (avg ψ h π ξ A v) =
      avg ψ h π (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵀ *ᵥ ξ) (pre g⁻¹ A)
        (π (blkAt k (m + 1) N (by omega) g) v) := by
  refine PositivityTheory.RgUd.Form.LeviSmoothness.mir.avg_conj ψ h π hψ hπ g ξ _ ?_ hA v
  intro x
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

end

section
variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

theorem form_inv (hB : Lv ψ h π s B) (g : GL (Fin (m + 1)) k) (hg : nabs k (Matrix.GeneralLinearGroup.det g) = 1)
    (a b : V) : B (π (blkAt k (m + 1) N (by omega) g) a) (π (blkAt k (m + 1) N (by omega) g) b) = B a b := by
  have e := hB.mir (glEmb k (m + 1) g) (glEmb_mem_Mir k (m + 1) g) a b
  rw [ColumnElementGluing.blkAt_glEmb h g, ColumnElementGluing.det_glEmb, hg, Real.one_rpow, Complex.ofReal_one, one_mul] at e
  exact e

end

end PositivityTheory.RgUd.Form.LeviSmoothness.stab
