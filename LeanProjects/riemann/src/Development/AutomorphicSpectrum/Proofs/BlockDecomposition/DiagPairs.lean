import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PExpbSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel

namespace GlobalTheory.CompanionTheory.IwJac

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

def nO : Subgroup (GL (Fin n) k) := iwahori k (Fin n) ⊓ unipB k (Fin n)

variable {k n}

def tor (ϖ : kˣ) (x : Fin n → ℤ) : GL (Fin n) k := diagT k (Fin n) fun i => ϖ ^ x i

def Deep (ϖ : kˣ) (x : Fin n → ℤ) (d : ℕ) (g : GL (Fin n) k) : Prop :=
  ∀ i j : Fin n, i < j → j.val ≤ i.val + d →
    valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k (((ϖ ^ (x i - x j) : kˣ)) : k)

theorem Deep.mul {ϖ : kˣ} {x : Fin n → ℤ} {d : ℕ} {g h : GL (Fin n) k} (hg : g ∈ nO k n) (hh : h ∈ nO k n)
    (dg : Deep ϖ x d g) (dh : Deep ϖ x d h) : Deep ϖ x d (g * h) := by
  intro i j hij hd
  obtain ⟨g0, g1⟩ := (mem_unipB k).1 hg.2
  obtain ⟨h0, h1⟩ := (mem_unipB k).1 hh.2
  rw [Units.val_mul, Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rcases lt_trichotomy l i with hl | rfl | hl
  · rw [g0 i l hl, zero_mul, map_zero]; exact zero_le'
  · rw [g1, one_mul]; exact dh _ _ hij hd
  rcases lt_trichotomy l j with hl' | rfl | hl'
  · rw [map_mul]
    have e : (((ϖ ^ (x i - x j) : kˣ)) : k) = ((ϖ ^ (x i - x l) : kˣ) : k) * ((ϖ ^ (x l - x j) : kˣ) : k) := by
      rw [← Units.val_mul, ← _root_.zpow_add]; congr 2; ring
    rw [e, map_mul]
    exact mul_le_mul' (dg _ _ hl (by have := Fin.lt_def.1 hl'; omega))
      (dh _ _ hl' (by have := Fin.lt_def.1 hl; omega))
  · rw [h1, mul_one]; exact dg _ _ hij hd
  · rw [h0 l j hl', mul_zero, map_zero]; exact zero_le'

def filt (ϖ : kˣ) (x : Fin n → ℤ) (d : ℕ) : Subgroup (GL (Fin n) k) where
  carrier := {g | g ∈ nO k n ∧ Deep ϖ x d g ∧ Deep ϖ x d g⁻¹}
  one_mem' := by
    have h1 : Deep ϖ x d (1 : GL (Fin n) k) := fun i j hij _ => by
      rw [Units.val_one, Matrix.one_apply_ne hij.ne, map_zero]; exact zero_le'
    exact ⟨one_mem _, h1, by simpa using h1⟩
  mul_mem' := by
    rintro g h ⟨hg, dg, dg'⟩ ⟨hh, dh, dh'⟩
    refine ⟨mul_mem hg hh, dg.mul hg hh dh, ?_⟩
    rw [_root_.mul_inv_rev]
    exact dh'.mul (inv_mem hh) (inv_mem hg) dg'
  inv_mem' := by
    rintro g ⟨hg, dg, dg'⟩
    exact ⟨inv_mem hg, dg', by simpa using dg⟩

theorem mem_filt {ϖ : kˣ} {x : Fin n → ℤ} {d : ℕ} {g : GL (Fin n) k} :
    g ∈ filt ϖ x d ↔ g ∈ nO k n ∧ Deep ϖ x d g ∧ Deep ϖ x d g⁻¹ := Iff.rfl

def diagPairs (n d : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.2.val = p.1.val + (d + 1)

end GlobalTheory.CompanionTheory.IwJac

end
