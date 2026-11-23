import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth

theorem continuous_glEmb (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ) :
    Continuous (glEmb k n) := by
  have hm : Continuous (glEmbMat k n) := by
    refine continuous_matrix fun a b => ?_
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simpa [glEmbMat] using continuous_const
      | cast b => simpa [glEmbMat] using continuous_const
    | cast a =>
      induction b using Fin.lastCases with
      | last => simpa [glEmbMat] using continuous_const
      | cast b =>
        simpa [glEmbMat] using (continuous_id.matrix_elem a b)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hm.comp Units.continuous_val
  · exact hm.comp (Units.continuous_coe_inv)

theorem continuous_sEmb (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : Continuous (sEmb k n) :=
  Continuous.subtype_mk ((continuous_glEmb k (n + 1)).comp continuous_subtype_val) _

theorem isOpen_rightInv {M X : Type} [Group M] [TopologicalSpace M] [IsTopologicalGroup M] (e : M → X) (A : Set M)
    (hA : IsOpen A) (h1 : (1 : M) ∈ A) (h : ∀ g ∈ A, ∀ m, e (m * g) = e m) :
    IsOpen {g : M | ∀ m, e (m * g) = e m} := by
  let T : Subgroup M :=
    { carrier := {g | ∀ m, e (m * g) = e m}
      mul_mem' := by
        intro a b ha hb m
        rw [← mul_assoc, hb, ha]
      one_mem' := by
        intro m
        rw [mul_one]
      inv_mem' := by
        intro a ha m
        have := ha (m * a⁻¹)
        rw [inv_mul_cancel_right] at this
        exact this.symm }
  exact T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hA.mem_nhds h1) h)

section Fix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}
  {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

def fixX (f : XS τ σ) : Set (Mir k ((i + 1) + (t + 1))) :=
  {x | ind (HPG k (i + 1) (t + 1)) (sigX τ σ) x (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1 =
    (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1}

theorem isOpen_fixX (f : XS τ σ) : IsOpen (fixX f) :=
  (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).2

theorem one_mem_fixX (f : XS τ σ) : (1 : Mir k ((i + 1) + (t + 1))) ∈ fixX f := by
  show ind (HPG k (i + 1) (t + 1)) (sigX τ σ) 1 _ = _
  rw [map_one]
  rfl

theorem evX_mul_of_mem (f : XS τ σ) {x : Mir k ((i + 1) + (t + 1))} (hx : x ∈ fixX f)
    (p : Mir k ((i + 1) + (t + 1))) : evX f (p * x) = evX f p :=
  congrArg (fun w : indSpace (HPG k (i + 1) (t + 1)) (sigX τ σ) => w.1 p) hx

theorem intC_mul (ψ : AddChar k Circle) (f : XS τ σ) (m g : Mir k ((i + 1) + t))
    (h : sEmb k ((i + 1) + t) g ∈ fixX f) :
    intC ψ f (sEmb k ((i + 1) + t) (m * g)) = intC ψ f (sEmb k ((i + 1) + t) m) := by
  unfold intC
  congr 1
  funext d
  have h2 : dEmb k i t d * sEmb k ((i + 1) + t) (m * g) =
      (dEmb k i t d * sEmb k ((i + 1) + t) m) * sEmb k ((i + 1) + t) g := by
    rw [MonoidHom.map_mul, mul_assoc]
  rw [h2]
  exact congrArg (fun v => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • v)
    (evX_mul_of_mem f h (dEmb k i t d * sEmb k ((i + 1) + t) m))

theorem eC_mul (ψ : AddChar k Circle) (f : XS τ σ) (m g : Mir k ((i + 1) + t))
    (h : sEmb k ((i + 1) + t) g ∈ fixX f) (h2 : dpowM (k := k) ((i + 1) + t) (-1 / 2) g = 1) :
    eC ψ f (m * g) = eC ψ f m := by
  have h5 : dpowM (k := k) ((i + 1) + t) (-1 / 2) (m * g) = dpowM ((i + 1) + t) (-1 / 2) m :=
    ((dpowM (k := k) ((i + 1) + t) (-1 / 2)).map_mul m g).trans (by rw [h2, mul_one])
  unfold eC
  exact congrArg₂ (fun (c : ℂˣ) v => (c : ℂ) • qC τ σ v) h5 (intC_mul ψ f m g h)

end Fix

theorem isOpen_eC_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1))
    (σ : GRep k (t + 1)) (f : XS τ σ),
    IsOpen {g : Mir k ((i + 1) + t) | ∀ m, eC ψ f (m * g) = eC ψ f m} := by
  intro k _ _ _ _ i t ψ τ σ f
  have hA : IsOpen ((sEmb k ((i + 1) + t)) ⁻¹' fixX f) := (isOpen_fixX f).preimage (continuous_sEmb k _)
  have hB : IsOpen {g : Mir k ((i + 1) + t) | dpowM (k := k) ((i + 1) + t) (-1 / 2) g = 1} :=
    (GlobalTheory.CompanionTheory.LeibPhi.isOpen_ker_dpow k ((i + 1) + t + 1) (-1 / 2)).preimage continuous_subtype_val
  refine isOpen_rightInv (eC ψ f) _ (hA.inter hB) ⟨?_, ?_⟩ fun g hg m => eC_mul ψ f m g hg.1 hg.2
  · show sEmb k ((i + 1) + t) 1 ∈ fixX f
    rw [MonoidHom.map_one]
    exact one_mem_fixX f
  · exact (dpowM (k := k) ((i + 1) + t) (-1 / 2)).map_one

end GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth
