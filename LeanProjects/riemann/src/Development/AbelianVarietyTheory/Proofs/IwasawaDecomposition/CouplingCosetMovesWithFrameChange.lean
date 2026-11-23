import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

open Classical in

theorem frsF_ya_symm {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    (Λ : LevFam X.E X.K (R.N j) Pr.vGs) (Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
    (g : FrmG Λ Θ) (r : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)) (hP : P.1 ∉ Pr.vGs) (y : Sp X.E (R.N j)) :
    (frsF sel mu (ya Λ Θ g r).1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm (g.1.1 y) =
      (g.2.2.1 P).1 ((frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y) := by
  rw [LinearEquiv.symm_apply_eq]
  have e1 : (⟨P.1, (Finset.mem_union.mp (Finset.mem_union_right _ P.2)).resolve_left hP⟩ : QE sel (mu : Chr X.F X.E X.K)) = P :=
    Subtype.ext rfl
  simp only [frsF, dif_neg hP, e1]
  show _ = (g.1.1 * r.1.1.1.2 P * ((g.2.2.1 P)⁻¹).1) ((g.2.2.1 P).1 ((r.1.1.1.2 P).symm y))
  have e2 : ((g.2.2.1 P)⁻¹).1 ((g.2.2.1 P).1 ((r.1.1.1.2 P).symm y)) = (r.1.1.1.2 P).symm y := by
    show (g.2.2.1 P).1.symm ((g.2.2.1 P).1 _) = _
    exact LinearEquiv.symm_apply_apply _ _
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e2]
  show g.1.1 y = g.1.1 ((r.1.1.1.2 P) ((r.1.1.1.2 P).symm y))
  rw [LinearEquiv.apply_symm_apply]

theorem invActs_cqOf : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → GlobalTheory.Mem.Col2.ChEx.InvActs (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  intro X Pr R sel S mu cst u j hQ Λ Θ g r P
  have hP := hQ P.1 P.2
  ext z
  simp only [cqOf, cosetIn, Set.mem_setOf_eq, Set.mem_image, if_neg hP]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
    refine ⟨(g.2.2.1 P).1.symm z, ⟨y, hy, ?_⟩, LinearEquiv.apply_symm_apply _ _⟩
    rw [frsF_ya_symm Λ Θ g r P hP y] at hz
    rw [← (g.2.2.1 P).2]
    rw [map_smul, map_sub, LinearEquiv.apply_symm_apply]
    exact hz
  · rintro ⟨z0, ⟨y, hy, hz⟩, rfl⟩
    refine ⟨g.1.1 y, ⟨y, hy, rfl⟩, ?_⟩
    rw [frsF_ya_symm Λ Θ g r P hP y, ← map_sub, ← map_smul]
    exact ((g.2.2.1 P).2 _).2 hz

end GlobalTheory.Mem.Col2.ChEx
