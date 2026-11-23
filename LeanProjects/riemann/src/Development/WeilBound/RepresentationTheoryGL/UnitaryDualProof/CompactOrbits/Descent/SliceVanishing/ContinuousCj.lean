import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.DistrC
import GroundTheory.AutomorphicForms.WhittakerDistribution

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def Tset (F : Set (Matrix (Fin n) (Fin n) k)) (P : k[X]) : Set (Matrix (Fin n) (Fin n) k) := {x | x ∈ F ∧ aeval x P = x}

def cj (g : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k := g.val * x * g⁻¹.val

theorem cj_mul (g h : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) : cj (g * h) x = cj g (cj h x) := by
  simp [cj, mul_assoc]

theorem cj_one (x : Matrix (Fin n) (Fin n) k) : cj (1 : GL (Fin n) k) x = x := by simp [cj]

theorem continuous_cj : Continuous fun p : GL (Fin n) k × Matrix (Fin n) (Fin n) k => cj p.1 p.2 :=
  ((Units.continuous_val.comp continuous_fst).matrix_mul continuous_snd).matrix_mul
    (Units.continuous_coe_inv.comp continuous_fst)

section Hyp

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {F : Set (Matrix (Fin n) (Fin n) k)} {P : k[X]}
  (hFinv : ∀ g ∈ Gz Z, ∀ x ∈ F, g.val * x * g⁻¹.val ∈ F)

include hFinv in
theorem cj_mem_Tset {g : GL (Fin n) k} (hg : g ∈ Gz Z) {x} (hx : x ∈ Tset F P) : cj g x ∈ Tset F P :=
  ⟨hFinv g hg x hx.1, by rw [cj, Asm.aeval_conj, hx.2]⟩

def actT : MulAction (GzS Z) (Tset F P) where
  smul g x := ⟨cj g.1 x.1, cj_mem_Tset hFinv g.2 x.2⟩
  one_smul x := Subtype.ext (cj_one x.1)
  mul_smul g h x := Subtype.ext (cj_mul g.1 h.1 x.1)

end Hyp

end PositivityTheory.RgUd.T.Desc.SLF
