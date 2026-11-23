import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial

noncomputable section

open NumberField ReciprocityTheory.Aut Formalism.BasicNotions

namespace GlobalTheory.AlgWtF

section Rat

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem includeL_injective : Function.Injective (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
  haveI : Nontrivial (AFplus L) := Formalism.L2.GlobalTheoryTheory.Br.finiteAdeleRing_nontrivial
  exact Algebra.TensorProduct.includeLeft_injective (S := L) (RingHom.injective _)

abbrev incGL : GL (Fin n) L →* GL (Fin n) (AL L) :=
  Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)

theorem incGL_injective : Function.Injective (incGL (L := L) (n := n)) := by
  intro a b h
  apply Units.ext
  ext i j
  apply includeL_injective (L := L)
  have := congrArg (fun g : GL (Fin n) (AL L) => (g : Matrix (Fin n) (Fin n) (AL L)) i j) h
  simpa using this

theorem mem_incGL (γ : GQ L n) : ((γ : GA L n) : GL (Fin n) (AL L)) ∈ (GQ0 L n).map incGL :=
  Subgroup.mem_subgroupOf.1 γ.2

def ratFun (γ : GQ L n) : GL (Fin n) L := (Subgroup.mem_map.1 (mem_incGL γ)).choose

theorem ratFun_mem (γ : GQ L n) : ratFun γ ∈ GQ0 L n := (Subgroup.mem_map.1 (mem_incGL γ)).choose_spec.1

theorem incGL_ratFun (γ : GQ L n) : incGL (ratFun γ) = ((γ : GA L n) : GL (Fin n) (AL L)) :=
  (Subgroup.mem_map.1 (mem_incGL γ)).choose_spec.2

def ratHom : GQ L n →* GL (Fin n) L where
  toFun := ratFun
  map_one' := incGL_injective (by rw [incGL_ratFun, map_one]; rfl)
  map_mul' γ δ := incGL_injective (by rw [map_mul, incGL_ratFun, incGL_ratFun, incGL_ratFun]; rfl)

theorem ratHom_mem (γ : GQ L n) : ratHom γ ∈ GQ0 L n := ratFun_mem γ

theorem ratHom_eq_of_match (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (h : (((γ : GA L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) : γ₀ = ratHom γ := by
  apply incGL_injective
  rw [show ratHom γ = ratFun γ from rfl, incGL_ratFun]
  exact (Units.ext h).symm

end Rat

section Rep

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K]

instance finVV (lam : ι → DomWeight n) : FiniteDimensional K (Formalism.L2.DIV.VV K lam) :=
  Module.Finite.of_basis (Formalism.L2.DIV.bVV K lam)

instance finDualVV (lam : ι → DomWeight n) : FiniteDimensional K (Module.Dual K (Formalism.L2.DIV.VV K lam)) := inferInstance

def embGLF (emb : ι → L →+* K) : GL (Fin n) L →* (ι → GL (Fin n) K) :=
  MonoidHom.pi fun τ => Matrix.GeneralLinearGroup.map (emb τ)

def tenRepF (emb : ι → L →+* K) (lam : ι → DomWeight n) :
    Representation K (GQ L n) (Formalism.L2.DIV.VV K lam) :=
  (Formalism.L2.DIV.rhoK lam).comp ((embGLF emb).comp ratHom)

def wtRepF (emb : ι → L →+* K) (lam : ι → DomWeight n) :
    Representation K (GQ L n) (Module.Dual K (Formalism.L2.DIV.VV K lam)) :=
  (tenRepF emb lam).dual

def CMDist (emb : ι → L →+* K) : Prop :=
  Function.Injective emb ∧ ∀ τ τ', emb τ ≠ (emb τ').comp (IsCMField.complexConj L : L →+* L)

end Rep

end GlobalTheory.AlgWtF
