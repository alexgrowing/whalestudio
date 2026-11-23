import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensIdxA

noncomputable section

namespace PI.VolStabW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing

namespace IdxHW

theorem sigma_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra h
  push Not at h
  have hc := hCM.2.1
  let w : InfinitePlace E := Classical.arbitrary _
  have hcw : w.IsComplex := hc.isComplex w
  apply InfinitePlace.not_isReal_iff_isComplex.2 hcw
  rw [InfinitePlace.isReal_iff]
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq]
  have h1 := hCM.2.2.2 w.embedding x
  rw [h x] at h1
  exact h1.symm

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)

def Cmat : Matrix (Fin 2) (Fin 2) F := fun k l => b.repr (σ (b l)) k

def cr (y : Fv F v ⊗[F] E) (k : Fin 2) : Fv F v := (Algebra.TensorProduct.basis (Fv F v) b).repr y k

theorem cr_sig (y : Fv F v ⊗[F] E) (k : Fin 2) :
    cr b v (sigR (Fv F v) σ y) k = ∑ l, algebraMap F (Fv F v) (Cmat b σ k l) * cr b v y l :=
  crd_sigR b v σ y k

theorem cr_smul_one (t : Fv F v) (k : Fin 2) :
    cr b v (t • (1 : Fv F v ⊗[F] E)) k = t * algebraMap F (Fv F v) (b.repr 1 k) := by
  simp [cr, Algebra.TensorProduct.one_def, Algebra.TensorProduct.basis_repr_tmul, map_smul]

theorem cr_symm (f : Fin 2 → Fv F v) (k : Fin 2) :
    cr b v ((Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm f) k = f k := by
  have : cr b v ((Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm f) k =
      (Algebra.TensorProduct.basis (Fv F v) b).equivFun
        ((Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm f) k := by
    simp [cr, Module.Basis.equivFun_apply]
  rw [this, LinearEquiv.apply_symm_apply]

theorem crdS_eq (S : HermR (Fv F v) σ a) (i j : Fin a) (k : Fin 2) :
    crdS b v σ a S i j k = cr b v ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k := rfl

def psi (k0 : Fin 2) : hermO b v σ a →+ (Fin a × Fin a → v.adicCompletionIntegers F) where
  toFun S q := if q.1 < q.2 then ⟨crdS b v σ a S q.1 q.2 0, (mem_hermO_iff b v σ a S).1 S.2 _ _ _⟩
    else if q.2 < q.1 then ⟨crdS b v σ a S q.2 q.1 1, (mem_hermO_iff b v σ a S).1 S.2 _ _ _⟩
    else ⟨crdS b v σ a S q.1 q.1 k0, (mem_hermO_iff b v σ a S).1 S.2 _ _ _⟩
  map_zero' := by
    funext q
    split_ifs <;> ext <;> simp [crdS]
  map_add' S T := by
    funext q
    simp only [Pi.add_apply]
    by_cases h1 : q.1 < q.2
    · simp only [if_pos h1]
      ext
      simp [crdS_add]
    · by_cases h2 : q.2 < q.1
      · simp only [if_neg h1, if_pos h2]
        ext
        simp [crdS_add]
      · simp only [if_neg h1, if_neg h2]
        ext
        simp [crdS_add]

end Main

end IdxHW

end PI.VolStabW
