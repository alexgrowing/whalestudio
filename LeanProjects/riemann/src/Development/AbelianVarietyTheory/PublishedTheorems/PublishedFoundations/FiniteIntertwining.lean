import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant

open MvPolynomial Formalism.BasicNotions
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

noncomputable section

namespace GlobalTheory.Branching

def sqRep (R : Type) [CommRing R] (N : ℕ) (lam : DomWeight N) :
    Representation R (GL (Fin N) R) (nablaSq R N lam) where
  toFun g :=
    { toFun := fun f => ⟨sqAct R N lam g f, (factSqStable R N lam g).1 f f.2⟩
      map_add' := fun f f' => Subtype.ext (by simp [sqAct])
      map_smul' := fun c f => Subtype.ext (by simp [sqAct, smul_comm c]) }
  map_one' := by
    ext1 f
    apply Subtype.ext
    have h : Formalism.GradedWeylDivisibility.rowAct R (n := N) (1 : Matrix (Fin N) (Fin N) R) = AlgHom.id R _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_X, Matrix.one_apply, AlgHom.id_apply]
      rw [Finset.sum_eq_single v.1]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    simp [sqAct, detPow, h]
  map_mul' g g' := by
    ext1 f
    apply Subtype.ext
    exact (factSqActMul R N lam g g' f).1

@[simp] theorem sqRep_coe (R : Type) [CommRing R] (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) R)
    (f : nablaSq R N lam) :
    (sqRep R N lam g f : MvPolynomial (Fin N × Fin N) R) = sqAct R N lam g f := rfl

instance finite_nablaSq (K : Type) [Field K] (N : ℕ) (lam : DomWeight N) :
    FiniteDimensional K (nablaSq K N lam) := by
  obtain ⟨b, ⟨-, hb, -⟩, -⟩ := Formalism.GradedWeylDivisibility.sSBasis K N N lam.natW
  have : Finite (Formalism.GradedWeylDivisibility.ssIdx N N lam.natW) := (Formalism.GradedWeylDivisibility.sSIdxFinite N N _).to_subtype
  unfold nablaSq
  rw [← hb]
  exact FiniteDimensional.span_of_finite K (Set.finite_range b)

instance nontrivial_nablaSq (K : Type) [Field K] (N : ℕ) (lam : DomWeight N) :
    Nontrivial (nablaSq K N lam) := by
  have ha : Antitone lam.natW := fun i j hij => by
    have := lam.anti hij
    simp only [DomWeight.natW]
    omega
  refine ⟨⟨⟨_, Formalism.GradedWeylDivisibility.hwMem K N N le_rfl _ ha⟩, 0, fun h => ?_⟩⟩
  exact Formalism.GradedWeylDivisibility.hwNe K N N le_rfl lam.natW (congrArg Subtype.val h)

def unitaryIncl (n : ℕ) : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin n) ℂ := Unitary.toUnits

@[simp] theorem unitaryIncl_coe (n : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ) :
    (unitaryIncl n u : Matrix (Fin n) (Fin n) ℂ) = u := rfl

theorem embGL_apply (R : Type) [CommRing R] {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) R) (a b : Fin N) :
    (embGL R n N h g : Matrix (Fin N) (Fin N) R) a b =
      if hab : a.val < n ∧ b.val < n then (g : Matrix (Fin n) (Fin n) R) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩
      else if a = b then 1 else 0 := by
  subst h
  have e : (embGL R n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) a b =
      Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) R) 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
        (finSumFinEquiv.symm a) (finSumFinEquiv.symm b) := rfl
  rw [e]
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
  simp only [Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases a with a | a <;> rcases b with b | b
  · simp
  · simp
  · simp
  · simp [Subsingleton.elim a b]

abbrev Below {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) : Type :=
  {mu : DomWeight n // Interlace h lam mu}

instance finite_below {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) : Finite (Below h lam) := by
  let F : Below h lam → ∀ i : Fin n,
      Finset.Icc (lam.w ⟨i.1 + 1, by omega⟩) (lam.w ⟨i.1, by omega⟩) :=
    fun mu i => ⟨mu.1.w i, Finset.mem_Icc.2 ⟨(mu.2 i).2, (mu.2 i).1⟩⟩
  refine Finite.of_injective F fun mu nu e => ?_
  obtain ⟨⟨w, hw⟩, h1⟩ := mu
  obtain ⟨⟨w', hw'⟩, h2⟩ := nu
  have : w = w' := funext fun i => congrArg Subtype.val (congrFun e i)
  subst this
  rfl

section Along

variable {H : Type} [Group H] {n N : ℕ} (ι : H →* GL (Fin n) ℂ) (h : n + 1 = N)

def smallRep (mu : DomWeight n) : Representation ℂ H (nablaSq ℂ n mu) := (sqRep ℂ n mu).comp ι

def resRep (lam : DomWeight N) : Representation ℂ H (nablaSq ℂ N lam) :=
  (sqRep ℂ N lam).comp ((embGL ℂ n N h).comp ι)

def sumRep (lam : DomWeight N) : Representation ℂ H (⨁ mu : Below h lam, nablaSq ℂ n mu.1) :=
  Representation.directSum fun mu : Below h lam => smallRep ι mu.1

def mult (lam : DomWeight N) (mu : DomWeight n) : ℕ :=
  Module.finrank ℂ ((smallRep ι mu).IntertwiningMap (resRep ι h lam))

instance finite_intertwining (lam : DomWeight N) (mu : DomWeight n) :
    FiniteDimensional ℂ ((smallRep ι mu).IntertwiningMap (resRep ι h lam)) := by
  let L : (smallRep ι mu).IntertwiningMap (resRep ι h lam) →ₗ[ℂ] (nablaSq ℂ n mu →ₗ[ℂ] nablaSq ℂ N lam) :=
    { toFun := fun f => f.toLinearMap, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective L fun _ _ e => Representation.IntertwiningMap.ext e

def BranchesAlong (lam : DomWeight N) : Prop :=
  Nonempty ((sumRep ι h lam).Equiv (resRep ι h lam)) ∧
    ∀ mu : DomWeight n, (Interlace h lam mu → mult ι h lam mu = 1) ∧ (¬ Interlace h lam mu → mult ι h lam mu = 0)

end Along

end GlobalTheory.Branching

namespace GlobalTheory.Published

open GlobalTheory.Branching

def WeylBranching : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N), 1 ≤ n → ∀ lam : DomWeight N,
    BranchesAlong (MonoidHom.id (GL (Fin n) ℂ)) h lam ∧ BranchesAlong (unitaryIncl n) h lam

end GlobalTheory.Published
