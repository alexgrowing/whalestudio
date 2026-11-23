import Formalism.SharpRestriction.LevelLetterCocycles.MapEqOfProdEq
import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionEveryLocalisation
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
  Formalism.MainNotions.N.Inst Formalism.MainNotions.LargeLevelLemmas.Br

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)

abbrev blk (R : Ranks) : Fin R.nV → Fin (R.t + 1) := blkG R.r R.t

def repX : GE N →* (N.X i → MatN N i) := MonoidHom.pi fun x => rO N i r x

theorem repX_apply (γ : GE N) (x : N.X i) : repX N r γ x = rO N i r x γ := rfl

def NormAt : Prop :=
  (∀ g a b, blk R a ≠ blk R b → rO N i r π g a b = 0) ∧
  (∀ g (c : Fin R.t), rO N i r π g (Fin.natAdd R.r c) (Fin.natAdd R.r c) =
    ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i)) ∧
  (∀ g (a b : Fin R.r), rO N i r π g (Fin.castAdd R.t a) (Fin.castAdd R.t b) = rhoO N i ρ π g a b)

theorem repX_mem (γ : GE N) : repX N r γ ∈ tSpan (N.T i) (repX N r) := by
  refine ⟨{γ}, fun _ => 1, fun _ => one_mem _, ?_⟩
  simp

theorem e_of_bd (M : MatN N i) (hM : ∀ a b, blk R a ≠ blk R b → M a b = 0)
    (B : Matrix (Fin R.r) (Fin R.r) (N.O i))
    (hB : ∀ a b, M (Fin.castAdd R.t a) (Fin.castAdd R.t b) = B a b) (χ : Fin R.t → N.O i)
    (hχ : ∀ c, M (Fin.natAdd R.r c) (Fin.natAdd R.r c) = χ c) (u : Fin R.nV → KK N i) :
    eG R.r R.t (KK N i) ((M.map (toK N i)).mulVec u) =
      ((B.map (toK N i)).mulVec (eG R.r R.t (KK N i) u).1,
        fun c => toK N i (χ c) * (eG R.r R.t (KK N i) u).2 c) := by
  refine (eG_mulVec (M.map (toK N i)) (fun a b h => by
    show toK N i (M a b) = 0
    rw [hM a b h, map_zero]) u).trans ?_
  congr 1
  · congr 2
    ext a b
    show toK N i (M (Fin.castAdd R.t a) (Fin.castAdd R.t b)) = toK N i (B a b)
    rw [hB]
  · funext c
    show toK N i (M (Fin.natAdd R.r c) (Fin.natAdd R.r c)) * _ = _
    rw [hχ]

section Mk

variable (g0 : GE N) (eB e₁ X0 : N.X i → MatN N i)

abbrev Pf : N.X i → Polynomial (N.O i) := fun x => blockPoly (eB x) (X0 x)

def mk51 (hfin : Finite (SplitPts R.t (Pf N eB X0))) (π' : SplitPts R.t (Pf N eB X0)) :
    IdempotentChoiceData N i where
  eB := eB
  e1 := e₁
  g0 := g0
  X0 := X0
  X' := SplitPts R.t (Pf N eB X0)
  finX' := @Fintype.ofFinite _ hfin
  decX' := Classical.decEq _
  p := fun y => y.1.1
  T' := splitT (N.T i) R.t (Pf N eB X0)
  rr := fun c y => if h : 1 ≤ c ∧ c ≤ R.t then y.1.2 ⟨c - 1, by omega⟩ else 0
  π' := π'
  e := eG R.r R.t (KK N i)
  ψρ := fun a => (a π').submatrix (Fin.castAdd R.t) (Fin.castAdd R.t)
  ψχ := fun c a => a π' (Fin.natAdd R.r c) (Fin.natAdd R.r c)

variable (hfin : Finite (SplitPts R.t (Pf N eB X0))) (π' : SplitPts R.t (Pf N eB X0))

end Mk

theorem blockPoly_eq {A : Type} [CommRing A] {d : Type} [Fintype d] [DecidableEq d] (e a : Matrix d d A) :
    blockPoly e a = Matrix.det ((Polynomial.X : Polynomial A) • e.map (Polynomial.C (R := A)) -
      a.map (Polynomial.C (R := A)) + 1 - e.map (Polynomial.C (R := A))) := by
  rw [blockPoly]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring

theorem e_of_diag (β : Fin R.nV → N.O i) (u : Fin R.nV → KK N i) :
    eG R.r R.t (KK N i) (((Matrix.diagonal fun a => if blk R a = 0 then 0 else β a : MatN N i).map
        (toK N i)).mulVec u) =
      (0, fun c => toK N i (β (Fin.natAdd R.r c)) * (eG R.r R.t (KK N i) u).2 c) := by
  refine (eG_mulVec _ (fun a b h => ?_) u).trans ?_
  · have hab : a ≠ b := fun hab => h (by rw [hab])
    show toK N i (if a = b then (if blk R a = 0 then (0 : N.O i) else β a) else 0) = 0
    rw [if_neg hab, map_zero]
  · congr 1
    · have h0 : ∀ a b : Fin R.r, ((Matrix.diagonal (fun a => if blk R a = 0 then (0 : N.O i) else β a)).map (toK N i)) (Fin.castAdd R.t a) (Fin.castAdd R.t b) = 0 := by
        intro a b
        show toK N i (if Fin.castAdd R.t a = Fin.castAdd R.t b then
          (if blk R (Fin.castAdd R.t a) = 0 then (0 : N.O i) else β (Fin.castAdd R.t a)) else 0) = 0
        have hblk : blk R (Fin.castAdd R.t a) = 0 := by simp [blkG]
        by_cases hab : a = b
        · subst hab
          rw [if_pos rfl, if_pos hblk, map_zero]
        · rw [if_neg (fun h => hab (Fin.castAdd_injective _ _ h)), map_zero]
      funext a
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      exact Finset.sum_eq_zero fun b _ => by
        rw [mul_eq_zero]
        left
        exact h0 a b
    · funext c
      have hblk : blk R (Fin.natAdd R.r c) ≠ 0 := by simp [blkG, Fin.ext_iff]
      show toK N i (if Fin.natAdd R.r c = Fin.natAdd R.r c then
        (if blk R (Fin.natAdd R.r c) = 0 then (0 : N.O i) else β (Fin.natAdd R.r c)) else 0) * _ = _
      rw [if_pos rfl, if_neg hblk]

end Formalism.MainNotions.N.RepresentationBoundsCohomology

end
