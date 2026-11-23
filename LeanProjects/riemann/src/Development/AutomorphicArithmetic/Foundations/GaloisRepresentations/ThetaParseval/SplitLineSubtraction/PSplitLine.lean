import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

noncomputable section

namespace UpperTheory.Gal.TP.Sub

section SplitLineAux

variable {Γ k : Type} [Group Γ] [Field k] {m : ℕ}

private lemma sumRep_val (s : Γ →* GL (Fin m) k) (c : Γ →* kˣ) (g : Γ) :
    ((sumRep s (rk1 c) g : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      (Matrix.fromBlocks (s g : Matrix (Fin m) (Fin m) k) 0 0
        ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := rfl

private lemma rankOneRep_val (c : Γ →* kˣ) (g : Γ) (i j : Fin 1) :
    ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) i j = (c g : k) := by
  simp [rk1, Subsingleton.elim i j]

private def resHom (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') : Γ →* Module.End k W' where
  toFun g := (Matrix.mulVecLin (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).restrict (hinv g)
  map_one' := by ext x; simp
  map_mul' g h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (r (g * h) : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (x : Fin (m + 1) → k) =
      (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec
        ((r h : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (x : Fin (m + 1) → k))
    simp [Matrix.mulVec_mulVec]

private def subRep (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') (b : Module.Basis (Fin m) k W') : Γ →* GL (Fin m) k :=
  MonoidHom.toHomUnits
    { toFun := fun g => LinearMap.toMatrix b b (resHom r hinv g)
      map_one' := by simp [LinearMap.toMatrix_one]
      map_mul' := fun g h => by
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp b b b] }

private lemma subRep_val (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') (b : Module.Basis (Fin m) k W') (g : Γ) :
    ((subRep r hinv b g : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) =
      LinearMap.toMatrix b b (resHom r hinv g) := rfl

private def colM {W' : Submodule k (Fin (m + 1) → k)} (b : Module.Basis (Fin m) k W')
    (v : Fin (m + 1) → k) : Matrix (Fin (m + 1)) (Fin m ⊕ Fin 1) k :=
  Matrix.of fun i => Sum.elim (fun j => (b j : Fin (m + 1) → k) i) (fun _ => v i)

private lemma intertw (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') (b : Module.Basis (Fin m) k W') (c : Γ →* kˣ) (v : Fin (m + 1) → k)
    (hv : ∀ g, (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec v = (c g : k) • v) (g : Γ) :
    (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * colM b v =
      colM b v * Matrix.fromBlocks (subRep r hinv b g : Matrix (Fin m) (Fin m) k) 0 0
        ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) := by
  ext i j
  rcases j with j | j
  · have h1 : ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * colM b v) i (Sum.inl j) =
        ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (b j : Fin (m + 1) → k)) i := rfl
    have h2 := b.sum_repr (resHom r hinv g (b j))
    have h4 : ((resHom r hinv g (b j) : W') : Fin (m + 1) → k) =
        (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (b j : Fin (m + 1) → k) := rfl
    have h3 : ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (b j : Fin (m + 1) → k)) i =
        ∑ a, (b.repr (resHom r hinv g (b j))) a * (b a : Fin (m + 1) → k) i := by
      have h5 := congrArg (fun u : W' => (u : Fin (m + 1) → k) i) h2
      simp only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] at h5
      rw [← h4, h5]
    rw [h1, h3, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [subRep_val, colM, LinearMap.toMatrix_apply, mul_comm]
  · have h1 : ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * colM b v) i (Sum.inr j) =
        ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec v) i := rfl
    rw [h1, hv g, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [colM, rankOneRep_val, mul_comm]

private lemma col_indep {W' : Submodule k (Fin (m + 1) → k)} (b : Module.Basis (Fin m) k W')
    {v : Fin (m + 1) → k} (hv0 : v ≠ 0) (hc : IsCompl (Submodule.span k {v}) W') :
    LinearIndependent k (Sum.elim (fun j => (b j : Fin (m + 1) → k)) (fun _ : Fin 1 => v)) := by
  refine LinearIndependent.sum_type
    (b.linearIndependent.map' W'.subtype (Submodule.ker_subtype W'))
    (LinearIndependent.of_subsingleton (0 : Fin 1) hv0) ?_
  refine Disjoint.mono ?_ ?_ hc.disjoint.symm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (b j).2
  · rw [Set.range_const]

end SplitLineAux

end UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.splitLine_holds : SplitLine := by
  intro Γ k _ _ m r hss c ⟨v, hv0, hv⟩
  have hW : IsInv r (Submodule.span k {v}) := by
    intro g x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [Matrix.mulVec_smul, hv g, smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  obtain ⟨W', hinv, hc⟩ := hss _ hW
  have hfr : Module.finrank k W' = m := by
    have h := Submodule.finrank_add_eq_of_isCompl hc
    rw [finrank_span_singleton hv0, Module.finrank_fin_fun] at h
    omega
  let b : Module.Basis (Fin m) k W' := Module.finBasisOfFinrankEq k W' hfr
  let Q : Matrix (Fin (m + 1)) (Fin (m + 1)) k := (colM b v).submatrix id finSumFinEquiv.symm
  have hQ : IsUnit Q := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have := (col_indep b hv0 hc).comp finSumFinEquiv.symm finSumFinEquiv.symm.injective
    convert this using 1
    ext j i
    rcases h : finSumFinEquiv.symm j with j' | j' <;> simp [Q, colM, Matrix.col, h]
  obtain ⟨q, hq⟩ := hQ
  refine ⟨subRep r hinv b, q⁻¹, fun g => ?_⟩
  have key : (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * Q =
      Q * (sumRep (subRep r hinv b) (rk1 c) g : GL (Fin (m + 1)) k) := by
    rw [sumRep_val]
    change _ * (colM b v).submatrix id finSumFinEquiv.symm =
      (colM b v).submatrix id finSumFinEquiv.symm * _
    rw [Matrix.submatrix_mul_equiv, ← intertw r hinv b c v hv g]
    ext i j
    rfl
  have key2 : r g * q = q * sumRep (subRep r hinv b) (rk1 c) g := Units.ext (by
    simpa [hq] using key)
  rw [inv_inv, mul_assoc, key2, ← mul_assoc, inv_mul_cancel, one_mul]
