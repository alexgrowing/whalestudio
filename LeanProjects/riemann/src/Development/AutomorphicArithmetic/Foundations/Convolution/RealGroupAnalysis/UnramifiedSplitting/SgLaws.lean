import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.H

variable {K : Type} [Field K] [NumberField K]

private theorem sg_fst (v : P K) (x : Kv v) : (sg v x).1 = 0 := rfl

private theorem sg_snd_self (v : P K) (x : Kv v) : (sg v x).2 v = x := by
  change GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd v x v = x
  rw [GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd_apply, Pi.single_eq_same]

private theorem sg_snd_ne (v : P K) (x : Kv v) {w : P K} (h : w ≠ v) : (sg v x).2 w = 0 := by
  change GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd v x w = 0
  rw [GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd_apply, Pi.single_eq_of_ne h]

private theorem ext_a {a b : A K} (h1 : a.1 = b.1) (h2 : ∀ w : P K, a.2 w = b.2 w) : a = b :=
  Prod.ext h1 (FiniteAdeleRing.ext K h2)

private theorem sg_add (v : P K) (x y : Kv v) : sg v (x + y) = sg v x + sg v y := by
  refine ext_a (by simp [sg_fst]) fun w => ?_
  by_cases h : w = v
  · subst h
    change _ = (sg w x).2 w + (sg w y).2 w
    simp only [sg_snd_self]
  · change _ = (sg v x).2 w + (sg v y).2 w
    simp only [sg_snd_ne _ _ h, add_zero]

private theorem sg_mul (v : P K) (a : A K) (x : Kv v) : a * sg v x = sg v (cp v a * x) := by
  refine ext_a (by change a.1 * (sg v x).1 = _; simp [sg_fst]) fun w => ?_
  change a.2 w * (sg v x).2 w = _
  by_cases h : w = v
  · subst h
    simp only [sg_snd_self]; rfl
  · simp only [sg_snd_ne _ _ h, mul_zero]

private theorem cp_sg (v : P K) (x : Kv v) : cp v (sg v x) = x := sg_snd_self v x

private theorem idl_eq (v : P K) (x : (Kv v)ˣ) :
    ((idl v x : (A K)ˣ) : A K) = 1 + sg v ((x : Kv v) - 1) := by
  refine ext_a ?_ fun w => ?_
  · change (1 : InfiniteAdeleRing K) = 1 + (sg v _).1
    rw [sg_fst, add_zero]
  · change (idl v x : (A K)ˣ).val.2 w = 1 + (sg v _).2 w
    by_cases h : w = v
    · subst h
      rw [sg_snd_self]
      have : (localIdele K w x).val.2 w = x := by
        classical
        exact Pi.mulSingle_eq_same w _
      change (localIdele K w x).val.2 w = _
      rw [this]; ring
    · rw [sg_snd_ne _ _ h, add_zero]
      have : (localIdele K v x).val.2 w = 1 := by
        classical
        exact Pi.mulSingle_eq_of_ne h _
      exact this

private theorem cont_sg (v : P K) : Continuous (sg v) :=
  continuous_const.prodMk (GroundTheory.Global.continuous_finiteAdeleSingleAdd (K := K) v)

private theorem lc_fst (v : P K) (g : GL (Fin 2) (Kv v)) (i j : Fin 2) :
    ((lc v g).val i j).1 = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j := by
  have h : Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (Af K)) (lc v g) = 1 := by
    change Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (Af K))
      (finGL K 2 (locGL K 2 v g)) = 1
    rw [← Fb.finEmb_eq]
    exact congrArg Prod.fst
      (GroundTheory.Automorphic.AutomorphicForm.prodEquiv_finEmb (locGL K 2 v g))
  exact congrArg (fun x : GL (Fin 2) (InfiniteAdeleRing K) => x.val i j) h

private theorem lc_snd (v w : P K) (g : GL (Fin 2) (Kv v)) (i j : Fin 2) :
    ((lc v g).val i j).2 w =
      (Matrix.GeneralLinearGroup.map (pLoc K w) (locGL K 2 v g)).val i j := by
  have h := pFin_finGL (E := K) (a := 2) (locGL K 2 v g)
  have e : ((lc v g).val i j).2 = (locGL K 2 v g).val i j :=
    congrArg (fun x : GL (Fin 2) (Af K) => x.val i j) h
  rw [e]
  rfl

private theorem one_fst (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (A K)) i j).1 = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem one_snd (w : P K) (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (A K)) i j).2 w = (1 : Matrix (Fin 2) (Fin 2) (Kv w)) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem lc_entry (v : P K) (g : GL (Fin 2) (Kv v)) (i j : Fin 2) :
    (lc v g).val i j = (1 : Matrix (Fin 2) (Fin 2) (A K)) i j +
      sg v (g.val i j - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i j) := by
  refine ext_a ?_ fun w => ?_
  · change _ = ((1 : Matrix (Fin 2) (Fin 2) (A K)) i j).1 + (sg v _).1
    rw [lc_fst, sg_fst, add_zero, one_fst]
  · rw [lc_snd]
    change _ = ((1 : Matrix (Fin 2) (Fin 2) (A K)) i j).2 w + (sg v _).2 w
    by_cases h : w = v
    · subst h
      rw [pLoc_locGL, sg_snd_self, one_snd]
      ring
    · rw [pLoc_locGL_of_ne h, sg_snd_ne _ _ h, add_zero, one_snd]
      rfl

private theorem ab_idl (v : P K) (x : (Kv v)ˣ) : ab (idl v x) = ‖(x : Kv v)‖ := by
  have e : idl v x = GroundTheory.Global.IdeleGroup.finiteEmbedding v x := by
    apply Units.ext
    rfl
  rw [e]
  exact GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x

private theorem norm_of_val (v : P K) (x : Kv v) (n : ℤ) (h : Valued.v x = WithZero.exp n) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  rw [NumberField.FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp [WithZero.exp]

private theorem ab_unif (v : P K) (ϖ : (Kv v)ˣ) (h : IsU ϖ) :
    ab (idl v ϖ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [ab_idl, norm_of_val v _ (-1) h, _root_.zpow_neg_one]

private theorem ab_unit (v : P K) (x : (Kv v)ˣ) (h : Valued.v (x : Kv v) = 1) : ab (idl v x) = 1 := by
  rw [ab_idl, norm_of_val v _ 0 (by simpa using h), zpow_zero]

private theorem cont_val_lc (v : P K) :
    Continuous fun g : GL (Fin 2) (Kv v) => ((lc v g : GL (Fin 2) (A K)) : Matrix (Fin 2) (Fin 2) (A K)) := by
  refine continuous_matrix fun i j => ?_
  simp only [lc_entry]
  refine continuous_const.add ((cont_sg v).comp (Continuous.sub ?_ continuous_const))
  exact Continuous.matrix_elem (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (Kv v))) i j

private theorem cont_lc (v : P K) : Continuous (lc v) := by
  refine Units.continuous_iff.2 ⟨cont_val_lc v, ?_⟩
  have e : (fun g : GL (Fin 2) (Kv v) => (((lc v g)⁻¹ : GL (Fin 2) (A K)) : Matrix (Fin 2) (Fin 2) (A K))) =
      (fun g : GL (Fin 2) (Kv v) => ((lc v g : GL (Fin 2) (A K)) : Matrix (Fin 2) (Fin 2) (A K))) ∘
        fun g => g⁻¹ := by
    funext g
    simp only [Function.comp, map_inv]
  exact e ▸ (cont_val_lc v).comp continuous_inv

end UpperTheory.ConvolutionTheory.R2.H

theorem UpperTheory.ConvolutionTheory.R2.H.sgLaws :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K), (∀ x y, sg v (x + y) = sg v x + sg v y) ∧ (∀ (a : A K) x, a * sg v x = sg v (cp v a * x)) ∧ (∀ x, cp v (sg v x) = x) ∧
      (∀ x, ((idl v x : (A K)ˣ) : A K) = 1 + sg v ((x : Kv v) - 1)) ∧
      (∀ (g : GL (Fin 2) (Kv v)) i j, (lc v g).val i j = (1 : Matrix (Fin 2) (Fin 2) (A K)) i j + sg v (g.val i j - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i j)) ∧
      (∀ ϖ, IsU ϖ → ab (idl v ϖ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) ∧ (∀ x : (Kv v)ˣ, Valued.v (x : Kv v) = 1 → ab (idl v x) = 1) ∧
      (∀ x, (sg v x).1 = 0 ∧ ∀ v' ≠ v, (sg v x).2 v' = 0) ∧ Continuous (lc v) ∧ Continuous (sg v) := by
  intro K _ _ v
  exact ⟨sg_add v, sg_mul v, cp_sg v, idl_eq v, lc_entry v, ab_unif v, ab_unit v,
    fun x => ⟨sg_fst v x, fun _ h => sg_snd_ne v x h⟩, cont_lc v, cont_sg v⟩
