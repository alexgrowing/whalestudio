import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyTB

noncomputable section

open MeasureTheory MvPolynomial
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.FFTSteps.AsmT

open AsmA

variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]

variable (ι A B) in

abbrev NN : ℕ := Fintype.card ι + (Fintype.card A + Fintype.card B)

def emb (i : ι) : Fin (NN ι A B) := Fin.castAdd _ (Fintype.equivFin ι i)

theorem emb_injective : Function.Injective (emb (ι := ι) (A := A) (B := B)) := fun i i' h => by
  simpa [emb] using h

variable (A B) in

def invE (j : Fin (NN ι A B)) : Option ι :=
  if h : (j : ℕ) < Fintype.card ι then some ((Fintype.equivFin ι).symm ⟨j, h⟩) else none

theorem sum_invE (f : Fin (NN ι A B) → ℂ) (g : ι → ℂ) :
    ∑ j, f j * (invE A B j).elim 0 g = ∑ i, f (emb i) * g i := by
  rw [Fin.sum_univ_add]
  have h2 : ∑ j : Fin (Fintype.card A + Fintype.card B), f (Fin.natAdd _ j) * (invE A B (Fin.natAdd _ j)).elim 0 g = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have : invE A B (Fin.natAdd (Fintype.card ι) j) = none := by
      simp [invE]
    rw [this]; simp
  rw [h2, add_zero]
  have h1 : ∀ j : Fin (Fintype.card ι), invE A B (Fin.castAdd _ j) = some ((Fintype.equivFin ι).symm j) := by
    intro j
    simp [invE]
  simp_rw [h1]
  simp only [Option.elim]
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => f (emb i) * g i)).symm.trans
    (Finset.sum_congr rfl fun j _ => by simp [emb]) |>.symm

variable (ι) in

def resφ : (Fin (NN ι A B) × A) ⊕ (Fin (NN ι A B) × B) → PV ι A B :=
  Sum.elim (fun x => (invE A B x.1).elim 0 fun i => X (Sum.inl (i, x.2)))
    (fun y => (invE A B y.1).elim 0 fun i => X (Sum.inr (i, y.2)))

def res : PV (Fin (NN ι A B)) A B →ₐ[ℂ] PV ι A B := aeval (resφ ι)

def ren : (ι × A) ⊕ (ι × B) → (Fin (NN ι A B) × A) ⊕ (Fin (NN ι A B) × B) :=
  Sum.map (Prod.map emb id) (Prod.map emb id)

def blk (u : Matrix (Fin (NN ι A B)) (Fin (NN ι A B)) ℂ) : Matrix ι ι ℂ := fun i i' => u (emb i) (emb i')

theorem eval_resφ (z : (ι × A) ⊕ (ι × B) → ℂ) (v : (Fin (NN ι A B) × A) ⊕ (Fin (NN ι A B) × B)) :
    eval z (resφ ι v) = Sum.elim (fun x : Fin (NN ι A B) × A => (invE A B x.1).elim 0 fun i => z (Sum.inl (i, x.2)))
      (fun y : Fin (NN ι A B) × B => (invE A B y.1).elim 0 fun i => z (Sum.inr (i, y.2))) v := by
  rcases v with ⟨j, a⟩ | ⟨j, b⟩ <;> cases h : invE A B j <;> simp [resφ, h]

theorem act_ren (u : Matrix (Fin (NN ι A B)) (Fin (NN ι A B)) ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    (act u (u.map star) (fun v => eval z (resφ ι v))) ∘ ren = act (blk u) ((blk u).map star) z := by
  funext v
  rcases v with ⟨i, a⟩ | ⟨i, b⟩
  · simp only [Function.comp, ren, Sum.map_inl, Prod.map, act, Sum.elim_inl, id, eval_resφ]
    exact sum_invE (fun j => u (emb i) j) (fun i' => z (Sum.inl (i', a)))
  · simp only [Function.comp, ren, Sum.map_inr, Prod.map, act, Sum.elim_inr, id, eval_resφ, Matrix.map_apply]
    exact sum_invE (fun j => star (u (emb i) j)) (fun i' => z (Sum.inr (i', b)))

def Tf (hA : Avg) (q : PV ι A B) : PV ι A B := res (Classical.choose (hA (NN ι A B) A B (rename ren q)))

theorem continuous_toMK (N : ℕ) :
    Continuous fun k : Formalism.REAL.KG (fun _ : Fin N => true) => Formalism.REAL.toMK k :=
  Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_blk : Continuous fun k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true) =>
    blk (ι := ι) (A := A) (B := B) (Formalism.REAL.toMK k) :=
  continuous_pi fun i => continuous_pi fun i' => (continuous_toMK _).matrix_elem _ _

theorem eval_Tf (hA : Avg) (q : PV ι A B) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval z (Tf hA q) = ∫ k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true),
      eval (act (blk (Formalism.REAL.toMK k)) ((blk (Formalism.REAL.toMK k)).map star) z) q
        ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) := by
  have hs := Classical.choose_spec (hA (NN ι A B) A B (rename ren q))
  rw [Tf, res, eval_aeval', hs.2.2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only
  rw [AsmA.eval_sub, eval_rename, act_ren]

theorem Tf_mem (hS : Stable) (hA : Avg) (q : PV ι A B) : Tf hA q ∈ pairAlg ι A B := by
  have hs := Classical.choose_spec (hA (NN ι A B) A B (rename ren q))
  have hP := hS (Fin (NN ι A B)) A B (by simp only [Fintype.card_fin, NN]; omega) (by simp only [Fintype.card_fin, NN]; omega) _ hs.1
  have hle : Subalgebra.map (res (ι := ι) (A := A) (B := B)) (pairAlg (Fin (NN ι A B)) A B) ≤ pairAlg ι A B := by
    rw [pairAlg, AlgHom.map_adjoin]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨_, ⟨⟨a, b⟩, rfl⟩, rfl⟩
    refine Algebra.subset_adjoin ⟨(a, b), ?_⟩
    apply MvPolynomial.funext
    intro z
    simp only [res, map_sum, map_mul, aeval_X, eval_resφ, Sum.elim_inl, Sum.elim_inr]
    rw [sum_invE (fun j => (invE A B j).elim 0 fun i => z (Sum.inl (i, a))) (fun i => z (Sum.inr (i, b)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : invE A B (emb (A := A) (B := B) i) = some i := by simp [invE, emb]
    simp [this]
  exact hle ⟨_, hP, rfl⟩

theorem Tf_deg (hA : Avg) (q : PV ι A B) : (Tf hA q).totalDegree ≤ q.totalDegree := by
  have hs := Classical.choose_spec (hA (NN ι A B) A B (rename ren q))
  refine (totalDegree_aeval_le _ (fun v => ?_) _).trans (hs.2.1.trans (totalDegree_rename_le _ _))
  rcases v with ⟨j, a⟩ | ⟨j, b⟩
  · simp only [resφ, Sum.elim_inl]
    cases h : invE A B j <;> simp [Option.elim, totalDegree_X]
  · simp only [resφ, Sum.elim_inr]
    cases h : invE A B j <;> simp [Option.elim, totalDegree_X]

theorem integrable_eval_act (hA : Avg) (F G : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true) → Matrix ι ι ℂ)
    (hF : Continuous F) (hG : Continuous G) (z : (ι × A) ⊕ (ι × B) → ℂ) (q : PV ι A B) :
    Integrable (fun k => eval (act (F k) (G k) z) q) (Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) :=
  integrableOn_univ.mp ((continuous_act_eval hF hG z q).continuousOn.integrableOn_compact isCompact_univ)

end PositivityTheory.Rg.Sw.FFTSteps.AsmT
