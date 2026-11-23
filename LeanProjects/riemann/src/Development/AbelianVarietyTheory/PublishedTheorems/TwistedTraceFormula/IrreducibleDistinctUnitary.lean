import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroMapEqZeroOfWeightNe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwiningGlOfUnitary

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open scoped DirectSum TensorProduct Kronecker Matrix

noncomputable section

namespace GlobalTheory.GLDuality

def matRep (n n' : ℕ) :
    Representation ℂ (GL (Fin n) ℂ × GL (Fin n') ℂ) (MvPolynomial (Fin n' × Fin n) ℂ) where
  toFun p := (sub ((p.2 : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (p.1 : Matrix (Fin n) (Fin n) ℂ))ᵀ).toLinearMap
  map_one' := by
    simp only [Prod.snd_one, Prod.fst_one, Units.val_one, Matrix.one_kronecker_one, Matrix.transpose_one,
      LFocks_sub_one]
    rfl
  map_mul' p q := by
    simp only [Prod.snd_mul, Prod.fst_mul, Units.val_mul, Matrix.mul_kronecker_mul, Matrix.transpose_mul]
    rw [← LFocks_sub_comp]
    rfl

theorem matRep_apply {n n' : ℕ} (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) (f : MvPolynomial (Fin n' × Fin n) ℂ) :
    matRep n n' (g, h) f = sub ((h : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (g : Matrix (Fin n) (Fin n) ℂ))ᵀ f := rfl

theorem matRep_X {n n' : ℕ} (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) (a : Fin n') (s : Fin n) :
    matRep n n' (g, h) (X (a, s)) = ∑ b, ∑ t, C (h b a * g t s) * X (b, t) := by
  simp [matRep_apply, sub, Fintype.sum_prod_type]

theorem eval_matRep {n n' : ℕ} (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) (x : Matrix (Fin n') (Fin n) ℂ)
    (f : MvPolynomial (Fin n' × Fin n) ℂ) :
    eval (fun v => x v.1 v.2) (matRep n n' (g, h) f) =
      eval (fun v => ((h : Matrix (Fin n') (Fin n') ℂ)ᵀ * x * (g : Matrix (Fin n) (Fin n) ℂ)) v.1 v.2) f := by
  rw [matRep_apply]
  induction f using MvPolynomial.induction_on with
  | C a => simp [sub]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    obtain ⟨a, s⟩ := v
    simp only [map_mul, hp, eval_X]
    congr 1
    simp only [sub, aeval_X, map_sum, map_mul, eval_C, eval_X, Fintype.sum_prod_type, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem matRep_one_left {n n' : ℕ} (h : GL (Fin n') ℂ) (f : MvPolynomial (Fin n' × Fin n) ℂ) :
    matRep n n' (1, h) f = rowAct ℂ (h : Matrix (Fin n') (Fin n') ℂ)ᵀ f := by
  have : sub ((h : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ ((1 : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ =
      rowAct ℂ (n := n) (h : Matrix (Fin n') (Fin n') ℂ)ᵀ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [sub, rowAct, Fintype.sum_prod_type, Matrix.one_apply, apply_ite C]
  rw [matRep_apply, this]

abbrev Part (m : ℕ) : Type := {a : Fin m → ℕ // Antitone a}

def pad {m : ℕ} (N : ℕ) (a : Part m) : DomWeight N where
  w i := (rowNu (r := N) a.1 i : ℕ)
  anti i j hij := by
    have hij' : i.val ≤ j.val := hij
    simp only [rowNu, Nat.cast_le]
    split_ifs with h1 h2
    · exact a.2 (show (⟨i.val, h2⟩ : Fin m) ≤ ⟨j.val, h1⟩ from hij')
    · omega
    · exact Nat.zero_le _
    · exact le_rfl

theorem pad_w_of_lt {m N : ℕ} (a : Part m) (i : Fin N) (hi : i.val < m) : (pad N a).w i = a.1 ⟨i.val, hi⟩ := by
  simp [pad, rowNu, hi]

theorem pad_w_of_le {m N : ℕ} (a : Part m) (i : Fin N) (hi : m ≤ i.val) : (pad N a).w i = 0 := by
  simp [pad, rowNu, Nat.not_lt.2 hi]

theorem pad_injective {m N : ℕ} (h : m ≤ N) : Function.Injective (pad (m := m) N) := by
  intro a b e
  refine Subtype.ext (funext fun i => ?_)
  have h1 := pad_w_of_lt a (Fin.castLE h i) i.2
  have h2 := pad_w_of_lt b (Fin.castLE h i) i.2
  rw [e, h2] at h1
  exact_mod_cast h1.symm

section Along

variable {H H' : Type} [Group H] [Group H'] {n n' : ℕ} (ι : H →* GL (Fin n) ℂ) (ι' : H' →* GL (Fin n') ℂ)

def polyRep : Representation ℂ (H × H') (MvPolynomial (Fin n' × Fin n) ℂ) := (matRep n n').comp (ι.prodMap ι')

def pieceRep (a : Part (min n n')) :
    Representation ℂ (H × H') (nablaSq ℂ n (pad n a) ⊗[ℂ] nablaSq ℂ n' (pad n' a)) :=
  Representation.tprod ((smallRep ι (pad n a)).comp (MonoidHom.fst H H'))
    ((smallRep ι' (pad n' a)).comp (MonoidHom.snd H H'))

@[simp] theorem pieceRep_tmul (a : Part (min n n')) (p : H × H') (v : nablaSq ℂ n (pad n a))
    (w : nablaSq ℂ n' (pad n' a)) :
    pieceRep ι ι' a p (v ⊗ₜ w) = smallRep ι (pad n a) p.1 v ⊗ₜ smallRep ι' (pad n' a) p.2 w := by
  simp [pieceRep]

def IrreducibleDistinct (m : ℕ) : Prop :=
  (∀ a : Part m, (smallRep ι (pad n a)).IsIrreducible) ∧
    ∀ a b : Part m, Nonempty ((smallRep ι (pad n a)).Equiv (smallRep ι (pad n b))) → a = b

def DualAlong : Prop :=
  Nonempty ((Representation.directSum fun a : Part (min n n') => pieceRep ι ι' a).Equiv (polyRep ι ι')) ∧
    IrreducibleDistinct ι (min n n') ∧ IrreducibleDistinct ι' (min n n')

end Along

theorem irreducibleDistinct_unitary {m n : ℕ} (h : m ≤ n) : IrreducibleDistinct (unitaryIncl n) m := by
  refine ⟨fun a => isIrreducible_smallRep_unitary n _, fun a b ⟨e⟩ => ?_⟩
  by_contra hne
  let φ : (sqRep ℂ n (pad n a)).IntertwiningMap (sqRep ℂ n (pad n b)) :=
    ⟨e.toLinearMap, fun g => LinearMap.ext fun f => intertwining_gl_of_unitary n _ _ e.toIntertwiningMap g f⟩
  obtain ⟨f, hf, h0⟩ := exists_ne_zero_map_eq_zero_of_weight_ne n _ _ (fun e' => hne (pad_injective h e')) φ
  exact hf (e.toLinearEquiv.map_eq_zero_iff.1 h0)

theorem irreducibleDistinct_gl {m n : ℕ} (h : m ≤ n) : IrreducibleDistinct (MonoidHom.id (GL (Fin n) ℂ)) m := by
  refine ⟨fun a => ?_, fun a b ⟨e⟩ => (irreducibleDistinct_unitary h).2 a b
    ⟨Representation.Equiv.mk e.toLinearEquiv fun u => e.isIntertwining' (unitaryIncl n u)⟩⟩
  have hU := isIrreducible_smallRep_unitary n (pad n a)
  have hnt : Nontrivial (Subrepresentation (smallRep (MonoidHom.id (GL (Fin n) ℂ)) (pad n a))) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation (smallRep (unitaryIncl n) (pad n a)) :=
    ⟨S.toSubmodule, fun u _ hv => S.apply_mem_toSubmodule (unitaryIncl n u) hv⟩
  rcases eq_bot_or_eq_top T with e | e
  · exact Or.inl (Subrepresentation.ext (congrArg Subrepresentation.toSubmodule e :))
  · exact Or.inr (Subrepresentation.ext (congrArg Subrepresentation.toSubmodule e :))

end GlobalTheory.GLDuality

namespace GlobalTheory.Published

open GlobalTheory.GLDuality

def GLHoweDuality : Prop :=
  ∀ n n' : ℕ, 1 ≤ n → 1 ≤ n' →
    DualAlong (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) ∧
      DualAlong (unitaryIncl n) (unitaryIncl n')

theorem glHoweDuality_of_equiv
    (h : ∀ n n' : ℕ, 1 ≤ n → 1 ≤ n' → Nonempty ((Representation.directSum fun a : Part (min n n') =>
      pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).Equiv
        (polyRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ))))) : GLHoweDuality := by
  intro n n' hn hn'
  obtain ⟨e⟩ := h n n' hn hn'
  refine ⟨⟨⟨e⟩, irreducibleDistinct_gl (min_le_left _ _), irreducibleDistinct_gl (min_le_right _ _)⟩,
    ⟨⟨Representation.Equiv.mk e.toLinearEquiv fun u => e.isIntertwining' (unitaryIncl n u.1, unitaryIncl n' u.2)⟩,
      irreducibleDistinct_unitary (min_le_left _ _), irreducibleDistinct_unitary (min_le_right _ _)⟩⟩

end GlobalTheory.Published
