import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeftStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.ProdReorder

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace GrothendieckAssociativity

theorem class_congr_equiv {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (φ : Nonempty (π.Equiv τ)) : cl0 π = cl0 τ := by
  obtain ⟨φ⟩ := φ
  unfold cl0
  by_cases h : HasFiniteLength π
  · rw [dif_pos h, dif_pos (h.of_equiv φ)]
    exact clsGL_congr φ _ _
  · rw [dif_neg h, dif_neg (fun h' => h (h'.of_equiv φ.symm))]

theorem class_induced_cast {r t N : ℕ} (h : r + t = N) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin r) k × GL (Fin t) k) W) :
    cl0 (ind₂ (stdSum h) ρ) = cl0 (ind₂ (stdSum (rfl : r + t = r + t)) ρ) := by
  subst h
  rfl

theorem class_of_chosen_rep (x : IrrGL k) : cl0 (IrrGL.rep x) = sg x := by
  exact (dif_pos x.2.rep.hasFiniteLength).trans ((clsGL_irr x.2.rep x.2.rep.hasFiniteLength).trans
    (congrArg (fun c => Finsupp.single (⟨x.1, c⟩ : IrrGL k) (1 : ℤ)) x.2.cl_rep))

theorem mulR_sg (x y : IrrGL k) : mulR (sg x) (sg y) = cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y)) := by
  have h1 := Finsupp.sum_single_index (a := x) (b := (1 : ℤ)) (h := fun z m => (sg y).sum fun w n => (m * n) • cl0 (prod₂ (IrrGL.rep z) (IrrGL.rep w))) (by simp only [Finsupp.sum, zero_mul, zero_smul, Finset.sum_const_zero])
  have h2 := Finsupp.sum_single_index (a := y) (b := (1 : ℤ)) (h := fun w n => ((1 : ℤ) * n) • cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep w))) (by simp only [mul_zero, zero_smul])
  exact h1.trans (h2.trans (by simp only [mul_one, one_smul]))

theorem assoc_gen (h : MulCls k) {r s t : ℕ} {V₁ V₂ V₃ U U' : Type} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U']
    (π₁ : Representation ℂ (GL (Fin r) k) V₁) (π₂ : Representation ℂ (GL (Fin s) k) V₂)
    (π₃ : Representation ℂ (GL (Fin t) k) V₃) (P : Representation ℂ (GL (Fin (r + s)) k) U)
    (R : Representation ℂ (GL (Fin (s + t)) k) U') (φ : Nonempty (P.Equiv (prod₂ π₁ π₂)))
    (ψ : Nonempty (R.Equiv (prod₂ π₂ π₃))) (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) (s₃ : IsSmooth π₃)
    (sP : IsSmooth P) (sR : IsSmooth R) (f₁ : HasFiniteLength π₁) (f₃ : HasFiniteLength π₃)
    (fP : HasFiniteLength P) (fR : HasFiniteLength R) :
    mulR (cl0 P) (cl0 π₃) = mulR (cl0 π₁) (cl0 R) := by
  obtain ⟨a⟩ := ind₂_congr (k := k) (rfl : r + s + t = r + s + t) φ (eqv_refl π₃)
  obtain ⟨b⟩ := ind₂_assoc' (k := k) (rfl : r + s = r + s) (rfl : r + s + t = r + s + t) (rfl : s + t = s + t)
    (Nat.add_assoc r s t).symm π₁ π₂ π₃ s₁ s₂ s₃
  obtain ⟨c⟩ := ind₂_congr (k := k) (Nat.add_assoc r s t).symm (eqv_refl π₁) (eqv_symm ψ)
  have e1 : mulR (cl0 P) (cl0 π₃) = cl0 (prod₂ P π₃) := (h _ _ _ _ P π₃ fP f₃ sP s₃).2.symm
  have e2 : cl0 (prod₂ P π₃) = cl0 (ind₂ (stdSum (Nat.add_assoc r s t).symm) (extTensor π₁ R)) :=
    class_congr_equiv ⟨(a.trans b).trans c⟩
  have e3 : cl0 (ind₂ (stdSum (Nat.add_assoc r s t).symm) (extTensor π₁ R)) = cl0 (prod₂ π₁ R) :=
    class_induced_cast (Nat.add_assoc r s t).symm (extTensor π₁ R)
  have e4 : cl0 (prod₂ π₁ R) = mulR (cl0 π₁) (cl0 R) := (h _ _ _ _ π₁ R f₁ fR s₁ sR).2
  exact e1.trans (e2.trans (e3.trans e4))

end GrothendieckAssociativity

open GrothendieckAssociativity

variable (k)

theorem assoc (h : MulCls k) : Assoc k := by
  intro x y z
  have hxy : HasFiniteLength (prod₂ (IrrGL.rep x) (IrrGL.rep y)) :=
    (h x.1 y.1 _ _ (IrrGL.rep x) (IrrGL.rep y) x.2.rep.hasFiniteLength y.2.rep.hasFiniteLength
      x.2.rep.smooth y.2.rep.smooth).1
  have hyz : HasFiniteLength (prod₂ (IrrGL.rep y) (IrrGL.rep z)) :=
    (h y.1 z.1 _ _ (IrrGL.rep y) (IrrGL.rep z) y.2.rep.hasFiniteLength z.2.rep.hasFiniteLength
      y.2.rep.smooth z.2.rep.smooth).1
  have e1 : mulR (mulR (sg x) (sg y)) (sg z) = mulR (cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y))) (cl0 (IrrGL.rep z)) :=
    (congrArg (fun a => mulR a (sg z)) (mulR_sg x y)).trans
      (congrArg (mulR (cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y)))) (class_of_chosen_rep z).symm)
  have e2 : mulR (cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y))) (cl0 (IrrGL.rep z)) =
      mulR (cl0 (IrrGL.rep x)) (cl0 (prod₂ (IrrGL.rep y) (IrrGL.rep z))) :=
    assoc_gen h (IrrGL.rep x) (IrrGL.rep y) (IrrGL.rep z) (prod₂ (IrrGL.rep x) (IrrGL.rep y))
      (prod₂ (IrrGL.rep y) (IrrGL.rep z)) (eqv_refl _) (eqv_refl _) x.2.rep.smooth y.2.rep.smooth
      z.2.rep.smooth (isSmooth_prod₂ _ _) (isSmooth_prod₂ _ _) x.2.rep.hasFiniteLength
      z.2.rep.hasFiniteLength hxy hyz
  have e3 : mulR (cl0 (IrrGL.rep x)) (cl0 (prod₂ (IrrGL.rep y) (IrrGL.rep z))) = mulR (sg x) (mulR (sg y) (sg z)) :=
    (congrArg (fun a => mulR a (cl0 (prod₂ (IrrGL.rep y) (IrrGL.rep z)))) (class_of_chosen_rep x)).trans
      (congrArg (mulR (sg x)) (mulR_sg y z).symm)
  exact e1.trans (e2.trans e3)

theorem one : One k := by
  intro x
  let c0 : IrrCl (GL (Fin 0) k) := (IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one).cl
  let e : (Σ _ : Fin 0, Fin 0) ≃ Fin 0 := Equiv.equivOfIsEmpty _ _
  let τ : ∀ a : Fin 0, Representation ℂ (GL (Fin ((fun _ : Fin 0 => 0) a)) k) ((fun _ : Fin 0 => ℂ) a) :=
    fun a => a.elim0
  have A : Nonempty ((multiProd e τ).Equiv (IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one).ρ) :=
    SupportRing.nonempty_equiv_unit e τ
  have B : Nonempty ((IrrGL.rep (⟨0, c0⟩ : IrrGL k)).Equiv (multiProd e τ)) :=
    eqv_trans (IrrRep.nonempty_equiv_rep _) (eqv_symm A)
  have C : Nonempty ((ind₂ (stdSum (Nat.zero_add x.1)) (extTensor (IrrGL.rep (⟨0, c0⟩ : IrrGL k)) (IrrGL.rep x))).Equiv
      (ind₂ (stdSum (Nat.zero_add x.1)) (extTensor (multiProd e τ) (IrrGL.rep x)))) :=
    ind₂_congr (k := k) (Nat.zero_add x.1) B (eqv_refl (IrrGL.rep x))
  have D : Nonempty ((ind₂ (stdSum (Nat.zero_add x.1)) (extTensor (multiProd e τ) (IrrGL.rep x))).Equiv (IrrGL.rep x)) :=
    GlobalTheory.T.parabolicInductionTwoBlocks_empty_product_left k x.1 0 (Nat.zero_add x.1) _ (IrrGL.rep x) x.2.rep.smooth (fun _ => 0) (fun _ => ℂ) τ e
  have e1 : mulR (GrothGL.unit k) (sg x) = cl0 (prod₂ (IrrGL.rep (⟨0, c0⟩ : IrrGL k)) (IrrGL.rep x)) :=
    mulR_sg _ _
  have e2 : cl0 (prod₂ (IrrGL.rep (⟨0, c0⟩ : IrrGL k)) (IrrGL.rep x)) =
      cl0 (ind₂ (stdSum (Nat.zero_add x.1)) (extTensor (IrrGL.rep (⟨0, c0⟩ : IrrGL k)) (IrrGL.rep x))) :=
    (class_induced_cast (Nat.zero_add x.1) _).symm
  obtain ⟨c⟩ := C
  obtain ⟨dd⟩ := D
  exact e1.trans (e2.trans ((class_congr_equiv ⟨c.trans dd⟩).trans (class_of_chosen_rep x)))

end CompanionTheory.Groth
