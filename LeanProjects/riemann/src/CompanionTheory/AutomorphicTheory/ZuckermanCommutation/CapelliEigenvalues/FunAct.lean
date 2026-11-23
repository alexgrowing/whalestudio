import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.Transport

open Matrix Formalism.REAL Formalism.QuantumDeterminants PI.DSInfCharCap

noncomputable section

namespace CompanionTheory.CapEig

theorem algHom_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  have hT : ∀ v a b, φ (Tm E v a b) = Tm (fun a b => φ (E a b)) v a b := by
    intro v a b
    by_cases hab : a = b <;> simp [Tm, hab]
  simp only [qdet, qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, hT]

theorem lift_eq_sum {X A : Type} [Ring A] [Algebra ℂ A] (f : X → A) (p : FreeAlgebra ℂ X) :
    FreeAlgebra.lift ℂ f p = (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff.sum
      fun w c => c • (w.toList.map f).prod := by
  have e : FreeAlgebra.lift ℂ f = (MonoidAlgebra.lift ℂ A (FreeMonoid X) (FreeMonoid.lift f)).comp
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := X)).toAlgHom := by
    ext x
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [e]
  show MonoidAlgebra.lift ℂ A (FreeMonoid X) (FreeMonoid.lift f) (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) = _
  rw [MonoidAlgebra.lift_apply]
  simp only [FreeMonoid.lift_apply]

section vec

variable {n : ℕ} {ε : Fin n → Bool} {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)}

theorem inUJ_one : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp [inUJ]

theorem rd_vec (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs}
    (hv : SmoothOnGV ε fun x => σ x v) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) :
    RdV X (fun x => σ x v) g = σ g (PI.PhMeasCore.dsig σ X v) := by
  have e0 : PI.PhMeasCore.dsig σ X v = RdV X (fun x => σ x v) 1 := by
    unfold PI.PhMeasCore.dsig RdV
    simp only [Matrix.one_mul]
  rw [e0, (rdVPair n ε Hs Hs (σ g) _ X 1 hv hX inUJ_one).2,
    io_rd_congr (f' := fun x => σ (g * x) v) (fun x hx => by rw [hm g x hg hx]; rfl) hX inUJ_one,
    rdLeftV n Hs (fun x => σ x v) X g 1, Matrix.mul_one]

theorem eab_vec (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs}
    (hv : SmoothOnGV ε fun x => σ x v) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b (fun x => σ x v) g = σ g (dsigC ε σ (unitM (a, b)) v) := by
  obtain ⟨h1, h2, -, -⟩ := cpartMem n ε (Matrix.single a b 1)
  unfold EabV EcV dsigC
  rw [rd_vec hm hv h1 hg, rd_vec hm hv h2 hg, map_add, map_smul]
  simp only [cpart1, cpart2, thetaJ, unitM, sub_neg_eq_add, ← sub_eq_add_neg]

theorem word_rep (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs} {x : ioS ε Hs}
    (hx : IORep (fun y => σ y v) x.1) : ∀ w : List (Fin n × Fin n),
    IORep (fun y => σ y (dsigCW ε σ (w.map unitM) v)) ((w.map fun ab => ioE ε Hs ab.1 ab.2).prod x).1
  | [] => by simpa [dsigCW] using hx
  | ab :: w => by
    have ih := word_rep hm hx w
    have hs : SmoothOnGV ε fun y => σ y (dsigCW ε σ (w.map unitM) v) :=
      io_smooth_congr (fun g hg => (io_rep_ext _ g hg).trans (ih g hg).symm) (io_mem_smooth _)
    intro g hg
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, dsigCW]
    rw [← ioE_rep ih ab.1 ab.2 g hg, eab_vec hm hs ab.1 ab.2 hg]

theorem actU_rep (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs} {x : ioS ε Hs}
    (hx : IORep (fun y => σ y v) x.1) (p : FreeAlgebra ℂ (Fin n × Fin n)) :
    IORep (fun y => σ y (actU ε σ p v)) (FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => ioE ε Hs ab.1 ab.2) p x).1 := by
  intro g hg
  rw [lift_eq_sum]
  unfold actU Finsupp.sum
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← word_rep hm hx w.toList g hg]

theorem capelli_vec (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs}
    (hv : SmoothOnGV ε fun x => σ x v) (u : ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    capelli ε u (fun x => σ x v) g = σ g (actU ε σ (qdet (Egl n) u) v) := by
  obtain ⟨x, hx⟩ := io_rep_mk hv
  have h1 := io_qminor_rep id id u hx g hg
  have h2 := actU_rep hm hx (qdet (Egl n) u) g hg
  rw [algHom_qdet] at h2
  simp only [Egl, FreeAlgebra.lift_ι_apply] at h2
  unfold capelli qdetOp
  rw [h1]
  exact h2.symm

end vec

end CompanionTheory.CapEig

end
