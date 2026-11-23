import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivProdIrrZero

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem class_of_finite_length {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (h : HasFiniteLength π) : cl0 π = clsGL π h := by
  rw [cl0, dif_pos h]

theorem class_congr_iso {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W} (φ : π.Equiv τ) :
    cl0 π = cl0 τ := by
  by_cases h : HasFiniteLength π
  · have h' : HasFiniteLength τ := h.of_equiv φ
    rw [class_of_finite_length h, class_of_finite_length h', clsGL_congr φ h h']
  · have h' : ¬ HasFiniteLength τ := fun h' => h (h'.of_equiv φ.symm)
    rw [cl0, cl0, dif_neg h, dif_neg h']

theorem class_chosen_rep_basis (x : IrrGL k) : cl0 x.rep = sg x := by
  rw [class_of_finite_length x.2.rep.hasFiniteLength]
  exact (clsGL_irr x.2.rep _).trans (by rw [IrrCl.cl_rep]; rfl)

theorem prodIrr_cast {h h' N N' : ℕ} (e : h = h') (x : Fin h → IrrGL k) (y : Fin h' → IrrGL k)
    (hxy : ∀ i, x i = y (Fin.cast e i)) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N') :
    (HasFiniteLength (prodIrr x hx) ↔ HasFiniteLength (prodIrr y hy)) ∧
      cl0 (prodIrr x hx) = cl0 (prodIrr y hy) := by
  subst e
  have hxy' : x = y := funext fun i => hxy i
  subst hxy'
  have hN : N = N' := hx.symm.trans hy
  subst hN
  exact ⟨Iff.rfl, rfl⟩

theorem prodIrr_zero {N : ℕ} (x : Fin 0 → IrrGL k) (hd : ∑ a, (x a).1 = N) :
    HasFiniteLength (prodIrr x hd) ∧ cl0 (prodIrr x hd) = GrothGL.unit k := by
  obtain rfl : N = 0 := by simpa using hd.symm
  obtain ⟨φ⟩ := GlobalTheory.LocGL.Tests.nonempty_equiv_prodIrr_zero x hd
  have h1 : HasFiniteLength (IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one).ρ :=
    (IrrRep.det (Fin 0) 1 isSmoothChar_one).hasFiniteLength
  have hfl : HasFiniteLength (prodIrr x hd) := h1.of_equiv φ
  refine ⟨hfl, ?_⟩
  rw [← class_congr_iso φ]
  exact (class_of_finite_length h1).trans (clsGL_irr _ _)

theorem prodIrr_one (x : IrrGL k) (hd : ∑ _ : Fin 1, x.1 = x.1) :
    HasFiniteLength (prodIrr (fun _ : Fin 1 => x) hd) ∧ cl0 (prodIrr (fun _ : Fin 1 => x) hd) = sg x := by
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_one x hd
  exact ⟨x.2.rep.hasFiniteLength.of_equiv φ, (class_congr_iso φ).symm.trans (class_chosen_rep_basis x)⟩

theorem class_of_product_equiv (hM : MulCls k) {r t : ℕ} {U W X : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup X] [Module ℂ X] (π₁ : Representation ℂ (GL (Fin r) k) U)
    (π₂ : Representation ℂ (GL (Fin t) k) W) (τ : Representation ℂ (GL (Fin (r + t)) k) X)
    (F : (prod₂ π₁ π₂).Equiv τ) (h₁ : HasFiniteLength π₁) (h₂ : HasFiniteLength π₂) (s₁ : IsSmooth π₁)
    (s₂ : IsSmooth π₂) : HasFiniteLength τ ∧ cl0 τ = mulR (cl0 π₁) (cl0 π₂) := by
  obtain ⟨h, hc⟩ := hM r t U W π₁ π₂ h₁ h₂ s₁ s₂
  exact ⟨h.of_equiv F, (class_congr_iso F).symm.trans hc⟩

theorem prodIrr_append_one (hM : MulCls k) {h : ℕ} (x₀ : IrrGL k) (y : Fin h → IrrGL k)
    (hy : ∑ a, (y a).1 = ∑ a, (y a).1) (hfl : HasFiniteLength (prodIrr y hy))
    (happ : ∑ a, (Fin.append (fun _ : Fin 1 => x₀) y a).1 = x₀.1 + ∑ a, (y a).1) :
    HasFiniteLength (prodIrr (Fin.append (fun _ : Fin 1 => x₀) y) happ) ∧
      cl0 (prodIrr (Fin.append (fun _ : Fin 1 => x₀) y) happ) = mulR (sg x₀) (cl0 (prodIrr y hy)) := by
  have hx1 : ∑ _ : Fin 1, x₀.1 = x₀.1 := by simp
  obtain ⟨F⟩ := GlobalTheory.T.product_irreducible_append_equiv k 1 h x₀.1 (∑ a, (y a).1) (fun _ : Fin 1 => x₀) y hx1 hy happ
  have H1 := prodIrr_one x₀ hx1
  have H3 := class_of_product_equiv hM (prodIrr (fun _ : Fin 1 => x₀) hx1) (prodIrr y hy) _ F H1.1 hfl
    (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)
  exact ⟨H3.1, H3.2.trans (congrArg (fun a => mulR a (cl0 (prodIrr y hy))) H1.2)⟩

theorem class_product_irreducible_fold (hM : MulCls k) : ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N),
    HasFiniteLength (prodIrr x hd) ∧
      cl0 (prodIrr x hd) = (List.ofFn x).foldr (fun y a => mulR (sg y) a) (GrothGL.unit k) := by
  intro h
  induction h with
  | zero =>
    intro N x hd
    obtain ⟨hfl, hc⟩ := prodIrr_zero x hd
    refine ⟨hfl, ?_⟩
    rw [hc]
    rfl
  | succ h ih =>
    intro N x hd
    have hy : ∑ a, (Fin.tail x a).1 = ∑ a, (Fin.tail x a).1 := rfl
    have happ : ∑ a, (Fin.append (fun _ : Fin 1 => x 0) (Fin.tail x) a).1 = (x 0).1 + ∑ a, (Fin.tail x a).1 := by
      rw [Fin.sum_univ_add]
      simp
    have H2 := ih _ (Fin.tail x) hy
    have H := prodIrr_append_one hM (x 0) (Fin.tail x) hy H2.1 happ
    have hcast := prodIrr_cast (Nat.add_comm 1 h) (Fin.append (fun _ : Fin 1 => x 0) (Fin.tail x)) x
      (fun i => by rw [Fin.append_left_eq_cons, Function.comp_apply, Fin.cons_self_tail]) happ hd
    refine ⟨hcast.1.1 H.1, hcast.2.symm.trans (H.2.trans ?_)⟩
    rw [H2.2, List.ofFn_succ, List.foldr_cons]
    rfl

variable (k) in

theorem prodList (h : MulCls k) : ProdList k :=
  fun n N x hd => (class_product_irreducible_fold h n N x hd).2

end PositivityTheory.Groth

end
