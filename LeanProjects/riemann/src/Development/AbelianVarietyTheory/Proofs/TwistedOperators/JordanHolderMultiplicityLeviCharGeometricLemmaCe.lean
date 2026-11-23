import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicInductionDetCharactersRankOneEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTensorEquivLeviCharacter

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL.Exponents

theorem leviChar_unit_injective {R β : Type} [CommRing R] [Fintype β] {χ ψ : β → Rˣ →* ℂˣ}
    (h : leviChar (fun _ : β => Unit) χ = leviChar (fun _ : β => Unit) ψ) : χ = ψ := by
  classical
  funext j
  ext1 x
  have key : ∀ φ : β → Rˣ →* ℂˣ, leviChar (fun _ : β => Unit) φ
      (Pi.mulSingle j (Matrix.GeneralLinearGroup.scalar Unit x)) = φ j x := by
    intro φ
    rw [leviChar_apply, Finset.prod_eq_single j]
    · rw [Pi.mulSingle_eq_same]
      congr 1
      ext
      simp
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one]
    · simp
  rw [← key χ, ← key ψ, h]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_leviChar_of_smooth {β : Type} [Fintype β] (c : β → Type) [∀ j, Fintype (c j)]
    [∀ j, DecidableEq (c j)] {χ : β → kˣ →* ℂˣ} (h : ∀ j, IsSmoothChar (χ j)) :
    IsSmoothChar (leviChar c χ) := by
  unfold leviChar
  refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one
    fun a _ => ?_
  exact (h a).detChar.comp _ (continuous_apply a)

theorem nonempty_cell_term_equiv {α β : Type} [Fintype α] [LinearOrder α] [Fintype β]
    {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (g : ∀ j, (Σ i, c i j) ≃ Unit) (s : ∀ i j, IrrRep (GL (c i j) k)) (ψ : α → β → kˣ →* ℂˣ)
    (hψ : ∀ i j, IsSmoothChar (ψ i j)) (e : ∀ i j, Nonempty ((s i j).ρ.Equiv (detRep (c i j) (ψ i j)))) :
    Nonempty ((piTensor fun j => multiProd (g j) fun i => (s i j).ρ).Equiv
      (ofChar (leviChar (fun _ : β => Unit) fun j => ψ ((g j).symm ()).1 j))) := by
  obtain ⟨a⟩ := nonempty_piTensor_detRep_equiv k β (fun _ => Unit) fun j => ψ ((g j).symm ()).1 j
  refine ⟨Representation.Equiv.trans (LocGL.piTensorEquiv fun j => ?_) a⟩
  exact (LocGL.multiProdEquiv (g j) fun i => (e i j).some).trans
    (GlobalTheory.T.parabolicInduction_detCharacters_rank_one_equiv k α (fun i => c i j) (g j) (fun i => ψ i j) (fun i => hψ i j)).some

theorem jhMult_leviChar_cellFunctor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], CellSemisimplification k → ∀ (α β : Type) [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ Unit) (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)), (∀ i, IsSmooth (ρ i)) → (∀ i, HasFiniteLength (ρ i)) → ∀ χ : β → kˣ →* ℂˣ, (∀ j, IsSmoothChar (χ j)) → jhMult (ofChar (leviChar (fun _ : β => Unit) χ)) (cellFunctor (m' := fun _ : β => Unit) f g (piTensor ρ)) = ∏ i, jhMult (ofChar (leviChar (c i) χ)) (jac (f i) (ρ i)) := by
  intro k _ _ _ _ hC α β _ _ _ _ m _ _ c _ _ f g X _ _ ρ hρ hl χ hχ
  obtain ⟨T, hT0, hT⟩ := hC α β m (fun _ => Unit) c f g X ρ hρ hl
  have h1 := hT (IrrRep.ofChar (leviChar (fun _ : β => Unit) χ) (isSmoothChar_leviChar_of_smooth _ hχ))
  refine Eq.trans h1 ?_
  let s₀ : ∀ i j, IrrCl (GL (c i j) k) := fun i j => (IrrRep.det (c i j) (χ j) (hχ j)).cl
  have e₀ : ∀ i j, Nonempty ((s₀ i j).rep.ρ.Equiv (detRep (c i j) (χ j))) := fun i j =>
    (IrrRep.det (c i j) (χ j) (hχ j)).nonempty_equiv_rep
  have hfac : ∀ i, jhMult (piTensor fun j => (s₀ i j).rep.ρ) (jac (f i) (ρ i)) =
      jhMult (ofChar (leviChar (c i) χ)) (jac (f i) (ρ i)) := fun i =>
    jhMult_congr_left ((LocGL.piTensorEquiv fun j => (e₀ i j).some).trans
      (nonempty_piTensor_detRep_equiv k β (c i) χ).some) _
  rw [Finset.sum_eq_single s₀]
  · obtain ⟨a⟩ := nonempty_cell_term_equiv g (fun i j => (s₀ i j).rep) (fun _ j => χ j)
      (fun _ j => hχ j) e₀
    have h2 : jhMult (ofChar (leviChar (fun _ : β => Unit) χ))
        (piTensor fun j => multiProd (g j) fun i => (s₀ i j).rep.ρ) = 1 :=
      (jhMult_congr_right _ a).trans (jhMult_self (isIrreducible_ofChar _))
    exact (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => hfac i) h2).trans (mul_one _)
  · intro s _ hs
    have hsub : ∀ i j, Subsingleton (c i j) := fun i j =>
      ⟨fun x y => sigma_mk_injective (β := fun i => c i j) ((g j).injective (Subsingleton.elim _ _))⟩
    choose ψ hψ e using fun i j =>
      GlobalTheory.T.exists_equiv_detCharacter_of_irreducible_rank_le_one k (c i j) _ (s i j).rep.ρ (s i j).rep.smooth (s i j).rep.irr
    obtain ⟨a⟩ := nonempty_cell_term_equiv g (fun i j => (s i j).rep) ψ hψ e
    refine mul_eq_zero_of_right _ ((jhMult_congr_right _ a).trans (Model.jhMult_ofChar_ne fun h => hs ?_))
    have h3 := leviChar_unit_injective h
    funext i j
    have h4 : detChar (c i j) (ψ i j) = detChar (c i j) (χ j) := by
      rcases isEmpty_or_nonempty (c i j) with hc | ⟨⟨x⟩⟩
      · ext1 y
        rw [detChar_apply, detChar_apply, show Matrix.GeneralLinearGroup.det y = 1 from
          Units.ext (by simp), map_one, map_one]
      · have : (g j).symm () = ⟨i, x⟩ := (g j).injective (Subsingleton.elim _ _)
        rw [congrFun h3 j, this]
    rw [← (s i j).cl_rep]
    refine IrrRep.cl_eq_iff.2 ⟨(e i j).some.trans ?_⟩
    show (ofChar (detChar (c i j) (ψ i j))).Equiv (ofChar (detChar (c i j) (χ j)))
    rw [h4]
    exact .refl _
  · intro hs
    obtain ⟨i, hi⟩ := hT0 s₀ hs
    exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i) hi) _

end GlobalTheory.SmGL.Exponents
