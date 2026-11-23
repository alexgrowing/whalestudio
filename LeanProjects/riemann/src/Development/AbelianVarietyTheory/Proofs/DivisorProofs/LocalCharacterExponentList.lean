import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorOfCharCentral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeMatrixCharacterSlotExistsStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.LeviBlockExponentLocal

set_option maxHeartbeats 1000000 in

theorem position_exponents : GlobalTheory.Published.GeometricLemmaFiltration → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N i : ℕ) (hi : i + 1 ≤ N) (b : Fin 2 → ℕ) (hb : b 0 + b 1 = N) (χ : Fin 2 → kˣ →* ℂˣ),
    (∀ j, IsSmoothChar (χ j)) → (∀ j y, ‖((χ j y : ℂˣ) : ℂ)‖ = 1) → ∀ ϖ : kˣ, ∃ L : List ℂ,
      (∀ c ∈ L, ∃ (j : Fin 2) (l : ℕ), l ≤ i ∧ ‖c‖ = nabs k ϖ ^ ((1 - (b j : ℝ)) / 2 + l)) ∧
      ∀ w, polyAt (jac (blockIndex hi) (pairInd k b hb χ) (blockScalar₂ k N i ϖ)) L w = 0 := by
  intro hG k _ _ _ _ N i hi b hb χ hsm hn ϖ
  unfold pairInd
  obtain ⟨M, bb, hbb⟩ := hG k (Fin 2) (Fin (i + 2)) (Fin N) (fun j => Fin (b j))
    (fun j => Fin (blockSizes₂ N i j)) (pairPlace b hb) (blockIndex hi)
  have hchar : IsSmoothChar (pairChar k b χ) := by
    unfold pairChar
    refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) ?_ fun a _ => ?_
    · unfold IsSmoothChar; simp
    · exact (hsm a).detChar.comp _ (continuous_apply a)
  obtain ⟨S, -, h0, htop, hS⟩ := hbb ℂ (ofChar (pairChar k b χ)) ((isSmooth_ofChar_iff _).2 hchar)
  have key : ∀ t : Fin M, ∃ c : ℂ, (∃ (j : Fin 2) (l : ℕ), l ≤ i ∧ ‖c‖ = nabs k ϖ ^ ((1 - (b j : ℝ)) / 2 + l)) ∧
      ∀ v ∈ (S t.succ).toSubmodule,
        jac (blockIndex hi) (parInd (pairPlace b hb) (ofChar (pairChar k b χ))) (blockScalar₂ k N i ϖ) v - c • v ∈
          (S t.castSucc).toSubmodule := by
    intro t
    obtain ⟨f⟩ := (bb t).nonempty_rows
    obtain ⟨g⟩ := (bb t).nonempty_cols
    have φ := Classical.choice (hS t f g)
    have hB := GlobalTheory.T.exists_size_matrix_character k N i b χ hn ϖ (bb t) f g
    refine ⟨_, hB, fun v hv => ?_⟩
    let x : (S t.succ).toSubmodule ⧸ Submodule.comap (S t.succ).toSubmodule.subtype (S t.castSucc).toSubmodule :=
      Submodule.Quotient.mk ⟨v, hv⟩
    have hq : subQuot (S t.succ) (S t.castSucc) (blockScalar₂ k N i ϖ) x =
        ((cellScalar f g (pairChar k b χ) ⟨blockScalar₂ k N i ϖ, blockScalar_mem_relParab N i ϖ g⟩ : ℂˣ) : ℂ) • x := by
      apply φ.toLinearEquiv.injective
      have h1 : φ.toLinearEquiv (subQuot (S t.succ) (S t.castSucc) (blockScalar₂ k N i ϖ) x) =
          cellFunctor f g (ofChar (pairChar k b χ)) (blockScalar₂ k N i ϖ) (φ.toLinearEquiv x) :=
        Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap (blockScalar₂ k N i ϖ) x
      refine h1.trans ((cellFunctor_ofChar_central f g _ _ (blockScalar_mem_relParab N i ϖ g) (blockScalar_comm N i ϖ) _).trans ?_)
      exact (φ.toLinearEquiv.map_smul _ _).symm
    have h2 := (Submodule.Quotient.eq _).1 (show
      (Submodule.Quotient.mk ((S t.succ).toRepresentation (blockScalar₂ k N i ϖ) ⟨v, hv⟩) :
        (S t.succ).toSubmodule ⧸ Submodule.comap (S t.succ).toSubmodule.subtype (S t.castSucc).toSubmodule) =
        Submodule.Quotient.mk
          (((cellScalar f g (pairChar k b χ) ⟨blockScalar₂ k N i ϖ, blockScalar_mem_relParab N i ϖ g⟩ : ℂˣ) : ℂ) •
            (⟨v, hv⟩ : (S t.succ).toSubmodule)) from hq)
    exact h2
  choose c hcn hc using key
  refine ⟨List.ofFn c, fun a ha => ?_, fun w => ?_⟩
  · obtain ⟨t, rfl⟩ := List.mem_ofFn.1 ha
    exact hcn t
  · have h0' : (S 0).toSubmodule = ⊥ := (congrArg Subrepresentation.toSubmodule h0).trans (toSubmodule_bot' _)
    have ht' : (S (Fin.last M)).toSubmodule = ⊤ :=
      (congrArg Subrepresentation.toSubmodule htop).trans (toSubmodule_top' _)
    exact prod_ofFn_eq_zero _ M (fun t => (S t).toSubmodule) c hc h0' w (ht' ▸ Submodule.mem_top)

end GlobalTheory.LeviBlockExponentLocal
