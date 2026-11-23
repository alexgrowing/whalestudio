import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit

open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel Matrix

noncomputable section

namespace GlobalTheory.SeeSaw.MuUnits

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem Phi_eq {a t : Type} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] (Q Q' : TypeDatum k a)
    (hJ : Q.J = Q'.J) (hl : ∀ x (hx : x ∈ Q.J) (hx' : x ∈ Q'.J), Q.lam ⟨x, hx⟩ = Q'.lam ⟨x, hx'⟩)
    (μ μ' : kˣ →* ℂˣ) (hμ : ∀ x : kˣ, valuation k (x : k) = 1 → μ x = μ' x) (x : Matrix (a ⊕ t) a k) :
    Q.Phi t μ x = Q'.Phi t μ' x := by
  by_cases h : (∃ g ∈ Q.J, g.val = x.toRows₁) ∧ MaxM x.toRows₂
  · obtain ⟨⟨g, hg, e⟩, h2⟩ := h
    have hg' : g ∈ Q'.J := hJ ▸ hg
    rw [Q.Phi_of_mem μ ⟨g, hg⟩ e h2, Q'.Phi_of_mem μ' ⟨g, hg'⟩ e h2, hl g hg hg',
      hμ _ (valuation_det_of_mem_KO (Q.le_KO hg))]
  · have h' : ¬ ((∃ g ∈ Q'.J, g.val = x.toRows₁) ∧ MaxM x.toRows₂) := by rwa [← hJ]
    rw [not_not.1 (mt (Q.Phi_ne_zero_iff μ).1 h), not_not.1 (mt (Q'.Phi_ne_zero_iff μ').1 h')]

theorem iter_eq {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ μ' : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hμ' : ∀ j, IsTame (μ' j))
    (h : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = μ' j x) (j : ℕ) :
    (P.iter t μ hμ j).J = (P.iter t μ' hμ' j).J ∧ ∀ x (hx : x ∈ (P.iter t μ hμ j).J) (hx' : x ∈ (P.iter t μ' hμ' j).J),
      (P.iter t μ hμ j).lam ⟨x, hx⟩ = (P.iter t μ' hμ' j).lam ⟨x, hx'⟩ := by
  induction j with
  | zero => exact ⟨rfl, fun _ _ _ => rfl⟩
  | succ j ih =>
    obtain ⟨hJ, hl⟩ := ih
    set Q := P.iter t μ hμ j
    set Q' := P.iter t μ' hμ' j
    have hS : Q.stepJ t = Q'.stepJ t := by
      ext g; rw [TypeDatum.mem_stepJ, TypeDatum.mem_stepJ, hJ]
    refine ⟨?_, fun x hx hx' => ?_⟩
    · rw [TypeDatum.iter_succ, TypeDatum.iter_succ]
      change (Q.stepJ t).comap _ = (Q'.stepJ t).comap _
      rw [hS]
    · have hx1 : (reGL (ixSucc r t j)).symm x ∈ Q.stepJ t := hx
      have hx1' : (reGL (ixSucc r t j)).symm x ∈ Q'.stepJ t := hx'
      change (Q.step t (μ (j + 1)) (hμ _)).lam ⟨_, hx1⟩ = (Q'.step t (μ' (j + 1)) (hμ' _)).lam ⟨_, hx1'⟩
      have hg' : ((Q.corner ⟨_, hx1⟩ : Q.J) : GL _ k) ∈ Q'.J := hJ ▸ (Q.corner ⟨_, hx1⟩).2
      refine (Q.step_lam _ _ ⟨_, hx1⟩ (Q.corner ⟨_, hx1⟩) (Q.corner_val _)).trans
        (Eq.trans ?_ (Q'.step_lam _ _ ⟨_, hx1'⟩ ⟨_, hg'⟩ (Q.corner_val _)).symm)
      rw [hl _ (Q.corner ⟨_, hx1⟩).2 hg',
        h _ _ (valuation_det_of_mem_KO (Q.le_KO (Q.corner ⟨_, hx1⟩).2)), h _ _ (valuation_det_of_mem_KO hx1.1)]

theorem withMu_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ)
    (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) :
    (∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) →
      (∀ j a H, ((withMu S μ hμ).T t).Phi j a H = (S.T t).Phi j a H) ∧
      ∀ j a H, (((withMu S μ hμ).T t).lev j a H).J = ((S.T t).lev j a H).J ∧
        ∀ x hx hx', (((withMu S μ hμ).T t).lev j a H).lam ⟨x, hx⟩ = ((S.T t).lev j a H).lam ⟨x, hx'⟩ := by
  intro h
  have E := iter_eq (t := t) S.P μ S.μ hμ S.tame h
  refine ⟨fun j a H => funext fun x => ?_, fun j a H => ⟨?_, fun x hx hx' => ?_⟩⟩
  · change (S.P.iter t μ hμ j).Phi t (μ (j + 1)) _ = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1)) _
    exact Phi_eq _ _ (E j).1 (E j).2 _ _ (h (j + 1)) _
  · change (S.P.iter t μ hμ j).J.comap _ = (S.P.iter t S.μ S.tame j).J.comap _
    rw [(E j).1]; rfl
  · exact (E j).2 _ hx hx'

end GlobalTheory.SeeSaw.MuUnits
