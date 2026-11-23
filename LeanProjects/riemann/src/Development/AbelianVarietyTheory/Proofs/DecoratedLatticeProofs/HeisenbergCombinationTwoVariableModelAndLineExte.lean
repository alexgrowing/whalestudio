import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocalModelSliceSourceLineStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocalModelSliceTargetLineStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section
namespace GlobalTheory.BiComb

variable {D : D7}

theorem heisO_resS_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (F : WO V S → ℂ)
    (w u : WO A S) (v : WO L S) :
    heisO ψ V S ((o.resS S).symm (w, 0)) F ((o.resS S).symm (u, v)) =
      heisO ψ A S w (fun u' => F ((o.resS S).symm (u', v))) u := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem heisO_resT_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (F : WO S V → ℂ)
    (w u : WO S A) (v : WO S L) :
    heisO ψ S V ((o.resT S).symm (w, 0)) F ((o.resT S).symm (u, v)) =
      heisO ψ S A w (fun u' => F ((o.resT S).symm (u', v))) u := by
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem comb_resS_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (c : WO A S →₀ ℂ)
    (F : WO V S → ℂ) (u : WO A S) (v : WO L S) :
    comb ψ V S (c.mapDomain fun w => (o.resS S).symm (w, 0)) F ((o.resS S).symm (u, v)) =
      comb ψ A S c (fun u' => F ((o.resS S).symm (u', v))) u := by
  classical
  have hinj : Function.Injective fun w : WO A S => (o.resS S).symm (w, 0) := fun a b h => by
    have := congrArg (o.resS S) h
    simp only [AddEquiv.apply_symm_apply, Prod.mk.injEq, and_true] at this
    exact this
  simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finsupp.mapDomain_apply hinj, heisO_resS_slice]

theorem comb_resT_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (c : WO S A →₀ ℂ)
    (F : WO S V → ℂ) (u : WO S A) (v : WO S L) :
    comb ψ S V (c.mapDomain fun w => (o.resT S).symm (w, 0)) F ((o.resT S).symm (u, v)) =
      comb ψ S A c (fun u' => F ((o.resT S).symm (u', v))) u := by
  classical
  have hinj : Function.Injective fun w : WO S A => (o.resT S).symm (w, 0) := fun a b h => by
    have := congrArg (o.resT S) h
    simp only [AddEquiv.apply_symm_apply, Prod.mk.injEq, and_true] at this
    exact this
  simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finsupp.mapDomain_apply hinj, heisO_resT_slice]

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_isOne (Y Y' : Type) [Fintype Y] [Fintype Y'] : ∃ Φ : SB (Matrix Y Y' k), IsOne Φ := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} := GlobalTheory.SplitFlip.isCompact_intMatrix
  exact ⟨⟨_, GlobalTheory.LocFlat.CFac.Span.indicator_one_mem_SB hc ⟨hc.isClosed, GlobalTheory.SplitFlip.isOpen_intMatrix⟩⟩, rfl⟩

end Loc

theorem source_slice_model : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO B.L S, ∃ T₁, p.IsModel ψ FA FS T₁ ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ())) → ∀ u, T₀ Ψ ((B.o.resS S).symm (u, v)) = T₁ Ξ u := GlobalTheory.T.exists_local_model_slice_source_line

theorem target_slice_model : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ FS F₀ T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO S B.L, ∃ T₁, p.IsModel ψ FS FA T₁ ∧ ∀ (Ξ : SB (Matrix n' n k)) (Ψ : SB (Matrix (n' ⊕ Unit) n k)), (∀ x, Ψ.1 x = Ξ.1 x.toRows₁ * a (x (Sum.inr ()))) → ∀ u, T₀ Ψ ((B.o.resT S).symm (u, v)) = T₁ Ξ u := GlobalTheory.T.exists_local_model_slice_target_line

theorem comb_bimodel_and_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''], (∀ (A S A' : HSp D) (FA : Frame k A.rank n') (FS : Frame k S.rank n) (FA' : Frame k A'.rank n'') Λ c c' (Ξ₁ O₁ : SB (Matrix n n' k)) (Ξ₂ O₂ : SB (Matrix n'' n k)) (Ξ O : SB (Matrix n n' k × Matrix n'' n k)), p.IsBiModel ψ FA FS FA' Λ → p.IsCombAt ψ FA FS c Ξ₁.1 → p.IsCombAt ψ FS FA' c' Ξ₂.1 → IsOne O₁ → IsOne O₂ → (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) → (∀ q, O.1 q = O₁.1 q.1 * O₂.1 q.2) → Λ Ξ = biComb ψ A S A' c c' (Λ O)) ∧ ∀ (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), IsStdChar D ψ (-1) → p.IsCoreFrame B s FA F₀ → (∀ T₀ c (Ξ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ F₀ FS T₀ → p.IsCombAt ψ FA FS c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toCols₁ * a fun r => x r (Sum.inr ())) → (∀ x, O.1 x = Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toCols₁ * a fun r => x r (Sum.inr ())) → T₀ Ψ = comb ψ B.V₀ S (c.mapDomain fun w => (B.o.resS S).symm (w, 0)) (T₀ O)) ∧ ∀ T₀ c (Ξ : Matrix n' n k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ FS F₀ T₀ → p.IsCombAt ψ FS FA c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toRows₁ * a (x (Sum.inr ()))) → (∀ x, O.1 x = Set.indicator {x : Matrix n' n k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toRows₁ * a (x (Sum.inr ()))) → T₀ Ψ = comb ψ S B.V₀ (c.mapDomain fun w => (B.o.resT S).symm (w, 0)) (T₀ O) := by
  intro D k _ _ _ _ p ψ n n' n'' _ _ _ _ _ _
  refine ⟨?_, ?_⟩
  · intro A S A' FA FS FA' Λ c c' Ξ₁ O₁ Ξ₂ O₂ Ξ O hΛ hc hc' hO₁ hO₂ hΞ hO
    funext u v
    obtain ⟨T₁, hT₁, e₁⟩ := hΛ.1 Ξ₂ v
    let P : SB (Matrix n n' k × Matrix n'' n k) := ⟨_, GlobalTheory.LocFlat.CFac.prodFn_mem_SB O₁.2 Ξ₂.2⟩
    rw [e₁ Ξ₁ Ξ hΞ u, hc.2 T₁ hT₁ O₁ Ξ₁ hO₁ rfl]
    have hf : T₁ O₁ = fun u' => comb ψ S A' c' (Λ O u') v := by
      funext u'
      rw [← e₁ O₁ P (fun q => rfl) u']
      obtain ⟨T₂, hT₂, e₂⟩ := hΛ.2 O₁ u'
      rw [e₂ Ξ₂ P (fun q => rfl) v, hc'.2 T₂ hT₂ O₂ Ξ₂ hO₂ rfl]
      have hg : T₂ O₂ = Λ O u' := funext fun v' => (e₂ O₂ O hO v').symm
      rw [hg]
    rw [hf]
    rfl
  · intro ρ B S s FA F₀ FS _ hF
    refine ⟨?_, ?_⟩
    · intro T₀ c Ξ a Ψ O hT hc hΞ ha hΨ hO
      funext x
      obtain ⟨T₁, hT₁, e⟩ := source_slice_model D k p ψ n n' ρ B S s FA F₀ FS hF T₀ hT a ha (B.o.resS S x).2
      obtain ⟨O₁, hO₁⟩ := exists_isOne (k := k) n n'
      have h1 := hc.2 T₁ hT₁ O₁ ⟨Ξ, hΞ⟩ hO₁ rfl
      have hx : x = (B.o.resS S).symm ((B.o.resS S x).1, (B.o.resS S x).2) := by simp
      rw [hx, e ⟨Ξ, hΞ⟩ Ψ hΨ, h1, comb_resS_slice]
      have hg : T₁ O₁ = fun u' => T₀ O ((B.o.resS S).symm (u', (B.o.resS S x).2)) :=
        funext fun u' => (e O₁ O (fun y => by rw [hO₁]; exact hO y) u').symm
      rw [hg]
    · intro T₀ c Ξ a Ψ O hT hc hΞ ha hΨ hO
      funext x
      obtain ⟨T₁, hT₁, e⟩ := target_slice_model D k p ψ n n' ρ B S s FA F₀ FS hF T₀ hT a ha (B.o.resT S x).2
      obtain ⟨O₁, hO₁⟩ := exists_isOne (k := k) n' n
      have h1 := hc.2 T₁ hT₁ O₁ ⟨Ξ, hΞ⟩ hO₁ rfl
      have hx : x = (B.o.resT S).symm ((B.o.resT S x).1, (B.o.resT S x).2) := by simp
      rw [hx, e ⟨Ξ, hΞ⟩ Ψ hΨ, h1, comb_resT_slice]
      have hg : T₁ O₁ = fun u' => T₀ O ((B.o.resT S).symm (u', (B.o.resT S x).2)) :=
        funext fun u' => (e O₁ O (fun y => by rw [hO₁]; exact hO y) u').symm
      rw [hg]

end GlobalTheory.BiComb
