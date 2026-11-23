import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

noncomputable section

namespace GlobalTheory.RealQuot.SemisimpleSpan

open GlobalTheory.RealQuot

theorem isStab_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M] {σ : ι → Module.End ℂ M}
    (W : κ → Submodule ℂ M) (h : ∀ k, IsStab σ (W k)) : IsStab σ (⨆ k, W k) := by
  intro i
  have hle : (⨆ k, W k) ≤ (⨆ k, W k).comap (σ i) :=
    iSup_le fun k x hx => Submodule.mem_iSup_of_mem k (h k i x hx)
  exact fun x hx => hle hx

theorem exists_stab_compl_of_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M] (σ : ι → Module.End ℂ M)
    (W : κ → Submodule ℂ M) (hW : ∀ k, IsStab σ (W k))
    (hs : ∀ k (V : Submodule ℂ M), IsStab σ V → V ≤ W k → V = ⊥ ∨ V = W k) (htop : ⨆ k, W k = ⊤) :
    ∀ N : Submodule ℂ M, IsStab σ N → ∃ N' : Submodule ℂ M, IsStab σ N' ∧ IsCompl N N' := by
  letI : Module (FreeAlgebra ℂ ι) M :=
    Module.compHom M (FreeAlgebra.lift ℂ σ : FreeAlgebra ℂ ι →ₐ[ℂ] Module.End ℂ M).toRingHom
  have smul_def : ∀ (a : FreeAlgebra ℂ ι) (x : M), a • x = FreeAlgebra.lift ℂ σ a x := fun _ _ => rfl
  haveI : IsScalarTower ℂ (FreeAlgebra ℂ ι) M := ⟨fun c a x => by
    rw [smul_def, smul_def, map_smul]
    rfl⟩
  have key : ∀ N : Submodule ℂ M, IsStab σ N →
      ∃ W' : Submodule (FreeAlgebra ℂ ι) M, W'.restrictScalars ℂ = N := by
    intro N hN
    have hst : ∀ a : FreeAlgebra ℂ ι, ∀ x ∈ N, FreeAlgebra.lift ℂ σ a x ∈ N := by
      intro a
      induction a using FreeAlgebra.induction with
      | grade0 r =>
        intro x hx
        rw [AlgHom.commutes, Module.algebraMap_end_apply]
        exact N.smul_mem r hx
      | grade1 i =>
        intro x hx
        rw [FreeAlgebra.lift_ι_apply]
        exact hN i x hx
      | mul a b ha hb =>
        intro x hx
        rw [map_mul, Module.End.mul_apply]
        exact ha _ (hb x hx)
      | add a b ha hb =>
        intro x hx
        rw [map_add, LinearMap.add_apply]
        exact N.add_mem (ha x hx) (hb x hx)
    refine ⟨{ carrier := N
              add_mem' := N.add_mem
              zero_mem' := N.zero_mem
              smul_mem' := fun a x hx => hst a x hx }, ?_⟩
    ext x
    rfl
  have stabR : ∀ W' : Submodule (FreeAlgebra ℂ ι) M, IsStab σ (W'.restrictScalars ℂ) := by
    intro W' i x hx
    have : σ i x = (FreeAlgebra.ι ℂ i) • x := by rw [smul_def, FreeAlgebra.lift_ι_apply]
    rw [this]
    exact W'.smul_mem _ hx
  have hss : IsSemisimpleModule (FreeAlgebra ℂ ι) M := by
    rw [← sSup_simples_eq_top_iff_isSemisimpleModule, ← Submodule.restrictScalars_eq_top_iff ℂ,
      eq_top_iff, ← htop]
    refine iSup_le fun k => ?_
    obtain ⟨Wk, hWk⟩ := key (W k) (hW k)
    rw [← hWk]
    refine Submodule.restrictScalars_mono ℂ ?_
    by_cases h0 : Wk = ⊥
    · rw [h0]
      exact bot_le
    · refine le_sSup (isSimpleModule_iff_isAtom.2 ⟨h0, fun V hV => ?_⟩)
      rcases hs k (V.restrictScalars ℂ) (stabR V) (hWk ▸ Submodule.restrictScalars_mono ℂ hV.le) with h | h
      · exact (Submodule.restrictScalars_eq_bot_iff ℂ _ _).1 h
      · exact absurd ((Submodule.restrictScalars_injective ℂ _ _) (h.trans hWk.symm)) hV.ne
  intro N hN
  obtain ⟨WN, hWN⟩ := key N hN
  obtain ⟨W', hc⟩ := exists_isCompl WN
  refine ⟨W'.restrictScalars ℂ, stabR W', ⟨?_, ?_⟩⟩
  · rw [disjoint_iff, ← hWN, ← Submodule.restrictScalars_inf, hc.inf_eq_bot]
    rfl
  · rw [codisjoint_iff, ← hWN, ← Submodule.restrictScalars_sup, hc.sup_eq_top]
    rfl

theorem exists_stab_compl : ∀ (ι J Fm Q Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pi] [Module ℂ Pi] (ρ : ι → Module.End ℂ Q)
  (C : Submodule ℂ Q) (σ : ι → Module.End ℂ Pi) (τ : J → Module.End ℂ Pi) (β : Fm → Q →ₗ[ℂ] Pi),
  GlobalTheory.RealQuot.HoweCond ρ C → (∀ f i, β f ∘ₗ ρ i = σ i ∘ₗ β f) → (∀ f, C ≤ LinearMap.ker (β f)) →
  (∀ j f, ∃ f', τ j ∘ₗ β f = β f') → (⨆ f, LinearMap.range (β f)) = ⊤ →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → GlobalTheory.RealQuot.IsStab τ N → N = ⊥ ∨ N = ⊤) →
  ∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N' := by
  intro ι J Fm Q Pi _ _ _ _ ρ C σ τ β hH hint hker hτ hspan hirr
  obtain ⟨⟨L, hL⟩, -⟩ := hH
  have hcomm : ∀ f i x, β f (ρ i x) = σ i (β f x) := fun f i x => by
    rw [← LinearMap.comp_apply (β f) (ρ i), hint f i, LinearMap.comp_apply]
  let K : Submodule ℂ Q := ⨅ f, LinearMap.ker (β f)
  have hKf : ∀ f, K ≤ LinearMap.ker (β f) := fun f => iInf_le _ f
  have hKs : IsStab ρ K := by
    intro i x hx
    refine Submodule.mem_iInf _ |>.2 fun f => ?_
    rw [LinearMap.mem_ker, hcomm, LinearMap.mem_ker.1 (hKf f hx), map_zero]
  have hCK : C ≤ K := le_iInf hker

  have hmapS : ∀ S : Submodule ℂ Q, IsStab ρ S → ∀ f, IsStab σ (S.map (β f)) := by
    rintro S hS f i _ ⟨x, hx, rfl⟩
    exact ⟨ρ i x, hS i x hx, hcomm f i x⟩
  have hNS : ∀ S : Submodule ℂ Q, IsStab ρ S → (⨆ f, S.map (β f)) = ⊥ ∨ (⨆ f, S.map (β f)) = ⊤ := by
    intro S hS
    refine hirr _ (isStab_iSup _ (hmapS S hS)) ?_
    intro j
    have hle : (⨆ f, S.map (β f)) ≤ (⨆ f, S.map (β f)).comap (τ j) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨f', hf'⟩ := hτ j f
      show τ j (β f x) ∈ ⨆ f, S.map (β f)
      rw [← LinearMap.comp_apply, hf']
      exact Submodule.mem_iSup_of_mem f' ⟨x, hx, rfl⟩
    exact fun x hx => hle hx

  obtain ⟨S, hSst, hStop, hsimp⟩ : ∃ S : Submodule ℂ Q, IsStab ρ S ∧ (⨆ f, S.map (β f)) = ⊤ ∧
      ∀ f (V : Submodule ℂ Pi), IsStab σ V → V ≤ S.map (β f) → V = ⊥ ∨ V = S.map (β f) := by
    by_cases hK : K = ⊤
    · refine ⟨⊤, fun i x _ => Submodule.mem_top, by simpa [Submodule.map_top] using hspan, fun f V _ hV => Or.inl ?_⟩
      have h0 : (⊤ : Submodule ℂ Q).map (β f) = ⊥ := by
        rw [Submodule.map_top, LinearMap.range_eq_bot]
        exact LinearMap.ker_eq_top.1 (top_le_iff.1 (hK ▸ hKf f))
      exact le_bot_iff.1 (h0 ▸ hV)
    · let T : Type := {S : Submodule ℂ Q // IsStab ρ S ∧ C ≤ S}
      have wf : WellFounded (fun x y : T => x.1 < y.1) := by
        refine ⟨fun x => ?_⟩
        by_contra hx
        obtain ⟨g, -, hg⟩ := not_acc_iff_exists_descending_chain.1 hx
        have anti : StrictAnti fun n => (g n).1 := strictAnti_nat_of_succ_lt hg
        have mono : StrictMono fun k : Fin (L + 1) => (g (L - k.1)).1 := by
          intro a b hab
          exact anti (by have := a.2; have := b.2; simp only [Fin.lt_def] at hab; omega)
        have := hL (L + 1) _ mono fun k => (g (L - k.1)).2
        omega
      obtain ⟨M, hMK0, hMmin⟩ := wf.has_min {x : T | K < x.1}
        ⟨⟨⊤, fun i x _ => Submodule.mem_top, le_top⟩, lt_top_iff_ne_top.2 hK⟩
      have hMK : K < M.1 := hMK0
      refine ⟨M.1, M.2.1, ?_, ?_⟩
      · rcases hNS M.1 M.2.1 with h | h
        · exfalso
          refine hMK.2 (le_iInf fun f => ?_)
          intro x hx
          have h1 : β f x ∈ M.1.map (β f) := Submodule.mem_map_of_mem hx
          rw [iSup_eq_bot.1 h f] at h1
          exact LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 h1)
        · exact h
      · intro f V hVs hV
        let U : Submodule ℂ Q := M.1 ⊓ V.comap (β f)
        have hUs : IsStab ρ U := by
          rintro i x ⟨hx1, hx2⟩
          refine ⟨M.2.1 i x hx1, ?_⟩
          show β f (ρ i x) ∈ V
          rw [hcomm]
          exact hVs i _ hx2
        have hKU : K ≤ U := fun x hx => ⟨hMK.le hx, by
          show β f x ∈ V
          rw [LinearMap.mem_ker.1 (hKf f hx)]
          exact V.zero_mem⟩
        by_cases hlt : K < U
        · right
          have hUM : U = M.1 := by
            by_contra hne
            exact hMmin ⟨U, hUs, hCK.trans hKU⟩ hlt (lt_of_le_of_ne inf_le_left hne)
          refine le_antisymm hV ?_
          rintro _ ⟨x, hx, rfl⟩
          have : x ∈ U := hUM ▸ hx
          exact this.2
        · left
          have hUK : U = K := (eq_of_le_of_not_lt hKU hlt).symm
          rw [eq_bot_iff]
          intro v hv
          obtain ⟨x, hx, rfl⟩ := hV hv
          have : x ∈ U := ⟨hx, hv⟩
          rw [hUK] at this
          exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 (hKf f this))
  exact exists_stab_compl_of_iSup σ (fun f => S.map (β f)) (hmapS S hSst) hsimp hStop

end GlobalTheory.RealQuot.SemisimpleSpan

end
