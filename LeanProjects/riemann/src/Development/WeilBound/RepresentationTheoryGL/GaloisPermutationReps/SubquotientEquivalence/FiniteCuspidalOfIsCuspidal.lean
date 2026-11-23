import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleTransportRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCuspidalWithLabelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalLabelUniqueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentsSimpleFDRepFiniteFinsumEqOne

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

private theorem exists_block_lt_unipotent_lemma {K : Type} [Field K] {n s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) {g : GL (Fin n) K} (hg : g ∈ GlobalTheory.SmGL.unipRad K e) (i j : Fin n)
    (hij : GlobalTheory.SmGL.blk e i = GlobalTheory.SmGL.blk e j) :
    (g : Matrix (Fin n) (Fin n) K) i j = if i = j then 1 else 0 := by
  obtain ⟨⟨y, hy⟩, hk, rfl⟩ := Subgroup.mem_map.1 hg
  rw [MonoidHom.mem_ker] at hk
  obtain ⟨a, i', hi⟩ : ∃ a i', e.symm i = ⟨a, i'⟩ := ⟨_, _, rfl⟩
  obtain ⟨b, j', hj⟩ : ∃ b j', e.symm j = ⟨b, j'⟩ := ⟨_, _, rfl⟩
  have hab : a = b := by
    simp only [GlobalTheory.SmGL.blk, hi, hj] at hij
    exact hij
  subst hab
  have hi2 : i = e ⟨a, i'⟩ := by
    rw [← hi, Equiv.apply_symm_apply]
  have hj2 : j = e ⟨a, j'⟩ := by
    rw [← hj, Equiv.apply_symm_apply]
  have h3 := congrArg (fun u => ((u a : GL (Fin (d a)) K) : Matrix (Fin (d a)) (Fin (d a)) K) i' j') hk
  simp [GlobalTheory.SmGL.leviProj, GlobalTheory.SmGL.diagBlock, Matrix.one_apply] at h3
  subst hi2 hj2
  simp [h3]

theorem exists_block_lt_unipotent {K : Type} [Field K] {n s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) (h : GlobalTheory.SmGL.unipRad K e ≠ ⊥) :
    ∃ i j : Fin n, GlobalTheory.SmGL.blk e i < GlobalTheory.SmGL.blk e j := by
  by_contra hcon
  push_neg at hcon
  apply h
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [exists_block_lt_unipotent_lemma e hg i j (le_antisymm (hcon j i) (hcon i j))]
  simp [Matrix.one_apply]

private theorem finite_cuspidal_of_isCuspidal_lemma {K : Type} [Field K] {n s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) (g : GL (Fin n) K)
    (h1 : (g : Matrix (Fin n) (Fin n) K).BlockTriangular (GlobalTheory.SmGL.blk e))
    (h2 : ∀ i j, GlobalTheory.SmGL.blk e i = GlobalTheory.SmGL.blk e j → (g : Matrix (Fin n) (Fin n) K) i j = if i = j then 1 else 0) :
    g ∈ GlobalTheory.SmGL.unipRad K e := by
  refine Subgroup.mem_map.2 ⟨⟨g, h1⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  funext a
  refine Units.ext ?_
  ext i' j'
  have h3 := h2 (e ⟨a, i'⟩) (e ⟨a, j'⟩) (by simp [GlobalTheory.SmGL.blk])
  simp [GlobalTheory.SmGL.leviProj, GlobalTheory.SmGL.diagBlock, Matrix.one_apply, h3]

private theorem finite_cuspidal_of_isCuspidal_lemma_2 {K : Type} [Field K] [Fintype K] [DecidableEq K] {n s : ℕ}
    {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s) (u : GL (Fin n) K)
    (hu : u ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (fun i => if GlobalTheory.SmGL.blk e i < t then (0 : Fin 2) else 1)) :
    u ∈ GlobalTheory.SmGL.unipRad K e := by
  obtain ⟨⟨hut, -⟩, hud⟩ := hu
  refine finite_cuspidal_of_isCuspidal_lemma e u ?_ ?_
  · intro i j hji
    by_cases hb : (if GlobalTheory.SmGL.blk e j < t then (0 : Fin 2) else 1) <
        (if GlobalTheory.SmGL.blk e i < t then (0 : Fin 2) else 1)
    · exact hut i j hb
    · have hne : i ≠ j := by
        intro h
        subst h
        exact lt_irrefl _ hji
      rw [hud i j ?_, if_neg hne]
      by_cases h1 : GlobalTheory.SmGL.blk e i < t
      · have h2 : GlobalTheory.SmGL.blk e j < t := lt_trans hji h1
        simp [h1, h2]
      · by_cases h2 : GlobalTheory.SmGL.blk e j < t
        · simp [h1, h2] at hb
        · simp [h1, h2]
  · intro i j hij
    rw [hud i j (by simp [hij])]

theorem finite_cuspidal_of_isCuspidal {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}
    (τ : FDRep ℂ (GL (Fin n) K)) (h : Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ) : FinCusp τ.ρ := by
  unfold FinCusp
  intro s d e hne v hv
  obtain ⟨i0, j0, hlt⟩ := exists_block_lt_unipotent e hne
  refine h 2 (fun i => if GlobalTheory.SmGL.blk e i < GlobalTheory.SmGL.blk e j0 then 0 else 1) ?_ le_rfl v ?_
  · intro k
    fin_cases k
    · exact ⟨i0, by simp [hlt]⟩
    · exact ⟨j0, by simp⟩
  · intro u hu
    exact hv u (finite_cuspidal_of_isCuspidal_lemma_2 e _ u hu)

theorem hasCuspLabel_of_equiv {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K) {n : ℕ} {τ τ' : FDRep ℂ (GL (Fin n) K)} (e : τ ≃ₗ[ℂ] τ')
    (he : ∀ g v, e (τ.ρ g v) = τ'.ρ g (e v)) {P : K[X]} (h : Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ P) :
    Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ' P := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun x hx γ hγ z hz m hm => ?_⟩
  rw [← h5 x hx γ hγ z hz m hm]
  have hc : τ'.ρ γ = (e.toLinearMap ∘ₗ τ.ρ γ) ∘ₗ e.symm.toLinearMap := by
    ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he, LinearEquiv.apply_symm_apply]
  rw [hc, ← LinearEquiv.conj_apply, LinearMap.trace_conj']

theorem st7 : St7 := by
  intro K _ _ n hn
  classical
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨C⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.nonempty_labelConv K
  obtain ⟨P0, a0, b0, c0, d0⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.exists_monic_irreducible K n hn
  obtain ⟨τ0, -⟩ := GlobalTheory.T.exists_cuspidal_with_label K C n hn P0 a0 b0 c0 d0
  have hex : ∀ P : K[X], ∃ τ : FDRep ℂ (GL (Fin n) K), P ∈ Lab K n →
      CategoryTheory.Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ P := by
    intro P
    by_cases hP : P ∈ Lab K n
    · obtain ⟨p1, p2, p3, p4⟩ := hP
      obtain ⟨τ, hs, hc, hl⟩ := GlobalTheory.T.exists_cuspidal_with_label K C n hn P p1 p2 p3 p4
      exact ⟨τ, fun _ => ⟨hs, hc, hl⟩⟩
    · exact ⟨τ0, fun h' => absurd h' hP⟩
  choose τ hτ using hex
  refine ⟨τ, fun P hP => ⟨GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple _ (hτ P hP).1,
    finite_cuspidal_of_isCuspidal _ (hτ P hP).2.1⟩, ?_⟩
  rintro P hP P' hP' ⟨e, he⟩
  exact GlobalTheory.T.cuspidal_label_unique K C (Fin n) (τ P') P P' (hasCuspLabel_of_equiv C e he (hτ P hP).2.2)
    (hτ P' hP').2.2

end PositivityTheory.Rg.DzCount

end
