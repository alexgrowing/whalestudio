import Mathlib
import Formalism.PeriodIntegrals.IdxCalc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.DvTransferIdxOf

noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem idx_self (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) V) : idxAt w M M = 0 := sub_self _

theorem idx_anti (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) : idxAt w M N = -idxAt w N M :=
  (neg_sub _ _).symm

theorem one_notMem_w (w : HeightOneSpectrum (𝓞 K)) : (1 : 𝓞 K) ∉ w.asIdeal :=
  fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

theorem idx_chain (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (M N P : Submodule (𝓞 K) V) (hM : M.FG) (hN : N.FG)
    (hP : P.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (h2 : Submodule.span K (P : Set V) = Submodule.span K (N : Set V)) :
    idxAt w M P = idxAt w M N + idxAt w N P :=
  (hI K V w M N hM hN h1).2.1 P hP h2

theorem idx_nonneg_of_le (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V)) (hle : N ≤ M) :
    0 ≤ idxAt w M N := by
  have := (hI K V w M N hM hN h1).2.2.2.1 0 (fun x hx => ⟨1, one_notMem_w w, by
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, one_smul]; exact hle hx⟩)
  simpa using this

theorem idx_le_nat (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V)) (n : ℕ) (hn : 0 < n)
    (hle : N ≤ M) (hsm : ∀ x ∈ M, ((n : ℕ) : 𝓞 K) • x ∈ N) :
    idxAt w M N ≤ (Formalism.HN.rkK M : ℤ) * vAdd w ((n : ℕ) : K) :=
  (hI K V w M N hM hN h1).2.2.2.2.2 n hn hle hsm

theorem idx_map (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {V' : Type} [AddCommGroup V'] [Module K V']
    [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (φ : V →ₗ[K] V') (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (hker : M ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = N ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) :
    idxAt w M N = idxAt w (M.map (φ.restrictScalars (𝓞 K))) (N.map (φ.restrictScalars (𝓞 K))) := by
  have := (hI K V w M N hM hN h1).2.2.1 V' φ
  rw [hker, idx_self, zero_add] at this
  exact this

theorem idx_map_inj (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {V' : Type} [AddCommGroup V'] [Module K V']
    [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (φ : V →ₗ[K] V') (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (hinjM : ∀ x ∈ M, φ x = 0 → x = 0) (hinjN : ∀ x ∈ N, φ x = 0 → x = 0) :
    idxAt w M N = idxAt w (M.map (φ.restrictScalars (𝓞 K))) (N.map (φ.restrictScalars (𝓞 K))) := by
  refine idx_map hI w φ M N hM hN h1 ?_
  have hb : ∀ P : Submodule (𝓞 K) V, (∀ x ∈ P, φ x = 0 → x = 0) →
      P ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = ⊥ := by
    intro P hP
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact (Submodule.mem_bot _).mpr (hP x hx1 hx2)
  rw [hb M hinjM, hb N hinjN]

theorem span_pi_eq {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V) :
    Submodule.span K ((Submodule.pi Set.univ M : Submodule (𝓞 K) (ι → V)) : Set (ι → V)) =
      Submodule.pi Set.univ (fun i => Submodule.span K (M i : Set V)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx i _
    exact Submodule.subset_span (hx i (Set.mem_univ i))
  · rw [← Submodule.iSup_map_single]
    refine iSup_le fun i => ?_
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    intro m hm
    rw [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    intro j _
    by_cases h : j = i
    · subst h; simpa using hm
    · simp [h]

theorem idx_pi (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (M N : ι → Submodule (𝓞 K) V) (hM : ∀ i, (M i).FG) (hN : ∀ i, (N i).FG)
    (hsp : ∀ i, Submodule.span K (M i : Set V) = Submodule.span K (N i : Set V)) :
    idxAt w (Submodule.pi Set.univ M) (Submodule.pi Set.univ N) = ∑ i, idxAt w (M i) (N i) := by
  have key : ∀ s : Finset ι, idxAt w (Submodule.pi Set.univ fun i => if i ∈ s then M i else ⊥)
      (Submodule.pi Set.univ fun i => if i ∈ s then N i else ⊥) = ∑ i ∈ s, idxAt w (M i) (N i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [idx_self]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ← ih]
      have fg : ∀ P : ι → Submodule (𝓞 K) V, (∀ i, (P i).FG) →
          (Submodule.pi Set.univ fun i => if i ∈ insert a s then P i else ⊥).FG := fun P hP =>
        Submodule.fg_pi fun i => by split_ifs; exacts [hP i, Submodule.fg_bot]
      have sp : Submodule.span K ((Submodule.pi Set.univ fun i => if i ∈ insert a s then M i else ⊥ :
          Submodule (𝓞 K) (ι → V)) : Set (ι → V)) =
          Submodule.span K ((Submodule.pi Set.univ fun i => if i ∈ insert a s then N i else ⊥ :
          Submodule (𝓞 K) (ι → V)) : Set (ι → V)) := by
        rw [span_pi_eq, span_pi_eq]
        congr 1; funext i; split_ifs
        · exact hsp i
        · simp
      have hc := (hI K (ι → V) w _ _ (fg M hM) (fg N hN) sp).2.2.1 V (LinearMap.proj a)
      have hker : ∀ P : ι → Submodule (𝓞 K) V,
          (Submodule.pi Set.univ fun i => if i ∈ insert a s then P i else ⊥) ⊓
            (LinearMap.ker (LinearMap.proj a : (ι → V) →ₗ[K] V)).restrictScalars (𝓞 K) =
          Submodule.pi Set.univ fun i => if i ∈ s then P i else ⊥ := by
        intro P
        ext x
        simp only [Submodule.mem_inf, Submodule.mem_pi, Set.mem_univ, true_implies,
          Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.proj_apply]
        constructor
        · rintro ⟨h1, h2⟩ i
          by_cases hi : i = a
          · subst hi; simp [ha, h2]
          · have := h1 i; simpa [Finset.mem_insert, hi] using this
        · intro h
          refine ⟨fun i => ?_, ?_⟩
          · by_cases hi : i = a
            · subst hi; have := h i; simp only [ha, if_false, Submodule.mem_bot] at this; simp [this]
            · have := h i; simpa [Finset.mem_insert, hi] using this
          · have := h a; simpa [ha] using this
      have hmap : ∀ P : ι → Submodule (𝓞 K) V,
          (Submodule.pi Set.univ fun i => if i ∈ insert a s then P i else ⊥).map
            ((LinearMap.proj a : (ι → V) →ₗ[K] V).restrictScalars (𝓞 K)) = P a := by
        intro P
        ext m
        simp only [Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies,
          LinearMap.coe_restrictScalars, LinearMap.proj_apply]
        constructor
        · rintro ⟨x, hx, rfl⟩; have := hx a; simpa using this
        · intro hm
          refine ⟨Pi.single a m, fun i => ?_, by simp⟩
          by_cases hi : i = a
          · subst hi; simpa using hm
          · simp [hi]
      rw [hc, hker, hker, hmap, hmap, add_comm]
  simpa using key Finset.univ

end Gen

end PI.Dv.TIW
