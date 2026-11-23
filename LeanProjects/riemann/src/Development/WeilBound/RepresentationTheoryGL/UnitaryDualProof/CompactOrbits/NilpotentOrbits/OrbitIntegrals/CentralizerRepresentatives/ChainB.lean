import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.CbExistsChainOfGen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChainsOfRange

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module Submodule

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem cb_step (N : W →ₗ[E] W) (hN : IsNilpotent N) {ι : Type} [Fintype ι] [DecidableEq ι] {l : ι → ℕ}
    (hl : ∀ a, 0 < l a) (v : W) (y : ι → W) (s : ι → ℕ) (hy0 : ∀ a, (N ^ l a) (y a) = 0)
    (B : Module.Basis (Σ a, Fin (l a)) E W) (hB : IsChain N l B) (hBy : ∀ p, B p = cbFam N l y p)
    (hs : ∀ a, s a ≤ l a) (hv : v = ∑ a, (N ^ s a) (y a)) (a b : ι) (hab : s b + (l a - l b) < s a) :
    ∃ (y' : ι → W) (s' : ι → ℕ), (∀ a, (N ^ l a) (y' a) = 0) ∧
      (∃ B' : Module.Basis (Σ a, Fin (l a)) E W, IsChain N l B' ∧ ∀ p, B' p = cbFam N l y' p) ∧
      (∀ a, s' a ≤ l a) ∧ v = ∑ a, (N ^ s' a) (y' a) ∧ ∑ a, s' a < ∑ a, s a := by
  have hne : a ≠ b := by rintro rfl; simp at hab
  set i0 := l a - l b with hi0
  set d := s a - (s b + i0) with hd
  have hdpos : 0 < d := by omega
  set y' : ι → W := Function.update (Function.update y b (y b - (N ^ i0) (y a))) a
    (y a + (N ^ d) (y a)) with hy'
  set s' : ι → ℕ := Function.update s a (s b + i0) with hs'
  have y'a : y' a = y a + (N ^ d) (y a) := by simp [y']
  have y'b : y' b = y b - (N ^ i0) (y a) := by simp [y', hne.symm]
  have y'c : ∀ c, c ≠ a → c ≠ b → y' c = y c := by intro c h1 h2; simp [y', h1, h2]
  have s'a : s' a = s b + i0 := by simp [s']
  have s'c : ∀ c, c ≠ a → s' c = s c := by intro c h; simp [s', h]
  have hy0' : ∀ c, (N ^ l c) (y' c) = 0 := by
    intro c
    by_cases hca : c = a
    · rw [hca, y'a, map_add, hy0, cb_pow_pow, cb_pow_zero_of_le N (hy0 a) (by omega), add_zero]
    by_cases hcb : c = b
    · rw [hcb, y'b, map_sub, hy0, cb_pow_pow, cb_pow_zero_of_le N (hy0 a) (by omega), sub_zero]
    · rw [y'c c hca hcb, hy0]
  have hgen : ∀ c, B ⟨c, ⟨0, hl c⟩⟩ ∈ span E (Set.range (cbFam N l y')) ⊔ LinearMap.range N := by
    set T := span E (Set.range (cbFam N l y')) ⊔ LinearMap.range N with hT
    have hmemS : ∀ c, y' c ∈ T := fun c =>
      Submodule.mem_sup_left (subset_span ⟨⟨c, ⟨0, hl c⟩⟩, by simp [cbFam]⟩)
    have hmemR : ∀ j x, 0 < j → (N ^ j) x ∈ T := fun j x hj =>
      Submodule.mem_sup_right ⟨(N ^ (j - 1)) x, by rw [cb_pow_succ, show j - 1 + 1 = j by omega]⟩
    have hya : y a ∈ T := by
      have : y a = y' a - (N ^ d) (y a) := by rw [y'a]; abel
      rw [this]; exact T.sub_mem (hmemS a) (hmemR d _ hdpos)
    have hyb : y b ∈ T := by
      have : y b = y' b + (N ^ i0) (y a) := by rw [y'b]; abel
      rw [this]; refine T.add_mem (hmemS b) ?_
      rcases Nat.eq_zero_or_pos i0 with h | h
      · rw [h, pow_zero, Module.End.one_apply]; exact hya
      · exact hmemR i0 _ h
    intro c
    have hc : B ⟨c, ⟨0, hl c⟩⟩ = y c := by rw [hBy]; simp [cbFam]
    rw [hc]
    by_cases hca : c = a
    · rw [hca]; exact hya
    by_cases hcb : c = b
    · rw [hcb]; exact hyb
    rw [← y'c c hca hcb]; exact hmemS c
  obtain ⟨B', hB', hB'y⟩ := cb_exists_chain_of_gen N hN B hB hl y' hy0' hgen
  have hsle : ∀ c, s' c ≤ l c := by
    intro c
    by_cases hca : c = a
    · rw [hca, s'a]; have := hs a; omega
    · rw [s'c c hca]; exact hs c
  have hterm : ∀ c, (N ^ s' c) (y' c) = (N ^ s c) (y c) +
      ((if c = a then (N ^ (s b + i0)) (y a) else 0) - (if c = b then (N ^ (s b + i0)) (y a) else 0)) := by
    intro c
    by_cases hca : c = a
    · rw [hca, s'a, y'a, if_pos rfl, if_neg hne, map_add, cb_pow_pow, show s b + i0 + d = s a by omega]
      abel
    by_cases hcb : c = b
    · rw [hcb, s'c b (fun h => hne h.symm), y'b, if_neg (fun h => hne h.symm), if_pos rfl, map_sub, cb_pow_pow]
      abel
    · rw [s'c c hca, y'c c hca hcb, if_neg hca, if_neg hcb, sub_zero, add_zero]
  have hv' : v = ∑ c, (N ^ s' c) (y' c) := by
    rw [hv, Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp
  have hsum : ∑ c, s' c < ∑ c, s c := by
    rw [hs', Finset.sum_update_of_mem (Finset.mem_univ a), Finset.sdiff_singleton_eq_erase,
      ← Finset.add_sum_erase Finset.univ s (Finset.mem_univ a)]
    omega
  exact ⟨y', s', hy0', ⟨B', hB', hB'y⟩, hsle, hv', hsum⟩

theorem exists_good [FiniteDimensional E W] (N : W →ₗ[E] W) (hN : IsNilpotent N) (v : W) :
    ∃ (ι : Type) (_ : Fintype ι) (l s : ι → ℕ) (B : Module.Basis (Σ a, Fin (l a)) E W), IsChain N l B ∧
      (∀ a, 0 < l a) ∧ (∀ a, s a ≤ l a) ∧ (∀ a b, s a ≤ s b + (l a - l b)) ∧
      v = ∑ a, if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0 := by
  classical
  obtain ⟨ι, _, e, u, he, hu0, hli, hsp⟩ := GlobalTheory.CompanionTheory.JordanChain.exists_chain_basis N hN
  let B0 : Module.Basis (Σ a, Fin (e a)) E W := Basis.mk hli (by rw [hsp])
  have hB0p : ∀ p, B0 p = cbFam N e u p := fun p => by simp [B0, cbFam]
  have hB0 : IsChain N e B0 := cb_isChain_of_fam N e u hu0 B0 hB0p
  obtain ⟨y, s, hy0, hyg, hs, hv⟩ := cb_init N B0 hB0 he v
  obtain ⟨B1, hB1, hB1y⟩ := cb_exists_chain_of_gen N hN B0 hB0 he y hy0 hyg
  have hex : ∃ k, ∃ (y : ι → W) (s : ι → ℕ), ((∀ a, (N ^ e a) (y a) = 0) ∧
      (∃ B : Module.Basis (Σ a, Fin (e a)) E W, IsChain N e B ∧ ∀ p, B p = cbFam N e y p) ∧
      (∀ a, s a ≤ e a) ∧ v = ∑ a, (N ^ s a) (y a)) ∧ ∑ a, s a = k :=
    ⟨_, y, s, ⟨hy0, ⟨B1, hB1, hB1y⟩, hs, hv⟩, rfl⟩
  obtain ⟨y, s, ⟨hy0, ⟨B, hB, hBy⟩, hs, hv⟩, hk⟩ := Nat.find_spec hex
  have hC : ∀ a b, s a ≤ s b + (e a - e b) := by
    intro a b
    by_contra hab
    push Not at hab
    obtain ⟨y', s', h1, h2, h3, h4, h5⟩ := cb_step N hN he v y s hy0 B hB hBy hs hv a b hab
    exact Nat.find_min hex (hk ▸ h5) ⟨y', s', ⟨h1, h2, h3, h4⟩, rfl⟩
  refine ⟨ι, inferInstance, e, s, B, hB, he, hs, hC, ?_⟩
  rw [hv]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [hBy]; rfl
  · rw [show s a = e a by have := hs a; omega, hy0]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
