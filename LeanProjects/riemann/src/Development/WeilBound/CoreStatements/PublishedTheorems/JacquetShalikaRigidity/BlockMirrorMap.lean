import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace BlockMirrorMap

theorem blk_mono {R : Type} [CommRing R] {a i j : ℕ} (hij : i ≤ j) {c : GL (Fin a) R} (h : GlobalTheory i c) : GlobalTheory j c :=
  fun p q hpq => h p q (by omega)

theorem blk_mul {R : Type} [CommRing R] {a j : ℕ} {c c' : GL (Fin a) R} (hc : GlobalTheory j c) (hc' : GlobalTheory j c') :
    GlobalTheory j (c * c') := by
  intro p q hpq
  rw [Units.val_mul]
  rcases hpq with h | h
  · calc (c.val * c'.val) p q = ((1 : Matrix (Fin a) (Fin a) R) * c'.val) p q := by
          simp only [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun s _ => by rw [hc p s (Or.inl h)]
      _ = _ := by rw [Matrix.one_mul]; exact hc' p q (Or.inl h)
  · calc (c.val * c'.val) p q = (c.val * (1 : Matrix (Fin a) (Fin a) R)) p q := by
          simp only [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun s _ => by rw [hc' s q (Or.inr h)]
      _ = _ := by rw [Matrix.mul_one]; exact hc p q (Or.inr h)

theorem mir_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {a m : ℕ} {g : GL (Fin a) R}
    (h : Mir m g) : Mir m (GeneralLinearGroup.map f g) := by
  intro p q hpq
  show f (g.val p q) = _
  rw [h p q hpq, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem grow {G X : Type} [TopologicalSpace G] [MulOneClass G] [ContinuousMul G] {Q : X → Prop}
    {bl bi : G → Prop} {B B' : Set G → X → Prop}
    (hbl : ∀ a b, bl a → bl b → bl (a * b)) (hi : ∀ c, bi c → bl c)
    (h : ∀ U ∈ 𝓝 (1 : G), ∃ x C, C ⊆ U ∧ Q x ∧ (∀ c ∈ C, bl c) ∧ B C x)
    (hs : ∀ U ∈ 𝓝 (1 : G), ∀ x C, Q x → B C x →
      ∃ x' C₀, C₀ ⊆ U ∧ Q x' ∧ (∀ c ∈ C₀, bi c) ∧ B' (Set.image2 (· * ·) C C₀) x') :
    ∀ U ∈ 𝓝 (1 : G), ∃ x C, C ⊆ U ∧ Q x ∧ (∀ c ∈ C, bl c) ∧ B' C x := by
  intro U hU
  obtain ⟨V, hV, hVU⟩ := exists_nhds_one_split hU
  obtain ⟨x, C, hCV, hQ, hbC, hB⟩ := h V hV
  obtain ⟨x', C₀, hC₀V, hQ', hb₀, hB'⟩ := hs V hV x C hQ hB
  refine ⟨x', Set.image2 (· * ·) C C₀, ?_, hQ', ?_, hB'⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hVU a (hCV ha) b (hC₀V hb)
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hbl a b (hbC a ha) (hi b (hb₀ b hb))

end BlockMirrorMap

theorem kept_block_at_of_pair_level_chain_threshold : jumpWindows.MirabolicColumnBlock → jumpWindows.G0 → InfinitePlaceStep → FinitePlaceStep → K4 := by
  classical
  intro hS10 hG0 h4a h4b E _ _ _ k wt ρ J hW ψ hψ S Y hY j hj U hU x hxY hxS hxL h1
  have ins1 : InS S (1 : GA E k) := fun v _ => map_one _
  have uu1 : UU 0 (1 : GA E k) :=
    ⟨fun p q h => by rw [Units.val_one, Matrix.one_apply_ne (ne_of_lt h).symm], fun p => by simp,
      fun p q _ => rfl⟩
  have ps1 : psN ψ (1 : GA E k) = 1 := by
    have e : (∑ p : Fin k × Fin k with (p.2 : ℕ) = p.1 + 1, (1 : GA E k).val p.1 p.2) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Units.val_one, Matrix.one_apply_ne]
      intro h
      rw [h] at hp
      omega
    unfold psN
    rw [e, AddChar.map_zero_eq_one]
  have om0 : ∀ g : GA E k, Om 0 0 g → g = 1 := by
    intro g hg
    apply (hG0 E k).2.2.2.2.2.1
    · rw [(hS10 _ k 0).2.1 _ hg.1, map_one]
    · intro v
      rw [(hS10 _ k 0).2.1 _ (hg.2 v), map_one]
  have start : Bump ψ S (Om 0 0) {1} (Wh ψ (J x)) := by
    refine ⟨isCompact_singleton, ?_, ⟨1, one_pos, by rw [h1]; simp⟩, ?_⟩
    · intro c hc
      rw [Set.mem_singleton_iff.mp hc]
      exact ins1
    · intro g hg _
      obtain rfl := om0 g hg
      exact ⟨1, 1, rfl, 1, uu1, ins1, (mul_one 1).symm, zero_le_one, by rw [h1, ps1]; simp⟩
  let P : ℕ → (Pl E → ℕ) → Prop := fun n m => ∀ V ∈ 𝓝 (1 : GA E k), ∃ x' C, C ⊆ V ∧
    (J x' ∈ Y ∧ SmV (ρ.comp (infGL E k)) x' ∧ Lev S (J x')) ∧ (∀ c ∈ C, GlobalTheory j c) ∧
      Bump ψ S (Om n m) C (Wh ψ (J x'))
  have p0 : P 0 0 := by
    intro V hV
    exact ⟨x, {1}, Set.singleton_subset_iff.mpr (mem_of_mem_nhds hV), ⟨hxY, hxS, hxL⟩,
      fun c hc => by rw [Set.mem_singleton_iff.mp hc]; exact (hS10 _ k j).2.2.2.1, start⟩
  have stepInf : ∀ n, n ≤ j → P n 0 := by
    intro n
    induction n with
    | zero => intro _; exact p0
    | succ n ih =>
      intro hn
      refine BlockMirrorMap.grow (fun a b ha hb => BlockMirrorMap.blk_mul ha hb) (fun c hc => BlockMirrorMap.blk_mono hn hc) (ih (by omega)) ?_
      intro V hV x C hQ hB
      obtain ⟨x', C₀, a, b, c, d, e, f⟩ :=
        h4a E k wt ρ J hW ψ hψ S Y hY n 0 (by omega) (fun _ _ => rfl) V hV x C hQ.1 hQ.2.1 hQ.2.2 hB
      exact ⟨x', C₀, a, ⟨b, c, d⟩, e, f⟩
  have stepFin : ∀ (v : Pl E), v ∈ S → ∀ m : Pl E → ℕ, m v = 0 → (∀ u, u ∉ S → m u = 0) → P j m →
      ∀ i, i ≤ j → P j (Function.update m v i) := by
    intro v hv m hmv hm hP i
    induction i with
    | zero => intro _; rw [Function.update_eq_self_iff.mpr hmv.symm]; exact hP
    | succ i ih =>
      intro hi
      have supp : ∀ u, u ∉ S → Function.update m v i u = 0 := by
        intro u hu
        have hne : u ≠ v := fun h => hu (h ▸ hv)
        rw [Function.update_of_ne hne]
        exact hm u hu
      refine BlockMirrorMap.grow (bi := fun c => GlobalTheory (Function.update m v i v + 1) c) (fun a b ha hb => BlockMirrorMap.blk_mul ha hb)
        (fun c hc => BlockMirrorMap.blk_mono (by simp; omega) hc) (ih (by omega)) ?_
      intro V hV x C hQ hB
      obtain ⟨x', C₀, a, b, c, d, e, f⟩ :=
        h4b E k wt ρ J hW ψ hψ S Y hY j (Function.update m v i) v hv (by simp; omega) supp V hV x C
          hQ.1 hQ.2.1 hQ.2.2 hB
      simp only [Function.update_self, Function.update_idem] at f
      exact ⟨x', C₀, a, ⟨b, c, d⟩, e, f⟩
  have key : ∀ T : Finset (Pl E), T ⊆ S → P j (fun w => if w ∈ T then j else 0) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro _
      have e : (fun w : Pl E => if w ∈ (∅ : Finset (Pl E)) then j else 0) = 0 := by
        funext w
        simp
      rw [e]
      exact stepInf j le_rfl
    · intro v T hv ih hT
      have h := stepFin v (hT (Finset.mem_insert_self v T)) (fun w => if w ∈ T then j else 0)
        (by simp [hv]) (fun u hu => by simp [show u ∉ T from fun h => hu (hT (Finset.mem_insert_of_mem h))])
        (ih (subset_trans (Finset.subset_insert v T) hT)) j le_rfl
      convert h using 1
      funext w
      by_cases hw : w = v
      · subst hw; simp
      · simp [hw]
  obtain ⟨x', C, hCU, ⟨hY', hS', hL'⟩, hbl, hB⟩ := key S subset_rfl U hU
  refine ⟨x', C, hCU, hY', hS', hL', hbl, hB.1, hB.2.1, hB.2.2.1, fun g hg hW0 => hB.2.2.2 g ?_ hW0⟩
  refine ⟨BlockMirrorMap.mir_map _ hg.2, fun v => ?_⟩
  by_cases hv : v ∈ S
  · simp only [hv, if_true]
    exact BlockMirrorMap.mir_map _ hg.2
  · simp only [hv, if_false]
    rw [hg.1 v hv]
    exact (hS10 _ k 0).2.2.1

end PositivityTheory.AdelicQuotientData

end
