import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAdjointIntegralEndOfLadicLimit
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNotMemForallMem

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.PlaceProj

theorem exists_lim_pair {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) {d : ℕ} [NeZero d] {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)
    (ρ : O →+* Matrix (Fin dd) (Fin dd) C) (hρ : ∀ a v, linAct (Y.B.A.act a) v = (ρ a).mulVec v) :
    ∃ M : Fin 2 → Matrix (Fin dd) (Fin dd) C, IsEnd (Y.raw p) V (M 0) (M 1) ∧ IsEnd (Y.raw p) V (M 1) (M 0) ∧
      ∀ g, ∃ (ε : O) (a : ℕ → O), IsLim V ρ a (M g) ∧ (∃ y, ε * ε - ε = (V.l : O) * y) ∧
        (∀ t, V.MM (p.em g t ε - 1)) ∧ (∀ x : O, (∀ t, V.MM (p.em g t x)) → ∃ y, ε * x = (V.l : O) * y) ∧
        (∀ m, ∃ y, a m * a m - a m = (V.l : O) ^ m * y) ∧ ∀ m, ∃ y, a m - ε = (V.l : O) * y := by
  obtain ⟨ε, hε, hε1, hεP⟩ := p.em_unr 0
  obtain ⟨a, h1, h2, h3⟩ := exists_idem_seq (V.l : O) ε hε
  obtain ⟨M, M', e1, e2, l1, l2⟩ := GlobalTheory.ActionLimit.exists_isEnd_of_limit C V O dd Y d I p a h1
  simp only [hρ] at l1 l2
  refine ⟨![M, M'], e1, e2, Fin.forall_fin_two.2 ⟨⟨ε, a, l1, hε, hε1, hεP, h2, h3⟩,
    star ε, fun m => star (a m), l2, ?_, fun t => ?_, fun x hx => ?_, fun m => ?_, fun m => ?_⟩⟩
  · obtain ⟨y, hy⟩ := hε
    exact ⟨star y, by simpa [mul_comm] using congrArg star hy⟩
  · rw [p.em_conj, star_star]; exact hε1 t
  · obtain ⟨y, hy⟩ := hεP (star x) fun t => by rw [← p.em_conj]; exact hx t
    exact ⟨star y, by simpa [mul_comm] using congrArg star hy⟩
  · obtain ⟨y, hy⟩ := h2 m
    exact ⟨star y, by simpa [mul_comm] using congrArg star hy⟩
  · obtain ⟨y, hy⟩ := h3 m
    exact ⟨star y, by simpa [mul_comm] using congrArg star hy⟩

theorem exists_orth_proj : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (Orb : Type) (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] (p : ∀ o, PairData Y d (I o)), (∀ x x' : Orb × Fin 2 × ZMod d, x ≠ x' → ∃ a : O, V.v ((p x.1).em x.2.1 x.2.2 a - (p x'.1).em x'.2.1 x'.2.2 a) = 0) → ∃ M : Orb → Fin 2 → Matrix (Fin dd) (Fin dd) C, (∀ o, IsEnd (Y.raw (p o)) V (M o 0) (M o 1) ∧ IsEnd (Y.raw (p o)) V (M o 1) (M o 0)) ∧ (∀ o g c, (M o g).mulVec ((p o).u g c) = (p o).u g c) ∧ (∀ o g o' g' c, (o, g) ≠ (o', g') → (M o g).mulVec ((p o').u g' c) = 0) ∧ ∀ o g v, ∃ b : I o g → C, (M o g).mulVec v = ∑ c, b c • (p o).u g c := by
  intro C _ _ V O _ _ dd Y d _ Orb I _ p hsep
  haveI := Y.algClosed
  obtain ⟨ρ, hρ1, hρ⟩ := exists_linHom Y.B.G Y.B.A
  have hint : ∀ x i j, V.Ge 0 (ρ x i j) := fun x i j => by rw [hρ1]; exact Y.intAct x i _
  choose M e1 e2 hM using fun o => exists_lim_pair Y (p o) ρ hρ
  have hs : ∀ o g (a a' : ZMod d), a ≠ a' → ∃ x, V.v ((p o).em g a x - (p o).em g a' x) = 0 :=
    fun o g a a' h => (p o).em_sep (g, a) (g, a') fun h' => h (congrArg Prod.snd h')
  refine ⟨M, fun o => ⟨e1 o, e2 o⟩, fun o g c => ?_, fun o g o' g' c hne => ?_, fun o g v => ?_⟩
  · obtain ⟨ε, a, hl, -, hε1, -, ha, ha0⟩ := hM o g
    have := hl.eig ((p o).em g ((p o).ty g c)) 1 (seq_one ha ha0 _ ((p o).em_int g _) (hε1 _)) ((p o).u g c)
      (fun x => by rw [← hρ, (p o).u_eig])
    rwa [one_smul] at this
  · obtain ⟨ε, a, hl, hε, hε1, hεP, ha, ha0⟩ := hM o g
    have hmm : V.MM ((p o').em g' ((p o').ty g' c) ε) := by
      by_contra hmm
      obtain ⟨t, ht⟩ := eq_em_of_not_mm ((p o).em g) ((p o).em_int g) ((p o).em_frob g) (hs o g) ε hε hε1 hεP _
        ((p o').em_int g' _) hmm
      obtain ⟨x, hx⟩ := hsep (o, g, t) (o', g', (p o').ty g' c) fun h =>
        hne (congrArg (fun z : Orb × Fin 2 × ZMod d => (z.1, z.2.1)) h)
      simp [ht] at hx
    have := hl.eig ((p o').em g' ((p o').ty g' c)) 0 (seq_zero ha ha0 _ ((p o').em_int g' _) hmm) ((p o').u g' c)
      (fun x => by rw [← hρ, (p o').u_eig])
    rwa [zero_smul] at this
  · obtain ⟨ε, a, hl, hε, hε1, hεP, ha, ha0⟩ := hM o g
    have := hl.range hint ((p o).em g) ((p o).em_int g) ((p o).em_frob g) (hs o g) ε hε hε1 hεP ha ha0
      (Submodule.span C (Set.range ((p o).u g))) (fun t w hw => by
        obtain ⟨b, -, hb⟩ := (p o).u_full g t w fun x => by rw [hρ, hw]
        exact (Submodule.mem_span_range_iff_exists_fun C).2 ⟨b, hb.symm⟩) v
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 this
    exact ⟨b, hb.symm⟩

end GlobalTheory.PlaceProj
