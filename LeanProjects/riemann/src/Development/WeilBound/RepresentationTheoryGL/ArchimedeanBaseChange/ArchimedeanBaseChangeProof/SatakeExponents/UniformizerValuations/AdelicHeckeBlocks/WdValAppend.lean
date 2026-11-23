import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GlobalTheory
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Word

theorem wdVal_append {A Γ : Type} [Monoid A] [Star A] (gen : Γ → A) (u v : List (Γ × Bool)) :
    wdVal gen (u ++ v) = wdVal gen u * wdVal gen v := by
  simp [wdVal, List.map_append, List.prod_append]

theorem wdVal_star {A Γ : Type} [Monoid A] [StarMul A] (gen : Γ → A) (w : List (Γ × Bool)) :
    star (wdVal gen w) = wdVal gen (w.map fun p => (p.1, !p.2)).reverse := by
  induction w with
  | nil => simp [wdVal]
  | cons p w ih =>
    have e : wdVal gen (p :: w) = (if p.2 then star (gen p.1) else gen p.1) * wdVal gen w := by
      simp [wdVal]
    rw [e, star_mul, ih, List.map_cons, List.reverse_cons, wdVal_append]
    congr 1
    obtain ⟨x, b⟩ := p
    cases b <;> simp [wdVal]

theorem pow_eq {A Γ J : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype J] (gen : Γ → A) (c : J → ℂ)
    (w : J → List (Γ × Bool)) (k : ℕ) :
    (∑ j, c j • wdVal gen (w j)) ^ k =
      ∑ f : Fin k → J, (∏ i, c (f i)) • wdVal gen (List.ofFn fun i => w (f i)).flatten := by
  induction k with
  | zero => simp [wdVal]
  | succ k ih =>
    rw [pow_succ', ih, Finset.sum_mul_sum, ← (Fin.consEquiv fun _ => J).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun f _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      List.ofFn_succ, List.flatten_cons, wdVal_append, smul_mul_smul_comm]

end Word

theorem adjWords : AdjWords := by
  intro A Γ _ _ _ _ gen a ha
  suffices h : ∃ (J : Type) (_ : Fintype J) (c : J → ℂ) (w : J → List (Γ × Bool)) (L : ℕ),
      (∀ j, (w j).length ≤ L) ∧ a = ∑ j, c j • wdVal gen (w j) by
    obtain ⟨J, _, c, w, L, hL, rfl⟩ := h
    exact ⟨J, inferInstance, c, w, L, hL, rfl, Word.pow_eq gen c w⟩
  induction ha using StarAlgebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨Unit, inferInstance, fun _ => 1, fun _ => [(i, false)], 1, fun _ => le_rfl, by simp [wdVal]⟩
  | algebraMap r =>
    exact ⟨Unit, inferInstance, fun _ => r, fun _ => [], 0, fun _ => le_rfl, by
      simp [wdVal, Algebra.algebraMap_eq_smul_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨J, _, c, w, L, hL, rfl⟩ := hx
    obtain ⟨J', _, c', w', L', hL', rfl⟩ := hy
    refine ⟨J ⊕ J', inferInstance, Sum.elim c c', Sum.elim w w', max L L', ?_, ?_⟩
    · rintro (j | j)
      · exact (hL j).trans (le_max_left _ _)
      · exact (hL' j).trans (le_max_right _ _)
    · simp [Fintype.sum_sum_type]
  | mul x y _ _ hx hy =>
    obtain ⟨J, _, c, w, L, hL, rfl⟩ := hx
    obtain ⟨J', _, c', w', L', hL', rfl⟩ := hy
    refine ⟨J × J', inferInstance, fun p => c p.1 * c' p.2, fun p => w p.1 ++ w' p.2, L + L', ?_, ?_⟩
    · rintro ⟨j, j'⟩
      simpa using Nat.add_le_add (hL j) (hL' j')
    · rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      dsimp only
      rw [smul_mul_smul_comm, Word.wdVal_append]
  | star x _ hx =>
    obtain ⟨J, _, c, w, L, hL, rfl⟩ := hx
    refine ⟨J, inferInstance, fun j => star (c j), fun j => ((w j).map fun p => (p.1, !p.2)).reverse, L, ?_, ?_⟩
    · intro j
      simpa using hL j
    · simp [star_sum, star_smul, Word.wdVal_star]

namespace Word

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E}

theorem sc_inl (c : ℂ) (w : List (BGen B)) : BGen.sc (Sum.inl c :: w) = c * BGen.sc w := by
  simp [BGen.sc]

theorem sc_inr (s : PT B) (w : List (BGen B)) : BGen.sc (Sum.inr s :: w) = BGen.sc w := by
  simp [BGen.sc]

end Word

theorem blkWord (h : BlockOperatorsProductAdjoint) : BlockWordOperators := by
  intro E _ _ _ B w t₀ R hw ht₀ hR hs
  have hadj : ∀ g : BGen B, g.Ok → g.adj.Ok ∧ g.adj.op = ContinuousLinearMap.adjoint g.op := by
    rintro (c | s) hg
    · refine ⟨trivial, ?_⟩
      show (starRingEnd ℂ c) • (1 : B.Hb →L[ℂ] B.Hb) = ContinuousLinearMap.adjoint (c • 1)
      rw [LinearIsometryEquiv.map_smulₛₗ]
      congr 1
      exact ContinuousLinearMap.adjoint_id.symm
    · exact ⟨(h E B s s hg hg).2.2.2.2.1, (h E B s s hg hg).2.2.2.2.2.1⟩
  suffices main : (BGen.wd w t₀).Ok ∧ (w.map BGen.op).prod * t₀.op = BGen.sc w • (BGen.wd w t₀).op ∧
      (BGen.wd w t₀).T ≤ t₀.T + w.length * R ∧ (BGen.wd w t₀).r ≤ t₀.r + w.length * R ∧
      ∀ χa χb, (BGen.wd w t₀).val χa χb =
        (w.map (Sum.elim (fun _ => 1) fun s => s.val χa χb)).prod * t₀.val χa χb by
    obtain ⟨m1, m2, m3, m4, m5⟩ := main
    exact ⟨m1, m2, m3, m4, hadj, m5⟩
  induction w with
  | nil => simp [BGen.wd, BGen.sc, ht₀]
  | cons g w ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (fun g hg => hw g (List.mem_cons_of_mem _ hg))
      (fun s hs' => hs s (List.mem_cons_of_mem _ hs'))
    have hg := hw g List.mem_cons_self
    rcases g with c | s
    · have ew : BGen.wd (Sum.inl c :: w) t₀ = BGen.wd w t₀ := rfl
      rw [ew, Word.sc_inl]
      refine ⟨h1, ?_, ?_, ?_, ?_⟩
      · rw [List.map_cons, List.prod_cons, mul_assoc, h2]
        show (c • (1 : B.Hb →L[ℂ] B.Hb)) * _ = _
        rw [smul_mul_assoc, one_mul, smul_smul]
      · simp only [List.length_cons]; push_cast; nlinarith
      · simp only [List.length_cons]; push_cast; nlinarith
      · intro χa χb
        simp [h5]
    · have ew : BGen.wd (Sum.inr s :: w) t₀ = s.mul (BGen.wd w t₀) := rfl
      have hsR := hs s List.mem_cons_self
      have hop := h E B s (BGen.wd w t₀) hg h1
      rw [ew, Word.sc_inr]
      refine ⟨hop.2.2.1, ?_, ?_, ?_, ?_⟩
      · rw [List.map_cons, List.prod_cons, mul_assoc, h2, hop.2.2.2.1]
        show s.op * _ = _
        rw [mul_smul_comm]
      · show s.T + (BGen.wd w t₀).T ≤ _
        simp only [List.length_cons]; push_cast; linarith [hsR.1]
      · show s.r + (BGen.wd w t₀).r + B.c ≤ _
        simp only [List.length_cons]; push_cast; linarith [hsR.2]
      · intro χa χb
        rw [hop.2.2.2.2.2.2.1, h5]
        simp [mul_assoc]

theorem blockEx (h1 : CompatEx) (h2 : SizeBasic) : BlockEx := by
  intro E _ _ _ a b D Ma Mb κ _ μa μb ha hb
  have : BorelSpace (G a) := ⟨rfl⟩
  have : BorelSpace (G b) := ⟨rfl⟩
  have : BorelSpace (Hf E a b) := ⟨rfl⟩
  obtain ⟨ν, hν, hν', hc⟩ := h1 E a b D μa μb
  obtain ⟨ca, hca⟩ := (h2 E a).2.2.2
  obtain ⟨cb, hcb⟩ := (h2 E b).2.2.2
  refine ⟨ν, ha, hb, hν, hν', hc, max 0 (max ca cb), le_max_left _ _, fun g h => ?_, fun g h => ?_, rfl⟩
  · linarith [hca g h, le_max_left ca cb, le_max_right 0 (max ca cb)]
  · linarith [hcb g h, le_max_right ca cb, le_max_right 0 (max ca cb)]

end PositivityTheory.Rg.BcB.F

end
