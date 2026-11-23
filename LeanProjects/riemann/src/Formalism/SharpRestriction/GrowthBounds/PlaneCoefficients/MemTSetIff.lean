import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RestPlOf
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.ProdRangeZmod
import Formalism.SharpRestriction.GrowthBounds.AevalValuation.ValGen

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.TraceSpectra
  Formalism.MainNotions.NormalSetCounting
open Formalism.MainNotions.TestSideWords.TwistedFiltration.G3 Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

theorem valS_off {R : Type} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R) (h : ∀ v ∈ F.vars, v.1 ∉ S) : 0 ≤ valS LL S F := by
  have e : valS LL S F = valS LL ∅ F := by
    unfold valS sDegs
    rw [twistSub_congr LL LL S ∅ _ F fun v hv =>
      ⟨⟨fun h' => absurd h' (h v hv), fun h' => absurd h' (Set.notMem_empty _)⟩, rfl⟩]
  rw [e]
  unfold valS
  refine Finset.le_inf fun k hk => ?_
  have := Formalism.MainNotions.G.Joints.StandardMonomialSpace.sDegs_empty_subset LL (lastIdx n) F k hk
  rw [Set.mem_singleton_iff] at this
  rw [this]
  rfl

section Phi

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n' r : ℕ} [NeZero n'] [NeZero r]
  {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J)

theorem PhiJ_nonW (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (y : ℤ)
    (hy : y ∈ Fr.letters (segZ j)) (hw : y ∉ wSet Fr (segZ j)) :
    ∃ s, posTL Fr (⟨j, s⟩ : TL J Dt.nL r) = y ∧ ∀ a : Fin r, PhiJ Fr Dt j (X (y, a)) = X (⟨j, s⟩, a) := by
  rcases restSpec n' r Fr L₁ N₁ hV J Dt.nL hnL j y hy with ⟨l, hyl, hml⟩ | ⟨m, hym, hml⟩ | ⟨m, hym, _⟩
  · exact ⟨Sum.inl l, hyl.symm, fun a => by
      simp only [PhiJ, AlgHom.comp_apply, chi, aeval_X, if_pos hy, hml, SignedChainData.ph]⟩
  · exact ⟨Sum.inr m, hym.symm, fun a => by
      simp only [PhiJ, AlgHom.comp_apply, chi, aeval_X, if_pos hy, hml, SignedChainData.ph]⟩
  · exact absurd ⟨m, hym⟩ hw

theorem PhiJ_w (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (y : ℤ)
    (hw : y ∈ wSet Fr (segZ j)) (a : Fin r) :
    PhiJ Fr Dt j (X (y, a)) ∈ supported (KK O) {u : TL J Dt.nL r × Fin r | u.1.1 = j - 1} := by
  obtain ⟨m, rfl⟩ := hw
  by_cases hy : Fr.fr (segZ j - 1) (r - 1 - m.val) ∈ Fr.letters (segZ j)
  · have : PhiJ Fr Dt j (X (Fr.fr (segZ j - 1) (r - 1 - m.val), a)) = X (⟨j - 1, Sum.inr m⟩, a) ^ Dt.P (j - 1) m := by
      simp only [PhiJ, AlgHom.comp_apply, chi, aeval_X, if_pos hy, mlOf_wc hV hnL j m, SignedChainData.ph]
    rw [this]
    refine Subalgebra.pow_mem _ ?_ _
    rw [X_mem_supported, Set.mem_ofPred_eq]
  · have : PhiJ Fr Dt j (X (Fr.fr (segZ j - 1) (r - 1 - m.val), a)) = 0 := by
      simp only [PhiJ, AlgHom.comp_apply, chi, aeval_X, if_neg hy, map_zero]
    rw [this]
    exact Subalgebra.zero_mem _

theorem mem_TSet_iff (j : ZMod J) (mm : Fin r) (s : Fin (Dt.nL j) ⊕ Fin r) :
    (⟨j, s⟩ : TL J Dt.nL r) ∈ Dt.TSet j mm ↔ (⟨j, s⟩ : TL J Dt.nL r) ∈ NSet Dt.nL j (Dt.nL j + (r - 1 - mm.val)) := by
  rcases s with l | m
  · rw [mem_NSet_inl]
    constructor
    · intro _
      have := l.isLt
      omega
    · intro _
      exact Or.inl ⟨l, rfl⟩
  · rw [mem_NSet_inr]
    have h1 := m.isLt
    have h2 := mm.isLt
    constructor
    · rintro (⟨l, h⟩ | ⟨m', hm, h⟩)
      · cases h
      · cases h
        have : mm.val < m.val := hm
        omega
    · intro h
      exact Or.inr ⟨m, (by show mm.val < m.val; omega), rfl⟩

theorem TSet_fst {j : ZMod J} {mm : Fin r} {t : TL J Dt.nL r} (h : t ∈ Dt.TSet j mm) : t.1 = j := by
  rcases h with ⟨l, rfl⟩ | ⟨m, _, rfl⟩ <;> rfl

end Phi

theorem linkL : LinkL := by
  intro p _ n' r _ _ O _ _ _ Fr L₁ N₁ hV hn J _ Dt hT hJ2 j mm hmm F hF dw hdeg th hth
  obtain ⟨hJ, hnL, hsgn, -, -, -⟩ := hT
  have hr : 1 ≤ r := NeZero.one_le
  have hmm' := mm.isLt
  set u := Dt.nL j + (r - 1 - mm.val) with hu
  have hul : u < Dt.nL j + r := by omega
  set w := wSet Fr (segZ j) with hwdef
  set Sz : Set ℤ := {y | y < posU Fr (Dt.nL j) (segZ j) u} with hSz
  have hwS : w ⊆ Sz := by
    rintro y ⟨m, rfl⟩
    have := m.isLt
    exact w_lt_posU' hV hr (segZ j) (Dt.nL j) (hnL j) _ u (by omega) hul
  have hun : (Sz \ w) ∪ w = Sz := Set.sdiff_union_of_subset hwS
  have hwv : ∀ l ∈ w, LZ.vec l = true := by
    rintro y ⟨m, rfl⟩
    have := m.isLt
    exact decide_eq_true (hV.2.2.2.2.1 _ _ (by omega)).2
  have hne : j - 1 ≠ j := by
    have : Fact (1 < J) := ⟨by omega⟩
    intro h
    exact one_ne_zero (sub_eq_self.1 h)
  have hPhi : ∀ H, PhiJ Fr Dt j H = aeval (fun v => PhiJ Fr Dt j (X v)) H := by
    intro H
    exact congrArg (fun φ : _ →ₐ[KK O] _ => φ H) (aeval_unique (PhiJ Fr Dt j))
  have hsum := sum_wCoeff w F
  have e := congrArg (PhiJ Fr Dt j) hsum
  rw [map_sum] at e
  rw [e]
  refine valS_sum_ge _ _ _ _ _ fun M hM => ?_
  rw [map_mul]
  simp only [Finset.mem_image] at hM
  obtain ⟨μ0, hμ0, rfl⟩ := hM

  have h0 : 0 ≤ valS Dt.trueLet (Dt.TSet j mm) (PhiJ Fr Dt j (monomial (μ0.filter (fun v => v.1 ∈ w)) 1)) := by
    have hs : PhiJ Fr Dt j (monomial (μ0.filter (fun v => v.1 ∈ w)) 1) ∈
        supported (KK O) {u : TL J Dt.nL r × Fin r | u.1.1 = j - 1} := by
      rw [hPhi, aeval_monomial, map_one, one_mul]
      refine Subalgebra.prod_mem _ fun v hv => Subalgebra.pow_mem _ ?_ _
      have hv' := (Finsupp.mem_support_iff.1 hv)
      rw [Finsupp.filter_apply] at hv'
      have hvw : v.1 ∈ w := by
        by_contra hc
        rw [if_neg hc] at hv'
        exact hv' rfl
      exact PhiJ_w Dt hV hnL j v.1 hvw v.2
    refine valS_off _ _ _ fun v hv hvT => ?_
    have h1 : v.1.1 = j - 1 := (mem_supported.1 hs) (Finset.mem_coe.2 hv)
    exact hne (h1.symm.trans (TSet_fst Dt hvT))

  have h1 := valS_wCoeff_ge LZ (Sz \ w) w hwv Set.disjoint_sdiff_left F dw hdeg th (by rw [hun]; exact hth)
    (μ0.filter (fun v => v.1 ∈ w))
  have hsup : wCoeff w (μ0.filter (fun v => v.1 ∈ w)) F ∈
      supported (KK O) {v : ℤ × Fin r | v.1 ∈ {y | y ∈ Fr.letters (segZ j) ∧ y ∉ w}} := by
    rw [mem_supported]
    intro v hv
    obtain ⟨ν, hν, hvν⟩ := (mem_vars_iff_mem_support v).1 (Finset.mem_coe.1 hv)
    have hc := mem_support_iff.1 hν
    rw [coeff_wCoeff] at hc
    have hv' := Finsupp.mem_support_iff.1 hvν
    split_ifs at hc with hcond
    · have hvw : v.1 ∉ w := by
        intro hvw
        have h5 : (ν.filter (fun v => v.1 ∈ w)) v = 0 := by rw [hcond.1]; rfl
        rw [Finsupp.filter_apply, if_pos hvw] at h5
        exact hv' h5
      have hvF : v ∈ F.vars := (mem_vars_iff_mem_support v).2 ⟨_, mem_support_iff.2 hc, by
        rw [Finsupp.mem_support_iff, Finsupp.add_apply]; omega⟩
      exact ⟨(mem_supported.1 hF) (Finset.mem_coe.2 hvF), hvw⟩
    · exact absurd rfl hc
  have h2 : valS LZ (Sz \ w) (wCoeff w (μ0.filter (fun v => v.1 ∈ w)) F) ≤
      valS Dt.trueLet (Dt.TSet j mm) (PhiJ Fr Dt j (wCoeff w (μ0.filter (fun v => v.1 ∈ w)) F)) := by
    rw [hPhi]
    refine valAeval (KK O) ℤ (TL J Dt.nL r) r LZ Dt.trueLet (Sz \ w) {y | y ∈ Fr.letters (segZ j) ∧ y ∉ w}
      (Dt.TSet j mm) (gT Fr Dt.nL) _ _ hsup ?_ ?_
    · rintro ⟨y, a⟩ ⟨hy, hyw⟩ hyS
      obtain ⟨s, hs, hX⟩ := PhiJ_nonW Dt hV hnL j y hy hyw
      have hg : gT Fr Dt.nL y = ⟨j, s⟩ := by rw [← hs, gT_posTL hV hnL]
      refine ⟨by simp only [hg]; exact hX a, ?_, ?_⟩
      · simp only [hg]
        rw [mem_TSet_iff, NSet_lt hV hnL j u hul s, hs]
        exact hyS.1
      · simp only [hg]
        rw [trueLet_vec Dt hV hsgn, hs]
    · rintro ⟨y, a⟩ ⟨hy, hyw⟩ hyS
      obtain ⟨s, hs, hX⟩ := PhiJ_nonW Dt hV hnL j y hy hyw
      simp only [hX a]
      refine X_mem_supported.2 ?_
      show (⟨j, s⟩ : TL J Dt.nL r) ∉ Dt.TSet j mm
      rw [mem_TSet_iff, NSet_lt hV hnL j u hul s, hs]
      intro hlt
      exact hyS ⟨hlt, hyw⟩
  have h3 := flt_valS_mul_ge Dt.trueLet (Dt.TSet j mm) (PhiJ Fr Dt j (monomial (μ0.filter (fun v => v.1 ∈ w)) 1))
    (PhiJ Fr Dt j (wCoeff w (μ0.filter (fun v => v.1 ∈ w)) F))
  refine le_trans ?_ h3
  calc ((th - dw : ℤ) : WithTop ℤ) = 0 + ((th - dw : ℤ) : WithTop ℤ) := (zero_add _).symm
    _ ≤ _ := add_le_add h0 (le_trans h1 h2)

end Formalism.MainNotions.PairMembershipBlocks
