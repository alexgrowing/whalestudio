import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SeenTr
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocComm
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F

namespace PSeen

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isHecke_smul {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (c : ℂ) {f : G → ℂ}
    (h : IsHecke K f) : IsHecke K (c • f) := by
  have := LocComm.isHecke_sum K ({()} : Finset Unit) (fun _ => c) (fun _ => f) (fun _ _ => h)
  convert this using 1
  funext y
  simp

theorem isHecke_fsum {G ι : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (s : Finset ι)
    (g : ι → G → ℂ) (h : ∀ i ∈ s, IsHecke K (g i)) : IsHecke K (∑ i ∈ s, g i) := by
  have := LocComm.isHecke_sum K s (fun _ => 1) g h
  convert this using 1
  funext y
  simp [Finset.sum_apply]

theorem mconv_hecke {a b : ℕ} {w : Pl E} (K : Subgroup (GLw a w × GLw b w)) {f g : LF a b w}
    (hf : IsHecke K f) (hg : IsHecke K g) : IsHecke K (mconv f g) := by
  have := FinConv.cv_hecke ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) K K f g hf hg
  rw [inf_idem] at this
  exact this

variable {n : ℕ} (d : LocData E n)

theorem notGood {w : Pl E} (hw : w ∈ d.B) : ¬ d.Good w := by
  rintro ⟨-, hT, hS, hB, -⟩
  simp only [LocData.B, Finset.mem_union] at hw
  tauto

theorem L_ok (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hw : w ∈ d.S₀ ∪ d.Bad) :
    IsOpen (d.L a w : Set (GLw a w × GLw (n - a) w)) ∧ d.L a w ≤ K2 a (n - a) w := by
  obtain ⟨L₁, L₂, e, h1, h2⟩ := hd.L a ha w hw
  rw [e]
  refine ⟨?_, Subgroup.prod_mono h1.2.1 h2.2.1⟩
  rw [Subgroup.coe_prod]
  exact h1.1.prod h2.1

theorem lev₂_ok (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev₂ a w : Set (GLw a w × GLw (n - a) w)) ∧ d.lev₂ a w ≤ K2 a (n - a) w := by
  unfold LocData.lev₂
  split_ifs with h
  · exact L_ok d hd ha h
  · exact ⟨LocComm.isOpen_levelSubgroup' _ _ _, le_rfl⟩

theorem notT (hd : d.Ok) {w : Pl E} (hw : w ∈ d.S₀ ∪ d.Bad) : w ∉ d.T := by
  intro hT
  rcases Finset.mem_union.1 hw with h | h
  · exact Finset.disjoint_left.1 hd.disj.1 hT h
  · exact Finset.disjoint_left.1 hd.disj.2.1 hT h

theorem lev_eq (hd : d.Ok) {a : ℕ} {w : Pl E} (hw : w ∈ d.S₀ ∪ d.Bad) : d.lev a w = d.L a w := by
  simp [LocData.lev, notT d hd hw, hw]

theorem lev₂_eq {a : ℕ} {w : Pl E} (hw : w ∈ d.S₀ ∪ d.Bad) : d.lev₂ a w = d.L a w := by
  simp [LocData.lev₂, hw]

theorem isLetter_t_eq_idem_lev₂ {a : ℕ} {ha : a ≤ n} {L : LM d.kap a (n - a)} (hL : d.IsLetter a ha L) {w : Pl E}
    (hw : w ∈ d.B) : L.t w = idem (d.lev₂ a w) := by
  have hG := notGood d hw
  have gt : ∀ {L' : LM d.kap a (n - a)}, d.IsGen a ha L' → L'.t w = idem (d.lev₂ a w) := by
    intro L' hL'
    rcases LocComm.generator_second_levi_position d hL' w with h | ⟨h, -⟩
    · exact h
    · exact absurd h hG
  rcases hL with hg | ⟨L', hg, rfl⟩ | rfl | rfl
  · exact gt hg
  · show lfStar (L'.t w) = _
    rw [gt hg, LocComm.lfStar_idem]
  · rfl
  · rfl

theorem prod_t (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (ls : List (LM d.kap a (n - a))) (hls : ∀ L ∈ ls, d.IsLetter a ha L)
    {w : Pl E} (hw : w ∈ d.B) : (ls.foldr LM.mul (d.eL a)).t w = idem (d.lev₂ a w) := by
  induction ls with
  | nil => rfl
  | cons L ls ih =>
    have ih' := ih fun L' h => hls L' (List.mem_cons_of_mem _ h)
    show mconv (L.t w) ((ls.foldr LM.mul (d.eL a)).t w) = _
    rw [isLetter_t_eq_idem_lev₂ d (hls L (List.mem_cons_self ..)) hw, ih']
    obtain ⟨ho, hle⟩ := lev₂_ok d hd ha w
    obtain ⟨hI, -, hf⟩ := idemAlg E a (n - a) w _ ho hle
    exact (hf _ hI).1

def Inv {a : ℕ} (w : Pl E) (L : LM d.kap a (n - a)) : Prop :=
  (w ∈ d.S₀ → ∀ x y, IsHecke (d.L a w) (L.m w x y)) ∧ (w ∈ d.Bad → IsHecke (d.L a w) (L.s w))

theorem inv_mul {a : ℕ} {w : Pl E} {L L' : LM d.kap a (n - a)} (h : Inv d w L) (h' : Inv d w L') :
    Inv d w (L.mul L') := by
  refine ⟨fun hS x y => ?_, fun hB => ?_⟩
  · show IsHecke _ (∑ z, mconv (L.m w x z) (L'.m w z y))
    exact isHecke_fsum _ _ _ fun z _ => mconv_hecke _ (h.1 hS x z) (h'.1 hS z y)
  · exact mconv_hecke _ (h.2 hB) (h'.2 hB)

theorem inv_letter (h3 : LocOpUniformizer E) (hd : d.Ok) {a : ℕ} {ha : a ≤ n} {L : LM d.kap a (n - a)}
    (hL : d.IsLetter a ha L) {w : Pl E} (hw : w ∈ d.S₀ ∪ d.Bad) : Inv d w L := by
  have hwB : w ∈ d.B := by
    simp only [LocData.B, Finset.mem_union] at hw ⊢
    tauto
  have hG := notGood d hwB
  have hlev := lev_eq d hd (a := a) hw
  obtain ⟨ho, hle⟩ := L_ok d hd ha hw
  obtain ⟨hI, -, -⟩ := idemAlg E a (n - a) w _ ho hle
  have eM : ∀ x y, IsHecke (d.L a w) ((d.eL a).m w x y) := by
    intro x y
    show IsHecke _ (d.diag (fun _ => idem (d.lev a w)) x y)
    unfold LocData.diag
    rw [hlev]
    split_ifs
    · exact hI
    · exact LocComm.isHecke_zero _
  have gs : ∀ {L' : LM d.kap a (n - a)}, d.IsGen a ha L' → L'.s w = idem (d.L a w) := by
    intro L' hL'
    rcases LocComm.generator_first_levi_position d hL' w with h | ⟨h, -⟩
    · rw [h, hlev]
    · exact absurd h hG
  rcases hL with hg | ⟨L', hg, rfl⟩ | rfl | rfl
  · refine ⟨fun _ x y => ?_, fun _ => ?_⟩
    · rw [LocComm.gen_m d hg]
      exact eM x y
    · rw [gs hg]
      exact hI
  · refine ⟨fun _ x y => ?_, fun _ => ?_⟩
    · rw [LocComm.adj_m d hg]
      exact eM x y
    · show IsHecke _ (lfStar (L'.s w))
      rw [gs hg, LocComm.lfStar_idem]
      exact hI
  · refine ⟨fun hS x y => ?_, fun _ => ?_⟩
    · have := LocComm.hecke_beta d h3 hd ha (Finset.mem_union_right _ hS) x y
      rwa [hlev] at this
    · show IsHecke _ (idem (d.lev a w))
      rw [hlev]
      exact hI
  · refine ⟨fun _ x y => ?_, fun hB => ?_⟩
    · show IsHecke _ (d.diag (fun _ => if w ∈ d.T then idem (d.lev a w) else d.sgn a w • idem (d.lev a w)) x y)
      unfold LocData.diag
      rw [hlev]
      split_ifs
      · exact hI
      · exact isHecke_smul _ _ hI
      · exact LocComm.isHecke_zero _
    · show IsHecke _ (if w ∈ d.Bad then d.fix a w else idem (d.lev a w))
      rw [if_pos hB]
      exact hd.fix a ha w hB

theorem inv_prod (h3 : LocOpUniformizer E) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (ls : List (LM d.kap a (n - a)))
    (hls : ∀ L ∈ ls, d.IsLetter a ha L) {w : Pl E} (hw : w ∈ d.S₀ ∪ d.Bad) :
    Inv d w (ls.foldr LM.mul (d.eL a)) := by
  induction ls with
  | nil =>
    have := inv_letter d h3 hd (ha := ha) (L := d.eL a) (Or.inl (Or.inl rfl)) hw
    exact this
  | cons L ls ih =>
    exact inv_mul d (inv_letter d h3 hd (hls L (List.mem_cons_self ..)) hw)
      (ih fun L' h => hls L' (List.mem_cons_of_mem _ h))

end PSeen

open PSeen in
theorem seenTr (h3 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], LocOpUniformizer E) : SeenTr := by
  intro E _ _ _ n d hd a ha ls N hls w hwB
  have ht := prod_t d hd ha ls hls hwB
  refine ⟨ht, fun hc => ?_⟩
  by_cases hs : IsSplitAt w
  · have hT : w ∉ d.T := fun h => hc h hs
    have hw : w ∈ d.S₀ ∪ d.Bad := by
      simp only [LocData.B, Finset.mem_union] at hwB
      exact Finset.mem_union.2 (by tauto)
    have hinv := inv_prod d (h3 E) hd ha ls hls hw
    obtain ⟨ho, hle⟩ := L_ok d hd ha hw
    obtain ⟨-, -, hf⟩ := idemAlg E a (n - a) w _ ho hle
    have hH : IsHecke (d.L a w) ((ls.foldr LM.mul (d.eL a)).tr d.P N w) := by
      unfold LM.tr
      split_ifs with hP
      · have hS : w ∈ d.S₀ := by
          simp only [LocData.P, Finset.mem_union] at hP
          tauto
        exact isHecke_fsum _ _ _ fun x _ => isHecke_fsum _ _ _ fun y _ => isHecke_smul _ _ (hinv.1 hS x y)
      · have hB : w ∈ d.Bad := by
          simp only [LocData.P, Finset.mem_union] at hP
          rcases Finset.mem_union.1 hw with h | h
          · exact absurd (Or.inr h) hP
          · exact h
        exact hinv.2 hB
    have key := (hf _ hH).2.1
    rw [← lev₂_eq d hw] at key
    funext y
    simp only [seen, if_pos hs, ht]
    exact congrFun key y
  · funext y
    simp only [seen, if_neg hs]

end PositivityTheory.Rg.BcB.F

end
