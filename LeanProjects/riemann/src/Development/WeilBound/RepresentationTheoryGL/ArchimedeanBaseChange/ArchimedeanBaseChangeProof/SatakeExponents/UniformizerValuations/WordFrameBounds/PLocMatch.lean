import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SeenTr
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.WordIdAt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.DoubleSumFinprodFactor
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.GeneratorPowSplitPlacesOfIdempotent
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HermitianConvolution.LpowMulPf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace PositivityTheory.Rg.BcB.F.B3

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option linter.unusedSectionVars false

namespace PLocMatch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem ok_mul {κ : Pl E → Type} [∀ w, Fintype (κ w)] (P : Finset (Pl E)) (hne : ∀ w, Nonempty (κ w))
    {L L' : LM κ a b} (hL : L.Ok P) (hL' : L'.Ok P) : (L.mul L').Ok P := by
  refine ⟨fun x y => ?_, FinConv.isTestFunction_mulConvolution hL.2 hL'.2⟩
  let z₀ : ∀ w : P, κ w := fun w => Classical.choice (hne w)
  have hT : ∀ z : (∀ w : P, κ w), IsTestP (fun w => mconv (L.ent P x z w) (L'.ent P z y w)) :=
    fun z => FinConv.isTestFunction_mulConvolution (hL.1 x z) (hL'.1 z y)
  refine Fm.isTestFunction_linearCombination (J := ∀ w : P, κ w) _ hT _ (fun w => ?_) (Fm.cof_off P (hT z₀) fun w hw => ?_)
  · by_cases hw : w ∈ P
    · refine ⟨κ w, inferInstance, fun i => Function.update z₀ ⟨w, hw⟩ i, fun _ => 1, ?_⟩
      simp [LM.ent, LM.mul, hw]
    · refine ⟨Unit, inferInstance, fun _ => z₀, fun _ => 1, ?_⟩
      simp [LM.ent, LM.mul, hw]
  · simp [LM.ent, LM.mul, hw]

theorem ok_foldr {κ : Pl E → Type} [∀ w, Fintype (κ w)] (P : Finset (Pl E)) (hne : ∀ w, Nonempty (κ w))
    {L₀ : LM κ a b} (h₀ : L₀.Ok P) : ∀ l : List (LM κ a b), (∀ L ∈ l, L.Ok P) → (l.foldr LM.mul L₀).Ok P
  | [], _ => h₀
  | L :: l, hl => ok_mul P hne (hl L List.mem_cons_self)
      (ok_foldr P hne h₀ l fun L' h' => hl L' (List.mem_cons_of_mem _ h'))

theorem isTestFunction_translate {κ : Pl E → Type} [∀ w, Fintype (κ w)] (P : Finset (Pl E)) (hne : ∀ w, Nonempty (κ w))
    {L : LM κ a b} (hL : L.Ok P) (N : ∀ w, κ w → κ w → ℂ) : IsTestP (L.tr P N) := by
  let z₀ : ∀ w : P, κ w := fun w => Classical.choice (hne w)
  refine Fm.isTestFunction_linearCombination (J := (∀ w : P, κ w) × (∀ w : P, κ w)) (fun p => L.ent P p.1 p.2) (fun p => hL.1 p.1 p.2) _
    (fun w => ?_) (Fm.cof_off P (hL.1 z₀ z₀) fun w hw => ?_)
  · by_cases hw : w ∈ P
    · refine ⟨κ w × κ w, inferInstance, fun i => (Function.update z₀ ⟨w, hw⟩ i.1, Function.update z₀ ⟨w, hw⟩ i.2),
        fun i => N w i.2 i.1, ?_⟩
      simp [LM.tr, LM.ent, hw, Fintype.sum_prod_type]
    · refine ⟨Unit, inferInstance, fun _ => (z₀, z₀), fun _ => 1, ?_⟩
      simp [LM.tr, LM.ent, hw]
  · simp [LM.tr, LM.ent, hw]

theorem seen_split {φ₁ φ₂ : ∀ w : Pl E, LF a b w} {w : Pl E} (hs : IsSplitAt w) :
    seen φ₁ φ₂ w = mconv (φ₁ w) (φ₂ w) := by
  funext y; simp only [seen, if_pos hs]; rfl

theorem seen_inert {φ₁ φ₂ : ∀ w : Pl E, LF a b w} {w : Pl E} (hs : ¬ IsSplitAt w) : seen φ₁ φ₂ w = φ₁ w := by
  funext y; simp only [seen, if_neg hs]

theorem testP_seen {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) : IsTestP (seen φ₁ φ₂) := by
  have hm := FinConv.isTestFunction_mulConvolution h₁ h₂
  refine Fm.isTestFunction_linearCombination (J := Bool) (fun j => if j then (fun w => mconv (φ₁ w) (φ₂ w)) else φ₁)
    (fun j => by cases j <;> simpa) _ (fun w => ⟨Unit, inferInstance, fun _ => decide (IsSplitAt w), fun _ => 1, ?_⟩) ?_
  · by_cases hs : IsSplitAt w
    · simp [hs, seen_split hs]
    · simp [hs, seen_inert hs]
  · filter_upwards [Fm.cof_of_test h₁, Fm.cof_of_test hm] with w e1 e2
    by_cases hs : IsSplitAt w
    · rw [seen_split hs]; exact e2
    · rw [seen_inert hs]; exact e1

theorem hk_fsum {G ι : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (s : Finset ι) (c : ι → ℂ)
    (f : ι → G → ℂ) (hf : ∀ i, IsHecke K (f i)) : IsHecke K (∑ i ∈ s, c i • f i) := by
  refine ⟨HasCompactSupport.finset_sum fun i _ => (hf i).1.mul_left (f := fun _ => c i), fun k hk x => ?_⟩
  simp only [Finset.sum_apply, Pi.smul_apply]
  exact ⟨Finset.sum_congr rfl fun i _ => by rw [((hf i).2 k hk x).1],
    Finset.sum_congr rfl fun i _ => by rw [((hf i).2 k hk x).2]⟩

theorem lone_hecke {n : ℕ} {w : Pl E} {K' : Subgroup (UL n w)} (hO : IsOpen (K' : Set (UL n w))) (hKK : K' ≤ KL n w) :
    IsHecke K' (U.lone K') := by
  have hK : IsCompact (KL n w : Set (UL n w)) := by
    rw [KL, Subgroup.coe_subgroupOf]
    exact (GlobalTheory.CompanionTheory.LevelU.isClosed_UL n w).isClosedEmbedding_subtypeVal.isCompact_preimage
      (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  have hC : IsClosed (K' : Set (UL n w)) := K'.isClosed_of_isOpen hO
  have hK'c : IsCompact (K' : Set (UL n w)) := hK.of_isClosed_subset hC hKK
  refine ⟨HasCompactSupport.intro' hK'c hC fun x hx => Set.indicator_of_notMem hx _, fun k hk x => ⟨?_, ?_⟩⟩
  · simp only [U.lone, Set.indicator_apply, SetLike.mem_coe, K'.mul_mem_cancel_left hk]
  · simp only [U.lone, Set.indicator_apply, SetLike.mem_coe, K'.mul_mem_cancel_right hk]

theorem lpow_hecke {n : ℕ} {w : Pl E} {K' : Subgroup (UL n w)} (hO : IsOpen (K' : Set (UL n w))) (hKK : K' ≤ KL n w)
    {g : UL n w → ℂ} (hg : IsHecke K' g) (k : ℕ) : IsHecke K' (U.lpow K' g k) := by
  induction k with
  | zero => exact lone_hecke hO hKK
  | succ j ih =>
    have := PositivityTheory.Rg.BcB.F.FinConv.cv_hecke (KL n w) K' K' g (U.lpow K' g j) hg ih
    rw [inf_idem] at this
    exact this

theorem initial_generator_isHecke {n : ℕ} (d : LocData E n) (hd : d.Ok) (hM : MLM.MOk d) {w : Pl E}
    (hO : IsOpen (d.KU w : Set (UL n w))) (hKK : d.KU w ≤ KL n w) (hw : w ∈ d.B) : IsHecke (d.KU w) (d.g₀ w) := by
  by_cases hT : w ∈ d.T
  · have hs := (hM.T w hT).1
    have e1 : d.KU w = iwU n w (d.b w) := by simp only [LocData.KU, if_pos hT]
    have e2 : d.g₀ w = ∑ x ∈ (d.c w).support,
        ((d.c w) x * (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ)) • fU n w (d.b w) (d.ϖ w) (PositivityTheory.Rg.Bc.ArchbcB.B.lOf x) := by
      funext y
      simp only [LocData.g₀, if_pos hT, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e1, e2]
    exact hk_fsum _ _ _ _ fun x => GlobalTheory.CompanionTheory.MatchPow.fU_hecke hs _ _ _ (GlobalTheory.LocFinU.continuous_cj w)
  by_cases hS : w ∈ d.S₀
  · have e1 : d.KU w = (d.K' w).subgroupOf (UL n w) := by simp only [LocData.KU, if_neg hT, if_pos hS]
    have e2 : d.g₀ w = fun y => d.e w y.1 := by simp only [LocData.g₀, if_neg hT, if_pos hS]
    have hk := (hd.K' w hS).2.2.2.2.2
    rw [e1, e2]
    refine ⟨hk.2.2.1.comp_isClosedEmbedding (GlobalTheory.CompanionTheory.LevelU.isClosed_UL n w).isClosedEmbedding_subtypeVal,
      fun k hk' x => ⟨?_, ?_⟩⟩
    · have := hk.2.2.2 k.1 (Subgroup.mem_subgroupOf.1 hk') 1 (Subgroup.one_mem _) x.1
      simpa using this
    · have := hk.2.2.2 1 (Subgroup.one_mem _) k.1 (Subgroup.mem_subgroupOf.1 hk') x.1
      simpa using this
  · have e2 : d.g₀ w = U.lone (d.KU w) := by simp only [LocData.g₀, if_neg hT, if_neg hS]
    rw [e2]; exact lone_hecke hO hKK

end PLocMatch

open PLocMatch in
theorem locMatch (h : LocWord) (h1 : MLM.MatchLMB2) (h2 : MLM.MatchLMWordS) (h3 : MLM.MatchLMUnit) : LocMatch := by
  intro E _ _ _ hE n d hd hM S hS hLev hTne hμ hGood ls m k hm hk hcnt lU hlU
  obtain ⟨N, hN⟩ : ∃ N, m * k = N + 1 := ⟨m * k - 1, by have := Nat.mul_pos hm hk; omega⟩
  have hO : ∀ w, IsOpen (d.KU w : Set (UL n w)) := fun w => (hLev.2.1.1 w).1
  have hKK : ∀ w, d.KU w ≤ KL n w := fun w => (hLev.2.1.1 w).2.1
  have hg0 : ∀ w ∈ d.B, IsHecke (d.KU w) (d.g₀ w) := fun w hw => initial_generator_isHecke d hd hM (hO w) (hKK w) hw
  have hfamB : ∀ w ∈ d.B, U.fam d.B d.KU (d.gU m) k lU w = d.gU (N + 1) w := by
    intro w hw
    simp only [U.fam, if_pos hw, LocData.gU]
    rw [FBL.lpowMul E n w (d.KU w) (d.g₀ w) (hO w) (hKK w) (hg0 w hw) m k, hN]
  have hBS : ∀ w ∈ d.B, w ∈ S := fun w hw => hLev.1 hw
  have hTB : ∀ w ∈ d.T, w ∈ d.B := fun w hw => by simp [LocData.B, hw]
  have hPB : ∀ w, w ∉ d.B → w ∉ d.P := fun w hw hP => hw (by
    simp only [LocData.P, Finset.mem_union] at hP; simp only [LocData.B, Finset.mem_union]; tauto)
  obtain ⟨w₀, hw₀⟩ := hTne
  refine ⟨fun w hw => lpow_hecke (hO w) (hKK w) (hg0 w hw) m, ⟨w₀, hBS _ (hTB _ hw₀), fun y hy => ?_⟩, fun a ha => ?_⟩
  · rw [hfamB w₀ (hTB _ hw₀)] at hy
    exact MLM.sepPowT E hE n d hd hM N w₀ hw₀ y hy
  obtain ⟨hlet, hBtr, hoff, hnil⟩ := h E n d hd a ha ls N (hcnt.trans hN)
  have hloc := BlockFiniteConvolution.locOk₀ E n d hd a ha
  have hne : ∀ w, Nonempty (d.kap w) := hloc.1
  have hpe : prodL d ls a = (d.fixL a :: ls.map (locL d a ha)).foldr LM.mul (d.eL a) := by
    simp only [prodL, dif_pos ha]
  have hall : ∀ L ∈ (d.fixL a :: ls.map (locL d a ha)), L.Ok d.P ∧ d.IsLetter a ha L := by
    intro L hL
    rcases List.mem_cons.1 hL with rfl | hL
    · exact ⟨hloc.2.2.1, Or.inr (Or.inr (Or.inr rfl))⟩
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hL
      exact ⟨(hlet p).1, (hlet p).2.2⟩
  have hok : (prodL d ls a).Ok d.P := by
    rw [hpe]; exact ok_foldr d.P hne (hloc.2.2.2 _ (Or.inl rfl)) _ fun L hL => (hall L hL).1
  have htr : IsTestP ((prodL d ls a).tr d.P d.one) := isTestFunction_translate d.P hne hok d.one
  have hseenB : ∀ w ∈ d.B, seen ((prodL d ls a).tr d.P d.one) (prodL d ls a).t w = (prodL d ls a).tr d.P d.one w := by
    intro w hw
    have := (BlockFiniteConvolution.seenTr₀ E n d hd a ha _ d.one (fun L hL => (hall L hL).2) w hw).2 fun hT => (hM.T w hT).1
    rw [← hpe] at this; exact this
  refine ⟨⟨htr, hok.2, testP_seen htr hok.2, fun w hwS => ?_⟩,
    ⟨w₀, hBS _ (hTB _ hw₀), (hM.T w₀ hw₀).1, ?_⟩⟩
  · by_cases hwB : w ∈ d.B
    · rw [hfamB w hwB, hseenB w hwB, hBtr w hwB]
      have hb := h1 E hE n d hd hM a ha N w hwB
      by_cases hmu : w ∈ d.S₀ ∨ (w ∈ d.Bad ∧ IsSplitAt w)
      · have e : MLM.muAt d w = d.μ w := by simp only [MLM.muAt, if_pos hmu]
        rwa [e] at hb
      · have hns : ¬ IsSplitAt w := by
          intro hs
          simp only [LocData.B, Finset.mem_union] at hwB
          rcases hwB with (hT | hS0) | hBad
          · exact (hM.T w hT).1 hs
          · exact hmu (Or.inl hS0)
          · exact hmu (Or.inr ⟨hBad, hs⟩)
        exact (MLM.muInert E n a (n - a) w hns _ _ _ _).1 hb
    · have hf : U.fam d.B d.KU (d.gU m) k lU w = MLM.wordUS d w (atPlace d w ls) := by
        simp only [U.fam, if_neg hwB]; exact hlU w hwB
      have e1 : (prodL d ls a).tr d.P d.one w = (MLM.wordLS d a ha w (atPlace d w ls)).tr d.P d.one w := by
        simp only [LM.tr, if_neg (hPB w hwB)]; exact (hoff w hwB).1
      rw [hf]
      by_cases hs : IsSplitAt w
      · rw [seen_split hs, e1, (hoff w hwB).2]
        exact h2 E hE n d hd a ha w (hGood w hwS hwB hs) (hμ w) _
      · rw [seen_inert hs, e1, hnil w fun hG => hs hG.1]
        have := h3 E hE n d hd a ha w hwB fun hs' => absurd hs' hs
        rw [if_neg hs] at this
        exact (MLM.muInert E n a (n - a) w hs _ _ _ _).1 this
  · rw [hBtr w₀ (hTB _ hw₀)]
    exact MLM.regPowT E hE n d hd hM a ha N w₀ hw₀

end PositivityTheory.Rg.BcB.F.B3

end
