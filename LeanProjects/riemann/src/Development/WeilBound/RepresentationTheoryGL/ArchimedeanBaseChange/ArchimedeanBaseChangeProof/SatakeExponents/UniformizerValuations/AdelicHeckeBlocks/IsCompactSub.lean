import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.RStabApply
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocComm

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Lev6

open FinConv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {S : Set (Pl E)}

section gen

variable (hmul : ∀ (i : Slot S) (x y : Gf E a b), i.cp a b (x * y) = i.cp a b x * i.cp a b y)

theorem fp_ind (hev : ∀ x : Gf E a b, ∀ᶠ i : Slot S in cofinite, i.cp a b x ∈ K2 a b i.pl)
    (L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl)) (v : Slot S → ℂ)
    (hLe : ∀ᶠ i in cofinite, L i = K2 a b i.pl ∧ v i = 1) (y : Gf E a b) :
    ∏ᶠ i, (L i : Set (GLw a i.pl × GLw b i.pl)).indicator (fun _ => v i) (i.cp a b y) =
      if y ∈ levelSub hmul L then ∏ᶠ i, v i else 0 := by
  have hfin : (Function.mulSupport fun i : Slot S =>
      (L i : Set (GLw a i.pl × GLw b i.pl)).indicator (fun _ => v i) (i.cp a b y)).Finite :=
    Filter.eventually_cofinite.1 ((hLe.and (hev y)).mono fun i hi => by
      show (L i : Set (GLw a i.pl × GLw b i.pl)).indicator (fun _ => v i) (i.cp a b y) = 1
      rw [hi.1.1, Set.indicator_of_mem (show i.cp a b y ∈ (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)) from hi.2),
        hi.1.2])
  by_cases hy : y ∈ levelSub hmul L
  · rw [if_pos hy]
    refine finprod_congr fun i => ?_
    exact Set.indicator_of_mem (show i.cp a b y ∈ (L i : Set (GLw a i.pl × GLw b i.pl)) from
      (mem_levelSub hmul L y).1 hy i) _
  · rw [if_neg hy]
    obtain ⟨i, hi⟩ := not_forall.1 (fun h => hy ((mem_levelSub hmul L y).2 h))
    exact finprod_eq_zero _ i
      (Set.indicator_of_notMem (show i.cp a b y ∉ (L i : Set (GLw a i.pl × GLw b i.pl)) from hi) _) hfin

theorem hint_ind_le {H : Type} [Group H] (K L : Subgroup H) (hLK : L ≤ K) (hidx : L.relIndex K ≠ 0) :
    hint K ((L : Set H).indicator 1) = ((L.relIndex K : ℕ) : ℂ)⁻¹ := by
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K L _ hLK (fun k hk => Hint.mem_rStab (Hint.ind_mul L hk)) hidx,
    Hint.idx_eq L L le_rfl (by rw [Subgroup.relIndex_self]; exact one_ne_zero), Subgroup.relIndex_self,
    Nat.cast_one, mul_one]

theorem hcs_ind {G : Type} [TopologicalSpace G] {L C : Set G} (hL : IsClosed L) (hC : IsCompact C) (h : L ⊆ C) :
    HasCompactSupport (L.indicator (1 : G → ℂ)) :=
  hC.of_isClosed_subset (isClosed_tsupport _)
    ((closure_minimal Set.support_indicator_subset hL).trans h)

theorem isCompact_sub {w : Pl E} {L : Subgroup (GLw a w × GLw b w)} (hL : IsOpen (L : Set (GLw a w × GLw b w)))
    (hle : L ≤ K2 a b w) : IsCompact (L : Set (GLw a w × GLw b w)) :=
  (GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK a b w).2.of_isClosed_subset (L.isClosed_of_isOpen hL) fun _ hx => hle hx

theorem index_eq (h2 : HintProd) (hcont : ∀ i : Slot S, Continuous (i.cp a b))
    (hinj : ∀ x y : Gf E a b, (∀ i : Slot S, i.cp a b x = i.cp a b y) → x = y)
    (hsurj : ∀ y : ∀ i : Slot S, GLw a i.pl × GLw b i.pl, (∀ᶠ i in cofinite, y i ∈ K2 a b i.pl) →
      ∃ x, ∀ i : Slot S, i.cp a b x = y i)
    (hev : ∀ x : Gf E a b, ∀ᶠ i : Slot S in cofinite, i.cp a b x ∈ K2 a b i.pl)
    (hK : ∀ x, x ∈ (Kf E a).prod (Kf E b) ↔ ∀ i : Slot S, i.cp a b x ∈ K2 a b i.pl)
    (L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl))
    (hL : ∀ i, IsOpen (L i : Set (GLw a i.pl × GLw b i.pl)) ∧ L i ≤ K2 a b i.pl)
    (hLe : ∀ᶠ i in cofinite, L i = K2 a b i.pl) :
    (((levelSub hmul L).relIndex ((Kf E a).prod (Kf E b)) : ℕ) : ℂ) =
      ∏ᶠ i, (((L i).relIndex (K2 a b i.pl) : ℕ) : ℂ) := by
  have hle : levelSub hmul L ≤ (Kf E a).prod (Kf E b) := fun x hx =>
    (hK x).2 fun i => (hL i).2 ((mem_levelSub hmul L x).1 hx i)
  have hidx : (levelSub hmul L).relIndex ((Kf E a).prod (Kf E b)) ≠ 0 :=
    Hint.relIndex_ne_zero (isOpen_levelSub hmul hcont hK L hL hLe) isCompact_maximal_pair
  have hp := h2 (Slot S) (Gf E a b) (fun i => GLw a i.pl × GLw b i.pl) (pc hmul) ((Kf E a).prod (Kf E b))
    (fun i => K2 a b i.pl) L (fun i => (L i : Set (GLw a i.pl × GLw b i.pl)).indicator (1 : GLw a i.pl × GLw b i.pl → ℂ)) hinj hsurj hev hK
    (fun i => ⟨(GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK a b i.pl).2, (GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK a b i.pl).1,
      (hL i).1, hcs_ind ((L i).isClosed_of_isOpen (hL i).1) (GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK a b i.pl).2
        (fun _ hx => (hL i).2 hx),
      fun u hu x => Hint.ind_mul (L i) hu x⟩)
    (hLe.mono fun i hi => by
      show (L i : Set (GLw a i.pl × GLw b i.pl)).indicator (1 : GLw a i.pl × GLw b i.pl → ℂ) =
        (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1
      rw [hi])
  have e1 : (fun x => ∏ᶠ i, (L i : Set (GLw a i.pl × GLw b i.pl)).indicator (1 : GLw a i.pl × GLw b i.pl → ℂ) (pc hmul i x)) =
      ((levelSub hmul L : Subgroup (Gf E a b)) : Set (Gf E a b)).indicator (1 : Gf E a b → ℂ) := by
    funext x
    have := fp_ind hmul hev L (fun _ => 1) (hLe.mono fun i hi => ⟨hi, rfl⟩) x
    rw [finprod_one] at this
    by_cases hx : x ∈ levelSub hmul L
    · rw [if_pos hx] at this
      rw [Set.indicator_of_mem (show x ∈ ((levelSub hmul L : Subgroup (Gf E a b)) : Set (Gf E a b)) from hx)]
      exact this
    · rw [if_neg hx] at this
      rw [Set.indicator_of_notMem (show x ∉ ((levelSub hmul L : Subgroup (Gf E a b)) : Set (Gf E a b)) from hx)]
      exact this
  have hp' : hint ((Kf E a).prod (Kf E b)) (((levelSub hmul L : Subgroup (Gf E a b)) : Set (Gf E a b)).indicator 1) =
      ∏ᶠ i, hint (K2 a b i.pl) ((L i : Set (GLw a i.pl × GLw b i.pl)).indicator 1) := by
    rw [← e1]; exact hp
  have e2 : ∀ i : Slot S, hint (K2 a b i.pl) ((L i : Set (GLw a i.pl × GLw b i.pl)).indicator 1) =
      (((L i).relIndex (K2 a b i.pl) : ℕ) : ℂ)⁻¹ := fun i =>
    hint_ind_le _ _ (hL i).2 (Hint.relIndex_ne_zero (hL i).1 (GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK a b i.pl).2)
  rw [hint_ind_le _ _ hle hidx, finprod_congr e2, finprod_inv_distrib] at hp'
  exact inv_inj.1 hp'

theorem vol_eq (ν : Measure (Gf E a b)) [ν.IsHaarMeasure] (V : Subgroup (Gf E a b)) (hVo : IsOpen (V : Set (Gf E a b)))
    (hVc : IsCompact (V : Set (Gf E a b))) (hVK : V ≤ (Kf E a).prod (Kf E b)) :
    (ν.real (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) : ℂ) =
      (ν.real (V : Set (Gf E a b)) : ℂ) * ((V.relIndex ((Kf E a).prod (Kf E b)) : ℕ) : ℂ) := by
  have : BorelSpace (Gf E a b) := ⟨rfl⟩
  have hidx : V.relIndex ((Kf E a).prod (Kf E b)) ≠ 0 := Hint.relIndex_ne_zero hVo isCompact_maximal_pair
  have hI := Hint.int_cosets ν V hVo hVc.measure_lt_top.ne
    ((((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)).indicator 1)
    (hcs_ind ((((Kf E a).prod (Kf E b)) : Subgroup (Gf E a b)).isClosed_of_isOpen isOpen_maximal_pair) isCompact_maximal_pair le_rfl)
    (fun v hv x => Hint.ind_mul _ (hVK hv) x)
  rw [Hint.idx_eq _ V hVK hidx] at hI
  rw [← hI]
  have e : ((((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)).indicator (1 : Gf E a b → ℂ)) =
      (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)).indicator (fun _ => (1 : ℂ)) := rfl
  rw [e, integral_indicator_const _ isOpen_maximal_pair.measurableSet, Complex.real_smul, mul_one]

theorem real_ne (ν : Measure (Gf E a b)) [ν.IsHaarMeasure] (V : Subgroup (Gf E a b)) (hVo : IsOpen (V : Set (Gf E a b)))
    (hVc : IsCompact (V : Set (Gf E a b))) : (ν.real (V : Set (Gf E a b)) : ℂ) ≠ 0 := by
  have hpos := hVo.measure_pos ν ⟨1, V.one_mem⟩
  exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos hpos.ne' hVc.measure_lt_top.ne).ne'

theorem cp_inl (i : Slot S) (g : GL (Fin a) (Af E)) : (i.cp a b ((g, 1) : Gf E a b)).2 = 1 := by
  cases i <;> simp [Slot.cp, atW, thP] <;> rfl

theorem cp_inr (i : Slot S) (h : GL (Fin b) (Af E)) : (i.cp a b ((1, h) : Gf E a b)).1 = 1 := by
  cases i <;> simp [Slot.cp, atW, thP] <;> rfl

theorem cp_split (hm : ∀ (i : Slot S) (x y : Gf E a b), i.cp a b (x * y) = i.cp a b x * i.cp a b y) (i : Slot S) (g : GL (Fin a) (Af E)) (h : GL (Fin b) (Af E)) :
    i.cp a b ((g, h) : Gf E a b) = ((i.cp a b ((g, 1) : Gf E a b)).1, (i.cp a b ((1, h) : Gf E a b)).2) := by
  have e : ((g, h) : Gf E a b) = ((g, 1) : Gf E a b) * ((1, h) : Gf E a b) := by
    rw [Prod.mk_mul_mk, mul_one, one_mul]
  rw [e, hm]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_mul, cp_inr, mul_one]
  · rw [Prod.snd_mul, cp_inl, one_mul]

theorem mem_prod_iff (L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl))
    (hprod : ∀ i, ∃ A B, L i = Subgroup.prod A B) (g : GL (Fin a) (Af E)) (h : GL (Fin b) (Af E)) :
    ((g, h) : Gf E a b) ∈ levelSub hmul L ↔
      ((g, 1) : Gf E a b) ∈ levelSub hmul L ∧ ((1, h) : Gf E a b) ∈ levelSub hmul L := by
  have key : ∀ i, (i.cp a b ((g, h) : Gf E a b) ∈ L i ↔
      i.cp a b ((g, 1) : Gf E a b) ∈ L i ∧ i.cp a b ((1, h) : Gf E a b) ∈ L i) := by
    intro i
    obtain ⟨A, B, e⟩ := hprod i
    rw [e, cp_split hmul i g h]
    simp only [Subgroup.mem_prod, cp_inl, cp_inr, Subgroup.one_mem, and_true, true_and]
  simp only [mem_levelSub, key, forall_and]

end gen

section loc

variable {n : ℕ} (d : LocData E n)

abbrev sL (S : Set (Pl E)) (a : ℕ) : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw (n - a) i.pl) :=
  slL (fun w => d.lev a w) (fun w => d.lev₂ a w)

def lvS (S : Set (Pl E)) (a : ℕ) : Set (Gf E a (n - a)) := {h | ∀ i : Slot S, i.cp a (n - a) h ∈ sL d S a i}

theorem mem_lvS (S : Set (Pl E)) (a : ℕ) (h : Gf E a (n - a)) :
    h ∈ lvS d S a ↔ ∀ w ∈ S, atW w h ∈ d.lev a w ∧ (IsSplitAt w → atW w (thP E a (n - a) h) ∈ d.lev₂ a w) := by
  constructor
  · intro H w hw
    exact ⟨H (Sum.inl ⟨w, hw⟩), fun hs => H (Sum.inr ⟨w, hw, hs⟩)⟩
  · intro H i
    cases i with
    | inl w => exact (H w.1 w.2).1
    | inr w => exact (H w.1 w.2.1).2 w.2.2

theorem levs_out {a : ℕ} {w : Pl E} (hw : w ∉ d.T ∪ d.S₀ ∪ d.Bad) :
    d.lev a w = K2 a (n - a) w ∧ d.lev₂ a w = K2 a (n - a) w := by
  simp only [Finset.mem_union, not_or] at hw
  have h' : w ∉ d.S₀ ∪ d.Bad := by simp [hw.1.2, hw.2]
  exact ⟨by simp only [LocData.lev, if_neg hw.1.1, if_neg h'], by simp only [LocData.lev₂, if_neg h']⟩

theorem lev_spec (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) :
    (IsOpen (d.lev a w : Set (GLw a w × GLw (n - a) w)) ∧ d.lev a w ≤ K2 a (n - a) w) ∧
      ∃ A B, d.lev a w = Subgroup.prod A B := by
  by_cases hT : w ∈ d.T
  · simp only [LocData.lev, if_pos hT]
    exact ⟨⟨LocComm.isOpen_iwahori_pair _ _ _, LocComm.iwahori_pair_le_maximal_pair _ _ _⟩, _, _, rfl⟩
  · by_cases hSB : w ∈ d.S₀ ∪ d.Bad
    · obtain ⟨L₁, L₂, e, h1, h2⟩ := hd.L a ha w hSB
      simp only [LocData.lev, if_neg hT, if_pos hSB, e]
      refine ⟨⟨?_, Subgroup.prod_mono h1.2.1 h2.2.1⟩, _, _, rfl⟩
      rw [Subgroup.coe_prod]; exact h1.1.prod h2.1
    · simp only [LocData.lev, if_neg hT, if_neg hSB]
      exact ⟨⟨(GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK a (n - a) w).1, le_rfl⟩, _, _, rfl⟩

theorem lev₂_spec (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) :
    (IsOpen (d.lev₂ a w : Set (GLw a w × GLw (n - a) w)) ∧ d.lev₂ a w ≤ K2 a (n - a) w) ∧
      ∃ A B, d.lev₂ a w = Subgroup.prod A B := by
  by_cases hSB : w ∈ d.S₀ ∪ d.Bad
  · obtain ⟨L₁, L₂, e, h1, h2⟩ := hd.L a ha w hSB
    simp only [LocData.lev₂, if_pos hSB, e]
    refine ⟨⟨?_, Subgroup.prod_mono h1.2.1 h2.2.1⟩, _, _, rfl⟩
    rw [Subgroup.coe_prod]; exact h1.1.prod h2.1
  · simp only [LocData.lev₂, if_neg hSB]
    exact ⟨⟨(GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK a (n - a) w).1, le_rfl⟩, _, _, rfl⟩

theorem position_spec (hd : d.Ok) {S : Set (Pl E)} {a : ℕ} (ha : a ≤ n) (i : Slot S) :
    (IsOpen (sL d S a i : Set (GLw a i.pl × GLw (n - a) i.pl)) ∧ sL d S a i ≤ K2 a (n - a) i.pl) ∧
      ∃ A B, sL d S a i = Subgroup.prod A B := by
  cases i with
  | inl w => exact lev_spec d hd ha w.1
  | inr w => exact lev₂_spec d hd ha w.1

theorem position_ev {S : Set (Pl E)} (a : ℕ) : ∀ᶠ i : Slot S in cofinite, sL d S a i = K2 a (n - a) i.pl :=
  ev_position (fun w => w ∉ d.T ∪ d.S₀ ∪ d.Bad)
    (Filter.eventually_cofinite.2 ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.subset fun w hw => by
      simp only [Set.mem_ofPred_eq, not_not] at hw; exact Finset.mem_coe.2 hw))
    fun i hi => by
      cases i with
      | inl w => exact (levs_out d hi).1
      | inr w => exact (levs_out d hi).2

theorem main (h2 : HintProd) (h3 : Slots) {S : Set (Pl E)} (a : ℕ) (ha : a ≤ n) (hS : IsSection S) (hd : d.Ok)
    (hPS : (↑d.P : Set (Pl E)) ⊆ S) :
    (∃ G₁ : Subgroup (GL (Fin a) (Af E)),
      (G₁ : Set (GL (Fin a) (Af E))) = {g | ((g, 1) : Gf E a (n - a)) ∈ lvS d S a}) ∧
    (∃ G₂ : Subgroup (GL (Fin (n - a)) (Af E)),
      (G₂ : Set (GL (Fin (n - a)) (Af E))) = {g | ((1, g) : Gf E a (n - a)) ∈ lvS d S a}) ∧
    (IsOpen {g : GL (Fin a) (Af E) | ((g, 1) : Gf E a (n - a)) ∈ lvS d S a} ∧
      IsCompact {g : GL (Fin a) (Af E) | ((g, 1) : Gf E a (n - a)) ∈ lvS d S a}) ∧
    (IsOpen {g : GL (Fin (n - a)) (Af E) | ((1, g) : Gf E a (n - a)) ∈ lvS d S a} ∧
      IsCompact {g : GL (Fin (n - a)) (Af E) | ((1, g) : Gf E a (n - a)) ∈ lvS d S a}) ∧
    (∀ g h, ((g, h) : Gf E a (n - a)) ∈ lvS d S a ↔
      ((g, 1) : Gf E a (n - a)) ∈ lvS d S a ∧ ((1, h) : Gf E a (n - a)) ∈ lvS d S a) ∧
    ∀ (ν : Measure (Gf E a (n - a))), ν.IsHaarMeasure → ((ν.real (lvS d S a) : ℝ) : ℂ) ≠ 0 ∧
      ∀ (x y : ∀ w : d.P, d.kap w) (h : Gf E a (n - a)),
        ((ν.real ((Kf E a).prod (Kf E (n - a)) : Subgroup (Gf E a (n - a))) : ℝ) : ℂ)⁻¹ *
            finFn S ((d.eL a).ent d.P x y) (d.eL a).t h =
          if x = y ∧ h ∈ lvS d S a then ((ν.real (lvS d S a) : ℝ) : ℂ)⁻¹ else 0 := by
  obtain ⟨hmul, hcont, hinj, hsurj, hev, hK, hcpt⟩ := h3 E a (n - a) S hS
  have hspec := position_spec d hd (S := S) ha
  have hLe := position_ev d (S := S) a
  have hL : ∀ i, IsOpen (sL d S a i : Set (GLw a i.pl × GLw (n - a) i.pl)) ∧ sL d S a i ≤ K2 a (n - a) i.pl :=
    fun i => (hspec i).1
  have hprod : ∀ i, ∃ A B, sL d S a i = Subgroup.prod A B := fun i => (hspec i).2
  have eLv : lvS d S a = (levelSub hmul (sL d S a) : Set (Gf E a (n - a))) :=
    Set.ext fun h => (mem_levelSub hmul (sL d S a) h).symm
  have hLvo := isOpen_levelSub hmul hcont hK (sL d S a) hL hLe
  have hLvc : IsCompact (levelSub hmul (sL d S a) : Set (Gf E a (n - a))) := by
    have e : (levelSub hmul (sL d S a) : Set (Gf E a (n - a))) =
        {x | ∀ i : Slot S, i.cp a (n - a) x ∈ (sL d S a i : Set (GLw a i.pl × GLw (n - a) i.pl))} :=
      Set.ext fun x => mem_levelSub hmul (sL d S a) x
    rw [e]
    exact hcpt _ (fun i => isCompact_sub (hL i).1 (hL i).2) (hLe.mono fun i hi => by rw [hi])
  have hle : levelSub hmul (sL d S a) ≤ (Kf E a).prod (Kf E (n - a)) := fun x hx =>
    (hK x).2 fun i => (hL i).2 ((mem_levelSub hmul (sL d S a) x).1 hx i)
  have hpi := mem_prod_iff hmul (sL d S a) hprod
  rw [eLv]
  refine ⟨⟨(levelSub hmul (sL d S a)).comap (MonoidHom.inl _ _), Set.ext fun _ => Iff.rfl⟩,
    ⟨(levelSub hmul (sL d S a)).comap (MonoidHom.inr _ _), Set.ext fun _ => Iff.rfl⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hpi, ?_⟩
  · exact hLvo.preimage (continuous_id.prodMk continuous_const)
  · have e : {g : GL (Fin a) (Af E) | ((g, 1) : Gf E a (n - a)) ∈ (levelSub hmul (sL d S a) : Set (Gf E a (n - a)))} =
        Prod.fst '' (levelSub hmul (sL d S a) : Set (Gf E a (n - a))) := by
      ext g
      constructor
      · intro hg; exact ⟨(g, 1), hg, rfl⟩
      · rintro ⟨⟨g', h⟩, hx, rfl⟩; exact ((hpi g' h).1 hx).1
    rw [e]; exact hLvc.image continuous_fst
  · exact hLvo.preimage (continuous_const.prodMk continuous_id)
  · have e : {g : GL (Fin (n - a)) (Af E) | ((1, g) : Gf E a (n - a)) ∈ (levelSub hmul (sL d S a) : Set (Gf E a (n - a)))} =
        Prod.snd '' (levelSub hmul (sL d S a) : Set (Gf E a (n - a))) := by
      ext g
      constructor
      · intro hg; exact ⟨(1, g), hg, rfl⟩
      · rintro ⟨⟨g', h⟩, hx, rfl⟩; exact ((hpi g' h).1 hx).2
    rw [e]; exact hLvc.image continuous_snd
  intro ν hν
  have hvol := vol_eq ν (levelSub hmul (sL d S a)) hLvo hLvc hle
  have hidx := index_eq hmul h2 hcont hinj hsurj hev hK (sL d S a) hL hLe
  have hidx0 : (levelSub hmul (sL d S a)).relIndex ((Kf E a).prod (Kf E (n - a))) ≠ 0 :=
    Hint.relIndex_ne_zero hLvo isCompact_maximal_pair
  refine ⟨real_ne ν _ hLvo hLvc, fun x y h => ?_⟩
  have hsfI : ∀ i : Slot S, sf (fun w => idem (d.lev a w)) (fun w => idem (d.lev₂ a w)) i =
      (sL d S a i : Set (GLw a i.pl × GLw (n - a) i.pl)).indicator
        (fun _ => (((sL d S a i).relIndex (K2 a (n - a) i.pl) : ℕ) : ℂ)) := by
    intro i; cases i <;> rfl
  have hv1 : ∀ᶠ i in cofinite, sL d S a i = K2 a (n - a) i.pl ∧
      (((sL d S a i).relIndex (K2 a (n - a) i.pl) : ℕ) : ℂ) = 1 :=
    hLe.mono fun i hi => ⟨hi, by rw [hi, Subgroup.relIndex_self, Nat.cast_one]⟩
  have hindI : ∀ᶠ i : Slot S in cofinite, sf (fun w => idem (d.lev a w)) (fun w => idem (d.lev₂ a w)) i =
      (K2 a (n - a) i.pl : Set (GLw a i.pl × GLw (n - a) i.pl)).indicator 1 :=
    hv1.mono fun i hi => by rw [hsfI i, hi.2, hi.1]; rfl
  by_cases hxy : x = y
  · subst hxy
    have eφ : (d.eL a).ent d.P x x = fun w => idem (d.lev a w) := by
      funext w
      unfold LM.ent
      split_ifs
      · simp [LocData.eL, LocData.diag]
      · rfl
    have ef : finFn S ((d.eL a).ent d.P x x) (d.eL a).t h = if h ∈ levelSub hmul (sL d S a) then
        ∏ᶠ i, (((sL d S a i).relIndex (K2 a (n - a) i.pl) : ℕ) : ℂ) else 0 := by
      rw [eφ, show (d.eL a).t = fun w => idem (d.lev₂ a w) from rfl, finFn_eq hev hindI h,
        ← fp_ind hmul hev (sL d S a) _ hv1 h]
      exact finprod_congr fun i => by rw [hsfI i]
    rw [ef, ← hidx]
    by_cases hh : h ∈ levelSub hmul (sL d S a)
    · rw [if_pos hh, if_pos ⟨rfl, hh⟩, hvol, mul_inv, mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hidx0), mul_one]
    · rw [if_neg hh, if_neg (fun h' => hh h'.2), mul_zero]
  · rw [if_neg (fun h' => hxy h'.1)]
    obtain ⟨w, hw⟩ := Function.ne_iff.1 hxy
    have hsame : ∀ i : Slot S, i.pl ∉ d.P → sf ((d.eL a).ent d.P x y) (d.eL a).t i =
        sf (fun w => idem (d.lev a w)) (fun w => idem (d.lev₂ a w)) i := by
      intro i hi
      cases i with
      | inl u =>
        show (d.eL a).ent d.P x y u.1 = idem (d.lev a u.1)
        unfold LM.ent
        rw [dif_neg (show u.1 ∉ d.P from hi)]
        rfl
      | inr u => rfl
    have hPf : ∀ᶠ w in cofinite, w ∉ d.P :=
      Filter.eventually_cofinite.2 (d.P.finite_toSet.subset fun w hw => by simpa using hw)
    have hind : ∀ᶠ i : Slot S in cofinite, sf ((d.eL a).ent d.P x y) (d.eL a).t i =
        (K2 a (n - a) i.pl : Set (GLw a i.pl × GLw (n - a) i.pl)).indicator 1 :=
      ((ev_position _ hPf fun i hi => hi).and hindI).mono fun i hi => (hsame i hi.1).trans hi.2
    rw [finFn_eq hev hind h]
    have h0 : sf ((d.eL a).ent d.P x y) (d.eL a).t (Sum.inl ⟨w.1, hPS w.2⟩)
        (Slot.cp a (n - a) (Sum.inl ⟨w.1, hPS w.2⟩ : Slot S) h) = 0 := by
      show (d.eL a).ent d.P x y w.1 _ = 0
      unfold LM.ent
      rw [dif_pos w.2]
      simp [LocData.eL, LocData.diag, hw]
      rfl
    rw [finprod_eq_zero (fun i : Slot S => sf ((d.eL a).ent d.P x y) (d.eL a).t i (Slot.cp a (n - a) i h))
      (Sum.inl ⟨w.1, hPS w.2⟩) h0 (fin_one hev hind h), mul_zero]

end loc

end Lev6

end PositivityTheory.Rg.BcB.F

end
