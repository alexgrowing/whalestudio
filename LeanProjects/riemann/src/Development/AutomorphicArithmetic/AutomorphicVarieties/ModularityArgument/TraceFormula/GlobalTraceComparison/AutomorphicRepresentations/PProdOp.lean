import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem fin_supp {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hK : IsOpen (K : Set G)) (f : G → ℂ) (hf : IsHecke K f) :
    (Function.support fun c : G ⧸ K => f c.out).Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport f) :=
    hf.1.isCompact.image continuous_quotient_mk'
  refine hc.finite_of_discrete.subset ?_
  intro c hc'
  exact ⟨c.out, subset_tsupport f hc', QuotientGroup.out_eq' c⟩

private theorem lv_ind {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (f : G → ℂ) (hf : ∀ g, f g = if g ∈ K then 1 else 0) (y : V) (hy : y ∈ fixed ρ K) :
    Lv ρ K f y = y := by
  have hout : ((1 : G) : G ⧸ K).out ∈ K := by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K (1 : G)
    rw [hh, one_mul]
    exact h.2
  have hz : ∀ q : G ⧸ K, q ≠ ((1 : G) : G ⧸ K) →
      f q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V)) = 0 := by
    intro q hq
    have hn : q.out ∉ K := by
      intro hm
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact (QuotientGroup.eq.2 (by simpa using hm))
    rw [hf, if_neg hn, zero_smul]
  have hfix : ρ ((1 : G) : G ⧸ K).out y = y := by
    have := hy ⟨_, hout⟩
    simpa using this
  unfold Lv levOp
  rw [Subgroup.relIndex_self, finsum_eq_single _ _ hz, hf, if_pos hout]
  simp [hfix]

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def tm (F : ∀ w : Pl E, Bool → GLw n w → ℂ) (g : GF E n) (w : Pl E) : ℂ :=
  F w false (qw n w false g) * if IsSplitAt w then F w true (qw n w true g) else 1

private theorem mem_lev {S : Set (Pl E)} {N : ∀ w : Pl E, Subgroup (GLw n w)} {g : GF E n} :
    g ∈ Lev S N ↔ ∀ i, Sl S i → qw n i.1 i.2 g ∈ N i.1 := by
  simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]

private theorem tm_unit {S : Set (Pl E)} {N : ∀ w : Pl E, Subgroup (GLw n w)} {I : Finset (Pl E × Bool)}
    {F : ∀ w : Pl E, Bool → GLw n w → ℂ} (hF : Fam S N I F) (g : GF E n) (w : Pl E) (hw : w ∈ S)
    (hI : ∀ b, (w, b) ∉ I) (hq : ∀ b, Sl S (w, b) → qw n w b g ∈ N w) : tm F g w = 1 := by
  have h0 : F w false (qw n w false g) = 1 := by
    have hs : Sl S (w, false) := ⟨hw, by simp⟩
    have e := hF.2 (w, false) hs (hI false)
    dsimp only at e
    rw [e]
    exact Set.indicator_of_mem (hq false hs) _
  by_cases hsp : IsSplitAt w
  · have hs : Sl S (w, true) := ⟨hw, fun _ => hsp⟩
    have e := hF.2 (w, true) hs (hI true)
    dsimp only at e
    have h1 : F w true (qw n w true g) = 1 := by
      rw [e]
      exact Set.indicator_of_mem (hq true hs) _
    simp [tm, h0, h1, hsp]
  · simp [tm, h0, hsp]

private theorem exP {S : Set (Pl E)} {Z : Finset (Pl E)} {N : ∀ w : Pl E, Subgroup (GLw n w)}
    {I : Finset (Pl E × Bool)} {F : ∀ w : Pl E, Bool → GLw n w → ℂ}
    (hb : ∀ g : GF E n, {i : Pl E × Bool | qw n i.1 i.2 g ∉ KGL i.1 n}.Finite)
    (hG : Good Z N) (hF : Fam S N I F) (g : GF E n) :
    ∃ P : Finset (Pl E), ∀ w ∈ S, w ∉ P → tm F g w = 1 := by
  refine ⟨Z ∪ I.image Prod.fst ∪ (hb g).toFinset.image Prod.fst, ?_⟩
  intro w hS hP
  have hZ : w ∉ Z := fun h => hP (by simp [h])
  have hI : ∀ b, (w, b) ∉ I := fun b h => hP (Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨(w, b), h, rfl⟩)))
  have hB : ∀ b, qw n w b g ∈ KGL w n := by
    intro b
    by_contra hc
    exact hP (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(w, b), by simpa using hc, rfl⟩))
  refine tm_unit hF g w hS hI fun b _ => ?_
  rw [(hG w).2.2.2 hZ]
  exact hB b

private theorem pf_eq {S : Set (Pl E)} {F : ∀ w : Pl E, Bool → GLw n w → ℂ} {g : GF E n}
    (P : Finset (Pl E)) (hP : ∀ w ∈ S, w ∉ P → tm F g w = 1) :
    pf S F g = ∏ w ∈ P.filter (· ∈ S), tm F g w := by
  refine finprod_mem_eq_prod_of_inter_mulSupport_eq (tm F g) ?_
  ext w
  simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.coe_filter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by_contra fun h => h2 (hP w h1 h), h1⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨h1, h2⟩

private theorem tm_zero {S : Set (Pl E)} {F : ∀ w : Pl E, Bool → GLw n w → ℂ} {g : GF E n}
    {i : Pl E × Bool} (hi : Sl S i) (h0 : F i.1 i.2 (qw n i.1 i.2 g) = 0) : tm F g i.1 = 0 := by
  obtain ⟨w, b⟩ := i
  cases b with
  | false =>
    dsimp only at h0 ⊢
    simp [tm, h0]
  | true =>
    have hs : IsSplitAt w := hi.2 rfl
    dsimp only at h0 ⊢
    simp [tm, h0, hs]

private theorem pf_zero {S : Set (Pl E)} {F : ∀ w : Pl E, Bool → GLw n w → ℂ} {g : GF E n}
    {P : Finset (Pl E)} (hP : ∀ w ∈ S, w ∉ P → tm F g w = 1) {i : Pl E × Bool} (hi : Sl S i)
    (h0 : F i.1 i.2 (qw n i.1 i.2 g) = 0) : pf S F g = 0 := by
  rw [pf_eq (insert i.1 P) fun w hw h => hP w hw fun h' => h (Finset.mem_insert_of_mem h')]
  exact Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hi.1⟩) (tm_zero hi h0)

private def rs (N : ∀ w : Pl E, Subgroup (GLw n w)) (F : ∀ w : Pl E, Bool → GLw n w → ℂ)
    (i : Pl E × Bool) : ∀ w : Pl E, Bool → GLw n w → ℂ :=
  fun w b => if (w, b) = i then (N w : Set (GLw n w)).indicator 1 else F w b

private theorem rs_same (N : ∀ w : Pl E, Subgroup (GLw n w)) (F : ∀ w : Pl E, Bool → GLw n w → ℂ)
    (w : Pl E) (b : Bool) : rs N F (w, b) w b = (N w : Set (GLw n w)).indicator 1 := by
  simp [rs]

private theorem rs_ne (N : ∀ w : Pl E, Subgroup (GLw n w)) (F : ∀ w : Pl E, Bool → GLw n w → ℂ)
    {i : Pl E × Bool} {w : Pl E} {b : Bool} (h : (w, b) ≠ i) : rs N F i w b = F w b := by
  simp [rs, h]

private theorem fam_rs {S : Set (Pl E)} {N : ∀ w : Pl E, Subgroup (GLw n w)} {L : List (Pl E × Bool)}
    {i : Pl E × Bool} {F : ∀ w : Pl E, Bool → GLw n w → ℂ} (hi : i ∉ L)
    (hF : Fam S N (i :: L).toFinset F) : Fam S N L.toFinset (rs N F i) := by
  constructor
  · rintro ⟨w, b⟩ hk
    have hk' : (w, b) ∈ L := List.mem_toFinset.1 hk
    have hne : (w, b) ≠ i := fun h => hi (h ▸ hk')
    have h := hF.1 (w, b) (List.mem_toFinset.2 (List.mem_cons_of_mem _ hk'))
    dsimp only
    rw [rs_ne N F hne]
    exact h
  · rintro ⟨w, b⟩ hk hkL
    dsimp only
    by_cases h : (w, b) = i
    · subst h
      exact rs_same N F w b
    · rw [rs_ne N F h]
      refine hF.2 (w, b) hk fun hm => ?_
      rcases List.mem_cons.1 (List.mem_toFinset.1 hm) with h' | h'
      · exact h h'
      · exact hkL (List.mem_toFinset.2 h')

private theorem tm_other {S : Set (Pl E)} (N : ∀ w : Pl E, Subgroup (GLw n w))
    (F : ∀ w : Pl E, Bool → GLw n w → ℂ)
    (hind : ∀ i k, Sl S i → Sl S k → i ≠ k → ∀ a, qw n k.1 k.2 (jw n i.1 i.2 a) = 1)
    {i : Pl E × Bool} (hi : Sl S i) (a : GLw n i.1) (g : GF E n) {w : Pl E} (hw : w ∈ S) (hne : w ≠ i.1) :
    tm (rs N F i) (jw n i.1 i.2 a * g) w = tm F g w := by
  have hq : ∀ b, Sl S (w, b) → qw n w b (jw n i.1 i.2 a * g) = qw n w b g := by
    intro b hs
    have hk : i ≠ (w, b) := fun h => hne (by rw [h])
    have := hind i (w, b) hi hs hk a
    dsimp only at this
    rw [map_mul, this, one_mul]
  have hr : ∀ b, rs N F i w b = F w b := fun b => rs_ne N F fun h => hne (by rw [← h])
  have h0 := hq false ⟨hw, by simp⟩
  by_cases hsp : IsSplitAt w
  · have h1 := hq true ⟨hw, fun _ => hsp⟩
    simp only [tm, hr, h0, h1]
  · simp only [tm, hr, h0, hsp, if_false]

private theorem tm_self {S : Set (Pl E)} (N : ∀ w : Pl E, Subgroup (GLw n w))
    (F : ∀ w : Pl E, Bool → GLw n w → ℂ)
    (hq : ∀ (w : Pl E) (b : Bool) (a : GLw n w), qw n w b (jw n w b a) = a)
    (hind : ∀ i k, Sl S i → Sl S k → i ≠ k → ∀ a, qw n k.1 k.2 (jw n i.1 i.2 a) = 1)
    {i : Pl E × Bool} (hi : Sl S i) (g : GF E n) :
    tm F g i.1 = F i.1 i.2 (qw n i.1 i.2 g) *
      tm (rs N F i) ((jw n i.1 i.2 (qw n i.1 i.2 g))⁻¹ * g) i.1 := by
  obtain ⟨w, b⟩ := i
  dsimp only at hi ⊢
  set g' := (jw n w b (qw n w b g))⁻¹ * g with hg'
  have hself : qw n w b g' = 1 := by
    rw [hg', map_mul, map_inv, hq, inv_mul_cancel]
  have hind1 : (rs N F (w, b) w b) (qw n w b g') = 1 := by
    rw [rs_same, hself]
    exact Set.indicator_of_mem (one_mem (N w)) _
  have hoth : Sl S (w, !b) → qw n w (!b) g' = qw n w (!b) g := by
    intro hs
    have hk : (w, b) ≠ (w, !b) := by simp
    have := hind (w, b) (w, !b) hi hs hk (qw n w b g)⁻¹
    dsimp only at this
    rw [hg', ← map_inv, map_mul, this, one_mul]
  have hr : rs N F (w, b) w (!b) = F w (!b) := rs_ne N F (by simp)
  cases b with
  | false =>
    by_cases hsp : IsSplitAt w
    · have h1 := hoth ⟨hi.1, fun _ => hsp⟩
      simp only [Bool.not_false] at h1 hr
      simp only [tm, hind1, hsp, if_true, h1, hr, one_mul]
    · simp only [tm, hind1, hsp, if_false, one_mul]
  | true =>
    have hsp : IsSplitAt w := hi.2 rfl
    have h1 := hoth ⟨hi.1, by simp⟩
    simp only [Bool.not_true] at h1 hr
    simp only [tm, hind1, hsp, if_true, h1, hr, mul_one]
    exact mul_comm _ _

private theorem pf_step {S : Set (Pl E)} (N : ∀ w : Pl E, Subgroup (GLw n w))
    (F : ∀ w : Pl E, Bool → GLw n w → ℂ)
    (hq : ∀ (w : Pl E) (b : Bool) (a : GLw n w), qw n w b (jw n w b a) = a)
    (hind : ∀ i k, Sl S i → Sl S k → i ≠ k → ∀ a, qw n k.1 k.2 (jw n i.1 i.2 a) = 1)
    {i : Pl E × Bool} (hi : Sl S i) (g : GF E n) (P : Finset (Pl E))
    (hP : ∀ w ∈ S, w ∉ P → tm F g w = 1)
    (hP' : ∀ w ∈ S, w ∉ P → tm (rs N F i) ((jw n i.1 i.2 (qw n i.1 i.2 g))⁻¹ * g) w = 1) :
    pf S F g = F i.1 i.2 (qw n i.1 i.2 g) * pf S (rs N F i) ((jw n i.1 i.2 (qw n i.1 i.2 g))⁻¹ * g) := by
  have hmem : i.1 ∈ (insert i.1 P).filter (· ∈ S) :=
    Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hi.1⟩
  rw [pf_eq (insert i.1 P) fun w hw h => hP w hw fun h' => h (Finset.mem_insert_of_mem h'),
    pf_eq (insert i.1 P) fun w hw h => hP' w hw fun h' => h (Finset.mem_insert_of_mem h'),
    ← Finset.mul_prod_erase _ (tm F g) hmem,
    ← Finset.mul_prod_erase _ (tm (rs N F i) ((jw n i.1 i.2 (qw n i.1 i.2 g))⁻¹ * g)) hmem,
    tm_self N F hq hind hi g, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun w hw => ?_
  have hw' := Finset.mem_erase.1 hw
  have := tm_other N F hind hi (qw n i.1 i.2 g)⁻¹ g (Finset.mem_filter.1 hw'.2).2 hw'.1
  rw [map_inv] at this
  exact this.symm

private theorem prod_list (hS : SlotBasic) (hT : LevTop) (hA : AbsStep) (hH : PfHecke)
    {S : Set (Pl E)} {Z : Finset (Pl E)} {N : ∀ w : Pl E, Subgroup (GLw n w)}
    (hsec : IsSection S) (hspl : SplitIn S Z) (hG : Good Z N) (L : List (Pl E × Bool)) :
    L.Nodup → ∀ F, Fam S N L.toFinset F → ∀ y ∈ fixed (finRep E n) (Lev S N),
      Lv (finRep E n) (Lev S N) (pf S F) y = (L.map fun i => Lw N i.1 i.2 (F i.1 i.2)).prod y := by
  obtain ⟨-, -, hloc, hind, hb, -, -⟩ := hS E n S hsec
  have hq : ∀ w b a, qw n w b (jw n w b a) = a := fun w b => (hloc w b).2.2.1
  induction L with
  | nil =>
    intro _ F hF y hy
    refine lv_ind _ _ _ (fun g => ?_) y hy
    obtain ⟨P, hP⟩ := exP hb hG hF g
    by_cases hg : g ∈ Lev S N
    · rw [if_pos hg, pf_eq P hP]
      refine Finset.prod_eq_one fun w hw => ?_
      exact tm_unit hF g w (Finset.mem_filter.1 hw).2 (by simp) fun b hs => mem_lev.1 hg (w, b) hs
    · rw [if_neg hg]
      obtain ⟨i, hi, hn⟩ : ∃ i, Sl S i ∧ qw n i.1 i.2 g ∉ N i.1 := by
        by_contra hc
        push_neg at hc
        exact hg (mem_lev.2 hc)
      refine pf_zero hP hi ?_
      rw [hF.2 i hi (by simp)]
      exact Set.indicator_of_notMem hn _
  | cons i L ih =>
    intro hnd F hF y hy
    have hi : i ∉ L := (List.nodup_cons.1 hnd).1
    have hL := (List.nodup_cons.1 hnd).2
    obtain ⟨hsl, hHk⟩ := hF.1 i (by simp)
    have hF' := fam_rs hi hF
    have hK' : IsHecke (Lev S N) (pf S (rs N F i)) := hH E n S Z N hsec hspl hG _ _ hF'
    have hopen : IsOpen (Lev S N : Set (GF E n)) := (hT E n S Z N hsec hspl hG).1
    have e := hA (GF E n) (GLw n i.1) (Sm E n) (finRep E n) (Lev S N) (N i.1) (jw n i.1 i.2) (qw n i.1 i.2)
      (F i.1 i.2) (pf S F) (pf S (rs N F i)) (hq _ _) (hloc _ _).2.2.2
      (fun a ha => mem_lev.2 fun k hk => by
        by_cases hki : i = k
        · subst hki
          rw [hq]
          exact ha
        · rw [hind i k hsl hk hki a]
          exact one_mem _)
      (fun k hk => mem_lev.1 hk i hsl)
      (fun g => by
        obtain ⟨P, hP⟩ := exP hb hG hF g
        obtain ⟨P', hP'⟩ := exP hb hG hF' ((jw n i.1 i.2 (qw n i.1 i.2 g))⁻¹ * g)
        exact pf_step N F hq hind hsl g (P ∪ P')
          (fun w hw h => hP w hw fun h' => h (Finset.mem_union_left _ h'))
          (fun w hw h => hP' w hw fun h' => h (Finset.mem_union_right _ h')))
      (fun g hg => by
        by_contra hn
        obtain ⟨P, hP⟩ := exP hb hG hF' g
        refine hg (pf_zero hP hsl ?_)
        obtain ⟨w, b⟩ := i
        dsimp only at hn ⊢
        rw [rs_same]
        exact Set.indicator_of_notMem hn _)
      (fun k hk g => hK'.2 k hk g)
      (fun a ha x => (hHk.2 a ha x).2)
      (fin_supp _ (hG i.1).1 _ hHk) (fin_supp _ hopen _ hK') y hy
    rw [e, ih hL _ hF' y hy]
    have hm : (L.map fun k => Lw N k.1 k.2 (rs N F i k.1 k.2)) = L.map fun k => Lw N k.1 k.2 (F k.1 k.2) :=
      List.map_congr_left fun k hk => by
        have hne : (k.1, k.2) ≠ i := fun h => hi (by rw [← h]; exact hk)
        rw [rs_ne N F hne]
    rw [hm]
    rfl

end

theorem prodOp_pf : SlotBasic → LevTop → AbsStep → PfHecke → ProdOp := by
  intro hS hT hA hH E _ _ _ n S Z N hsec hspl hG I F hF y hy
  exact prod_list hS hT hA hH hsec hspl hG I.toList (Finset.nodup_toList I) F
    (by rwa [Finset.toList_toFinset]) y hy

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
