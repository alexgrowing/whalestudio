import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open NumberField IsDedekindDomain Matrix Filter GlobalTheory.BCT GlobalTheory.LFun GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.two_block_test_function_reduce

private def dcs {H : Type} [Group H] (N : Subgroup H) (q : H) : Set H := {x | ∃ a ∈ N, ∃ b ∈ N, x = a * q * b}

private theorem dcs_self {H : Type} [Group H] (N : Subgroup H) (q : H) : q ∈ dcs N q :=
  ⟨1, N.one_mem, 1, N.one_mem, by simp⟩

private theorem dcs_left {H : Type} [Group H] {N : Subgroup H} {q k x : H} (hk : k ∈ N) :
    k * x ∈ dcs N q ↔ x ∈ dcs N q := by
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    exact ⟨k⁻¹ * a, N.mul_mem (N.inv_mem hk) ha, b, hb, by
      have h1 : x = k⁻¹ * (k * x) := by simp
      rw [h1, e]; simp [mul_assoc]⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨k * a, N.mul_mem hk ha, b, hb, by simp [mul_assoc]⟩

private theorem dcs_right {H : Type} [Group H] {N : Subgroup H} {q k x : H} (hk : k ∈ N) :
    x * k ∈ dcs N q ↔ x ∈ dcs N q := by
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    exact ⟨a, ha, b * k⁻¹, N.mul_mem hb (N.inv_mem hk), by rw [← mul_assoc, ← e]; simp⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b * k, N.mul_mem hb hk, by simp [mul_assoc]⟩

private theorem dcs_eq_of_mem {H : Type} [Group H] {N : Subgroup H} {q : H} (hq : q ∈ N) :
    dcs N q = (N : Set H) := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact N.mul_mem (N.mul_mem ha hq) hb
  · intro hx
    exact ⟨x * q⁻¹, N.mul_mem hx (N.inv_mem hq), 1, N.one_mem, by simp⟩

private theorem ind_inv {H : Type} [Group H] {N : Subgroup H} (q : H) {k : H} (hk : k ∈ N) (x : H) :
    (dcs N q).indicator (1 : H → ℂ) (k * x) = (dcs N q).indicator 1 x ∧
      (dcs N q).indicator (1 : H → ℂ) (x * k) = (dcs N q).indicator 1 x := by
  constructor
  · by_cases h : x ∈ dcs N q
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((dcs_left hk).2 h)]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((dcs_left hk).1 h'))]
  · by_cases h : x ∈ dcs N q
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((dcs_right hk).2 h)]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((dcs_right hk).1 h'))]

private theorem dcs_hecke {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {N : Subgroup H}
    (hc : IsCompact (N : Set H)) (q : H) : IsHecke N ((dcs N q).indicator (1 : H → ℂ)) := by
  refine ⟨?_, fun k hk x => ind_inv q hk x⟩
  have hcomp : IsCompact (dcs N q) := by
    have : dcs N q = (fun p : H × H => p.1 * q * p.2) '' ((N : Set H) ×ˢ (N : Set H)) := by
      ext x
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
    rw [this]
    exact (hc.prod hc).image (by fun_prop)
  exact HasCompactSupport.intro hcomp fun x hx => Set.indicator_of_notMem hx _

section Abs

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)

private def cs (f : G → ℂ) : Set (G ⧸ K) := {q | f q.out ≠ 0}

private theorem Lv_eq (f : G → ℂ) : Lv ρ K f = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out := by
  simp [Lv, levOp, Subgroup.relIndex_self]

private theorem cs_finite [TopologicalSpace G] [IsTopologicalGroup G] (hK : IsOpen (K : Set G)) {f : G → ℂ}
    (hf : HasCompactSupport f) : (cs K f).Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have h1 : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport f) :=
    IsCompact.image hf QuotientGroup.continuous_mk
  refine h1.finite_of_discrete.subset fun q hq => ?_
  exact ⟨q.out, subset_tsupport f hq, QuotientGroup.out_eq' q⟩

private theorem Lv_add {f f' : G → ℂ} (c : ℂ) (h1 : (cs K f).Finite) (h2 : (cs K f').Finite) :
    Lv ρ K (fun x => f x + c * f' x) = Lv ρ K f + c • Lv ρ K f' := by
  have s1 : (Function.support fun q : G ⧸ K => f q.out • ρ q.out).Finite :=
    h1.subset fun q hq h0 => hq (by simp [show f q.out = 0 from by simpa [cs] using h0])
  have s2 : (Function.support fun q : G ⧸ K => f' q.out • ρ q.out).Finite :=
    h2.subset fun q hq h0 => hq (by simp [show f' q.out = 0 from by simpa [cs] using h0])
  have s3 : (Function.support fun q : G ⧸ K => c • (f' q.out • ρ q.out)).Finite :=
    s2.subset fun q hq h0 => hq (by simp [show f' q.out • ρ q.out = 0 from h0])
  rw [Lv_eq, Lv_eq, Lv_eq, smul_finsum' c s2, ← finsum_add_distrib s1 s3]
  refine finsum_congr fun q => ?_
  rw [add_smul, mul_smul]

end Abs

section Gen

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)

private theorem gen_ind [TopologicalSpace G] [IsTopologicalGroup G] (hK : IsOpen (K : Set G)) (Wm : Submodule ℂ V)
    (Hg : ∀ g, IsHecke K ((dcs K g).indicator (1 : G → ℂ)) ∧
      ∀ y ∈ Wm, Lv ρ K ((dcs K g).indicator (1 : G → ℂ)) y ∈ Wm) :
    ∀ m : ℕ, ∀ h : G → ℂ, (∀ k ∈ K, ∀ x, h (k * x) = h x ∧ h (x * k) = h x) → (cs K h).Finite →
      (cs K h).ncard = m → ∀ y ∈ Wm, Lv ρ K h y ∈ Wm := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro h hinv hfin hm y hy
  by_cases hemp : cs K h = ∅
  · have h0 : Lv ρ K h = 0 := by
      rw [Lv_eq]
      apply finsum_eq_zero_of_forall_eq_zero
      intro q
      have h1 : h q.out = 0 := by
        by_contra h0
        exact (Set.eq_empty_iff_forall_notMem.1 hemp q) h0
      simp [h1]
    rw [h0]
    exact Wm.zero_mem
  · obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.2 hemp
    obtain ⟨g, hg⟩ : ∃ g, g = q.out := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, c = h g := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e, e = (dcs K g).indicator (1 : G → ℂ) := ⟨_, rfl⟩
    have hconst : ∀ x ∈ dcs K g, h x = c := by
      rintro x ⟨a, ha, b, hb, rfl⟩
      rw [(hinv b hb _).2, (hinv a ha _).1, hc]
    have he1 : ∀ x ∈ dcs K g, e x = 1 := fun x hx => by rw [he, Set.indicator_of_mem hx]; rfl
    have he0 : ∀ x, x ∉ dcs K g → e x = 0 := fun x hx => by rw [he, Set.indicator_of_notMem hx]
    have hcs : (cs K e).Finite := by
      rw [he]
      exact cs_finite K hK (Hg g).1.1
    let h' : G → ℂ := fun x => h x + (-c) * e x
    have hsub : cs K h' ⊆ cs K h := by
      intro q' hq' h0
      refine hq' ?_
      have hn : q'.out ∉ dcs K g := fun hx => by
        have := hconst _ hx
        have hc0 : c ≠ 0 := by rw [hc, hg]; exact hq
        exact hc0 (this.symm.trans h0)
      simp [h', h0, he0 _ hn]
    have hq' : q ∉ cs K h' := by
      intro h0
      refine h0 ?_
      rw [← hg]
      simp only [h']
      rw [he1 g (dcs_self K g), ← hc]
      ring
    have hfin' : (cs K h').Finite := hfin.subset hsub
    have hlt : (cs K h').ncard < m := by
      rw [← hm]
      exact Set.ncard_lt_ncard ⟨hsub, fun hh => hq' (hh hq)⟩ hfin
    have hinv' : ∀ k ∈ K, ∀ x, h' (k * x) = h' x ∧ h' (x * k) = h' x := by
      intro k hk x
      have h2 := ind_inv (N := K) g hk x
      rw [← he] at h2
      simp only [h']
      rw [(hinv k hk x).1, (hinv k hk x).2, h2.1, h2.2]
      exact ⟨rfl, rfl⟩
    have hsplit : h = fun x => h' x + c * e x := by
      funext x
      simp [h']
    rw [hsplit, Lv_add ρ K c hfin' hcs]
    refine Wm.add_mem (ih _ hlt h' hinv' hfin' rfl y hy) (Wm.smul_mem c ?_)
    rw [he]
    exact (Hg g).2 y hy

private theorem gen_abs [TopologicalSpace G] [IsTopologicalGroup G] (hK : IsOpen (K : Set G)) (Wm : Submodule ℂ V)
    (Hg : ∀ g, IsHecke K ((dcs K g).indicator (1 : G → ℂ)) ∧
      ∀ y ∈ Wm, Lv ρ K ((dcs K g).indicator (1 : G → ℂ)) y ∈ Wm) {h : G → ℂ} (hh : IsHecke K h) :
    ∀ y ∈ Wm, Lv ρ K h y ∈ Wm :=
  gen_ind ρ K hK Wm Hg _ h hh.2 (cs_finite K hK hh.1) rfl

end Gen

section Slots

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem mem_Lev {S : Set (Pl E)} {M : ∀ w : Pl E, Subgroup (GLw n w)} {x : GF E n} :
    x ∈ Lev S M ↔ ∀ i : Pl E × Bool, Sl S i → qw n i.1 i.2 x ∈ M i.1 := by
  simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]

private theorem exists_elt {S : Set (Pl E)}
    (hqj : ∀ (w : Pl E) b a, qw n w b (jw n w b a) = a)
    (hsep : ∀ i k, Sl S i → Sl S k → i ≠ k → ∀ a, qw n k.1 k.2 (jw n i.1 i.2 a) = 1)
    (A : ∀ i : Pl E × Bool, GLw n i.1) (J : Finset (Pl E × Bool)) (hJ : ∀ i ∈ J, Sl S i) :
    ∃ c : GF E n, ∀ k, Sl S k → qw n k.1 k.2 c = if k ∈ J then A k else 1 := by
  induction J using Finset.induction_on with
  | empty => exact ⟨1, fun k _ => by simp⟩
  | insert i J hi ih =>
    obtain ⟨c, hc⟩ := ih fun k hk => hJ k (Finset.mem_insert_of_mem hk)
    have hSi := hJ i (Finset.mem_insert_self i J)
    refine ⟨jw n i.1 i.2 (A i) * c, fun k hk => ?_⟩
    rw [map_mul, hc k hk]
    by_cases hki : k = i
    · subst hki
      simp [hi, hqj]
    · rw [hsep i k hSi hk (Ne.symm hki)]
      simp [hki]

private theorem mem_dcs_of_positions {S : Set (Pl E)} {N : ∀ w : Pl E, Subgroup (GLw n w)}
    (hqj : ∀ (w : Pl E) b a, qw n w b (jw n w b a) = a)
    (hsep : ∀ i k, Sl S i → Sl S k → i ≠ k → ∀ a, qw n k.1 k.2 (jw n i.1 i.2 a) = 1)
    (g x : GF E n) (hx : ∀ i : Pl E × Bool, Sl S i → qw n i.1 i.2 x ∈ dcs (N i.1) (qw n i.1 i.2 g))
    (hfin : {i : Pl E × Bool | Sl S i ∧ (qw n i.1 i.2 x ∉ N i.1 ∨ qw n i.1 i.2 g ∉ N i.1)}.Finite) :
    x ∈ dcs (Lev S N) g := by
  have hch : ∀ i : Pl E × Bool, ∃ a b : GLw n i.1, Sl S i → a ∈ N i.1 ∧ b ∈ N i.1 ∧
      qw n i.1 i.2 x = a * qw n i.1 i.2 g * b := by
    intro i
    by_cases hi : Sl S i
    · obtain ⟨a, ha, b, hb, e⟩ := hx i hi
      exact ⟨a, b, fun _ => ⟨ha, hb, e⟩⟩
    · exact ⟨1, 1, fun h => absurd h hi⟩
  choose A B hAB using hch
  have hJ : ∀ i ∈ hfin.toFinset, Sl S i := fun i hi => ((hfin.mem_toFinset).1 hi).1
  obtain ⟨c, hc⟩ := exists_elt hqj hsep A hfin.toFinset hJ
  obtain ⟨d, hd⟩ := exists_elt hqj hsep B hfin.toFinset hJ
  have hcL : c ∈ Lev S N := mem_Lev.2 fun i hi => by
    rw [hc i hi]
    split_ifs
    · exact (hAB i hi).1
    · exact (N i.1).one_mem
  have hdL : d ∈ Lev S N := mem_Lev.2 fun i hi => by
    rw [hd i hi]
    split_ifs
    · exact (hAB i hi).2.1
    · exact (N i.1).one_mem
  have hkL : g⁻¹ * c⁻¹ * x * d⁻¹ ∈ Lev S N := mem_Lev.2 fun i hi => by
    simp only [map_mul, map_inv]
    rw [hc i hi, hd i hi]
    by_cases hiJ : i ∈ hfin.toFinset
    · rw [if_pos hiJ, if_pos hiJ, (hAB i hi).2.2]
      simp [mul_assoc, (N i.1).one_mem]
    · rw [if_neg hiJ, if_neg hiJ]
      have hn : ¬ (qw n i.1 i.2 x ∉ N i.1 ∨ qw n i.1 i.2 g ∉ N i.1) := fun h =>
        hiJ ((hfin.mem_toFinset).2 ⟨hi, h⟩)
      push_neg at hn
      simpa using (N i.1).mul_mem ((N i.1).inv_mem hn.2) hn.1
  exact ⟨c, hcL, (g⁻¹ * c⁻¹ * x * d⁻¹) * d, (Lev S N).mul_mem hkL hdL, by simp [mul_assoc]⟩

private theorem bad_finite {Z : Finset (Pl E)} {S : Set (Pl E)} {N : ∀ w : Pl E, Subgroup (GLw n w)} (hG : Good Z N)
    (hbad : ∀ g : GF E n, {i : Pl E × Bool | qw n i.1 i.2 g ∉ KGL i.1 n}.Finite) (x g : GF E n) :
    {i : Pl E × Bool | Sl S i ∧ (qw n i.1 i.2 x ∉ N i.1 ∨ qw n i.1 i.2 g ∉ N i.1)}.Finite := by
  refine (((Z.finite_toSet).prod (Set.finite_univ (α := Bool))).union ((hbad x).union (hbad g))).subset ?_
  rintro i ⟨-, hi⟩
  by_cases hz : i.1 ∈ Z
  · exact Or.inl ⟨hz, trivial⟩
  · rw [(hG i.1).2.2.2 hz] at hi
    exact Or.inr hi

private theorem pf_eq {Z : Finset (Pl E)} {S : Set (Pl E)} {N : ∀ w : Pl E, Subgroup (GLw n w)} (hG : Good Z N)
    (hqj : ∀ (w : Pl E) b a, qw n w b (jw n w b a) = a)
    (hsep : ∀ i k, Sl S i → Sl S k → i ≠ k → ∀ a, qw n k.1 k.2 (jw n i.1 i.2 a) = 1)
    (hbad : ∀ g : GF E n, {i : Pl E × Bool | qw n i.1 i.2 g ∉ KGL i.1 n}.Finite) (g : GF E n) :
    pf S (fun w b => (dcs (N w) (qw n w b g)).indicator (1 : GLw n w → ℂ)) =
      (dcs (Lev S N) g).indicator (1 : GF E n → ℂ) := by
  funext x
  by_cases hx : x ∈ dcs (Lev S N) g
  · rw [Set.indicator_of_mem hx]
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have hs : ∀ i : Pl E × Bool, Sl S i → qw n i.1 i.2 (a * g * b) ∈ dcs (N i.1) (qw n i.1 i.2 g) :=
      fun i hi => ⟨_, mem_Lev.1 ha i hi, _, mem_Lev.1 hb i hi, by simp⟩
    unfold pf
    refine finprod_mem_of_eqOn_one fun w hw => ?_
    have h1 := hs (w, false) ⟨hw, by simp⟩
    simp only [Pi.one_apply]
    rw [Set.indicator_of_mem h1]
    split_ifs with hsp
    · rw [Set.indicator_of_mem (hs (w, true) ⟨hw, fun _ => hsp⟩)]
      simp
    · simp
  · rw [Set.indicator_of_notMem hx]
    obtain ⟨i, hi, hix⟩ : ∃ i : Pl E × Bool, Sl S i ∧ qw n i.1 i.2 x ∉ dcs (N i.1) (qw n i.1 i.2 g) := by
      by_contra hn
      push_neg at hn
      exact hx (mem_dcs_of_positions hqj hsep g x hn (bad_finite hG hbad x g))
    unfold pf
    rw [finprod_mem_def]
    refine finprod_eq_zero _ i.1 ?_ ?_
    · rw [Set.mulIndicator_of_mem hi.1]
      obtain ⟨w, b⟩ := i
      cases b with
      | false =>
        simp only at hix
        simp only
        rw [Set.indicator_of_notMem hix, zero_mul]
      | true =>
        have hsp : GlobalTheory.UnitaryBC.IsSplitAt w := hi.2 rfl
        simp only at hix
        simp only
        rw [if_pos hsp, Set.indicator_of_notMem hix, mul_zero]
    · refine ((Z.finite_toSet).union
        (((hbad x).union (hbad g)).image fun i : Pl E × Bool => i.1)).subset ?_
      intro w hw
      by_contra hT
      refine hw ?_
      have hwZ : w ∉ Z := fun h => hT (Or.inl h)
      have hK : ∀ b, qw n w b x ∈ N w ∧ qw n w b g ∈ N w := by
        intro b
        rw [(hG w).2.2.2 hwZ]
        constructor
        · by_contra h
          exact hT (Or.inr ⟨(w, b), Or.inl h, rfl⟩)
        · by_contra h
          exact hT (Or.inr ⟨(w, b), Or.inr h, rfl⟩)
      by_cases hwS : w ∈ S
      · rw [Set.mulIndicator_of_mem hwS]
        have hv : ∀ b, (dcs (N w) (qw n w b g)).indicator (1 : GLw n w → ℂ) (qw n w b x) = 1 := by
          intro b
          rw [dcs_eq_of_mem (hK b).2, Set.indicator_of_mem (hK b).1]
          rfl
        simp only [hv]
        simp
      · rw [Set.mulIndicator_of_notMem hwS]

private theorem list_mem {V : Type} [AddCommGroup V] [Module ℂ V] (Wm : Submodule ℂ V) (L : List (Module.End ℂ V))
    (hL : ∀ T ∈ L, ∀ y ∈ Wm, T y ∈ Wm) : ∀ y ∈ Wm, L.prod y ∈ Wm := by
  induction L with
  | nil => intro y hy; simpa using hy
  | cons T L ih =>
    intro y hy
    rw [List.prod_cons, Module.End.mul_apply]
    exact hL T (by simp) _ (ih (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) y hy)

end Slots

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.two_block_test_function_reduce

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.two_block_test_function_reduce in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.genLoc_pf :
    SlotBasic → LevTop → PfHecke → ProdOp → GenLoc := by
  intro hS hT hP hO E _ _ _ n S Z N hSec hZ hG W hW hloc h hh y hy
  obtain ⟨-, -, hl, hsep, hbad, -, -⟩ := hS E n S hSec
  obtain ⟨hop, hcp, -, -⟩ := hT E n S Z N hSec hZ hG
  have hqj : ∀ (w : Pl E) b a, qw n w b (jw n w b a) = a := fun w b a => (hl w b).2.2.1 a
  have hNc : ∀ i : Pl E × Bool, Sl S i → IsCompact (N i.1 : Set (GLw n i.1)) := by
    intro i hi
    have hset : (N i.1 : Set (GLw n i.1)) = qw n i.1 i.2 '' (Lev S N : Set (GF E n)) := by
      ext a
      constructor
      · intro ha
        refine ⟨jw n i.1 i.2 a, mem_Lev.2 fun k hk => ?_, hqj _ _ a⟩
        by_cases hki : k = i
        · subst hki
          rw [hqj]
          exact ha
        · rw [hsep i k hi hk (Ne.symm hki)]
          exact (N k.1).one_mem
      · rintro ⟨k, hk, rfl⟩
        exact mem_Lev.1 hk i hi
    rw [hset]
    exact hcp.image (hl i.1 i.2).2.1
  refine gen_abs (finRep E n) (Lev S N) hop W (fun g => ?_) hh y hy
  have hfin : {i : Pl E × Bool | Sl S i ∧ qw n i.1 i.2 g ∉ N i.1}.Finite :=
    (bad_finite hG hbad g g).subset fun i hi => ⟨hi.1, Or.inl hi.2⟩
  have hFam : Fam S N hfin.toFinset (fun w b => (dcs (N w) (qw n w b g)).indicator (1 : GLw n w → ℂ)) := by
    refine ⟨fun i hi => ?_, fun i hi hnI => ?_⟩
    · have hi' := ((hfin.mem_toFinset).1 hi).1
      exact ⟨hi', dcs_hecke (hNc i hi') _⟩
    · have hq : qw n i.1 i.2 g ∈ N i.1 := by
        by_contra h0
        exact hnI ((hfin.mem_toFinset).2 ⟨hi, h0⟩)
      simp only
      rw [dcs_eq_of_mem hq]
  have hpf := pf_eq (S := S) hG hqj hsep hbad g
  refine ⟨hpf ▸ hP E n S Z N hSec hZ hG _ _ hFam, fun y hy => ?_⟩
  rw [← hpf, hO E n S Z N hSec hZ hG _ _ hFam y (hW hy)]
  refine list_mem W _ ?_ y hy
  intro T hT
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hT
  have hi' := (Finset.mem_toList).1 hi
  exact hloc i (hFam.1 i hi').1 _ (hFam.1 i hi').2
