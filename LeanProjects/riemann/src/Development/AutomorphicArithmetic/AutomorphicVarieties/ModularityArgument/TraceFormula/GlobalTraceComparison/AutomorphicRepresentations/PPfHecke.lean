import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PfH

open scoped Pointwise

section Abs

variable {G ι : Type} [Group G] {A : ι → Type} [∀ i, Group (A i)]

private def boxes (j : ∀ i, A i →* G) (C : ∀ i, Set (A i)) : List ι → Set G
  | [] => {1}
  | i :: l => (j i '' C i) * boxes j C l

private def pr (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (x : G) (l : List ι) : G :=
  (l.map fun i => j i (q i x)).prod

private theorem boxes_compact [TopologicalSpace G] [ContinuousMul G] [∀ i, TopologicalSpace (A i)]
    (j : ∀ i, A i →* G) (C : ∀ i, Set (A i)) (hj : ∀ i, Continuous (j i)) (l : List ι)
    (h : ∀ i ∈ l, IsCompact (C i)) : IsCompact (boxes j C l) := by
  induction l with
  | nil => exact isCompact_singleton
  | cons i l ih =>
    exact ((h i (by simp)).image (hj i)).mul (ih fun k hk => h k (by simp [hk]))

private theorem pr_mem (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (C : ∀ i, Set (A i)) (x : G) (l : List ι)
    (h : ∀ i ∈ l, q i x ∈ C i) : pr j q x l ∈ boxes j C l := by
  induction l with
  | nil => simp [pr, boxes]
  | cons i l ih =>
    have h1 : j i (q i x) ∈ j i '' C i := ⟨_, h i (by simp), rfl⟩
    have h2 := ih fun k hk => h k (by simp [hk])
    simpa [pr, boxes] using Set.mul_mem_mul h1 h2

private theorem q_pr_out (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (P : ι → Prop)
    (hind : ∀ i k, P i → P k → i ≠ k → ∀ a, q k (j i a) = 1) (x : G) (k : ι) (hk : P k) (l : List ι)
    (hl : ∀ i ∈ l, P i) (hkl : k ∉ l) : q k (pr j q x l) = 1 := by
  induction l with
  | nil => simp [pr]
  | cons i l ih =>
    have hne : i ≠ k := fun e => hkl (by simp [e])
    have h2 : q k (pr j q x l) = 1 :=
      ih (fun m hm => hl m (by simp [hm])) (fun hm => hkl (by simp [hm]))
    have h3 : pr j q x (i :: l) = j i (q i x) * pr j q x l := by simp [pr]
    rw [h3, map_mul, h2, hind i k (hl i (by simp)) hk hne, one_mul]

private theorem q_pr_in (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (P : ι → Prop)
    (hjq : ∀ i a, q i (j i a) = a)
    (hind : ∀ i k, P i → P k → i ≠ k → ∀ a, q k (j i a) = 1) (x : G) (k : ι) (l : List ι)
    (hl : ∀ i ∈ l, P i) (hnd : l.Nodup) (hkl : k ∈ l) : q k (pr j q x l) = q k x := by
  induction l with
  | nil => simp at hkl
  | cons i l ih =>
    have h3 : pr j q x (i :: l) = j i (q i x) * pr j q x l := by simp [pr]
    have hl' : ∀ m ∈ l, P m := fun m hm => hl m (by simp [hm])
    obtain ⟨hi, hnd'⟩ := List.nodup_cons.1 hnd
    by_cases e : k = i
    · subst e
      rw [h3, map_mul, hjq, q_pr_out j q P hind x k (hl k (by simp)) l hl' hi, mul_one]
    · have hk' : k ∈ l := by simpa [e] using hkl
      rw [h3, map_mul, ih hl' hnd' hk', hind i k (hl i (by simp)) (hl k (by simp [hk'])) (Ne.symm e), one_mul]

private theorem abs_support [TopologicalSpace G] [IsTopologicalGroup G] [∀ i, TopologicalSpace (A i)]
    (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (hj : ∀ i, Continuous (j i)) (P : ι → Prop)
    (N : ∀ i, Subgroup (A i)) (L : Subgroup G) (hL : ∀ x, x ∈ L ↔ ∀ i, P i → q i x ∈ N i)
    (hLo : IsOpen (L : Set G)) (hLc : IsCompact (L : Set G)) (hjq : ∀ i a, q i (j i a) = a)
    (hind : ∀ i k, P i → P k → i ≠ k → ∀ a, q k (j i a) = 1) (I : Finset ι) (hI : ∀ i ∈ I, P i)
    (C : ∀ i, Set (A i)) (hC : ∀ i ∈ I, IsCompact (C i)) (f : G → ℂ)
    (hinv : ∀ k ∈ L, ∀ x, f (x * k) = f x)
    (hs : ∀ x, f x ≠ 0 → (∀ i ∈ I, q i x ∈ C i) ∧ ∀ i, P i → i ∉ I → q i x ∈ N i) :
    HasCompactSupport f := by
  classical
  have hcl : IsClosed (Function.support f) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hx0 : f x = 0 := by simpa using hx
    have hop : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (L : Set G)) :=
      hLo.preimage (continuous_const.mul continuous_id)
    have hmem : x ∈ (fun y => x⁻¹ * y) ⁻¹' (L : Set G) := by simp [L.one_mem]
    refine Filter.mem_of_superset (hop.mem_nhds hmem) ?_
    intro y hy
    have : f (x * (x⁻¹ * y)) = f x := hinv _ hy x
    simpa [hx0] using this
  have hl : ∀ i ∈ I.toList, P i := fun i hi => hI i (by simpa using hi)
  have hK : IsCompact (boxes j C I.toList * (L : Set G)) :=
    (boxes_compact j C hj _ fun i hi => hC i (by simpa using hi)).mul hLc
  have hsub : Function.support f ⊆ boxes j C I.toList * (L : Set G) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hs x hx
    have hb := pr_mem j q C x I.toList fun i hi => h1 i (by simpa using hi)
    have hy : (pr j q x I.toList)⁻¹ * x ∈ L := by
      refine (hL _).2 fun k hk => ?_
      by_cases hkI : k ∈ I
      · rw [map_mul, map_inv, q_pr_in j q P hjq hind x k _ hl I.nodup_toList (by simpa using hkI)]
        simp [(N k).one_mem]
      · rw [map_mul, map_inv, q_pr_out j q P hind x k hk _ hl (by simpa using hkI)]
        simpa using h2 k hk hkI
    have := Set.mul_mem_mul hb hy
    simpa using this
  show IsCompact (closure (Function.support f))
  rw [hcl.closure_eq]
  exact hK.of_isClosed_subset hcl hsub

end Abs

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PfH

open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun in
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PfH in
open scoped Classical in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pfHecke_pf :
    SlotBasic → LevTop → PfHecke := by
  intro hSF hLT E _ _ _ n S Z N hS hZ hN I F hF
  obtain ⟨-, -, hloc, hind, hfinK, -, -⟩ := hSF E n S hS
  obtain ⟨hLo, hLc, -, -⟩ := hLT E n S Z N hS hZ hN
  have hLev : ∀ x, x ∈ Lev S N ↔ ∀ i : Pl E × Bool, Sl S i → qw n i.1 i.2 x ∈ N i.1 := by
    intro x
    simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]

  have hposition : ∀ i : Pl E × Bool, Sl S i → ∀ a ∈ N i.1, ∀ x,
      F i.1 i.2 (a * x) = F i.1 i.2 x ∧ F i.1 i.2 (x * a) = F i.1 i.2 x := by
    intro i hi a ha x
    by_cases hiI : i ∈ I
    · exact (hF.1 i hiI).2.2 a ha x
    · rw [hF.2 i hi hiI]
      constructor
      · by_cases hx : x ∈ N i.1
        · rw [Set.indicator_of_mem (show a * x ∈ (N i.1 : Set _) from (N i.1).mul_mem ha hx),
            Set.indicator_of_mem (show x ∈ (N i.1 : Set _) from hx)]
          rfl
        · rw [Set.indicator_of_notMem (show a * x ∉ (N i.1 : Set _) from
              fun h => hx ((Subgroup.mul_mem_cancel_left _ ha).1 h)),
            Set.indicator_of_notMem (show x ∉ (N i.1 : Set _) from hx)]
      · by_cases hx : x ∈ N i.1
        · rw [Set.indicator_of_mem (show x * a ∈ (N i.1 : Set _) from (N i.1).mul_mem hx ha),
            Set.indicator_of_mem (show x ∈ (N i.1 : Set _) from hx)]
          rfl
        · rw [Set.indicator_of_notMem (show x * a ∉ (N i.1 : Set _) from
              fun h => hx ((Subgroup.mul_mem_cancel_right _ ha).1 h)),
            Set.indicator_of_notMem (show x ∉ (N i.1 : Set _) from hx)]

  have hfalse : ∀ w, w ∈ S → Sl S (w, false) := fun w hw => ⟨hw, by simp⟩
  have htrue : ∀ w, w ∈ S → IsSplitAt w → Sl S (w, true) := fun w hw hs => ⟨hw, fun _ => hs⟩
  have hinvL : ∀ k ∈ Lev S N, ∀ x, pf S F (k * x) = pf S F x := by
    intro k hk x
    refine finprod_congr fun w => finprod_congr fun hw => ?_
    have hk' := (hLev k).1 hk
    have h1 := (hposition (w, false) (hfalse w hw) _ (hk' _ (hfalse w hw)) (qw n w false x)).1
    simp only [map_mul] at h1 ⊢
    rw [h1]
    by_cases hs : IsSplitAt w
    · have h2 := (hposition (w, true) (htrue w hw hs) _ (hk' _ (htrue w hw hs)) (qw n w true x)).1
      simp only [if_pos hs]
      rw [h2]
    · simp only [if_neg hs]
  have hinvR : ∀ k ∈ Lev S N, ∀ x, pf S F (x * k) = pf S F x := by
    intro k hk x
    refine finprod_congr fun w => finprod_congr fun hw => ?_
    have hk' := (hLev k).1 hk
    have h1 := (hposition (w, false) (hfalse w hw) _ (hk' _ (hfalse w hw)) (qw n w false x)).2
    simp only [map_mul] at h1 ⊢
    rw [h1]
    by_cases hs : IsSplitAt w
    · have h2 := (hposition (w, true) (htrue w hw hs) _ (hk' _ (htrue w hw hs)) (qw n w true x)).2
      simp only [if_pos hs]
      rw [h2]
    · simp only [if_neg hs]

  have hfac : ∀ x : GF E n, pf S F x ≠ 0 → ∀ w ∈ S,
      (F w false (qw n w false x) * if IsSplitAt w then F w true (qw n w true x) else 1) ≠ 0 := by
    intro x hx w hw h0
    apply hx
    classical
    set fac : Pl E → ℂ := fun w =>
      F w false (qw n w false x) * if IsSplitAt w then F w true (qw n w true x) else 1 with hfacdef
    have hbad := hfinK x
    have hfin : (S ∩ Function.mulSupport fac).Finite := by
      refine ((Z.finite_toSet.union (I.image Prod.fst).finite_toSet).union
        (hbad.image Prod.fst)).subset ?_
      rintro u ⟨hu, hne⟩
      by_contra hout
      simp only [Set.mem_union, Finset.mem_coe, Finset.mem_image, Set.mem_image, Set.mem_setOf_eq,
        not_or, not_exists, not_and] at hout
      obtain ⟨⟨huZ, huI⟩, hub⟩ := hout
      have hNu : N u = KGL u n := (hN u).2.2.2 huZ
      have hone : ∀ b, Sl S (u, b) → F u b (qw n u b x) = 1 := by
        intro b hb
        have hnotI : (u, b) ∉ I := fun h => huI (u, b) h rfl
        have hq : qw n u b x ∈ KGL u n := by
          by_contra hq
          exact hub (u, b) hq rfl
        rw [hF.2 (u, b) hb hnotI]
        simp only
        rw [hNu, Set.indicator_of_mem (show qw n u b x ∈ (KGL u n : Set _) from hq)]
        rfl
      apply hne
      simp only [hfacdef]
      rw [hone false (hfalse u hu)]
      by_cases hs : IsSplitAt u
      · simp only [if_pos hs]
        rw [hone true (htrue u hu hs), one_mul]
      · simp only [if_neg hs, one_mul]
    have hwm : w ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      refine ⟨hw, ?_⟩
      show fac w ≠ 1
      rw [show fac w = 0 from h0]
      exact zero_ne_one
    show (∏ᶠ w ∈ S, fac w) = 0
    rw [finprod_mem_eq_prod fac hfin]
    exact Finset.prod_eq_zero hwm h0

  have hval : ∀ x : GF E n, pf S F x ≠ 0 → ∀ i : Pl E × Bool, Sl S i → F i.1 i.2 (qw n i.1 i.2 x) ≠ 0 := by
    rintro x hx ⟨w, b⟩ ⟨hw, hb⟩
    have h := hfac x hx w hw
    cases b with
    | false => exact left_ne_zero_of_mul h
    | true =>
      have hs := hb rfl
      have h2 := right_ne_zero_of_mul h
      rwa [if_pos hs] at h2
  refine ⟨?_, fun k hk x => ⟨hinvL k hk x, hinvR k hk x⟩⟩
  refine abs_support (ι := Pl E × Bool) (A := fun i => GLw n i.1)
    (fun i => jw n i.1 i.2) (fun i => qw n i.1 i.2) (fun i => (hloc i.1 i.2).1) (Sl S)
    (fun i => N i.1) (Lev S N) hLev hLo hLc (fun i a => (hloc i.1 i.2).2.2.1 a)
    (fun i k hi hk hne a => hind i k hi hk hne a) I (fun i hi => (hF.1 i hi).1)
    (fun i => tsupport (F i.1 i.2)) (fun i hi => (hF.1 i hi).2.1) (pf S F) hinvR ?_
  intro x hx
  refine ⟨fun i hi => subset_tsupport _ (hval x hx i (hF.1 i hi).1), fun i hi hiI => ?_⟩
  have h := hval x hx i hi
  rw [hF.2 i hi hiI] at h
  by_contra hq
  exact h (Set.indicator_of_notMem hq _)
