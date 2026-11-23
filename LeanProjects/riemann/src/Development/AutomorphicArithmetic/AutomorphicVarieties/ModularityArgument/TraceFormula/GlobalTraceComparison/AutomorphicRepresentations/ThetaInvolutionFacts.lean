import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ListEig

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Abstract

variable {M ι : Type} [AddCommGroup M] [Module ℂ M]

private theorem list_eig (L : ι → Module.End ℂ M) (c : ι → ℂ) (x : M) (l : List ι)
    (h : ∀ i ∈ l, L i x = c i • x) : (l.map L).prod x = (l.map c).prod • x :=
  _root_.UpperTheory.Reformulated.B.Qk12.list_eig L c x l h

private theorem prod_split [DecidableEq ι] (L : ι → Module.End ℂ M) (I₀ I₁ : Finset ι) (hd : Disjoint I₀ I₁)
    (hc : ∀ i ∈ I₀ ∪ I₁, ∀ k ∈ I₀ ∪ I₁, i ≠ k → Commute (L i) (L k)) :
    ((I₀ ∪ I₁).toList.map L).prod = (I₀.toList.map L).prod * (I₁.toList.map L).prod := by
  have hp : (I₀ ∪ I₁).toList.Perm (I₀.toList ++ I₁.toList) := by
    refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) ?_).2 ?_
    · exact List.nodup_append.2 ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb hab =>
        Finset.disjoint_left.1 hd (Finset.mem_toList.1 ha) (hab ▸ Finset.mem_toList.1 hb)⟩
    · intro a
      simp
  have hq := hp.map L
  rw [hq.prod_eq' ?_, List.map_append, List.prod_append]
  rw [List.pairwise_map]
  exact (Finset.nodup_toList _).imp_of_mem fun ha hb hab =>
    hc _ (Finset.mem_toList.1 ha) _ (Finset.mem_toList.1 hb) hab

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem two_in {Z T T' : Finset (Pl E)} {w : Pl E} (hw : w ∈ Z) (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (b : Bool) :
    two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T' φ₂ e₂) w b = two φ₁ φ₂ w b := by
  cases b <;> funext g <;> simp [two, intersection_update_fsHerm_neg_one, hw]

private theorem slot_pair_functions_eq {Z T : Finset (Pl E)} {w : Pl E} (hw : w ∉ Z) (hT : w ∈ T) (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) :
    two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) w false = (fun g => fn2 n 0 w (e₁ w) (g, 1)) ∧
    two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) w true = (fun g => fn2 n 0 w (e₂ w) (g, 1)) := by
  constructor <;> funext g <;> simp [two, intersection_update_fsHerm_neg_one, hw, hT]

private theorem two_off {Z T : Finset (Pl E)} {w : Pl E} (hw : w ∉ Z) (hT : w ∉ T) (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (b : Bool) :
    two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) w b = (KGL w n : Set (GLw n w)).indicator 1 := by
  have key : ∀ g : GLw n w, (K2 n 0 w : Set (GLw n w × GLw 0 w)).indicator (1 : GLw n w × GLw 0 w → ℂ) (g, 1) =
      (KGL w n : Set (GLw n w)).indicator 1 g := by
    intro g
    by_cases hg : g ∈ KGL w n
    · rw [Set.indicator_of_mem, Set.indicator_of_mem] <;> simp [hg, K2, Subgroup.mem_prod]
    · rw [Set.indicator_of_notMem, Set.indicator_of_notMem] <;> simp [hg, K2, Subgroup.mem_prod]
  cases b <;> funext g <;> simpa [two, intersection_update_fsHerm_neg_one, hw, hT] using key g

private def slots (S : Set (Pl E)) (Z T : Finset (Pl E)) : Finset (Pl E × Bool) :=
  Z ×ˢ Finset.univ ∪ (T ×ˢ Finset.univ).filter (Sl S)

private theorem fam_positions (hEx : Ex2Act) {S : Set (Pl E)} {Z : Finset (Pl E)} {N : ∀ w : Pl E, Subgroup (GLw n w)}
    (hZ : SplitIn S Z) (hG : Good Z N) (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w)
    (hφ : ∀ w ∈ Z, ∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) (T : Finset (Pl E)) (hT : Disjoint T Z)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) :
    Fam S N (slots S Z T) (two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)) := by
  constructor
  · intro i hi
    rcases Finset.mem_union.1 hi with h | h
    · have hw := (Finset.mem_product.1 h).1
      refine ⟨⟨(hZ _ hw).1, fun _ => (hZ _ hw).2⟩, ?_⟩
      rw [two_in hw]
      exact hφ _ hw _
    · obtain ⟨h1, hs⟩ := Finset.mem_filter.1 h
      have hwT := (Finset.mem_product.1 h1).1
      have hwZ : i.1 ∉ Z := Finset.disjoint_left.1 hT hwT
      refine ⟨hs, ?_⟩
      rw [(hG i.1).2.2.2 hwZ]
      obtain ⟨w, b⟩ := i
      cases b
      · rw [(slot_pair_functions_eq hwZ hwT φ₁ φ₂ e₁ e₂).1]
        exact (hEx E n w (e₁ w)).1
      · rw [(slot_pair_functions_eq hwZ hwT φ₁ φ₂ e₁ e₂).2]
        exact (hEx E n w (e₂ w)).1
  · intro i hs hi
    have hwZ : i.1 ∉ Z := fun h => hi (Finset.mem_union_left _ (Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩))
    have hwT : i.1 ∉ T := fun h => hi (Finset.mem_union_right _
      (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩, hs⟩))
    rw [two_off hwZ hwT, (hG i.1).2.2.2 hwZ]

private def cv (B : Pl E → Multiset ℂˣ) (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (i : Pl E × Bool) : ℂ :=
  if i.2 then ev2 n 0 i.1 (e₂ i.1) (inv (B (cPl i.1))) 0 else ev2 n 0 i.1 (e₁ i.1) (B i.1) 0

private theorem prod_cv {S : Set (Pl E)} (T : Finset (Pl E)) (B : Pl E → Multiset ℂˣ)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (hT : TEv S T e₂) :
    ∏ i ∈ (T ×ˢ Finset.univ).filter (Sl S), cv B e₁ e₂ i = val T e₁ e₂ B 0 := by
  rw [Finset.prod_filter, Finset.prod_product, val]
  refine Finset.prod_congr rfl fun w hw => ?_
  have hS := hT.1 w hw
  rw [Fintype.prod_bool]
  by_cases hs : IsSplitAt w
  · have h1 : Sl S (w, true) := ⟨hS, fun _ => hs⟩
    have h2 : Sl S (w, false) := ⟨hS, by simp⟩
    simp [h1, h2, cv, inv, mul_comm]
  · have h1 : ¬ Sl S (w, true) := fun h => hs (h.2 rfl)
    have h2 : Sl S (w, false) := ⟨hS, by simp⟩
    have h3 : ev2 n 0 w (e₂ w) (inv (B (cPl w))) (inv ((0 : Pl E → Multiset ℂˣ) (cPl w))) = 1 := hT.2 w hw hs _
    simp only [h1, h2, if_true, if_false, cv, one_mul]
    rw [h3, mul_one]
    simp

private theorem off_of (hPl : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.Places) {S : Set (Pl E)} {Z : Finset (Pl E)} (hS : IsSection S)
    (hZ : SplitIn S Z) {w : Pl E} (hw : w ∈ S) (hwZ : w ∉ Z) : Off Z w ∧ Off Z (cPl w) := by
  have hc : cPl w ∉ Z := fun h => by
    have := ((hPl E).2.2.2 S hS w).2 hw (hZ _ h).1
    exact hwZ (this ▸ h)
  exact ⟨⟨hwZ, hc⟩, hc, by rwa [((hPl E).2.1 w).1]⟩

theorem tTr_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.Places → PfHecke → ProdOp → LocComm → YLoc → Ex2Act → SatAll → TTr := by
  intro hPl hPf hPO hLC _ hEx hSat E _ _ _ n S Z N hS hZ hG π y B hB φ₁ φ₂ hφ T hTZ e₁ e₂ hT
  have hF := fam_positions hEx hZ hG φ₁ φ₂ hφ T hTZ e₁ e₂
  have hF0 : Fam S N (Z ×ˢ Finset.univ) (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂)) := by
    simpa [slots] using fam_positions (S := S) hEx hZ hG φ₁ φ₂ hφ ∅ (Finset.disjoint_empty_left _) e₁ e₂
  have hH := hPf E n S Z N hS hZ hG _ _ hF
  have hH0 := hPf E n S Z N hS hZ hG _ _ hF0
  refine ⟨hH, hF0, LinearMap.ext fun x => Subtype.ext ?_⟩
  have hxf := y.fix x.2
  rw [LinearMap.smul_apply, Submodule.coe_smul, y.act _ hH x, y.act _ hH0 x,
    hPO E n S Z N hS hZ hG _ _ hF _ hxf, hPO E n S Z N hS hZ hG _ _ hF0 _ hxf]
  set F := two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) with hFdef
  set L : Pl E × Bool → Module.End ℂ (Sm E n) := fun i => Lw N i.1 i.2 (F i.1 i.2) with hL
  have hd : Disjoint (Z ×ˢ Finset.univ : Finset (Pl E × Bool)) ((T ×ˢ Finset.univ).filter (Sl S)) := by
    refine Finset.disjoint_left.2 fun i h1 h2 => ?_
    exact Finset.disjoint_left.1 hTZ (Finset.mem_product.1 (Finset.mem_filter.1 h2).1).1 (Finset.mem_product.1 h1).1
  have hcomm : ∀ i ∈ (Z ×ˢ Finset.univ : Finset (Pl E × Bool)) ∪ (T ×ˢ Finset.univ).filter (Sl S),
      ∀ k ∈ (Z ×ˢ Finset.univ : Finset (Pl E × Bool)) ∪ (T ×ˢ Finset.univ).filter (Sl S), i ≠ k → Commute (L i) (L k) := by
    intro i hi k hk hik
    exact (hLC E n S Z N hS hZ hG i (hF.1 i hi).1 _ (hF.1 i hi).2).2 k (hF.1 k hk).1 hik _ (hF.1 k hk).2
  have hsame : ((Z ×ˢ Finset.univ : Finset (Pl E × Bool)).toList.map fun i =>
      Lw N i.1 i.2 (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) i.1 i.2)) =
      (Z ×ˢ Finset.univ : Finset (Pl E × Bool)).toList.map L := by
    refine List.map_congr_left fun i hi => ?_
    have hw := (Finset.mem_product.1 (Finset.mem_toList.1 hi)).1
    simp only [hL, hFdef, two_in hw]
  have heig : ∀ i ∈ ((T ×ˢ Finset.univ).filter (Sl S)).toList, L i x.1 = cv B e₁ e₂ i • x.1 := by
    intro i hi
    obtain ⟨h1, hs⟩ := Finset.mem_filter.1 (Finset.mem_toList.1 hi)
    have hwT := (Finset.mem_product.1 h1).1
    have hwZ : i.1 ∉ Z := Finset.disjoint_left.1 hTZ hwT
    by_cases hx0 : x.1 = 0
    · simp [hx0]
    have hmem : i ∈ slots S Z T := Finset.mem_union_right _ (Finset.mem_filter.2 ⟨h1, hs⟩)
    have hfx := ((hLC E n S Z N hS hZ hG i hs _ (hF.1 i hmem).2).1 x.1 hxf).1
    rw [(hG i.1).2.2.2 hwZ] at hfx
    obtain ⟨ho, ho'⟩ := off_of hPl hS hZ hs.1 hwZ
    obtain ⟨w, b⟩ := i
    have hN : N w = KGL w n := (hG w).2.2.2 hwZ
    have hxV := y.le x.2
    cases b
    · have hv := (hSat E n π w (B w) x.1 hxV hx0).1 (hB w ho) hfx
      have := (hEx E n w (e₁ w)).2 _ _ x.1 (B w) hv
      simp only [hL, hFdef, (slot_pair_functions_eq hwZ hwT φ₁ φ₂ e₁ e₂).1, cv, Lw, hN]
      simpa using this
    · have hv := (hSat E n π w (B (cPl w)) x.1 hxV hx0).2 (by
        have := hB (cPl w) ho'
        exact this) hfx
      have := (hEx E n w (e₂ w)).2 _ _ x.1 _ hv
      simp only [hL, hFdef, (slot_pair_functions_eq hwZ hwT φ₁ φ₂ e₁ e₂).2, cv, Lw, hN]
      simpa using this
  have hI : slots S Z T = (Z ×ˢ Finset.univ : Finset (Pl E × Bool)) ∪ (T ×ˢ Finset.univ).filter (Sl S) := rfl
  rw [hsame, hI, prod_split L _ _ hd hcomm, Module.End.mul_apply, list_eig L (cv B e₁ e₂) x.1 _ heig,
    Finset.prod_map_toList, prod_cv T B e₁ e₂ hT, map_smul]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
