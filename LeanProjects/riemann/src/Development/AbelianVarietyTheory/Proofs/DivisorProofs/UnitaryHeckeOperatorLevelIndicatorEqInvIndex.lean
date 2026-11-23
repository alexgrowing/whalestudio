import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointLocalComponentMemLocalUn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteAdelicUnitaryComponentMemIntegra
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.HopLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_of_mem {G : Type} [Group G] (H : Subgroup G) {g : G} (h : g ∈ H) : toSub H g = ⟨g, h⟩ := by
  unfold toSub; rw [dif_pos h]

def comp (hU : Unr E) (n : ℕ) (w : Pl E) : finU E n →* UL n w :=
  ((cLoc w).comp (finU E n).subtype).codRestrict (UL n w) (fun x => cLoc_mem_UL E hU n w x)

theorem comp_eq (hU : Unr E) (w : Pl E) (x : finU E n) :
    comp hU n w x = toSub (UL n w) (cLoc w (x : UA E n)) :=
  (toSub_of_mem _ (cLoc_mem_UL E hU n w x)).symm

theorem mem_globLev (hU : Unr E) (S : Set (Pl E)) (L : ∀ w : Pl E, Subgroup (UL n w)) (x : finU E n) :
    x ∈ globLev S L ↔ ∀ w ∈ S, comp hU n w x ∈ L w := by
  unfold globLev
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype]
  refine forall_congr' fun w => forall_congr' fun _ => ⟨fun ⟨k, hk, e⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩
  have : k = comp hU n w x := Subtype.ext e
  rwa [← this]

theorem globFn_indicator (hU : Unr E) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (hK : ∀ᶠ w in cofinite, K' w = KL n w) (x : finU E n) :
    globFn S (fun w => (K' w : Set (UL n w)).indicator 1) x = if x ∈ globLev S K' then 1 else 0 := by
  unfold globFn
  simp_rw [← comp_eq hU]
  by_cases hx : x ∈ globLev S K'
  · rw [if_pos hx]
    refine finprod_mem_of_eqOn_one fun w hw => ?_
    rw [Set.indicator_of_mem ((mem_globLev hU S K' x).1 hx w hw)]
    rfl
  · rw [if_neg hx, finprod_mem_def]
    obtain ⟨w₀, hw₀, hn⟩ : ∃ w ∈ S, comp hU n w x ∉ K' w := by
      by_contra h; push_neg at h; exact hx ((mem_globLev hU S K' x).2 h)
    refine finprod_eq_zero _ w₀ ?_ ?_
    · rw [Set.mulIndicator_of_mem hw₀, Set.indicator_of_notMem hn]
    · have h1 := Filter.eventually_cofinite.1 hK
      have h2 := Filter.eventually_cofinite.1 (LocAE.eventually_mem_KL E hU n x)
      refine (h1.union h2).subset fun w hw => ?_
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
      apply hw
      rw [Set.mulIndicator_apply]
      split_ifs
      · rw [Set.indicator_of_mem]
        · rfl
        · rw [hc.1, comp_eq hU]; exact hc.2
      · rfl

end GlobalTheory.BCT.HopLev

noncomputable section

namespace GlobalTheory.BCT.HopLev2

open GlobalTheory.BCT.HopLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem index_pi_univ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_eq_prod {ι : Type} [Fintype ι] {G : Type} [Group G] {M : ι → Type} [∀ i, Group (M i)]
    (φ : G →* ((i : ι) → M i)) (Up U : Subgroup G) (K H : ∀ i, Subgroup (M i))
    (hK : ∀ g ∈ Up, ∀ i, φ g i ∈ K i) (hs : ∀ x : (i : ι) → M i, (∀ i, x i ∈ K i) → ∃ g ∈ Up, φ g = x)
    (hU : ∀ g, g ∈ U ↔ g ∈ Up ∧ ∀ i, φ g i ∈ H i) : U.relIndex Up = ∏ i, (H i).relIndex (K i) := by
  let ψ : Up →* ((i : ι) → K i) :=
    { toFun := fun g i => ⟨φ g.1 i, hK g.1 g.2 i⟩
      map_one' := by ext i; simp
      map_mul' := by intro x y; ext i; simp }
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨g, hg, e⟩ := hs (fun i => (x i).1) (fun i => (x i).2)
    exact ⟨⟨g, hg⟩, by ext i; simp [ψ, e]⟩
  have e : U.subgroupOf Up = (Subgroup.pi Set.univ fun i => (H i).subgroupOf (K i)).comap ψ := by
    ext g
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_pi, hU, g.2, ψ]
  rw [Subgroup.relIndex, e, Subgroup.index_comap_of_surjective _ hψ, index_pi_univ]
  rfl

theorem relIndex_globLev (hU : Unr E) (S : Set (Pl E)) (hS : IsSection S) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (hle : ∀ w, K' w ≤ KL n w) (hK : ∀ᶠ w in cofinite, K' w = KL n w) :
    (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ) = ∏ᶠ w ∈ S, (((K' w).relIndex (KL n w) : ℕ) : ℂ) := by
  have hfin := Filter.eventually_cofinite.1 hK
  obtain ⟨T, hTS, hnT⟩ : ∃ T : Finset (Pl E), (∀ w ∈ T, w ∈ S) ∧ ∀ w ∈ S, w ∉ T → K' w = KL n w :=
    ⟨hfin.toFinset.filter (· ∈ S), fun w hw => (Finset.mem_filter.1 hw).2, fun w hw h => by
      by_contra hc
      exact h (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hc, hw⟩)⟩
  rw [finprod_mem_eq_prod_of_inter_mulSupport_eq _ (t := T)]
  · rw [← Finset.prod_coe_sort T]
    rw [relIndex_eq_prod (MonoidHom.pi fun i : T => comp hU n i.1) (globLev S (KL n)) (globLev S K')
      (fun i => KL n i.1) (fun i => K' i.1)]
    · push_cast; rfl
    · intro g hg i
      exact (mem_globLev hU S (KL n) g).1 hg i.1 (hTS _ i.2)
    · intro x hx
      obtain ⟨y, hyT, hyn⟩ : ∃ y : ∀ w : Pl E, UL n w, (∀ i : T, y i.1 = x i) ∧ ∀ w, w ∉ T → y w = 1 :=
        ⟨fun w => if h : w ∈ T then x ⟨w, h⟩ else 1, fun i => dif_pos i.2, fun w h => dif_neg h⟩
      have hy : ∀ w, y w ∈ KL n w := fun w => by
        by_cases h : w ∈ T
        · have := hx ⟨w, h⟩
          rw [hyT ⟨w, h⟩]
          exact this
        · rw [hyn w h]; exact one_mem _
      obtain ⟨g, hg⟩ := exists_finU_of_loc E hU n S hS y (Filter.Eventually.of_forall hy)
      have hg' : ∀ w ∈ S, comp hU n w g = y w := fun w hw => by rw [comp_eq]; exact hg w hw
      refine ⟨g, (mem_globLev hU S (KL n) g).2 fun w hw => by rw [hg' w hw]; exact hy w, ?_⟩
      funext i
      show comp hU n i.1 g = x i
      rw [hg' i.1 (hTS _ i.2)]
      exact hyT i
    · intro g
      rw [mem_globLev hU S K' g, mem_globLev hU S (KL n) g]
      refine ⟨fun h => ⟨fun w hw => hle w (h w hw), fun i => h i.1 (hTS _ i.2)⟩, fun ⟨h1, h2⟩ w hw => ?_⟩
      by_cases hwT : w ∈ T
      · exact h2 ⟨w, hwT⟩
      · rw [hnT w hw hwT]; exact h1 w hw
  · ext w
    simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.mem_coe]
    refine ⟨fun ⟨hw, h⟩ => ⟨?_, h⟩, fun ⟨hw, h⟩ => ⟨hTS w hw, h⟩⟩
    by_contra hwT
    apply h
    rw [hnT w hw hwT, Subgroup.relIndex_self]
    simp

end GlobalTheory.BCT.HopLev2

open GlobalTheory.BCT.HopLev GlobalTheory.BCT.HopLev2 in

theorem GlobalTheory.BCT.hop_indicator_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ φ ∈ fixed (RF E n) (globLev S K'),
    hop S K' (fun w => (K' w : Set (UL n w)).indicator 1) φ = (∏ᶠ w ∈ S, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ • φ := by
  intro E _ _ _ hU n _ S hS K' hK φ hφ
  rw [← relIndex_globLev hU S hS K' (fun w => (hK.1 w).2.1) hK.2]
  unfold hop levOp
  rw [LinearMap.smul_apply]
  congr 1
  set H := globLev S K'
  have hq : ∀ q : finU E n ⧸ H, q ≠ ((1 : finU E n) : finU E n ⧸ H) → Quotient.out q ∉ H := by
    intro q hq hm
    apply hq
    rw [← QuotientGroup.out_eq' q, QuotientGroup.eq]
    simpa using hm
  have h1 : Quotient.out ((1 : finU E n) : finU E n ⧸ H) ∈ H := by
    have := QuotientGroup.out_eq' ((1 : finU E n) : finU E n ⧸ H)
    rw [QuotientGroup.eq] at this
    simpa using this
  rw [finsum_eq_single _ ((1 : finU E n) : finU E n ⧸ H)]
  · rw [globFn_indicator hU S K' hK.2, if_pos h1, one_smul, LinearMap.comp_id]
    have := hφ ⟨_, h1⟩
    simpa using this
  · intro q hne
    rw [globFn_indicator hU S K' hK.2, if_neg (hq q hne), zero_smul]
