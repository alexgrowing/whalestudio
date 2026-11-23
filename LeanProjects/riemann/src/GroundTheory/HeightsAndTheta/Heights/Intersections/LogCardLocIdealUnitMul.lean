import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.XcNotMemOfIsRelevant
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerFurther
import GroundTheory.HeightsAndTheta.Heights.Intersections.TwoMemFunFieldSpecZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerTer
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerMore
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem card_quot_span_mul {S : Type*} [CommRing S] [IsDomain S] (u v : S) (hu : u ≠ 0) :
    Nat.card (S ⧸ Ideal.span {u * v}) = Nat.card (S ⧸ Ideal.span {u}) * Nat.card (S ⧸ Ideal.span {v}) := by
  let f : S →+ S := AddMonoidHom.mulLeft u
  have hf : Function.Injective f := fun a b h => mul_left_cancel₀ hu h
  have e1 : (Ideal.span {v}).toAddSubgroup.map f = (Ideal.span {u * v}).toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, by simp only [f, AddMonoidHom.coe_mulLeft]; ring⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r * v, ⟨r, rfl⟩, by simp only [f, AddMonoidHom.coe_mulLeft]; ring⟩
  have e2 : (⊤ : AddSubgroup S).map f = (Ideal.span {u}).toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, Submodule.mem_toAddSubgroup,
      Ideal.mem_span_singleton', f, AddMonoidHom.coe_mulLeft]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← hy, mul_comm]⟩, fun ⟨r, hr⟩ => ⟨r, by rw [← hr, mul_comm]⟩⟩
  have hle : (Ideal.span {u * v}).toAddSubgroup ≤ (Ideal.span {u}).toAddSubgroup :=
    fun z hz => Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right u v) hz
  have h2 : (Ideal.span {u * v}).toAddSubgroup.relIndex (Ideal.span {u}).toAddSubgroup =
      (Ideal.span {v}).toAddSubgroup.index := by
    rw [← e1, ← e2, AddSubgroup.relIndex_map_map_of_injective _ _ hf, AddSubgroup.relIndex_top_right]
  have hc : ∀ I : Ideal S, Nat.card (S ⧸ I) = I.toAddSubgroup.index :=
    fun I => (AddSubgroup.index_eq_card _).symm
  rw [hc, hc, hc, ← AddSubgroup.relIndex_mul_index hle, h2, mul_comm]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_card_locIdeal_mul {P W : Ideal (MRing ι)} [P.IsPrime] {y₁ y₂ : FractionRing (MRing ι ⧸ P)}
    (h₁ : y₁ ∈ locRing P W) (h₂ : y₂ ∈ locRing P W) (hne : y₁ ≠ 0)
    (hf₁ : Finite (locRing P W ⧸ locIdeal P W y₁)) (hf₂ : Finite (locRing P W ⧸ locIdeal P W y₂)) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y₁ * y₂))) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W y₁)) + Real.log (Nat.card (locRing P W ⧸ locIdeal P W y₂)) := by
  rw [locIdeal_eq_span h₁] at hf₁ ⊢
  rw [locIdeal_eq_span h₂] at hf₂ ⊢
  rw [locIdeal_eq_span (mul_mem h₁ h₂)]
  have : (⟨y₁ * y₂, mul_mem h₁ h₂⟩ : locRing P W) = ⟨y₁, h₁⟩ * ⟨y₂, h₂⟩ := rfl
  rw [this, card_quot_span_mul _ _ (fun h => hne (congrArg Subtype.val h)), Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr Nat.card_pos.ne') (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]

theorem log_card_locIdeal_unit {P W : Ideal (MRing ι)} [P.IsPrime] {y z : FractionRing (MRing ι ⧸ P)}
    (hy : y ∈ locRing P W) (hz : z ∈ locRing P W) (h : y * z = 1) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W y)) = 0 := by
  rw [locIdeal_eq_span hy, Ideal.span_singleton_eq_top.mpr
    (IsUnit.of_mul_eq_one (⟨z, hz⟩ : locRing P W) (Subtype.ext h))]
  have : Subsingleton (locRing P W ⧸ (⊤ : Ideal (locRing P W))) := Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [Nat.card_of_subsingleton (0 : locRing P W ⧸ (⊤ : Ideal (locRing P W)))]
  simp

theorem log_card_locIdeal_unit_mul {P W : Ideal (MRing ι)} [P.IsPrime] {y z c : FractionRing (MRing ι ⧸ P)}
    (hy : y ∈ locRing P W) (hz : z ∈ locRing P W) (h : y * z = 1) (hc : c ∈ locRing P W) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y * c))) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W c)) := by
  rw [locIdeal_eq_span (mul_mem hy hc), locIdeal_eq_span hc]
  have : (⟨y * c, mul_mem hy hc⟩ : locRing P W) = ⟨y, hy⟩ * ⟨c, hc⟩ := rfl
  rw [this, Ideal.span_singleton_mul_left_unit (IsUnit.of_mul_eq_one (⟨z, hz⟩ : locRing P W) (Subtype.ext h))]

theorem frac_mem_locRing {P W : Ideal (MRing ι)} (hPW : P ≤ W) {u v : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hv : IsMultiHomog v a) (hvW : v ∉ W) [P.IsPrime] {y : FractionRing (MRing ι ⧸ P)}
    (hy : y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)) :
    y ∈ locRing P W := by
  have hvP : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero (by rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact fun h => hvW (hPW h))
  exact Subring.subset_closure ⟨u, v, a, hvP, hvW, hu, hv, IsLocalization.eq_mk'_iff_mul_eq.mpr hy⟩

theorem frac_unit_locRing {P W : Ideal (MRing ι)} (hPW : P ≤ W) {u v : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hv : IsMultiHomog v a) (huW : u ∉ W) (hvW : v ∉ W) [P.IsPrime]
    {y : FractionRing (MRing ι ⧸ P)}
    (hy : y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)) :
    y ∈ locRing P W ∧ ∃ z ∈ locRing P W, y * z = 1 := by
  have hu0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => huW (hPW h)
  have hv0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => hvW (hPW h)
  set z := algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) /
    algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)
  refine ⟨frac_mem_locRing hPW hu hv hvW hy, z, frac_mem_locRing hPW hv hu huW (div_mul_cancel₀ _ hu0), ?_⟩
  rw [mul_div_assoc', hy, div_self hu0]

theorem RegularityLocalProduct.proof (hN : RegularityFunctionFieldNumber.Statement) (hR : RegularityFormula.Statement)
    (hD : RegularityDenominator.Statement) (hC : RegularityDivisorSupportClosed.Statement) (hF : RegularityLocalFinite.Statement) :
    RegularityLocalProduct.Statement := by
  classical
  intro K _ ι _ P f g a x t yf yg hP hf hg hfP hgP hx ht
  have : P.IsPrime := hP.2.1.1
  obtain ⟨c, hc0, hcW⟩ := hD K ι P x hP
  have hφ : ∀ s, s ∉ P → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) ≠ 0 :=
    fun s hs => by rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]; exact hs
  have hx0 : x ≠ 0 := fun h => hφ f hfP (by rw [← hx, h]; simp)
  have hb0 : x * c ≠ 0 := mul_ne_zero hx0 hc0
  have hxc : ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) = x * c := rfl
  have hmem : ∀ {s : MRing ι} {W}, IsMultiHomog s a → s ∉ P → IsClosedPt W → P ≤ W → (W ∈ divSupp P s ↔ s ∈ W) :=
    fun hs hsP hWc hPW => (hC K ι P _ a _ hP hs hsP).trans ⟨fun h => h.2.2, fun h => ⟨hWc, hPW, h⟩⟩
  have key : ∀ W, IsClosedPt W → P ≤ W →
      (if W ∈ divSupp P f then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yf W))) else 0) -
          (if W ∈ divSupp P g then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yg W))) else 0) =
        Real.log (Nat.card (locRing P W ⧸ locIdeal P W ((x * c : funField P) : FractionRing (MRing ι ⧸ P)))) -
          Real.log (Nat.card (locRing P W ⧸ locIdeal P W (c : FractionRing (MRing ι ⧸ P)))) := by
    intro W hWc hPW
    obtain ⟨hcS, hbS⟩ := hcW W hWc hPW
    by_cases hU : W ∈ divSupp P f ∪ divSupp P g
    · obtain ⟨htW, htn, hyf, hyg⟩ := ht W hU
      have hyfS := frac_mem_locRing hPW hf htW htn hyf
      have hygS := frac_mem_locRing hPW hg htW htn hyg
      have hyf0 : yf W ≠ 0 := fun h => hφ f hfP (by rw [← hyf, h, zero_mul])
      have hyg0 : yg W ≠ 0 := fun h => hφ g hgP (by rw [← hyg, h, zero_mul])
      have hrel : yf W = x * yg W :=
        mul_right_cancel₀ (hφ _ fun h => htn (hPW h)) (by rw [hyf, mul_assoc, hyg, hx])
      obtain ⟨s, hs, hsP, hWs⟩ : ∃ s, IsMultiHomog s a ∧ s ∉ P ∧ W ∈ divSupp P s := by
        rcases hU with h | h
        exacts [⟨f, hf, hfP, h⟩, ⟨g, hg, hgP, h⟩]
      have fin : ∀ y, y ∈ locRing P W → y ≠ 0 → Finite (locRing P W ⧸ locIdeal P W y) :=
        fun y hy hy0 => hF K ι P s a W y hP hs hsP hWs hy hy0
      have hc0' : (c : FractionRing (MRing ι ⧸ P)) ≠ 0 := fun h => hc0 (Subtype.ext h)
      have hb0' : ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) ≠ 0 := fun h => hb0 (Subtype.ext h)
      have e : yf W * c = ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) * yg W := by
        rw [hrel, hxc]; ring
      have hm := log_card_locIdeal_mul hyfS hcS hyf0 (fin _ hyfS hyf0) (fin _ hcS hc0')
      have hm' := log_card_locIdeal_mul hbS hygS hb0' (fin _ hbS hb0') (fin _ hygS hyg0)
      rw [e] at hm
      by_cases h1 : W ∈ divSupp P f <;> by_cases h2 : W ∈ divSupp P g
      · rw [if_pos h1, if_pos h2]; linarith
      · obtain ⟨-, z, hz, hz1⟩ := frac_unit_locRing hPW hg htW (fun h => h2 ((hmem hg hgP hWc hPW).mpr h)) htn hyg
        have := log_card_locIdeal_unit hygS hz hz1
        rw [if_pos h1, if_neg h2]; linarith
      · obtain ⟨-, z, hz, hz1⟩ := frac_unit_locRing hPW hf htW (fun h => h1 ((hmem hf hfP hWc hPW).mpr h)) htn hyf
        have := log_card_locIdeal_unit hyfS hz hz1
        rw [if_neg h1, if_pos h2]; linarith
      · exact absurd hU (by simp [h1, h2])
    · have h1 : W ∉ divSupp P f := fun h => hU (Or.inl h)
      have h2 : W ∉ divSupp P g := fun h => hU (Or.inr h)
      obtain ⟨hxS, z, hz, hz1⟩ := frac_unit_locRing hPW hf hg (fun h => h1 ((hmem hf hfP hWc hPW).mpr h))
        (fun h => h2 ((hmem hg hgP hWc hPW).mpr h)) hx
      rw [if_neg h1, if_neg h2, hxc, log_card_locIdeal_unit_mul hxS hz hz1 hcS]
      ring
  obtain ⟨hbfin, hbsum⟩ := hR K ι P (x * c) hP hb0 (fun W h1 h2 => (hcW W h1 h2).2)
  obtain ⟨hcfin, hcsum⟩ := hR K ι P c hP hc0 (fun W h1 h2 => (hcW W h1 h2).1)
  have eq1 : ∀ (s : MRing ι) (y : Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)),
      ∑ᶠ W ∈ divSupp P s, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) =
        ∑ᶠ W, (if W ∈ divSupp P s then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) else 0) := by
    intro s y
    rw [finsum_mem_def]
    rfl
  have fsA : ∀ (s : MRing ι) (y : Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)),
      (Function.support fun W =>
        if W ∈ divSupp P s then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) else 0).Finite :=
    fun s y => (divSupp_finite P s).subset fun W hW => by
      by_contra h
      exact hW (if_neg h)
  have fsB : ∀ z : FractionRing (MRing ι ⧸ P),
      {W | IsClosedPt W ∧ P ≤ W ∧ Nat.card (locRing P W ⧸ locIdeal P W z) ≠ 1}.Finite →
      (Function.support ({W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
        fun W => Real.log (Nat.card (locRing P W ⧸ locIdeal P W z)))).Finite :=
    fun z hz => hz.subset fun W hW => by
      rw [Function.mem_support] at hW
      by_cases hWC : W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}
      · rw [Set.indicator_of_mem hWC] at hW
        exact ⟨hWC.1, hWC.2, fun h1 => hW (by rw [h1]; simp)⟩
      · rw [Set.indicator_of_notMem hWC] at hW
        exact absurd rfl hW
  obtain ⟨hFld, hNF⟩ := hN K ι P hP
  let _ := hFld.toField
  have hσ : ∀ y : funField P, y ≠ 0 → ∀ σ : funField P →+* ℂ, σ y ≠ 0 := fun y hy σ h => by
    obtain ⟨z, hz⟩ := hFld.mul_inv_cancel hy
    have := congrArg σ hz
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  calc _ = ∑ᶠ W, ((if W ∈ divSupp P f then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yf W))) else 0) -
          (if W ∈ divSupp P g then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yg W))) else 0)) := by
        rw [eq1 f yf, eq1 g yg, finsum_sub_distrib (fsA f yf) (fsA g yg)]
    _ = ∑ᶠ W, ({W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
            (fun W => Real.log (Nat.card (locRing P W ⧸
              locIdeal P W ((x * c : funField P) : FractionRing (MRing ι ⧸ P))))) W -
          {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
            (fun W => Real.log (Nat.card (locRing P W ⧸ locIdeal P W (c : FractionRing (MRing ι ⧸ P))))) W) := by
        refine finsum_congr fun W => ?_
        by_cases hWC : W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}
        · rw [Set.indicator_of_mem hWC, Set.indicator_of_mem hWC]
          exact key W hWC.1 hWC.2
        · rw [Set.indicator_of_notMem hWC, Set.indicator_of_notMem hWC,
            if_neg fun h => hWC ⟨((hC K ι P f a W hP hf hfP).mp h).1, ((hC K ι P f a W hP hf hfP).mp h).2.1⟩,
            if_neg fun h => hWC ⟨((hC K ι P g a W hP hg hgP).mp h).1, ((hC K ι P g a W hP hg hgP).mp h).2.1⟩]
    _ = ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ (x * c)‖ - ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ c‖ := by
        rw [finsum_sub_distrib (fsB _ hbfin) (fsB _ hcfin), ← finsum_mem_def, ← finsum_mem_def, hbsum, hcsum]
    _ = _ := by
        rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
        refine finsum_congr fun σ => ?_
        rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hσ x hx0 σ)) (norm_ne_zero_iff.mpr (hσ c hc0 σ))]
        ring

end

end GroundTheory.Heights₂.Heights.Inter
