import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationIndependentOfChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCombinationSquareZeroLiftsChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartSpecMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAwaySpanEqTop

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue.Cocycle

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (a : A →+* B) (b : B →+* C) : spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp]; rfl

theorem awayMap_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (r : R) : Function.Surjective (Localization.awayMap π r) := by
  intro y
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (π r)) y
  obtain ⟨b, rfl⟩ := hπ a
  refine ⟨IsLocalization.mk' _ b (⟨r ^ m, m, rfl⟩ : Submonoid.powers r), ?_⟩
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk']
  congr 1
  ext
  simp

theorem ker_awayMap_le {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (r : R) :
    RingHom.ker (Localization.awayMap π r) ≤
      (RingHom.ker π).map (algebraMap R (Localization.Away r)) := by
  intro x hx
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) x
  rw [RingHom.mem_ker] at hx
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk'] at hx
  rw [IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨_, p, rfl⟩, hp⟩ := hx
  rw [IsLocalization.mk'_mem_map_algebraMap_iff]
  refine ⟨r ^ p, ⟨p, rfl⟩, ?_⟩
  rw [RingHom.mem_ker, map_mul, map_pow]
  exact hp

theorem ker_awayMap_sq {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (h2 : RingHom.ker π ^ 2 = ⊥) (r : R) :
    RingHom.ker (Localization.awayMap π r) ^ 2 = ⊥ := by
  refine le_bot_iff.1 ((Ideal.pow_right_mono (ker_awayMap_le π r) 2).trans ?_)
  rw [← Ideal.map_pow, h2, Ideal.map_bot]

theorem isCombIn_restrict_chart {Y : Scheme.{0}} {V V' : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') {S T S' : Type} [CommRing S] [CommRing T] [CommRing S']
    (q : S →+* T) (hq : Function.Surjective q) (h2 : RingHom.ker q ^ 2 = ⊥) (g : S →+* S')
    {ι : Type} [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S)
    (hw : ∀ i, spMap q ≫ w i = spMap q ≫ u) (hC : IsCombIn V u c w a)
    (hu : (spMap g ≫ u) ⁻¹ᵁ V' = ⊤) :
    IsCombIn V' (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  let J : Ideal S' := (RingHom.ker q).map g
  have hle : RingHom.ker q ≤ RingHom.ker ((Ideal.Quotient.mk J).comp g) := by
    intro x hx
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem g hx
  let g' : T →+* S' ⧸ J := RingHom.liftOfSurjective q hq ⟨(Ideal.Quotient.mk J).comp g, hle⟩
  have hg' : g'.comp q = (Ideal.Quotient.mk J).comp g := RingHom.liftOfSurjective_comp q hq _
  refine GlobalTheory.T.isAffineCombination_independent_of_chart Y V V' hV hV' S' (S' ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    ?_ ι _ _ _ _ (fun i => ?_) (isCombIn_spMap_comp Y V S S' g ι u c w a hC) hu
  · rw [Ideal.mk_ker, ← Ideal.map_pow, h2, Ideal.map_bot]
  · rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, ← hg', ← spMap_comp_spMap,
      Category.assoc, Category.assoc, hw i]

theorem eq_of_cocycle {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) {S : Type} [CommRing S]
    {κ : Type} [Fintype κ] (u u' c c' : Sp S ⟶ Y) (w w' : κ → (Sp S ⟶ Y)) (a b : κ → S)
    (hab : ∑ k, a k * b k = 1) (h : IsCombIn W u c w a) (h' : IsCombIn W u' c' w' a)
    (hco : ∀ k, IsCombIn W u' (w k) ![w' k, u] ![1, 1 - b k]) : c = c' := by
  obtain ⟨hu, hc, hw, e⟩ := h
  obtain ⟨hu', hc', hw', e'⟩ := h'
  refine eq_of_chartHom_eq hW c c' hc hc' fun x => ?_
  have key : ∀ k, chartHom W (w k) (hw k) x - chartHom W u hu x =
      (chartHom W (w' k) (hw' k) x - chartHom W u' hu' x) -
        b k * (chartHom W u hu x - chartHom W u' hu' x) := by
    intro k
    obtain ⟨_, _, _, e''⟩ := hco k
    have := e'' x
    rw [Fin.sum_univ_two] at this
    have this' : chartHom W (w k) (hw k) x = chartHom W u' hu' x +
        (1 * (chartHom W (w' k) (hw' k) x - chartHom W u' hu' x) +
          (1 - b k) * (chartHom W u hu x - chartHom W u' hu' x)) := this
    rw [this']; ring
  rw [e x, e' x]
  simp only [key, mul_sub (a _) (_ - _), Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hab]
  ring

theorem exists_lifts_agree_of_cocycle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Fintype κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ (V : κ → X.left.Opens), (∀ k, IsAffineOpen (V k)) →
    ∀ (e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left),
    (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) →
    (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) →
    (∀ k, e k ⁻¹ᵁ V k = ⊤) →
    ∀ (N : ℕ) (t : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
    (∀ k j, t k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) →
    (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) →
    (∀ k j, t k j ⁻¹ᵁ V j = ⊤) →
    ∀ (n : κ → κ → ℕ) (s : ∀ j l, Fin (n j l) → Localization.Away (f j * f l)) (W : ∀ j l, Fin (n j l) → X.left.Opens),
    (∀ j l, Ideal.span (Set.range (s j l)) = ⊤) → (∀ j l i, IsAffineOpen (W j l i)) →
    (∀ j l i, (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j) ⁻¹ᵁ W j l i = ⊤) →
    (∀ j l k i, GlobalTheory.SecGlue.IsCombIn (W j l i) (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ e l)
        (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ t k j)
        ![spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ t k l, spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j]
        ![1, 1 - algebraMap R (Localization.Away (s j l i)) (f k) ^ (N)]) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by
  intro R R₀ _ _ π hπ h2 X g₀ hg₀ κ _ f hf V hV e he he₀ heV N t ht ht₀ htV n s W hs hW heW hco
  have hpow : Ideal.span (Set.range fun k => f k ^ N) = ⊤ := by
    have := Ideal.span_pow_eq_top _ hf N
    rwa [← Set.range_comp] at this
  obtain ⟨a, ha⟩ : ∃ a : κ → R, ∑ k, a k * f k ^ N = 1 :=
    Ideal.mem_span_range_iff_exists_fun.1 (hpow ▸ Submodule.mem_top)
  have hte : ∀ j k, spMap (Localization.awayMap π (f j)) ≫ t k j =
      spMap (Localization.awayMap π (f j)) ≫ e j := fun j k => (ht₀ k j).trans (he₀ j).symm
  choose c hc hc₀ hcp using fun j => GlobalTheory.T.exists_affineCombination_squareZero_lifts_chart X.left (V j) (hV j) _ _
    (Localization.awayMap π (f j)) (awayMap_surjective π hπ _) (ker_awayMap_sq π h2 _) κ (e j)
    (fun k => t k j) (fun k => algebraMap R _ (a k)) (heV j) (hte j)
  refine ⟨c, fun j => (hcp j R X.hom fun k => (ht k j).trans (he j).symm).trans (he j),
    fun j => (hc₀ j).trans (he₀ j), fun j l => ?_⟩
  refine hom_ext_of_span_eq_top _ _ (s j l) (hs j l) _ _ _ fun i => ?_
  obtain ⟨hlW, -⟩ := hco j l j i
  have hjW := heW j l i
  rw [← Category.assoc, spMap_comp_spMap] at hlW hjW
  have h₁ := isCombIn_restrict_chart (hV j) (hW j l i) _ (awayMap_surjective π hπ _)
    (ker_awayMap_sq π h2 _) _ _ _ _ _ (hte j) (hc j) hjW
  have h₂ := isCombIn_restrict_chart (hV l) (hW j l i) _ (awayMap_surjective π hπ _)
    (ker_awayMap_sq π h2 _) _ _ _ _ _ (hte l) (hc l) hlW
  simp only [RingHom.comp_apply, IsLocalization.Away.awayToAwayRight_eq,
    IsLocalization.Away.awayToAwayLeft_eq, ← IsScalarTower.algebraMap_apply,
    ← spMap_comp_spMap, Category.assoc] at h₁ h₂
  refine eq_of_cocycle (hW j l i) _ _ _ _ _ _ _
    (fun k => algebraMap R (Localization.Away (s j l i)) (f k) ^ N) ?_ h₁ h₂ fun k => hco j l k i
  simp only [← map_pow, ← map_mul, ← map_sum, ha, map_one]

end GlobalTheory.SecGlue.Cocycle
