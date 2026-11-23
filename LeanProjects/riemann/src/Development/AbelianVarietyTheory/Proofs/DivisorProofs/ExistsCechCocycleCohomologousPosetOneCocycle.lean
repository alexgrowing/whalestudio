import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset.CechPosetH1Surjective

open GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem hom_eq {a b : (NE κ)ᵒᵖ} (φ ψ : a ⟶ b) : φ = ψ :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

noncomputable def V (f : Z1 F) (b : (NE κ)ᵒᵖ) (x : κ) : F.obj b :=
  if hx : x ∈ sub b then
    f.1 (ne {x} (Finset.singleton_nonempty x)) b
      (homOf (show ({x} : Finset κ) ⊆ sub b from Finset.singleton_subset_iff.2 hx))
  else 0

variable {F}

theorem V_res (f : Z1 F) {a b : (NE κ)ᵒᵖ} (φ : a ⟶ b) {x : κ} (hx : x ∈ sub a) :
    mp F φ (V F f a x) = V F f b x - f.1 a b φ := by
  unfold V
  rw [dif_pos hx, dif_pos (sub_subset φ hx)]
  have e := Z1.comp f (homOf (a := ne {x} (Finset.singleton_nonempty x)) (b := a)
    (Finset.singleton_subset_iff.2 hx)) φ
  rw [hom_eq (_ ≫ φ) (homOf (a := ne {x} (Finset.singleton_nonempty x)) (b := b)
    (Finset.singleton_subset_iff.2 (sub_subset φ hx)))] at e
  rw [e]
  ring

noncomputable def zc (f : Z1 F) : CC F 1 := fun t =>
  V F f (ne t.1 (card_nonempty t)) (t.1.min' (card_nonempty t)) -
    V F f (ne t.1 (card_nonempty t)) (t.1.max' (card_nonempty t))

theorem zc_res (f : Z1 F) (s : {s : Finset κ // s.card = 1 + 1}) (b : (NE κ)ᵒᵖ)
    (h : sub (ne s.1 (card_nonempty s)) ⊆ sub b) :
    mp F (homOf h) (zc f s) = V F f b (s.1.min' (card_nonempty s)) - V F f b (s.1.max' (card_nonempty s)) := by
  unfold zc
  rw [map_sub, V_res f (homOf h) (x := s.1.min' (card_nonempty s)) (Finset.min'_mem _ _),
    V_res f (homOf h) (x := s.1.max' (card_nonempty s)) (Finset.max'_mem _ _)]
  ring

theorem pair_min_max {s : Finset κ} {x y : κ} (hs : s = {x, y}) (h : x < y) (hne : s.Nonempty) :
    s.min' hne = x ∧ s.max' hne = y := by
  subst hs
  constructor
  · exact le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by
      intro z hz; simp at hz; rcases hz with rfl | rfl
      · exact le_rfl
      · exact h.le))
  · exact le_antisymm (Finset.max'_le _ _ _ (by
      intro z hz; simp at hz; rcases hz with rfl | rfl
      · exact h.le
      · exact le_rfl)) (Finset.le_max' _ _ (by simp))

theorem exists_triple {s : Finset κ} (h : s.card = 3) : ∃ a b c, a < b ∧ b < c ∧ s = {a, b, c} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 h
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  all_goals first
    | exact absurd (h1.trans h3) (not_lt.2 h2.le)
    | exact absurd (h2.trans h3) (not_lt.2 h1.le)
    | exact absurd (h1.trans h2) (not_lt.2 h3.le)
    | exact absurd (h3.trans h1) (not_lt.2 h2.le)
    | exact absurd (h2.trans h1) (not_lt.2 h3.le)
    | exact absurd (h3.trans h2) (not_lt.2 h1.le)
    | (refine ⟨x, y, z, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨x, z, y, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨y, x, z, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨y, z, x, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨z, x, y, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨z, y, x, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)

end GlobalTheory.CechPoset.CechPosetH1Surjective

namespace GlobalTheory.CechPoset.CechPosetH1Surjective
open GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem erase3 {a b c : κ} (hab : a < b) (hbc : b < c) :
    ({a, b, c} : Finset κ).erase a = {b, c} ∧ ({a, b, c} : Finset κ).erase b = {a, c} ∧
      ({a, b, c} : Finset κ).erase c = {a, b} := by
  have hac := hab.trans hbc
  refine ⟨?_, ?_, ?_⟩ <;> ext w <;> simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] <;>
    constructor
  all_goals first
    | (rintro ⟨hw, h | h | h⟩ <;> first | exact absurd h hw | (subst h; simp))
    | (rintro (h | h) <;> subst h <;> simp [hab.ne, hab.ne', hbc.ne, hbc.ne', hac.ne, hac.ne'])

theorem sign3 {a b c : κ} (hab : a < b) (hbc : b < c) :
    GlobalTheory.cubeSign ({a, b, c} : Finset κ) a = 1 ∧ GlobalTheory.cubeSign ({a, b, c} : Finset κ) b = -1 ∧
      GlobalTheory.cubeSign ({a, b, c} : Finset κ) c = 1 := by
  have hac := hab.trans hbc
  refine ⟨?_, ?_, ?_⟩ <;> simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, hab, hbc, hac,
    not_lt.2 hab.le, not_lt.2 hbc.le, not_lt.2 hac.le, Finset.card_pair hab.ne]

theorem part2 (f : Z1 F) : f.1 - e1 F (zc f) = d0 F (fun a => V F f a (mn a)) := by
  funext a b φ
  simp only [Pi.sub_apply, amitsur_d0_apply]
  rw [V_res f φ (mn_mem a)]
  by_cases h : mn b < mn a
  · have e : e1 F (zc f) a b φ = -(mp F (homOf (a := ne {mn b, mn a} (Finset.insert_nonempty _ _)) (b := b)
        (pair_subset φ)) (zc f ⟨{mn b, mn a}, Finset.card_pair h.ne⟩)) := by
      simp [e1, h]
    have z := zc_res f ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ b (pair_subset φ)
    obtain ⟨h1, h2⟩ := pair_min_max (s := ({mn b, mn a} : Finset κ)) rfl h (Finset.insert_nonempty _ _)
    rw [h1, h2] at z
    rw [e]
    linear_combination z
  · have e : e1 F (zc f) a b φ = 0 := by simp [e1, h]
    have e' : mn b = mn a := le_antisymm (mn_le_of_hom φ) (not_lt.1 h)
    rw [e, e']
    ring

end GlobalTheory.CechPoset.CechPosetH1Surjective

namespace GlobalTheory.CechPoset.CechPosetH1Surjective
open GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

def term3 {M : Type} [AddCommGroup M] (W : κ → M) (a b c x : κ) : M :=
  GlobalTheory.cubeSign ({a, b, c} : Finset κ) x • (if x = a then W b - W c else if x = b then W a - W c else W a - W b)

theorem sum3 {M : Type} [AddCommGroup M] (W : κ → M) {a b c : κ} (hab : a < b) (hbc : b < c) :
    ∑ x ∈ ({a, b, c} : Finset κ), term3 W a b c x = 0 := by
  have hac := hab.trans hbc
  rw [Finset.sum_insert (by simp [hab.ne, hac.ne]), Finset.sum_insert (by simp [hbc.ne]),
    Finset.sum_singleton]
  obtain ⟨s1, s2, s3⟩ := sign3 hab hbc
  simp only [term3, if_pos rfl, if_neg hab.ne', if_neg hac.ne', if_neg hbc.ne', s1, s2, s3, one_smul, neg_smul]
  norm_num

theorem part1 (f : Z1 F) : δ F 1 (zc f) = 0 := by
  funext t
  rw [δ_apply]
  obtain ⟨s, hs⟩ := t
  obtain ⟨a, b, c, hab, hbc, rfl⟩ := exists_triple (s := s) (by rw [hs])
  have hac := hab.trans hbc
  obtain ⟨e1', e2', e3'⟩ := erase3 hab hbc
  refine (Finset.sum_congr rfl
    (g := fun i : ({a, b, c} : Finset κ) => term3 (V F f (ne {a, b, c} (card_nonempty ⟨_, hs⟩))) a b c i.1)
    fun i _ => ?_).trans ?_
  · have z := zc_res f (GlobalTheory.Cube.eraseIdx ⟨{a, b, c}, hs⟩ i) (ne _ (card_nonempty ⟨_, hs⟩))
      (Finset.erase_subset i.1 _)
    rw [z]
    obtain ⟨x, hx⟩ := i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{x, b, c}, hs⟩ ⟨x, by simp⟩).1) e1' hbc
        (card_nonempty _)
      rw [h1, h2, term3, if_pos rfl]
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{a, x, c}, hs⟩ ⟨x, by simp⟩).1) e2' hac
        (card_nonempty _)
      rw [h1, h2, term3, if_neg hab.ne', if_pos rfl]
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{a, b, x}, hs⟩ ⟨x, by simp⟩).1) e3' hab
        (card_nonempty _)
      rw [h1, h2, term3, if_neg hac.ne', if_neg hbc.ne']
  · refine (Finset.sum_coe_sort ({a, b, c} : Finset κ)
      (term3 (V F f (ne {a, b, c} (card_nonempty ⟨_, hs⟩))) a b c)).trans ?_
    exact sum3 _ hab hbc

end GlobalTheory.CechPoset.CechPosetH1Surjective

open GlobalTheory.CechPoset.CechPosetH1Surjective in

theorem GlobalTheory.CechPoset.exists_cech_cocycle_cohomologous : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (f : Z1 F),
    ∃ z : CC F 1, δ F 1 z = 0 ∧ ∃ g : C0 F, f.1 - e1 F z = d0 F g :=
  fun F f => ⟨zc f, part1 f, fun a => V F f a (mn a), part2 f⟩
