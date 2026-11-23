import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechHOneInj

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem hom_eq {a b : (NE κ)ᵒᵖ} (f f' : a ⟶ b) : f = f' :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem mp_transport0 (g : C0 F) {a a' b : (NE κ)ᵒᵖ} (e : a = a') (f : a ⟶ b) (f' : a' ⟶ b) :
    mp F f (g a) = mp F f' (g a') := by
  subst e; rw [hom_eq f f']

theorem mp_transport1 {p : ℕ} (x : CC F p) {s s' : {s : Finset κ // s.card = p + 1}} (e : s = s')
    {b : (NE κ)ᵒᵖ} (f : ne s.1 (card_nonempty s) ⟶ b) (f' : ne s'.1 (card_nonempty s') ⟶ b) :
    mp F f (x s) = mp F f' (x s') := by
  subst e; rw [hom_eq f f']

theorem ne_eq_ne {s s' : Finset κ} (hs : s.Nonempty) (hs' : s'.Nonempty) (e : s = s') :
    ne s hs = ne s' hs' := by
  subst e; rfl

theorem min'_pair {i j : κ} (h : i < j) : ({i, j} : Finset κ).min' (Finset.insert_nonempty _ _) = i :=
  le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self _ _))
    (Finset.le_min' _ _ _ (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> [exact le_rfl; exact h.le]))

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (z : CC F 1) {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) :
    e1 F z a b f = if h : mn b < mn a then
      -(mp F (homOf (a := ne {mn b, mn a} (Finset.insert_nonempty _ _)) (b := b) (pair_subset f))
        (z ⟨{mn b, mn a}, Finset.card_pair h.ne⟩)) else 0 := by
  simp only [e1, LinearMap.pi_apply]; split_ifs <;> simp

end GlobalTheory.CechHOneInj

namespace GlobalTheory.CechHOneInj

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem δ_pair (z : CC F 1) (g : C0 F) (hg : e1 F z = d0 F g) {i j : κ} (h : i < j)
    (hs : ({i, j} : Finset κ).card = 1 + 1) :
    δ F 0 (fun s => g (ne s.1 (card_nonempty s))) ⟨{i, j}, hs⟩ = z ⟨{i, j}, hs⟩ := by
  have hi : i ∈ ({i, j} : Finset κ) := Finset.mem_insert_self _ _
  have hj : j ∈ ({i, j} : Finset κ) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have sij : ({i} : Finset κ) ⊆ {i, j} := Finset.singleton_subset_iff.2 hi
  have sji : ({j} : Finset κ) ⊆ {i, j} := Finset.singleton_subset_iff.2 hj
  have ei : ({i, j} : Finset κ).erase i = {j} := Finset.erase_insert (by simp [h.ne])
  have ej : ({i, j} : Finset κ).erase j = {i} := by
    ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl⟩
      · rfl
      · exact absurd rfl hx
    · rintro rfl; exact ⟨h.ne, Or.inl rfl⟩
  have h1 := congrFun (congrFun (congrFun hg (ne {i} (Finset.singleton_nonempty _)))
    (ne {i, j} (Finset.insert_nonempty _ _))) (homOf sij)
  have h2 := congrFun (congrFun (congrFun hg (ne {j} (Finset.singleton_nonempty _)))
    (ne {i, j} (Finset.insert_nonempty _ _))) (homOf sji)
  have mi : mn (ne ({i} : Finset κ) (Finset.singleton_nonempty _)) = i := Finset.min'_singleton i
  have mj : mn (ne ({j} : Finset κ) (Finset.singleton_nonempty _)) = j := Finset.min'_singleton j
  have mij : mn (ne ({i, j} : Finset κ) (Finset.insert_nonempty _ _)) = i := min'_pair h
  rw [orderedCechToCatCochainsOne_apply_valueAtSubset, amitsur_d0_apply, dif_neg (by rw [mi, mij]; exact lt_irrefl i)] at h1
  rw [orderedCechToCatCochainsOne_apply_valueAtSubset, amitsur_d0_apply, dif_pos (by rw [mj, mij]; exact h)] at h2
  have key := mp_transport1 F z
    (s := ⟨{mn (ne {i, j} (Finset.insert_nonempty _ _)), mn (ne {j} (Finset.singleton_nonempty _))},
      Finset.card_pair (by rw [mj, mij]; exact h.ne)⟩) (s' := ⟨{i, j}, hs⟩)
    (Subtype.ext (by simp only [mj, mij])) (homOf (pair_subset (homOf sji))) (𝟙 _)
  rw [mp_id] at key
  have si : GlobalTheory.cubeSign ({i, j} : Finset κ) i = 1 :=
    GlobalTheory.cubeSign_eq_one_of_forall_le (by
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact le_rfl
      · exact h.le)
  have sj : GlobalTheory.cubeSign ({i, j} : Finset κ) j = -1 := by
    have := GlobalTheory.cubeSign_erase_of_lt hi h (t := ({i, j} : Finset κ))
    rw [ei, GlobalTheory.cubeSign_singleton] at this
    linarith
  rw [δ_apply, Fintype.sum_eq_add ⟨i, hi⟩ ⟨j, hj⟩ (by simp [h.ne]) (by
    rintro ⟨x, hx⟩ ⟨ha, hb⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact absurd rfl ha
    · exact absurd rfl hb)]
  dsimp only
  have tj := mp_transport0 F g (ne_eq_ne _ (Finset.singleton_nonempty j) ei)
    (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx (⟨{i, j}, hs⟩ : {s : Finset κ // s.card = 1 + 1}) ⟨i, hi⟩)))
      (b := ne {i, j} (Finset.insert_nonempty _ _)) (Finset.erase_subset _ _))
    (homOf (a := ne {j} (Finset.singleton_nonempty j)) (b := ne {i, j} (Finset.insert_nonempty _ _)) sji)
  have ti := mp_transport0 F g (ne_eq_ne _ (Finset.singleton_nonempty i) ej)
    (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx (⟨{i, j}, hs⟩ : {s : Finset κ // s.card = 1 + 1}) ⟨j, hj⟩)))
      (b := ne {i, j} (Finset.insert_nonempty _ _)) (Finset.erase_subset _ _))
    (homOf (a := ne {i} (Finset.singleton_nonempty i)) (b := ne {i, j} (Finset.insert_nonempty _ _)) sij)
  rw [si, sj, one_smul, neg_smul, one_smul]
  linear_combination h2 - h1 + key + tj - ti

theorem exists_cech_primitive : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (z : CC F 1), δ F 1 z = 0 →
    ∀ g : C0 F, e1 F z = d0 F g → ∃ c : CC F 0, δ F 0 c = z := by
  intro κ _ R _ F z _ g hg
  refine ⟨fun s => g (ne s.1 (card_nonempty s)), ?_⟩
  funext t
  obtain ⟨s, hs⟩ := t
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hs
  rcases lt_or_gt_of_ne hij with h | h
  · exact δ_pair F z g hg h hs
  · revert hs
    rw [Finset.pair_comm i j]
    exact δ_pair F z g hg h

end GlobalTheory.CechHOneInj
