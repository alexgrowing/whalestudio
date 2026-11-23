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

noncomputable section

namespace GlobalTheory.CechPoset

namespace CechPosetH2Surjective

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

def wv (w : C2 F) (a b d : (NE κ)ᵒᵖ) : F.obj d :=
  if h : sub a ⊆ sub b ∧ sub b ⊆ sub d then w a b d (homOf h.1) (homOf h.2) else 0

theorem wv_eq (w : C2 F) {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) : wv w a b d = w a b d f g := by
  rw [wv, dif_pos ⟨sub_subset f, sub_subset g⟩]
  congr 1 <;> exact Subsingleton.elim _ _

theorem wv_cocycle (w : Z2 F) {a b d e : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) (h : d ⟶ e) :
    mp F h (wv w.1 a b d) + wv w.1 a d e = wv w.1 a b e + wv w.1 b d e := by
  rw [wv_eq _ f g, wv_eq _ (f ≫ g) h, wv_eq _ f (g ≫ h), wv_eq _ g h]
  exact w.2 f g h

abbrev pt (i : κ) : (NE κ)ᵒᵖ := ne {i} (Finset.singleton_nonempty i)

abbrev pa (i j : κ) : (NE κ)ᵒᵖ := ne {i, j} (Finset.insert_nonempty _ _)

def u (w : C2 F) (i j : κ) (x : (NE κ)ᵒᵖ) : F.obj x := wv w (pt i) (pa i j) x - wv w (pt j) (pa i j) x

def V (w : C2 F) (i j k : κ) (x : (NE κ)ᵒᵖ) : F.obj x := u w i j x - u w i k x + u w j k x

theorem pa_subset {i j : κ} {t : (NE κ)ᵒᵖ} (hi : i ∈ sub t) (hj : j ∈ sub t) :
    ({i, j} : Finset κ) ⊆ sub t := by
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl <;> assumption

theorem u_res (w : Z2 F) {i j : κ} {t x : (NE κ)ᵒᵖ} (hi : i ∈ sub t) (hj : j ∈ sub t) (φ : t ⟶ x) :
    u w.1 i j x = mp F φ (u w.1 i j t) + wv w.1 (pt i) t x - wv w.1 (pt j) t x := by
  have e1 := wv_cocycle w (homOf (a := pt i) (b := pa i j) (by simp)) (homOf (a := pa i j) (b := t) (pa_subset hi hj)) φ
  have e2 := wv_cocycle w (homOf (a := pt j) (b := pa i j) (by simp)) (homOf (a := pa i j) (b := t) (pa_subset hi hj)) φ
  simp only [u, map_sub]
  linear_combination -e1 + e2

theorem V_res (w : Z2 F) {i j k : κ} {t x : (NE κ)ᵒᵖ} (hi : i ∈ sub t) (hj : j ∈ sub t) (hk : k ∈ sub t)
    (φ : t ⟶ x) : mp F φ (V w.1 i j k t) = V w.1 i j k x := by
  simp only [V, map_add, map_sub, u_res w hi hj φ, u_res w hi hk φ, u_res w hj hk φ]
  ring

theorem pt_hom (a : (NE κ)ᵒᵖ) : sub (pt (mn a)) ⊆ sub a := Finset.singleton_subset_iff.2 (mn_mem a)

def fc (w : C2 F) : C1 F := fun a b _ => wv w (pt (mn a)) a b - u w (mn a) (mn b) b

theorem posetTwoCocycle_sub_correcting_coboundary (w : Z2 F) {a b d : (NE κ)ᵒᵖ} (φ : a ⟶ b) (ψ : b ⟶ d) :
    w.1 a b d φ ψ - d1 F (fc w.1) a b d φ ψ = V w.1 (mn a) (mn b) (mn d) d := by
  have ha : mn a ∈ sub b := sub_subset φ (mn_mem a)
  have hb : mn b ∈ sub b := mn_mem b
  have hq := pa_subset ha hb
  have c1 := wv_cocycle w (homOf (a := pt (mn a)) (pt_hom a)) φ ψ
  have c3 := wv_cocycle w (homOf (a := pt (mn a)) (b := pa (mn a) (mn b)) (by simp))
    (homOf (a := pa (mn a) (mn b)) (b := b) hq) ψ
  have c4 := wv_cocycle w (homOf (a := pt (mn b)) (b := pa (mn a) (mn b)) (by simp))
    (homOf (a := pa (mn a) (mn b)) (b := b) hq) ψ
  rw [d1_apply, ← wv_eq w.1 φ ψ]
  simp only [fc, V, u, map_sub]
  linear_combination -c1 + c3 - c4

theorem V_self_left (w : C2 F) (i k : κ) (x : (NE κ)ᵒᵖ) : V w i i k x = 0 := by simp [V, u]

theorem V_self_right (w : C2 F) (i j : κ) (x : (NE κ)ᵒᵖ) : V w i j j x = 0 := by simp [V, u]

def mid3 (t : Finset κ) (h : t.card = 2 + 1) : κ :=
  (t.erase (t.min' (Finset.card_pos.1 (by omega)))).min'
    (Finset.card_pos.1 (by rw [Finset.card_erase_of_mem (Finset.min'_mem _ _), h]; omega))

theorem tri {t : Finset κ} {i j k : κ} (e : t = {i, j, k}) (hij : i < j) (hjk : j < k)
    (h : t.card = 2 + 1) (hne : t.Nonempty) :
    t.min' hne = i ∧ mid3 t h = j ∧ t.max' hne = k := by
  subst e
  have hmin : ({i, j, k} : Finset κ).min' hne = i := by
    refine le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ ?_)
    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> order
  refine ⟨hmin, ?_, ?_⟩
  · unfold mid3
    have e : ({i, j, k} : Finset κ).erase (({i, j, k} : Finset κ).min' (Finset.card_pos.1 (by omega))) = {j, k} := by
      rw [hmin, Finset.erase_insert (by simp [hij.ne, (hij.trans hjk).ne])]
    have key : ∀ (s : Finset κ) (hs : s.Nonempty), s = {j, k} → s.min' hs = j := by
      intro s hs es; subst es
      refine le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ ?_)
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> order
    exact key _ _ e
  · refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (by simp))
    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> order

def yc (w : C2 F) : CC F 2 := fun t =>
  -V w (t.1.max' (card_nonempty t)) (mid3 t.1 t.2) (t.1.min' (card_nonempty t)) (ne t.1 (card_nonempty t))

theorem alternatingToOrderedCech_cechTwoCochainOfPoset (w : Z2 F) {a b d : (NE κ)ᵒᵖ} (φ : a ⟶ b) (ψ : b ⟶ d) :
    e2 F (yc w.1) a b d φ ψ = V w.1 (mn a) (mn b) (mn d) d := by
  simp only [e2, LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply, yc]
    obtain ⟨h1, h2, h3⟩ := tri (t := ({mn d, mn b, mn a} : Finset κ)) rfl h.1 h.2 (card_three h.1 h.2)
      (Finset.insert_nonempty _ _)
    rw [h1, h2, h3, map_neg, neg_neg]
    have hs := triple_subset φ ψ
    have V' := V_res w (i := mn a) (j := mn b) (k := mn d) (t := ne {mn d, mn b, mn a} (Finset.insert_nonempty _ _))
      (show mn a ∈ ({mn d, mn b, mn a} : Finset κ) by simp) (show mn b ∈ ({mn d, mn b, mn a} : Finset κ) by simp)
      (show mn d ∈ ({mn d, mn b, mn a} : Finset κ) by simp) (homOf hs)
    exact V'
  · have hdb := mn_le_of_hom ψ
    have hba := mn_le_of_hom φ
    rw [LinearMap.zero_apply]
    rcases (not_and_or.1 h) with h' | h'
    · rw [le_antisymm (not_lt.1 h') hdb, V_self_right]
    · rw [le_antisymm (not_lt.1 h') hba, V_self_left]

theorem four {S : Finset κ} (hS : S.card = 2 + 1 + 1) :
    ∃ i0 i1 i2 i3 : κ, i0 < i1 ∧ i1 < i2 ∧ i2 < i3 ∧ S = {i0, i1, i2, i3} := by
  let e := S.orderEmbOfFin hS
  refine ⟨e 0, e 1, e 2, e 3, e.strictMono (by decide), e.strictMono (by decide),
    e.strictMono (by decide), ?_⟩
  ext y
  have hr := Finset.range_orderEmbOfFin S hS
  constructor
  · intro hy
    have : y ∈ Set.range e := by rw [hr]; exact hy
    obtain ⟨k, rfl⟩ := this
    fin_cases k <;> simp
  · intro hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    have mem : ∀ k, e k ∈ S := fun k => by
      have : e k ∈ Set.range e := ⟨k, rfl⟩
      rw [hr] at this; exact this
    rcases hy with rfl | rfl | rfl | rfl <;> exact mem _

theorem yc_term (w : Z2 F) (t : {s : Finset κ // s.card = 2 + 1 + 1}) (x : t.1) {i j k : κ}
    (e : t.1.erase x.1 = {i, j, k}) (hij : i < j) (hjk : j < k) :
    mp F (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx t x))) (b := ne _ (card_nonempty t))
      (Finset.erase_subset x.1 t.1)) (yc w.1 (GlobalTheory.Cube.eraseIdx t x)) =
      -V w.1 k j i (ne t.1 (card_nonempty t)) := by
  obtain ⟨h1, h2, h3⟩ := tri (t := (GlobalTheory.Cube.eraseIdx t x).1) e hij hjk (GlobalTheory.Cube.eraseIdx t x).2
    (card_nonempty (GlobalTheory.Cube.eraseIdx t x))
  simp only [yc]
  rw [h1, h2, h3, map_neg]
  have mem : ∀ y ∈ ({i, j, k} : Finset κ), y ∈ sub (ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx t x))) := by
    intro y hy; show y ∈ t.1.erase x.1; rw [e]; exact hy
  rw [V_res w (mem k (by simp)) (mem j (by simp)) (mem i (by simp))]

theorem erase4 {i0 i1 i2 i3 : κ} (h01 : i0 < i1) (h12 : i1 < i2) (h23 : i2 < i3) :
    ({i0, i1, i2, i3} : Finset κ).erase i0 = {i1, i2, i3} ∧
    ({i0, i1, i2, i3} : Finset κ).erase i1 = {i0, i2, i3} ∧
    ({i0, i1, i2, i3} : Finset κ).erase i2 = {i0, i1, i3} ∧
    ({i0, i1, i2, i3} : Finset κ).erase i3 = {i0, i1, i2} := by
  have := h01.ne; have := h12.ne; have := h23.ne; have := (h01.trans h12).ne; have := (h12.trans h23).ne
  have := (h01.trans (h12.trans h23)).ne
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext y; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    grind

theorem sign4 {i0 i1 i2 i3 : κ} (h01 : i0 < i1) (h12 : i1 < i2) (h23 : i2 < i3) :
    GlobalTheory.cubeSign ({i0, i1, i2, i3} : Finset κ) i0 = 1 ∧ GlobalTheory.cubeSign ({i0, i1, i2, i3} : Finset κ) i1 = -1 ∧
    GlobalTheory.cubeSign ({i0, i1, i2, i3} : Finset κ) i2 = 1 ∧ GlobalTheory.cubeSign ({i0, i1, i2, i3} : Finset κ) i3 = -1 := by
  have h02 := h01.trans h12; have h13 := h12.trans h23; have h03 := h01.trans h13
  simp [GlobalTheory.cubeSign, Finset.filter_insert, h01, h12, h23, h02, h13, h03, not_lt.2 h01.le,
    not_lt.2 h12.le, not_lt.2 h23.le, not_lt.2 h02.le, not_lt.2 h13.le, not_lt.2 h03.le,
    Finset.filter_singleton, h01.ne, h12.ne, h23.ne, h02.ne, h13.ne, h03.ne, lt_irrefl]

theorem δ_yc (w : Z2 F) : δ F 2 (yc w.1) = 0 := by
  funext t
  obtain ⟨S, hS⟩ := t
  obtain ⟨i0, i1, i2, i3, h01, h12, h23, rfl⟩ := four hS
  rw [δ_apply, Pi.zero_apply]
  obtain ⟨e0, e1', e2', e3⟩ := erase4 h01 h12 h23
  obtain ⟨s0, s1, s2, s3⟩ := sign4 h01 h12 h23
  let T : {s : Finset κ // s.card = 2 + 1 + 1} := ⟨{i0, i1, i2, i3}, hS⟩
  let G : κ → F.obj (ne T.1 (card_nonempty T)) := fun y => if h : y ∈ T.1 then
    GlobalTheory.cubeSign T.1 y • mp F (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx T ⟨y, h⟩)))
      (b := ne _ (card_nonempty T)) (Finset.erase_subset y T.1)) (yc w.1 (GlobalTheory.Cube.eraseIdx T ⟨y, h⟩)) else 0
  have hG : ∀ y (h : y ∈ T.1) {i j k : κ}, T.1.erase y = {i, j, k} → i < j → j < k →
      G y = GlobalTheory.cubeSign T.1 y • -V w.1 k j i (ne T.1 (card_nonempty T)) := by
    intro y h i j k e hij hjk
    simp only [G, dif_pos h]
    rw [yc_term w T ⟨y, h⟩ e hij hjk]
  rw [show (∑ i : T.1, _) = ∑ i : T.1, G i from Finset.sum_congr rfl fun i _ => (dif_pos i.2).symm]
  rw [Finset.sum_coe_sort T.1 G]
  have m : ∀ y ∈ ({i0, i1, i2, i3} : Finset κ), y ∈ T.1 := fun _ h => h
  have h02 := h01.trans h12; have h13 := h12.trans h23; have h03 := h01.trans h13
  show ∑ y ∈ ({i0, i1, i2, i3} : Finset κ), G y = 0
  rw [Finset.sum_insert (by simp [h01.ne, h02.ne, h03.ne]), Finset.sum_insert (by simp [h12.ne, h13.ne]),
    Finset.sum_pair h23.ne]
  rw [hG i0 (m _ (by simp)) e0 h12 h23, hG i1 (m _ (by simp)) e1' h02 h23, hG i2 (m _ (by simp)) e2' h01 h13,
    hG i3 (m _ (by simp)) e3 h01 h12]
  simp only [T, s0, s1, s2, s3, V, one_smul, neg_smul]
  abel

end CechPosetH2Surjective

open CechPosetH2Surjective in

theorem posetTwoCocycle_eq_cechImage_add_coboundary : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (w : Z2 F), ∃ y : CC F 2, δ F 2 y = 0 ∧ ∃ f : C1 F, w.1 - e2 F y = d1 F f := by
  intro κ _ R _ F w
  refine ⟨yc w.1, δ_yc w, fc w.1, ?_⟩
  funext a b d φ ψ
  simp only [Pi.sub_apply]
  rw [alternatingToOrderedCech_cechTwoCochainOfPoset w φ ψ, ← posetTwoCocycle_sub_correcting_coboundary w φ ψ]
  ring

end GlobalTheory.CechPoset
