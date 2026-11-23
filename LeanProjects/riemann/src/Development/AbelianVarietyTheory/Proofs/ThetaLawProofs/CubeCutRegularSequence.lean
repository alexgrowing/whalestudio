import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars

open CategoryTheory GlobalTheory

namespace GlobalTheory

namespace CubeCut

variable {K : Type} [CommRing K] {I : Type} [LinearOrder I]

def ExactMod (A : Cube.{0} I K) (J : ∀ s, Submodule K (A.obj s)) : Prop :=
  (∀ x : Cube.Term A 0, (∀ s, Cube.d A 0 x s ∈ J s.1) → ∀ s, x s ∈ J s.1) ∧
    ∀ (p : ℕ) (x : Cube.Term A (p + 1)), (∀ s, Cube.d A (p + 1) x s ∈ J s.1) →
      ∃ y : Cube.Term A p, ∀ s, (x - Cube.d A p y) s ∈ J s.1

theorem d_mem {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (hJ : ∀ {s t : Finset I} (h : s ⊆ t) (x : A.obj s), x ∈ J s → Cube.res A h x ∈ J t)
    {p : ℕ} {x : Cube.Term A p} (hx : ∀ s, x s ∈ J s.1) (t) : Cube.d A p x t ∈ J t.1 := by
  rw [Cube.d_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h1 : Cube.res A (Finset.erase_subset i.1 t.1) (x (Cube.eraseIdx t i)) ∈ J t.1 :=
    hJ (Finset.erase_subset i.1 t.1) _ (hx (Cube.eraseIdx t i))
  exact Submodule.smul_of_tower_mem _ _ h1

theorem exactMod_of_exact {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (hJ : ∀ s, J s = ⊥) (h : ∀ p, (cubeComplex A).ExactAt p) : ExactMod A J := by
  refine ⟨fun x hx s => ?_, fun p x hx => ?_⟩
  · have h0 : Cube.d A 0 x = 0 := funext fun s => by simpa [hJ] using hx s
    have h1 := (cubeComplex_exactAt_zero_iff' A).1 (h 0) (h0.trans (map_zero _).symm)
    simp [h1, hJ]
  · have h0 : Cube.d A (p + 1) x = 0 := funext fun s => by simpa [hJ] using hx s
    obtain ⟨y, hy⟩ := ((cubeComplex_exactAt_succ_iff A p).1 (h (p + 1)) x).1 h0
    exact ⟨y, fun s => by simp [hy, hJ]⟩

theorem ExactMod.mem_empty {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (h : ExactMod A J) (y : A.obj ∅)
    (hy : ∀ a : I, Cube.res A (Finset.empty_subset {a}) y ∈ J {a}) : y ∈ J ∅ := by
  have h1 := h.1 ((Cube.termZeroEquiv A).symm y) (fun s => by
    rw [Cube.d_zero_apply, LinearEquiv.apply_symm_apply, Cube.aug_apply]
    obtain ⟨s, hs⟩ := s
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hs
    exact hy a) ⟨∅, rfl⟩
  simpa using h1

theorem ExactMod.exists_glue {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (h : ExactMod A J) (y : ∀ a : I, A.obj {a})
    (hy : ∀ a a' : I, Cube.res A (show ({a} : Finset I) ⊆ {a, a'} by simp) (y a) -
      Cube.res A (show ({a'} : Finset I) ⊆ {a, a'} by simp) (y a') ∈ J {a, a'}) :
    ∃ y₀ : A.obj ∅, ∀ a, Cube.res A (Finset.empty_subset {a}) y₀ - y a ∈ J {a} := by
  have key : ∀ i j : I, (hij : i < j) →
      Cube.d A 1 (Cube.termOneEquiv A y) ⟨{i, j}, Finset.card_pair hij.ne⟩ ∈ J {i, j} := by
    intro i j hij
    rw [Cube.d_one_apply_pair A _ hij]
    simp only [Cube.termOneEquiv_apply]
    have h1 := (J {i, j}).neg_mem (hy i j)
    rwa [neg_sub] at h1
  have hx : ∀ s, Cube.d A 1 (Cube.termOneEquiv A y) s ∈ J s.1 := by
    rintro ⟨t, ht⟩
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 ht
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact key i j h'
    · revert ht
      rw [Finset.pair_comm i j]
      intro ht
      exact key j i h'
  obtain ⟨z, hz⟩ := h.2 0 (Cube.termOneEquiv A y) hx
  refine ⟨Cube.termZeroEquiv A z, fun a => ?_⟩
  have h1 := hz ⟨{a}, Finset.card_singleton a⟩
  rw [Pi.sub_apply, Cube.d_zero_apply, Cube.aug_apply, Cube.termOneEquiv_apply] at h1
  have h2 := (J {a}).neg_mem h1
  rwa [neg_sub] at h2

private theorem exists_term_d_sub_termMap_mem {A B : Cube.{0} I K} {JA : ∀ s, Submodule K (A.obj s)}
    {JB J : ∀ s, Submodule K (B.obj s)} (φ : A ⟶ B) (hA : ExactMod A JA)
    (hJB : ∀ {s t : Finset I} (h : s ⊆ t) (x : B.obj s), x ∈ JB s → Cube.res B h x ∈ JB t)
    (hφ : ∀ s x, x ∈ JA s → (φ.app s).hom x ∈ JB s)
    (hinj : ∀ s, s.Nonempty → ∀ x, (φ.app s).hom x ∈ JB s → x ∈ JA s)
    (hJ : ∀ s, J s = JB s ⊔ LinearMap.range (φ.app s).hom) {k : ℕ} (x : Cube.Term B k)
    (hx : ∀ s, Cube.d B k x s ∈ J s.1) :
    ∃ a₁ : Cube.Term A k, ∀ s, Cube.d B k (x - Cube.termMap φ k a₁) s ∈ JB s.1 := by
  have hx' : ∀ t : {s : Finset I // s.card = k + 1},
      ∃ a : A.obj t.1, Cube.d B k x t - (φ.app t.1).hom a ∈ JB t.1 := by
    intro t
    have h1 := hx t
    rw [hJ, Submodule.mem_sup] at h1
    obtain ⟨u, hu, _, ⟨a, rfl⟩, hua⟩ := h1
    refine ⟨a, ?_⟩
    rw [← hua, add_sub_cancel_right]
    exact hu
  choose a ha using hx'
  have hb : ∀ t, (Cube.d B k x - Cube.termMap φ (k + 1) a) t ∈ JB t.1 := fun t => by
    simpa using ha t
  have hda : ∀ u, Cube.d A (k + 1) a u ∈ JA u.1 := by
    intro u
    apply hinj u.1 (Finset.card_pos.1 (by rw [u.2]; omega))
    have h1 := congrFun (Cube.termMap_d φ (k + 1) a) u
    simp only [Cube.termMap_apply] at h1
    have h2 : (φ.app u.1).hom (Cube.d A (k + 1) a u) =
        -Cube.d B (k + 1) (Cube.d B k x - Cube.termMap φ (k + 1) a) u := by
      rw [h1, map_sub, Cube.d_d]
      simp
    rw [h2]
    exact neg_mem (d_mem hJB hb u)
  obtain ⟨a₁, ha₁⟩ := hA.2 k a hda
  refine ⟨a₁, fun s => ?_⟩
  have h1 : Cube.d B k (x - Cube.termMap φ k a₁) s =
      (Cube.d B k x - Cube.termMap φ (k + 1) a) s + (φ.app s.1).hom ((a - Cube.d A k a₁) s) := by
    rw [map_sub, ← Cube.termMap_d]
    simp only [Pi.sub_apply, Cube.termMap_apply, map_sub]
    abel
  rw [h1]
  exact add_mem (hb s) (hφ _ _ (ha₁ s))

theorem ExactMod.cut {A B : Cube.{0} I K} {JA : ∀ s, Submodule K (A.obj s)}
    {JB J : ∀ s, Submodule K (B.obj s)} (φ : A ⟶ B) (hA : ExactMod A JA) (hB : ExactMod B JB)
    (hJB : ∀ {s t : Finset I} (h : s ⊆ t) (x : B.obj s), x ∈ JB s → Cube.res B h x ∈ JB t)
    (hφ : ∀ s x, x ∈ JA s → (φ.app s).hom x ∈ JB s)
    (hinj : ∀ s, s.Nonempty → ∀ x, (φ.app s).hom x ∈ JB s → x ∈ JA s)
    (hJ : ∀ s, J s = JB s ⊔ LinearMap.range (φ.app s).hom) : ExactMod B J := by
  refine ⟨fun x hx s => ?_, fun p x hx => ?_⟩
  · obtain ⟨a₁, ha₁⟩ := exists_term_d_sub_termMap_mem φ hA hJB hφ hinj hJ x hx
    have h1 := hB.1 _ ha₁ s
    have h2 : x s = (x - Cube.termMap φ 0 a₁) s + (φ.app s.1).hom (a₁ s) := by simp
    rw [h2, hJ]
    exact Submodule.add_mem_sup h1 (LinearMap.mem_range_self _ _)
  · obtain ⟨a₁, ha₁⟩ := exists_term_d_sub_termMap_mem φ hA hJB hφ hinj hJ x hx
    obtain ⟨y, hy⟩ := hB.2 p _ ha₁
    refine ⟨y, fun s => ?_⟩
    have h2 : (x - Cube.d B p y) s =
        (x - Cube.termMap φ (p + 1) a₁ - Cube.d B p y) s + (φ.app s.1).hom (a₁ s) := by
      simp only [Pi.sub_apply, Cube.termMap_apply]
      abel
    rw [h2, hJ]
    exact Submodule.add_mem_sup (hy s) (LinearMap.mem_range_self _ _)

section Family

variable {g : ℕ} {A B : Cube.{0} I K} (φ : Fin g → (A ⟶ B))

abbrev imSum (k : ℕ) (s : Finset I) : Submodule K (B.obj s) :=
  ⨆ (j : Fin g) (_ : (j : ℕ) < k), LinearMap.range ((φ j).app s).hom

omit [LinearOrder I] in

theorem res_mem_imSum (k : ℕ) {s t : Finset I} (h : s ⊆ t) (x : B.obj s)
    (hx : x ∈ imSum φ k s) : Cube.res B h x ∈ imSum φ k t := by
  have key : imSum φ k s ≤ (imSum φ k t).comap (Cube.res B h) := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨a, rfl⟩
    rw [Submodule.mem_comap, ← Cube.app_res]
    exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (LinearMap.mem_range_self _ _))
  exact key hx

omit [LinearOrder I] in

theorem imSum_succ (i : Fin g) (s : Finset I) :
    imSum φ (i + 1) s = imSum φ i s ⊔ LinearMap.range ((φ i).app s).hom := by
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    by_cases h : (j : ℕ) < i
    · exact le_sup_of_le_left (le_iSup_of_le j (le_iSup_of_le h le_rfl))
    · have hji : j = i := Fin.ext (by omega)
      subst hji
      exact le_sup_right
  · exact sup_le (iSup₂_le fun j hj => le_iSup_of_le j (le_iSup_of_le (by omega) le_rfl))
      (le_iSup_of_le i (le_iSup_of_le (by omega) le_rfl))

end Family

end CubeCut

open CubeCut in

theorem cube_cut_regular_sequence : ∀ (K : Type) [CommRing K] (I : Type) [LinearOrder I] [Fintype I] (g : ℕ) (n : ℤ) (C : ℤ → Cube.{0} I K) (mu : Fin g → ∀ l l', C l ⟶ C l'), 0 < n → (∀ i j l l' l'', l' = l + n → l'' = l' + n → mu i l l' ≫ mu j l' l'' = mu j l l' ≫ mu i l' l'') → (∀ (T : Finset I), T.Nonempty → ∀ (i : Fin g) (l l' : ℤ) (y : (C l).obj T), l' = l + n → ((mu i l l').app T).hom y ∈ (⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j l l').app T).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j (l - n) l).app T).hom) → (∀ l, 0 < l → ∀ p, (cubeComplex (C l)).ExactAt p) → (∀ (i : Fin g) (l l' : ℤ) (y : (C l).obj ∅), l' = l + n → (i : ℕ) * n < l → ((mu i l l').app ∅).hom y ∈ (⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j l l').app ∅).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j (l - n) l).app ∅).hom) ∧ ∀ l : ℤ, g * n < l → (∀ y : (C l).obj ∅, (∀ a : I, Cube.res (C l) (Finset.empty_subset {a}) y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a}).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app ∅).hom) ∧ ∀ y : ∀ a : I, (C l).obj {a}, (∀ a a' : I, Cube.res (C l) (show ({a} : Finset I) ⊆ {a, a'} by simp) (y a) - Cube.res (C l) (show ({a'} : Finset I) ⊆ {a, a'} by simp) (y a') ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a, a'}).hom) → ∃ y₀ : (C l).obj ∅, ∀ a, Cube.res (C l) (Finset.empty_subset {a}) y₀ - y a ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a}).hom := by
  intro K _ I _ _ g n C mu hn hcomm hreg hac
  have P : ∀ k : ℕ, k ≤ g → ∀ l₀ l : ℤ, l = l₀ + n → (k : ℤ) * n < l →
      CubeCut.ExactMod (C l) (fun s => CubeCut.imSum (fun j => mu j l₀ l) k s) := by
    intro k
    induction k with
    | zero =>
      intro _ l₀ l _ hlt
      refine CubeCut.exactMod_of_exact (fun s => ?_) (hac l (by simpa using hlt))
      simp [CubeCut.imSum]
    | succ k ih =>
      intro hk l₀ l hl hlt
      push_cast at hlt
      have hA := ih (by omega) (l₀ - n) l₀ (by ring) (by linarith)
      have hB := ih (by omega) l₀ l hl (by linarith)
      let i : Fin g := ⟨k, by omega⟩
      refine CubeCut.ExactMod.cut (mu i l₀ l) hA hB
        (fun h x hx => CubeCut.res_mem_imSum _ _ h x hx) ?_
        (fun s hs x hx => hreg s hs i l₀ l x hl hx)
        (fun s => CubeCut.imSum_succ (fun j => mu j l₀ l) i s)
      intro s x hx
      have key : CubeCut.imSum (fun j => mu j (l₀ - n) l₀) k s ≤
          (CubeCut.imSum (fun j => mu j l₀ l) k s).comap ((mu i l₀ l).app s).hom := by
        refine iSup₂_le fun j hj => ?_
        rintro _ ⟨z, rfl⟩
        rw [Submodule.mem_comap]
        have e := congrArg (fun f => (f.app s).hom z) (hcomm j i (l₀ - n) l₀ l (by ring) hl)
        simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at e
        rw [e]
        exact Submodule.mem_iSup_of_mem j
          (Submodule.mem_iSup_of_mem hj (LinearMap.mem_range_self _ _))
      exact key hx
  refine ⟨fun i l l' y hl' hlt hy => ?_, fun l hlt => ?_⟩
  · have hE := P i i.2.le (l - n) l (by ring) hlt
    refine hE.mem_empty y fun a => ?_
    refine hreg {a} (Finset.singleton_nonempty a) i l l' _ hl' ?_
    rw [Cube.app_res]
    exact CubeCut.res_mem_imSum _ _ _ _ hy
  · have hE := P g le_rfl (l - n) l (by ring) hlt
    exact ⟨hE.mem_empty, hE.exists_glue⟩

end GlobalTheory
