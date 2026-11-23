import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiHBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainExt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ElementsBijectiveOfBijectiveAppStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InitialObjectAugmentedResolutionStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
open GlobalTheory.CatH (face toLast)
universe w w' w'' t t' v u v' u' v'' u''
namespace CrystallineSemistableComparison.Auxfc
open Finset in
theorem combN {M : Type*} [AddCommGroup M] (n : ℕ) (Q : ℕ → ℕ → M) (hQ : ∀ i < n+1, Q i (i+1) = Q (i+1) (i+1)) :
    ∑ j ∈ range (n+2), ∑ i ∈ range (n+1), (-1:ℤ)^(j+i) • (if j ≤ i then Q (i+1) j else Q i (j+1)) +
      ∑ i ∈ range (n+2), ∑ k ∈ range (n+3), (-1:ℤ)^(i+k) • Q i k = Q 0 0 - Q (n+1) (n+2) := by
  have h1 : ∑ j ∈ range (n+2), ∑ i ∈ range (n+1), (-1:ℤ)^(j+i) • (if j ≤ i then Q (i+1) j else Q i (j+1)) =
      ∑ i ∈ range (n+1), ∑ j ∈ range (i+1), (-1:ℤ)^(j+i) • Q (i+1) j +
      ∑ i ∈ range (n+1), ∑ j ∈ Ico (i+1) (n+2), (-1:ℤ)^(j+i) • Q i (j+1) := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i + 1 ≤ n + 2 := by simp at hi; omega
    rw [← Finset.sum_range_add_sum_Ico _ hi']
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp at hj; rw [if_pos (by omega)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp at hj; rw [if_neg (by omega)]
  have h2 : ∑ i ∈ range (n+2), ∑ k ∈ range (n+3), (-1:ℤ)^(i+k) • Q i k =
      ∑ i ∈ range (n+2), ∑ k ∈ range i, (-1:ℤ)^(i+k) • Q i k + ∑ i ∈ range (n+2), (Q i i - Q i (i+1)) +
      ∑ i ∈ range (n+2), ∑ k ∈ Ico (i+2) (n+3), (-1:ℤ)^(i+k) • Q i k := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp at hi
    rw [← Finset.sum_range_add_sum_Ico _ (show i ≤ n+3 by omega), Finset.sum_eq_sum_Ico_succ_bot (show i < n+3 by omega),
      Finset.sum_eq_sum_Ico_succ_bot (show i+1 < n+3 by omega)]
    have e1 : (-1:ℤ)^(i+i) = 1 := by rw [← two_mul, pow_mul]; simp
    have e2 : (-1:ℤ)^(i+(i+1)) = -1 := by rw [← add_assoc, pow_succ, ← two_mul, pow_mul]; simp
    rw [e1, e2, one_smul, neg_one_smul, show i + 1 + 1 = i + 2 by omega]; abel
  have h3 : ∑ i ∈ range (n+2), ∑ k ∈ range i, (-1:ℤ)^(i+k) • Q i k = -∑ i ∈ range (n+1), ∑ j ∈ range (i+1), (-1:ℤ)^(j+i) • Q (i+1) j := by
    rw [Finset.sum_range_succ', Finset.sum_range_zero, add_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show i + 1 + j = (j + i) + 1 by omega, pow_succ, mul_neg_one, neg_smul]
  have h4 : ∑ i ∈ range (n+2), ∑ k ∈ Ico (i+2) (n+3), (-1:ℤ)^(i+k) • Q i k = -∑ i ∈ range (n+1), ∑ j ∈ Ico (i+1) (n+2), (-1:ℤ)^(j+i) • Q i (j+1) := by
    rw [Finset.sum_range_succ, show n + 1 + 2 = n + 3 by omega, Finset.Ico_self, Finset.sum_empty, add_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_Ico_add' (fun k => (-1:ℤ)^(i+k) • Q i k) (i+1) (n+2) 1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show i + (j + 1) = (j + i) + 1 by omega, pow_succ, mul_neg_one, neg_smul]
  have h5 : ∑ i ∈ range (n+2), (Q i i - Q i (i+1)) = Q 0 0 - Q (n+1) (n+2) := by
    rw [Finset.sum_range_succ]
    have : ∑ i ∈ range (n+1), (Q i i - Q i (i+1)) = ∑ i ∈ range (n+1), (Q i i - Q (i+1) (i+1)) :=
      Finset.sum_congr rfl fun i hi => by simp at hi; rw [hQ i (by omega)]
    rw [this, Finset.sum_range_sub' (fun i => Q i i)]; abel
  rw [h1, h2, h3, h4, h5]; abel
end CrystallineSemistableComparison.Auxfc

namespace CrystallineSemistableComparison.Auxfc
variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'}

def Th {G G' : C' ⥤ C} (η : G ⟶ G') : C' × Fin 2 ⥤ C :=
  CategoryTheory.Prod.swap C' (Fin 2) ⋙ Functor.uncurry.obj (ComposableArrows.mk₁ η)

theorem cylinder_map_upper {G G' : C' ⥤ C} (η : G ⟶ G') {T T' : C'} (f : T ⟶ T') (g : (1 : Fin 2) ⟶ 1) :
    (Th η).map ((f, g) : (T, (1 : Fin 2)) ⟶ (T', 1)) = G'.map f := by
  rw [Subsingleton.elim g (𝟙 _)]; simp [Th]; exact Category.id_comp _

theorem cylinder_map_across {G G' : C' ⥤ C} (η : G ⟶ G') {T T' : C'} (f : T ⟶ T') (g : (0 : Fin 2) ⟶ 1) :
    (Th η).map ((f, g) : (T, (0 : Fin 2)) ⟶ (T', 1)) = G.map f ≫ η.app T' := by
  simp [Th]
  rfl

def ch {n k : ℕ} (s : ComposableArrows C' n) {a : Fin (k+1) → Fin (n+1)} {b : Fin (k+1) → Fin 2}
    (ha : Monotone a) (hb : Monotone b) : ComposableArrows (C' × Fin 2) k :=
  Functor.prod' (ha.functor ⋙ s) hb.functor

open Classical in

def tm (m' : Mor F F' σ) {G : C' ⥤ C} (η : G ⟶ m'.G) {n k : ℕ} (s : ComposableArrows C' n) (f : Cn F k)
    (a : Fin (k+1) → Fin (n+1)) (b : Fin (k+1) → Fin 2) : F'.obj (s.obj (Fin.last n)) :=
  if h : Monotone a ∧ Monotone b then
    m'.τ (s.obj (Fin.last n)) ((F.map ((Th η).map ((s.map (homOfLE (Fin.le_last (a (Fin.last k)))),
      homOfLE (show b (Fin.last k) ≤ 1 from Fin.le_last _)) :
        (s.obj (a (Fin.last k)), b (Fin.last k)) ⟶ (s.obj (Fin.last n), (1 : Fin 2))))).hom (f (ch s h.1 h.2 ⋙ Th η)))
  else 0

theorem Fmc {X Y Z : C} (F : C ⥤ ModuleCat.{w} R) (f : X ⟶ Y) (g : Y ⟶ Z) (x : F.obj X) :
    (F.map g).hom ((F.map f).hom x) = (F.map (f ≫ g)).hom x := by simp

theorem tm_zero (m' : Mor F F' σ) {G : C' ⥤ C} (η : G ⟶ m'.G) {n k : ℕ} (s : ComposableArrows C' n)
    (a : Fin (k+1) → Fin (n+1)) (b : Fin (k+1) → Fin 2) : tm m' η s (0 : Cn F k) a b = 0 := by
  unfold tm; split_ifs
  · change m'.τ _ ((F.map _).hom 0) = 0
    rw [map_zero, map_zero]
  · rfl

theorem tm_d (m' : Mor F F' σ) {G : C' ⥤ C} (η : G ⟶ m'.G) {n k : ℕ} (s : ComposableArrows C' n) (f : Cn F k)
    (a : Fin (k+2) → Fin (n+1)) (b : Fin (k+2) → Fin 2) (ha : Monotone a) (hb : Monotone b) :
    tm m' η s (d F k f) a b = ∑ i : Fin (k+2), (-1:ℤ)^(i:ℕ) • tm m' η s f (a ∘ i.succAbove) (b ∘ i.succAbove) := by
  have hs : ∀ i : Fin (k+2), Monotone (a ∘ i.succAbove) ∧ Monotone (b ∘ i.succAbove) := fun i =>
    ⟨ha.comp (Fin.strictMono_succAbove i).monotone, hb.comp (Fin.strictMono_succAbove i).monotone⟩
  unfold tm
  rw [dif_pos ⟨ha, hb⟩]
  simp only [dif_pos (hs _)]
  change m'.τ _ ((F.map _).hom (∑ i : Fin (k+2), (-1:ℤ)^(i:ℕ) • (F.map (toLast i (ch s ha hb ⋙ Th η))).hom (f (face i (ch s ha hb ⋙ Th η))))) = _
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul]
  erw [Fmc]
  congr 5
  change (Th η).map _ ≫ (Th η).map _ = _
  rw [← Functor.map_comp]
  congr 1
  apply Prod.ext
  · change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  · apply Subsingleton.elim

theorem tm_face (m' : Mor F F' σ) {G : C' ⥤ C} (η : G ⟶ m'.G) {n k : ℕ} (s : ComposableArrows C' (n+1)) (j : Fin (n+2))
    (f : Cn F k) (a : Fin (k+1) → Fin (n+1)) (b : Fin (k+1) → Fin 2) :
    (F'.map (toLast j s)).hom (tm m' η (face j s) f a b) = tm m' η s f (j.succAbove ∘ a) b := by
  unfold tm
  by_cases h : Monotone a ∧ Monotone b
  · have h' : Monotone (j.succAbove ∘ a) ∧ Monotone b := ⟨(Fin.strictMono_succAbove j).monotone.comp h.1, h.2⟩
    rw [dif_pos h, dif_pos h', ← m'.nat]
    erw [Fmc]
    rw [← cylinder_map_upper η _ (𝟙 _), ← Functor.map_comp]
    congr 5
    apply Prod.ext
    · change s.map _ ≫ s.map _ = _
      rw [← s.map_comp]; rfl
    · apply Subsingleton.elim
  · have h' : ¬ (Monotone (j.succAbove ∘ a) ∧ Monotone b) := fun h' =>
      h ⟨fun x y hxy => (Fin.strictMono_succAbove j).le_iff_le.1 (h'.1 hxy), h'.2⟩
    rw [dif_neg h, dif_neg h', map_zero]

end CrystallineSemistableComparison.Auxfc

namespace CrystallineSemistableComparison.Auxfc
variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'}

theorem cylinder_map_lower {G G' : C' ⥤ C} (η : G ⟶ G') {T T' : C'} (f : T ⟶ T') (g : (0 : Fin 2) ⟶ 0) :
    (Th η).map ((f, g) : (T, (0 : Fin 2)) ⟶ (T', 0)) = G.map f := by
  rw [Subsingleton.elim g (𝟙 _)]; simp [Th]; exact Category.id_comp _

theorem cylinder_map_upper_heq {G G' : C' ⥤ C} (η : G ⟶ G') {T T' : C'} (f : T ⟶ T') {b b' : Fin 2} (g : b ⟶ b')
    (hb : b = 1) (hb' : b' = 1) : HEq ((Th η).map ((f, g) : (T, b) ⟶ (T', b'))) (G'.map f) := by
  subst hb; subst hb'; exact heq_of_eq (cylinder_map_upper η f g)

theorem cylinder_map_lower_heq {G G' : C' ⥤ C} (η : G ⟶ G') {T T' : C'} (f : T ⟶ T') {b b' : Fin 2} (g : b ⟶ b')
    (hb : b = 0) (hb' : b' = 0) : HEq ((Th η).map ((f, g) : (T, b) ⟶ (T', b'))) (G.map f) := by
  subst hb; subst hb'; exact heq_of_eq (cylinder_map_lower η f g)

theorem cylinder_map_across_heq {G G' : C' ⥤ C} (η : G ⟶ G') {T T' : C'} (f : T ⟶ T') {b b' : Fin 2} (g : b ⟶ b')
    (hb : b = 0) (hb' : b' = 1) : HEq ((Th η).map ((f, g) : (T, b) ⟶ (T', b'))) (G.map f ≫ η.app T') := by
  subst hb; subst hb'; exact heq_of_eq (cylinder_map_across η f g)

theorem app_congr {k : ℕ} (f : Cn F k) {c c' : ComposableArrows C k} (hc : c = c') {Y : C}
    (g : c.obj (Fin.last k) ⟶ Y) (g' : c'.obj (Fin.last k) ⟶ Y) (hg : HEq g g') :
    (F.map g).hom (f c) = (F.map g').hom (f c') := by
  subst hc; cases hg; rfl

theorem map_self {n : ℕ} (s : ComposableArrows C' n) (i : Fin (n+1)) (h : i ≤ i) : s.map (homOfLE h) = 𝟙 _ := by
  rw [← s.map_id]; rfl

theorem tm_top (m' : Mor F F' σ) {G : C' ⥤ C} (η : G ⟶ m'.G) {n : ℕ} (s : ComposableArrows C' n) (f : Cn F n) :
    tm m' η s f id (fun _ => 1) = m'.pullC n f s := by
  unfold tm
  rw [dif_pos ⟨monotone_id, monotone_const⟩]
  have e : ch s monotone_id (monotone_const (β := Fin 2) (c := 1)) ⋙ Th η = s ⋙ m'.G := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j φ => ?_)
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact eq_of_heq ((cylinder_map_upper_heq η _ _ rfl rfl).trans (heq_of_eq (congrArg (fun ψ => m'.G.map (s.map ψ)) (Subsingleton.elim _ _))))
  show _ = m'.τ _ (f (s ⋙ m'.G))
  rw [show f (s ⋙ m'.G) = (F.map (𝟙 _)).hom (f (s ⋙ m'.G)) by simp]
  congr 1
  apply app_congr f e
  refine (cylinder_map_upper_heq η _ _ rfl rfl).trans (heq_of_eq ?_)
  rw [map_self, CategoryTheory.Functor.map_id]; rfl

theorem tm_bot (m m' : Mor F F' σ) (η : m.G ⟶ m'.G) (hτ : ∀ T x, m'.τ T ((F.map (η.app T)).hom x) = m.τ T x)
    {n : ℕ} (s : ComposableArrows C' n) (f : Cn F n) :
    tm m' η s f id (fun _ => 0) = m.pullC n f s := by
  unfold tm
  rw [dif_pos ⟨monotone_id, monotone_const⟩]
  have e : ch s monotone_id (monotone_const (β := Fin 2) (c := 0)) ⋙ Th η = s ⋙ m.G := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j φ => ?_)
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact eq_of_heq ((cylinder_map_lower_heq η _ _ rfl rfl).trans (heq_of_eq (congrArg (fun ψ => m.G.map (s.map ψ)) (Subsingleton.elim _ _))))
  change m'.τ _ ((F.map _).hom (f (ch s monotone_id (monotone_const (β := Fin 2) (c := 0)) ⋙ Th η))) = m.τ _ (f (s ⋙ m.G))
  rw [← hτ]
  congr 1
  apply app_congr f e
  refine (cylinder_map_across_heq η _ _ rfl rfl).trans (heq_of_eq ?_)
  rw [map_self, CategoryTheory.Functor.map_id, Category.id_comp]

end CrystallineSemistableComparison.Auxfc

namespace CrystallineSemistableComparison.Auxfc
variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'}

def bb {n : ℕ} (i : Fin (n+1)) : Fin (n+2) → Fin 2 := fun x => if i.castSucc < x then 1 else 0

theorem bb_mono {n : ℕ} (i : Fin (n+1)) : Monotone (bb i) := by
  intro x y hxy
  simp only [bb]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (lt_of_lt_of_le h1 hxy) h2
  · exact Fin.zero_le _
  · exact le_rfl

theorem vsA {n : ℕ} (p : Fin (n+1)) (x : Fin n) : (p.succAbove x : ℕ) = if (x:ℕ) < p then (x:ℕ) else x+1 := by
  unfold Fin.succAbove; split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]

theorem vpA {n : ℕ} (p : Fin n) (x : Fin (n+1)) : (p.predAbove x : ℕ) = if (p:ℕ) < x then (x:ℕ) - 1 else x := by
  unfold Fin.predAbove; split_ifs with h1 h2 h2 <;> rw [Fin.lt_def, Fin.val_castSucc] at h1 <;> simp_all <;> omega

theorem vbb {n : ℕ} (i : Fin (n+1)) (x : Fin (n+2)) : bb i x = if (i:ℕ) < x then 1 else 0 := by
  unfold bb; simp [Fin.lt_def]

macro "fin_tac" : tactic => `(tactic| (funext x; first | (apply Fin.ext; simp only [Function.comp_apply, vsA, vpA, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last, id]; split_ifs <;> omega) | (simp only [Function.comp_apply, vbb, vsA, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last]; split_ifs <;> first | rfl | (exfalso; omega))))

theorem E1 {n : ℕ} (i : Fin (n+1)) (j : Fin (n+2)) (h : (j:ℕ) ≤ i) :
    j.succAbove ∘ i.predAbove = i.succ.predAbove ∘ j.castSucc.succAbove := by fin_tac
theorem faceMap_comp_succAbove_castSucc {n : ℕ} (i : Fin (n+1)) (j : Fin (n+2)) (h : (j:ℕ) ≤ i) : bb i = bb i.succ ∘ j.castSucc.succAbove := by fin_tac
theorem E2 {n : ℕ} (i : Fin (n+1)) (j : Fin (n+2)) (h : (i:ℕ) < j) :
    j.succAbove ∘ i.predAbove = i.castSucc.predAbove ∘ j.succ.succAbove := by fin_tac
theorem E2b {n : ℕ} (i : Fin (n+1)) (j : Fin (n+2)) (h : (i:ℕ) < j) : bb i = bb i.castSucc ∘ j.succ.succAbove := by fin_tac
theorem E3 {n : ℕ} (i : Fin (n+1)) :
    i.castSucc.predAbove ∘ i.succ.castSucc.succAbove = i.succ.predAbove ∘ i.succ.castSucc.succAbove := by fin_tac
theorem faceMap_castSucc_comp_eq_succ {n : ℕ} (i : Fin (n+1)) :
    bb i.castSucc ∘ i.succ.castSucc.succAbove = bb i.succ ∘ i.succ.castSucc.succAbove := by fin_tac
theorem E4 {n : ℕ} : (0 : Fin (n+2)).predAbove ∘ (0 : Fin (n+3)).succAbove = id := by fin_tac
theorem faceMap_zero_comp_eq_one {n : ℕ} : bb (0 : Fin (n+2)) ∘ (0 : Fin (n+3)).succAbove = fun _ => 1 := by fin_tac
theorem E5 {n : ℕ} : (Fin.last (n+1)).predAbove ∘ (Fin.last (n+2)).succAbove = id := by fin_tac
theorem faceMap_last_comp_eq_zero {n : ℕ} : bb (Fin.last (n+1)) ∘ (Fin.last (n+2)).succAbove = fun _ => 0 := by fin_tac

end CrystallineSemistableComparison.Auxfc

namespace CrystallineSemistableComparison.Auxfc
variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'}

theorem combF {M : Type*} [AddCommGroup M] (n : ℕ) (T : (Fin (n+2) → Fin (n+2)) → (Fin (n+2) → Fin 2) → M) :
    ∑ j : Fin (n+2), ∑ i : Fin (n+1), (-1:ℤ)^(j:ℕ) • (-1:ℤ)^(i:ℕ) • T (j.succAbove ∘ i.predAbove) (bb i) +
    ∑ i : Fin (n+2), ∑ k : Fin (n+3), (-1:ℤ)^(i:ℕ) • (-1:ℤ)^(k:ℕ) • T (i.predAbove ∘ k.succAbove) (bb i ∘ k.succAbove) =
    T id (fun _ => 1) - T id (fun _ => 0) := by
  let Q : ℕ → ℕ → M := fun i k => if h : i < n+2 ∧ k < n+3 then
    T ((⟨i, h.1⟩ : Fin (n+2)).predAbove ∘ (⟨k, h.2⟩ : Fin (n+3)).succAbove)
      (bb (⟨i, h.1⟩ : Fin (n+2)) ∘ (⟨k, h.2⟩ : Fin (n+3)).succAbove) else 0
  have hQ : ∀ (i : Fin (n+2)) (k : Fin (n+3)), Q i k = T (i.predAbove ∘ k.succAbove) (bb i ∘ k.succAbove) :=
    fun i k => by simp only [Q, dif_pos (And.intro i.2 k.2)]
  have key := combN n Q (fun i hi => by
    have e1 := hQ (⟨i, hi⟩ : Fin (n+1)).castSucc (⟨i, hi⟩ : Fin (n+1)).succ.castSucc
    have e2 := hQ (⟨i, hi⟩ : Fin (n+1)).succ (⟨i, hi⟩ : Fin (n+1)).succ.castSucc
    simp only [Fin.val_castSucc, Fin.val_succ] at e1 e2
    rw [e1, e2, E3, faceMap_castSucc_comp_eq_succ])
  have q0 : Q 0 0 = T id (fun _ => 1) := by
    have e := hQ 0 0
    rw [Fin.val_zero, Fin.val_zero, E4, faceMap_zero_comp_eq_one] at e
    exact e
  have q1 : Q (n+1) (n+2) = T id (fun _ => 0) := by
    have e := hQ (Fin.last (n+1)) (Fin.last (n+2))
    rw [Fin.val_last, Fin.val_last, E5, faceMap_last_comp_eq_zero] at e
    exact e
  rw [← q0, ← q1, ← key]
  congr 1
  · rw [Finset.sum_range]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_range]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← pow_add]
    congr 1
    split_ifs with h
    · rw [E1 i j h, faceMap_comp_succAbove_castSucc i j h, ← hQ]; simp only [Fin.val_succ, Fin.val_castSucc]
    · rw [E2 i j (by omega), E2b i j (by omega), ← hQ]; simp only [Fin.val_succ, Fin.val_castSucc]
  · rw [Finset.sum_range]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, ← pow_add, hQ]

def hh (m' : Mor F F' σ) {G : C' ⥤ C} (η : G ⟶ m'.G) (n : ℕ) (f : Cn F (n+1)) : Cn F' n :=
  fun s => ∑ i : Fin (n+1), (-1:ℤ)^(i:ℕ) • tm m' η s f i.predAbove (bb i)

theorem htpy_zero (m m' : Mor F F' σ) (η : m.G ⟶ m'.G) (hτ : ∀ T x, m'.τ T ((F.map (η.app T)).hom x) = m.τ T x)
    (f : Cn F 0) (hf : d F 0 f = 0) : m'.pullC 0 f = m.pullC 0 f := by
  funext s
  have h := tm_d m' η s f (Fin.predAbove (0 : Fin 1)) (bb (0 : Fin 1)) (Fin.predAbove_right_monotone _) (bb_mono _)
  rw [hf, tm_zero, Fin.sum_univ_two] at h
  have a0 : (Fin.predAbove (0 : Fin 1)) ∘ (0 : Fin 2).succAbove = id := funext fun x => Subsingleton.elim _ _
  have a1 : (Fin.predAbove (0 : Fin 1)) ∘ (1 : Fin 2).succAbove = id := funext fun x => Subsingleton.elim _ _
  have b0 : bb (0 : Fin 1) ∘ (0 : Fin 2).succAbove = fun _ => 1 := by funext x; fin_cases x; rfl
  have b1 : bb (0 : Fin 1) ∘ (1 : Fin 2).succAbove = fun _ => 0 := by funext x; fin_cases x; rfl
  rw [a0, a1, b0, b1, tm_top, tm_bot m m' η hτ] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul] at h
  exact sub_eq_zero.1 ((sub_eq_add_neg _ _).trans h.symm)

end CrystallineSemistableComparison.Auxfc

namespace CrystallineSemistableComparison.Auxfc
variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'}

theorem htpy_succ (m m' : Mor F F' σ) (η : m.G ⟶ m'.G) (hτ : ∀ T x, m'.τ T ((F.map (η.app T)).hom x) = m.τ T x)
    (n : ℕ) (f : Cn F (n+1)) (hf : d F (n+1) f = 0) :
    m'.pullC (n+1) f - m.pullC (n+1) f = d F' n (hh m' η n f) := by
  funext s
  have h1 : d F' n (hh m' η n f) s = ∑ j : Fin (n+2), ∑ i : Fin (n+1),
      (-1:ℤ)^(j:ℕ) • (-1:ℤ)^(i:ℕ) • tm m' η s f (j.succAbove ∘ i.predAbove) (bb i) := by
    change ∑ j : Fin (n+2), (-1:ℤ)^(j:ℕ) • (F'.map (toLast j s)).hom
      (∑ i : Fin (n+1), (-1:ℤ)^(i:ℕ) • tm m' η (face j s) f i.predAbove (bb i)) = _
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, tm_face]
  have h2 : (0 : F'.obj (s.obj (Fin.last (n+1)))) = ∑ i : Fin (n+2), ∑ k : Fin (n+3),
      (-1:ℤ)^(i:ℕ) • (-1:ℤ)^(k:ℕ) • tm m' η s f (i.predAbove ∘ k.succAbove) (bb i ∘ k.succAbove) := by
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.smul_sum, ← tm_d m' η s f _ _ (Fin.predAbove_right_monotone i) (bb_mono i), hf, tm_zero, smul_zero]
  have h3 := combF n (tm m' η s f)
  rw [tm_top, tm_bot m m' η hτ, ← h2, add_zero, ← h1] at h3
  exact h3.symm

theorem prism_main (m m' : Mor F F' σ) (η : m.G ⟶ m'.G) (hτ : ∀ T x, m'.τ T ((F.map (η.app T)).hom x) = m.τ T x)
    (n : ℕ) (x : H F n) : m.pull n x = m'.pull n x :=
  (CrystallineSemistableComparison.P.mapH_htpy m'.hom m.hom (fun n f => hh m' η n f) (fun f hf => htpy_zero m m' η hτ f hf)
    (fun n f hf => htpy_succ m m' η hτ n f hf) n x).symm

end CrystallineSemistableComparison.Auxfc

theorem CrystallineSemistableComparison.P.pull_comp : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {σ : R →+* R'} {σ' : R' →+* R''} {σ'' : R →+* R''} [RingHomCompTriple σ σ' σ''] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C''] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {F'' : C'' ⥤ ModuleCat.{w''} R''} (m : Mor F F' σ) (m' : Mor F' F'' σ') (n : ℕ) (x : H F n), (m.comp m' : Mor F F'' σ'').pull n x = m'.pull n (m.pull n x) ∧ (Mor.id F).pull n x = x :=
  fun m m' n x => ⟨CrystallineSemistableComparison.P.mapH_comp m.hom m'.hom n x, by
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ n).1 x
    exact CrystallineSemistableComparison.P.mapH_cls _ n a ha ha⟩

theorem CrystallineSemistableComparison.P.prism : ∀ {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} (m m' : Mor F F' σ) (η : m.G ⟶ m'.G), (∀ T x, m'.τ T ((F.map (η.app T)).hom x) = m.τ T x) → ∀ n x, m.pull n x = m'.pull n x :=
  fun m m' η hτ n x => CrystallineSemistableComparison.Auxfc.prism_main m m' η hτ n x

theorem CrystallineSemistableComparison.P.adj : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (L : C' ⥤ C) (U : C ⥤ C') (a : L ⊣ U) (n : ℕ), Function.Bijective ((Mor.restrict F L).pull n) := by
  intro R _ C _ C' _ F L U a n
  let m : Mor (L ⋙ F) F (RingHom.id R) := ⟨U, fun T => (F.map (a.counit.app T)).hom, fun {T T'} φ x => by
    change (F.map (L.map (U.map φ)) ≫ F.map (a.counit.app T')).hom x = (F.map (a.counit.app T) ≫ F.map φ).hom x
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg (fun f => (F.map f).hom x) (a.counit_naturality φ)⟩
  have h1 : ∀ x, m.pull n ((Mor.restrict F L).pull n x) = x := fun x => by
    rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) (Mor.restrict F L) m n x).1,
      CrystallineSemistableComparison.P.prism ((Mor.restrict F L).comp m) (Mor.id F) a.counit (fun _ _ => rfl) n x]
    exact (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) (Mor.restrict F L) m n x).2
  have h2 : ∀ x, (Mor.restrict F L).pull n (m.pull n x) = x := fun x => by
    rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) m (Mor.restrict F L) n x).1,
      ← CrystallineSemistableComparison.P.prism (Mor.id (L ⋙ F)) (m.comp (Mor.restrict F L)) a.unit (fun T x => by
        change (F.map (L.map (a.unit.app T)) ≫ F.map (a.counit.app (L.obj T))).hom x = x
        rw [← F.map_comp]
        exact (congrArg (fun f => (F.map f).hom x) (a.left_triangle_components T)).trans
          (congrArg (fun f => ModuleCat.Hom.hom f x) (F.map_id _))) n x]
    exact (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) m (Mor.restrict F L) n x).2
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem CrystallineSemistableComparison.P.adj_mor : ∀ {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} (m : Mor F F' σ) [m.G.IsLeftAdjoint], (∀ T, Function.Bijective (m.τ T)) → ∀ n, Function.Bijective (m.pull n) := by
  intro R R' _ _ σ C _ C' _ F F' m _ h n
  let m' : Mor (m.G ⋙ F) F' σ := ⟨𝟭 C', m.τ, m.nat⟩
  have e : (m.pull n : H F n → H F' n) = m'.pull n ∘ (Mor.restrict F m.G).pull n := by
    funext x
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  rw [e]
  refine (CrystallineSemistableComparison.P.mapH_bij m'.hom (fun k => ⟨fun f g hfg => funext fun s => (h _).1 (congrFun hfg s), fun g => ?_⟩) n).comp
    (CrystallineSemistableComparison.P.adj F m.G _ (Adjunction.ofIsLeftAdjoint m.G) n)
  choose f hf using fun s : ComposableArrows C' k => (h _).2 (g s)
  exact ⟨f, funext hf⟩

theorem CrystallineSemistableComparison.P.initial : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (T₀ : C) (h : Limits.IsInitial T₀), (cx F).ResUpTo 1 (aug F fun T => (F.map (h.to T)).hom) := GlobalTheory.T.initial_object_augmented_resolution

theorem CrystallineSemistableComparison.P.el_iso : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R), (∀ T, Function.Bijective (p.app T)) → ∀ n, Function.Bijective ((elMor p F).hom.f n) := GlobalTheory.T.elements_bijective_of_bijective_app

theorem CrystallineSemistableComparison.P.pi_H : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {ι : Type w} (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ), Function.Bijective fun (x : H (piF F) n) (i : ι) => (piProj F i).pull n x := GlobalTheory.CompanionTheory.CatCohProd.piH_bijective

theorem CrystallineSemistableComparison.P.sigma_H : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {ι : Type t} (c : C → ι), (∀ {T T' : C}, (T ⟶ T') → c T = c T') → ∀ n, Function.Bijective fun (x : H F n) (i : ι) => (Mor.restrict F (ObjectProperty.ι fun T => c T = i)).pull n x := GlobalTheory.CompanionTheory.CatPieces.sigmaH
