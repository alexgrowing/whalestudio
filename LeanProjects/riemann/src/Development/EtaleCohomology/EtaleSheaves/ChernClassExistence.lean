import Development.EtaleCohomology.EtaleSheaves.ChernClassRootLocalization
import Development.EtaleCohomology.TateTwists.EtaleFirstChernCochainCoboundaryVanishesSimplexD

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassExistence

def LeafEvMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def LeafEvDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}), (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧ ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U), ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

def EtaleKummerChernEdgeValuesExistNatural : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      a U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def EtaleKummerChernTriangleValuesExistNatural : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      a U x = kumT q U v + kumT q U w - kumT q U (v * w)

def EtaleKummerChernCochainCoboundaryVanishesOnEdges : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev (δ 2 3 α) 1 2 (by simp) U x = 0

def EtaleKummerChernCochainCoboundaryVanishesOnTriangles : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 2 U), ev (δ 2 3 α) 2 1 (by simp) U x = 0

def EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 3 U), ev (δ 2 3 α) 3 0 (by simp) U x = 0

theorem cx_ext_pf : LateralTheory.EtaleFoundations.cx_ext := by
  intro R _ E I n α h
  apply LateralTheory.E.ChernCocycleExistenceAndUniqueness.cochain_ext_ev α 0
  intro p s hs U x
  rw [h]
  simp [ev]

theorem res_neg_pf : LateralTheory.EtaleFoundations.res_neg := by
  intro q s hs U a
  exact LateralTheory.EtaleFoundations.FirstChernUniqueness.sec_sub (LateralTheory.EtaleFoundations.FirstChernUniqueness.res_zero_neg q s hs) U a 0

theorem etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness (hmk : LeafEvMk) (hd : LeafEvDelta) (h1 : EtaleKummerChernEdgeValuesExistNatural) (h2 : EtaleKummerChernTriangleValuesExistNatural)
    (c1 : EtaleKummerChernCochainCoboundaryVanishesOnEdges) (c2 : EtaleKummerChernCochainCoboundaryVanishesOnTriangles) (c3 : EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra) : LateralTheory.E.ChernCocycleExistenceAndUniqueness.EtaleKummerChernCocycleExists := by
  intro q _ E L hi
  exact LateralTheory.EtaleFoundations.exists_closed_etale_kummer_chern_class_cochain_of_values hmk h1 h2 (LateralTheory.EtaleFoundations.etale_first_chern_cochain_closed_of_components hd cx_ext_pf res_neg_pf c1 c2 c3) q L hi

end LateralTheory.E.ChernClassExistence
