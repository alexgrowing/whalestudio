import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd
namespace ImgPf

variable {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R}
  (T0 : ∀ (P : PSh) (s : ℤ), ((free S).obj P ⟶ I.X s) →+ ((free R).obj P ⟶ J.X s))

def T' (E : Spc) (p s : ℤ) : (((chains S).obj E).X p ⟶ I.X s) →+ (((chains R).obj E).X p ⟶ J.X s) :=
  if h : -(((-p).toNat : ℕ) : ℤ) = p then
    { toFun := fun φ => (((chains R).obj E).XIsoOfEq h).inv ≫ (chainsXIso R E _).hom ≫
        T0 _ s ((chainsXIso S E _).inv ≫ (((chains S).obj E).XIsoOfEq h).hom ≫ φ)
      map_zero' := by simp
      map_add' := by intros; simp [Preadditive.comp_add] }
  else 0

theorem T'_eq (E : Spc) (k : ℕ) (s : ℤ) (φ : ((chains S).obj E).X (-(k : ℤ)) ⟶ I.X s) :
    T' T0 E (-(k : ℤ)) s φ = (chainsXIso R E k).hom ≫ T0 _ s ((chainsXIso S E k).inv ≫ φ) := by
  have key : ∀ (k' : ℕ) (h' : -(k' : ℤ) = -(k : ℤ)), (((chains R).obj E).XIsoOfEq h').inv ≫ (chainsXIso R E k').hom ≫
      T0 _ s ((chainsXIso S E k').inv ≫ (((chains S).obj E).XIsoOfEq h').hom ≫ φ) =
      (chainsXIso R E k).hom ≫ T0 _ s ((chainsXIso S E k).inv ≫ φ) := by
    intro k' h'
    obtain rfl : k' = k := by omega
    simp [HomologicalComplex.XIsoOfEq_rfl]
  unfold T'
  rw [dif_pos (by simp)]
  exact key _ _

theorem T'_pos (E : Spc) (p s : ℤ) (hp : 0 < p) : T' T0 E p s = 0 := by
  unfold T'
  rw [dif_neg (by omega)]

theorem T'_comp_d (E : Spc) (p s t : ℤ) (φ : ((chains S).obj E).X p ⟶ I.X s)
    (hd : ∀ (P : PSh) (s t : ℤ) (φ : (free S).obj P ⟶ I.X s), T0 P t (φ ≫ I.d s t) = T0 P s φ ≫ J.d s t) :
    T' T0 E p t (φ ≫ I.d s t) = T' T0 E p s φ ≫ J.d s t := by
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    rw [T'_eq, T'_eq, ← Category.assoc, hd, Category.assoc]
  · rw [T'_pos T0 E p t hp, T'_pos T0 E p s hp]
    simp

theorem T'_free (E E' : Spc) (k k' : ℕ) (s : ℤ) {ι : Type} [Fintype ι] (c : ι → ℤ)
    (u : ι → (E.obj (op (SimplexCategory.mk k)) ⟶ E'.obj (op (SimplexCategory.mk k'))))
    (gS : ((chains S).obj E).X (-(k : ℤ)) ⟶ ((chains S).obj E').X (-(k' : ℤ)))
    (gR : ((chains R).obj E).X (-(k : ℤ)) ⟶ ((chains R).obj E').X (-(k' : ℤ)))
    (hS : gS = (chainsXIso S E k).hom ≫ (∑ i, c i • (free S).map (u i)) ≫ (chainsXIso S E' k').inv)
    (hR : gR = (chainsXIso R E k).hom ≫ (∑ i, c i • (free R).map (u i)) ≫ (chainsXIso R E' k').inv)
    (hn : ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T0 P s ((free S).map f ≫ φ) = (free R).map f ≫ T0 P' s φ)
    (φ : ((chains S).obj E').X (-(k' : ℤ)) ⟶ I.X s) :
    T' T0 E (-(k : ℤ)) s (gS ≫ φ) = gR ≫ T' T0 E' (-(k' : ℤ)) s φ := by
  rw [T'_eq, T'_eq, hS, hR]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp, map_sum, map_zsmul, hn]

theorem T'_d (E : Spc) (p p' s : ℤ) (h : p + 1 = p') (φ : ((chains S).obj E).X p' ⟶ I.X s)
    (hn : ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T0 P s ((free S).map f ≫ φ) = (free R).map f ≫ T0 P' s φ) :
    T' T0 E p s (((chains S).obj E).d p p' ≫ φ) = ((chains R).obj E).d p p' ≫ T' T0 E p' s φ := by
  rcases lt_or_ge p 0 with hp | hp
  · obtain ⟨k, rfl, rfl⟩ : ∃ k : ℕ, p = -((k + 1 : ℕ) : ℤ) ∧ p' = -(k : ℤ) := ⟨(-p - 1).toNat, by omega, by omega⟩
    refine T'_free T0 E E k.succ k s (fun i : Fin (k + 2) => ((-1 : ℤ) ^ (i : ℕ))) (fun i => E.δ i) _ _ ?_ ?_ hn φ
    · refine (HomologicalComplex.extend_d_eq ((chainsN S).obj E) ComplexShape.embeddingDownNat
        (i' := -((k + 1 : ℕ) : ℤ)) (j' := -(k : ℤ)) (i := k + 1) (j := k) rfl rfl).trans ?_
      unfold chainsXIso
      congr 2
      exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ k
    · refine (HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat
        (i' := -((k + 1 : ℕ) : ℤ)) (j' := -(k : ℤ)) (i := k + 1) (j := k) rfl rfl).trans ?_
      unfold chainsXIso
      congr 2
      exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ k
  · have hz : ((chains S).obj E).d p p' = 0 := by
      apply (HomologicalComplex.isZero_extend_X _ _ p' ?_).eq_of_tgt
      intro i hi
      change -(i : ℤ) = p' at hi
      omega
    rw [hz, T'_pos T0 E p' s (by omega)]
    simp

theorem T'_map (E E' : Spc) (f : E ⟶ E') (p s : ℤ) (φ : ((chains S).obj E').X p ⟶ I.X s)
    (hn : ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T0 P s ((free S).map f ≫ φ) = (free R).map f ≫ T0 P' s φ) :
    T' T0 E p s (((chains S).map f).f p ≫ φ) = ((chains R).map f).f p ≫ T' T0 E' p s φ := by
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    refine T'_free T0 E E' k k s (fun _ : Unit => 1) (fun _ => f.app _) _ _ ?_ ?_ hn φ
    · refine (HomologicalComplex.extendMap_f ((chainsN S).map f) ComplexShape.embeddingDownNat
        (i := k) (i' := -(k : ℤ)) rfl).trans ?_
      unfold chainsXIso
      congr 2
      simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
      rfl
    · refine (HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat
        (i := k) (i' := -(k : ℤ)) rfl).trans ?_
      unfold chainsXIso
      congr 2
      simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
      rfl
  · rw [T'_pos T0 E p s hp, T'_pos T0 E' p s hp]
    simp

def TC (E : Spc) (n : ℤ) : Cochain ((chains S).obj E) I n →+ Cochain ((chains R).obj E) J n where
  toFun α := Cochain.mk fun p q h => T' T0 E p q (α.v p q h)
  map_zero' := Cochain.ext _ _ fun p q h => by simp
  map_add' α β := Cochain.ext _ _ fun p q h => by simp [Cochain.add_v]

theorem TC_v (E : Spc) (n : ℤ) (α : Cochain ((chains S).obj E) I n) (p q : ℤ) (h : p + n = q) :
    (TC T0 E n α).v p q h = T' T0 E p q (α.v p q h) :=
  Cochain.mk_v (fun p q h => T' T0 E p q (α.v p q h)) p q h

end ImgPf

open ImgPf in
theorem LeafImg_of (hI : LeafImgHom) : LeafImg := by
  intro S R _ _ I J ρ
  obtain ⟨T0, hgen, hd, hn⟩ := hI S R I J ρ
  refine ⟨fun E n => TC T0 E n, ?_, ?_, ?_⟩
  · intro E n α p s h U x
    unfold ev
    rw [TC_v, T'_eq, Iso.inv_hom_id_assoc]
    exact hgen _ _ _ U x
  · intro E n m α
    by_cases hnm : n + 1 = m
    · refine Cochain.ext _ _ fun p q hpq => ?_
      rw [TC_v, δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl, δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
        map_add, Units.smul_def, Units.smul_def, map_zsmul, T'_comp_d T0 E _ _ _ _ hd, TC_v, TC_v,
        T'_d T0 E p (p + 1) q rfl _ hn]
    · rw [δ_shape n m hnm, δ_shape n m hnm, map_zero]
  · intro E E' f n α
    refine Cochain.ext _ _ fun p q hpq => ?_
    simp only [pb, TC_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    exact T'_map T0 E E' f p q _ hn

end LateralTheory.CohomologicalPurity.Bd
