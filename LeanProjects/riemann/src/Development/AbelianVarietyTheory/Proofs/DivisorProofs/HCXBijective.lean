import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.HCTerms

variable (R : Type) [CommRing R]

theorem chainsXIso_inv_map {E E' : Spc} (f : E ⟶ E') (k : ℕ) :
    (chainsXIso R E k).inv ≫ ((chains R).map f).f (-(k : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk k))) ≫ (chainsXIso R E' k).inv := by
  have h := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl
  change (chainsXIso R E k).inv ≫ (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(k : ℤ)) = _
  rw [h]
  erw [Iso.inv_hom_id_assoc]
  rfl

theorem isZero_chains_X (E : Spc) (p : ℤ) (hp : 0 < p) : IsZero (((chains R).obj E).X p) := by
  apply HomologicalComplex.isZero_extend_X
  intro i h
  change -(i : ℤ) = p at h
  omega

def termEval (F : Shv R) (n : ℤ) (k : ℕ) :
    (HC R F ⋙ HomologicalComplex.eval _ _ n) ⟶ ((evaluation _ PSh).obj (op (SimplexCategory.mk k))).op ⋙ (free R).op ⋙
      preadditiveYoneda.obj ((res R F).X (n - k)) where
  app E := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun β : Cochain ((chains R).obj E.unop) (res R F) n => (chainsXIso R E.unop k).inv ≫ β.v (-(k : ℤ)) (n - k) (by omega))
    (fun a b => by simp only [Cochain.add_v, Preadditive.comp_add]; rfl))
  naturality E E' f := by
    ext β
    revert β
    change ∀ β : Cochain ((chains R).obj E.unop) (res R F) n,
      (chainsXIso R E'.unop k).inv ≫ ((Cochain.ofHom ((chains R).map f.unop)).comp β (zero_add n)).v (-(k : ℤ)) (n - k) (by omega) =
      (free R).map (f.unop.app (op (SimplexCategory.mk k))) ≫ (chainsXIso R E.unop k).inv ≫ β.v (-(k : ℤ)) (n - k) (by omega)
    intro β
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chainsXIso_inv_map, Category.assoc]

variable {R}

def blk {E : Spc} {F : Shv R} {n : ℤ} (g : ∀ k : ℕ, (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (res R F).X (n - k))
    (p q : ℤ) (m : ℕ) (h1 : p = -(m : ℤ)) (h2 : n - m = q) : ((chains R).obj E).X p ⟶ (res R F).X q :=
  (((chains R).obj E).XIsoOfEq h1).hom ≫ (chainsXIso R E m).hom ≫ g m ≫ ((res R F).XIsoOfEq h2).hom

theorem blk_eq {E : Spc} {F : Shv R} {n : ℤ} (g : ∀ k : ℕ, (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (res R F).X (n - k))
    (k m : ℕ) (hm : m = k) (h1 : -(k : ℤ) = -(m : ℤ)) (h2 : n - m = n - k) :
    blk g (-(k : ℤ)) (n - k) m h1 h2 = (chainsXIso R E k).hom ≫ g k := by
  subst hm
  simp [blk]

def ofFam {E : Spc} {F : Shv R} {n : ℤ} (g : ∀ k : ℕ, (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (res R F).X (n - k)) :
    Cochain ((chains R).obj E) (res R F) n :=
  Cochain.mk fun p q hpq => if hp : p ≤ 0 then blk g p q (-p).toNat (by omega) (by omega) else 0

theorem HC_X_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ), ∃ π : ∀ k : ℕ, (HC R F ⋙ HomologicalComplex.eval _ _ n) ⟶ ((evaluation _ PSh).obj (op (SimplexCategory.mk (k)))).op ⋙ (free R).op ⋙ preadditiveYoneda.obj ((res R F).X (n - k)), ∀ E : Spcᵒᵖ, Function.Bijective (fun (x : ((HC R F).obj E).X n) (k : ℕ) => (π k).app E x) := by
  intro R _ F n
  refine ⟨termEval R F n, fun E => ⟨fun x y hxy => ?_, fun g => ?_⟩⟩
  · revert x y
    change ∀ x y : Cochain ((chains R).obj E.unop) (res R F) n, _ → x = y
    intro x y hxy
    apply Cochain.ext
    intro p q hpq
    by_cases hp : 0 < p
    · exact (isZero_chains_X R E.unop p hp).eq_of_src _ _
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨p.natAbs, by omega⟩
      obtain rfl : q = n - k := by omega
      have h := congrFun hxy k
      change (chainsXIso R E.unop k).inv ≫ x.v (-(k : ℤ)) (n - k) _ = (chainsXIso R E.unop k).inv ≫ y.v (-(k : ℤ)) (n - k) _ at h
      exact (cancel_epi _).1 h
  · refine ⟨(ofFam (E := E.unop) g : Cochain ((chains R).obj E.unop) (res R F) n), funext fun k => ?_⟩
    change (chainsXIso R E.unop k).inv ≫ (ofFam g).v (-(k : ℤ)) (n - k) (by omega) = g k
    simp only [ofFam, Cochain.mk_v]
    rw [dif_pos (by omega), blk_eq g k _ (by omega)]
    erw [Iso.inv_hom_id_assoc]

end GlobalTheory.EtC.HCTerms
