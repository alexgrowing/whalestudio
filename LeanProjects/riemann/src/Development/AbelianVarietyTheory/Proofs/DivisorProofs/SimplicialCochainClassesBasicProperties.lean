import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ClsBasic

variable {R : Type} [CommRing R]

theorem single_add' {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {p q : ℤ}
    (f g : K.X p ⟶ L.X q) (n : ℤ) : Cochain.single (f + g) n = Cochain.single f n + Cochain.single g n := by
  ext p' q' h
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq; simp
    · simp [Cochain.single_v_eq_zero' _ _ _ _ _ hq]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp]

theorem ofHom_comp_single {C : Type*} [Category C] [Preadditive C] {K K' L : CochainComplex C ℤ} {p q : ℤ}
    (g : K' ⟶ K) (f : K.X p ⟶ L.X q) (n : ℤ) :
    (Cochain.ofHom g).comp (Cochain.single f n) (zero_add n) = Cochain.single (g.f p ≫ f) n := by
  ext p' q' h
  rw [Cochain.comp_v _ _ (zero_add n) p' p' q' (add_zero p') h, Cochain.ofHom_v]
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq; simp
    · simp [Cochain.single_v_eq_zero' _ _ _ _ _ hq]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp]

theorem resι_d (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  have h := (injectiveResolution F).ι'.comm 0 1
  have h0 : ((singleFunctor (Shv R) 0).obj F).d 0 1 = 0 := by simp
  rw [h0, zero_comp] at h
  change ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ (injectiveResolution F).ι'.f 0) ≫ (injectiveResolution F).cochainComplex.d 0 1 = 0
  erw [Category.assoc, h]
  all_goals first | rfl | exact comp_zero

theorem chains_d (E : Spc) (n : ℕ) :
    ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (chainsXIso R E (n + 1)).hom ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫
        (chainsXIso R E n).inv := by
  have h := HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := n + 1) (j := n) rfl rfl
  have h2 : ((chainsN R).obj E).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ n
  rw [← h2]
  exact h

theorem chainsXIso_nat {E E' : Spc} (f : E' ⟶ E) (n : ℕ) :
    ((chains R).map f).f (-(n : ℤ)) ≫ (chainsXIso R E n).hom = (chainsXIso R E' n).hom ≫ (free R).map (f.app (op ⦋n⦌)) := by
  have h := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl
  change (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(n : ℤ)) ≫ _ = _
  rw [h]
  simp only [chainsXIso]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem δ_cls {E : Spc} {F : Shv R} {n : ℕ} (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) :
    δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n) =
      (((n + 1 : ℕ) : ℤ)).negOnePow • Cochain.single (p := -((n + 1 : ℕ) : ℤ)) (q := 0)
        ((chainsXIso R E (n + 1)).hom ≫ cobd s ≫ resι R F) ((n + 1 : ℕ) : ℤ) := by
  rw [Cochain.δ_single _ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (-((n + 1 : ℕ) : ℤ)) 1 (by push_cast; ring) rfl]
  rw [Category.assoc, Category.assoc, resι_d, comp_zero, comp_zero, Cochain.single_zero, zero_add]
  congr 2
  rw [chains_d, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [← Category.assoc]
  congr 1
  rw [cobd, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.zsmul_comp]

end GlobalTheory.EtC.ClsBasic

open GlobalTheory.EtC.ClsBasic in

theorem GlobalTheory.EtC.isCls_basic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ), (∀ s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd s = 0 → ∃ x : H R E F n, IsCls s x) ∧ (∀ (s s' : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x x' : H R E F n), IsCls s x → IsCls s' x' → IsCls (s + s') (x + x')) ∧ (∀ (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x x' : H R E F n), IsCls s x → IsCls s x' → x = x') ∧ (∀ (t : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x : H R E F ((n + 1 : ℕ) : ℤ)), IsCls (cobd t) x → x = 0) ∧ ∀ (E' : Spc) (f : E' ⟶ E) (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x : H R E F n), IsCls s x → IsCls ((free R).map (f.app (op ⦋n⦌)) ≫ s) (pull R f F n x) := by
  intro R _ F E n
  refine ⟨fun s hs => ?_, fun s s' x x' hx hx' => ?_, fun s x x' hx hx' => ?_, fun t x hx => ?_, fun E' f s x hx => ?_⟩
  · refine ⟨CohomologyClass.mk (Cocycle.mk (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n)
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) ?_), _, rfl, rfl⟩
    rw [δ_cls, hs, zero_comp, comp_zero, Cochain.single_zero, smul_zero]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    refine ⟨z + z', (CohomologyClass.mk_add z z').symm, ?_⟩
    change z.1 + z'.1 = _
    rw [hz, hz', ← single_add', Preadditive.add_comp, Preadditive.comp_add]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    have : z = z' := Cocycle.ext (hz.trans hz'.symm)
    rw [this]
  · obtain ⟨z, rfl, hz⟩ := hx
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n : ℤ) (by push_cast; ring)]
    refine ⟨(((n + 1 : ℕ) : ℤ)).negOnePow • Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ t ≫ resι R F) n, ?_⟩
    rw [δ_units_smul, δ_cls, smul_smul, Int.units_mul_self, one_smul, hz]
  · obtain ⟨z, rfl, hz⟩ := hx
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add _), rfl, ?_⟩
    change (Cochain.ofHom ((chains R).map f)).comp z.1 (zero_add _) = _
    rw [hz, ofHom_comp_single, ← Category.assoc, chainsXIso_nat]
    simp only [Category.assoc]

end
