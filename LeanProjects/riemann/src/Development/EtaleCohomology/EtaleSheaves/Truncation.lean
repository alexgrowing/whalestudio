import Development.EtaleCohomology.EtaleSheaves.TruncPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces LateralTheory.E.FiltPf LateralTheory.E.TruncPf
open CochainComplex.HomComplex

namespace LateralTheory.E.TruncationInclusionIso

section Gen
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

local notation "eG" => ComplexShape.embeddingUpIntGE

abbrev sT (K : CochainComplex C ℤ) (a : ℤ) : CochainComplex C ℤ := (K.restriction (eG a)).extend (eG a)

def comp (K : CochainComplex C ℤ) (a : ℤ) {k : ℕ} {i : ℤ} (hk : (eG a).f k = i) : (sT K a).X i ⟶ K.X i :=
  ((K.restriction (eG a)).extendXIso (eG a) hk).hom ≫ (K.restrictionXIso (eG a) hk).hom

theorem comp_indep (K : CochainComplex C ℤ) (a : ℤ) {k k' : ℕ} {i : ℤ} (hk : (eG a).f k = i)
    (hk' : (eG a).f k' = i) : comp K a hk = comp K a hk' := by
  obtain rfl : k = k' := (eG a).injective_f (hk.trans hk'.symm)
  rfl

theorem sq (K : CochainComplex C ℤ) (a : ℤ) {k : ℕ} {i j : ℤ} (hi : (eG a).f k = i) (hj : (eG a).f (k + 1) = j) :
    comp K a hi ≫ K.d i j = (sT K a).d i j ≫ comp K a hj := by
  rw [HomologicalComplex.extend_d_eq _ _ hi hj, HomologicalComplex.restriction_d_eq _ _ hi hj]
  simp only [comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem le_of_f {a : ℤ} {k : ℕ} {i : ℤ} (hk : (eG a).f k = i) : a ≤ i := by
  change a + (k : ℤ) = i at hk; omega

theorem f_toNat {a i : ℤ} (h : a ≤ i) : (eG a).f (i - a).toNat = i := by
  change a + ((i - a).toNat : ℤ) = i; omega

theorem zero_below (K : CochainComplex C ℤ) {a i : ℤ} (h : i < a) : IsZero ((sT K a).X i) :=
  HomologicalComplex.isZero_extend_X _ _ i (fun _ hk => by have := le_of_f hk; omega)

def ιT (K : CochainComplex C ℤ) (a : ℤ) : sT K a ⟶ K where
  f i := if h : a ≤ i then comp K a (f_toNat h) else 0
  comm' i j hij := by
    change i + 1 = j at hij
    by_cases h : a ≤ i
    · rw [dif_pos h, dif_pos (by omega)]
      have hj : (eG a).f ((i - a).toNat + 1) = j := by
        change a + (((i - a).toNat + 1 : ℕ) : ℤ) = j; push_cast; omega
      rw [sq K a (f_toNat h) hj]
      congr 1
      apply comp_indep
    · exact (zero_below K (by omega)).eq_of_src _ _

theorem ιT_f (K : CochainComplex C ℤ) (a : ℤ) {k : ℕ} {i : ℤ} (hk : (eG a).f k = i) :
    (ιT K a).f i = comp K a hk := by
  dsimp only [ιT]
  rw [dif_pos (le_of_f hk)]
  apply comp_indep

instance (K : CochainComplex C ℤ) (a : ℤ) {k : ℕ} {i : ℤ} (hk : (eG a).f k = i) : IsIso (comp K a hk) := by
  dsimp only [comp]; infer_instance

theorem isIso_ιT (K : CochainComplex C ℤ) {a i : ℤ} (h : a ≤ i) : IsIso ((ιT K a).f i) := by
  rw [ιT_f K a (f_toNat h)]; infer_instance

def sTMap {K L : CochainComplex C ℤ} (f : K ⟶ L) (a : ℤ) : sT K a ⟶ sT L a :=
  HomologicalComplex.extendMap (HomologicalComplex.restrictionMap f (eG a)) (eG a)

theorem ιT_nat {K L : CochainComplex C ℤ} (f : K ⟶ L) (a : ℤ) : sTMap f a ≫ ιT L a = ιT K a ≫ f := by
  ext i
  simp only [HomologicalComplex.comp_f]
  by_cases h : a ≤ i
  · have hk := f_toNat h
    rw [ιT_f K a hk, ιT_f L a hk]
    rw [sTMap, HomologicalComplex.extendMap_f _ _ hk, HomologicalComplex.restrictionMap_f' _ _ hk]
    simp only [comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  · exact (zero_below K (by omega)).eq_of_src _ _

end Gen

def TruncData' : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  ∃ (P : ℕ) (K' L' : Cx R) (f' : K' ⟶ L') (g : K' ⟶ K) (h : L' ⟶ L),
    (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K'.X i) ∧ IsZero (L'.X i)) ∧ f' ≫ h = g ≫ f ∧
    (∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p) ∧ IsIso (h.f p)) ∧
    (∀ p : ℤ, p < -(n + 1) → IsZero (K'.X p) ∧ IsZero (L'.X p))

theorem truncData' : TruncData' := by
  intro R _ K L f n hz
  refine ⟨(n + 1).toNat, sT K (-(n + 1)), sT L (-(n + 1)), sTMap f _, ιT K _, ιT L _, fun i hi => ?_, ιT_nat f _,
    fun p hp => ⟨isIso_ιT K hp, isIso_ιT L hp⟩, fun p hp => ⟨zero_below K hp, zero_below L hp⟩⟩
  by_cases h : -(n + 1) ≤ i
  · have hi' : 0 < i := by omega
    have := isIso_ιT K h
    have := isIso_ιT L h
    exact ⟨(hz i hi').1.of_iso (asIso ((ιT K _).f i)), (hz i hi').2.of_iso (asIso ((ιT L _).f i))⟩
  · exact ⟨zero_below K (by omega), zero_below L (by omega)⟩

variable (R : Type) [CommRing R] (F : Shv R)

theorem relK_of_square' {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L') (g : K' ⟶ K) (h : L' ⟶ L)
    (w : f' ≫ h = g ≫ f) (n : ℤ)
    (hg : ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R g F m))
    (hh : ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R h F m))
    (hf' : RelK R F n f') : RelK R F n f := by
  have key : ∀ (m : ℤ) (z : HK R L F m),
      HK.pull R f' F m (HK.pull R h F m z) = HK.pull R g F m (HK.pull R f F m z) := by
    intro m z
    rw [← LateralTheory.E.TruncPf.pull_comp, ← LateralTheory.E.TruncPf.pull_comp, w]
  refine ⟨fun m hm y => ?_, fun x1 x2 hx => ?_⟩
  · obtain ⟨z', hz'⟩ := hf'.1 m hm (HK.pull R g F m y)
    obtain ⟨z, rfl⟩ := (hh m (by omega)).2 z'
    exact ⟨z, (hg m (by omega)).1 ((key m z).symm.trans hz')⟩
  · apply (hh n le_rfl).1
    apply hf'.2
    rw [key, key, hx]

theorem Trunc_of (hB : TruncBij) : LateralTheory.E.FiltPf.Trunc := by
  intro R _ F K L f n hz
  obtain ⟨P, K', L', f', g, h, hb, w, hiso, hzero⟩ := truncData' R f n hz
  refine ⟨P, K', L', f', hb, fun hp p => ?_, relK_of_square' R F f f' g h w n
    (hB R F g n fun q hq => (hiso q hq).1) (hB R F h n fun q hq => (hiso q hq).2)⟩
  by_cases hq : -(n + 1) ≤ -(p : ℤ)
  · have := (hiso _ hq).1
    have := (hiso _ hq).2
    refine relK_of_square R F (pieceC R f' p) (pieceC R f p)
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (g.f _))
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (h.f _)) ?_ n
      (fun m _ => pull_bij_of_iso R F _ m) (fun m _ => pull_bij_of_iso R F _ m) (hp p)
    simp only [pieceC, ← Functor.map_comp]
    congr 1
    have := congrArg (fun φ => HomologicalComplex.Hom.f φ (-(p : ℤ))) w
    simp only [HomologicalComplex.comp_f] at this
    exact this.symm
  · exact relK_of_isZero R F _ n
      (Functor.map_isZero _ (hzero _ (by omega)).1) (Functor.map_isZero _ (hzero _ (by omega)).2)

end LateralTheory.E.TruncationInclusionIso
