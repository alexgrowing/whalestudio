import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianShFactorStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LaurentNoeth

def lmap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : LaurentPolynomial R →+* LaurentPolynomial S :=
  LaurentPolynomial.eval₂ ((LaurentPolynomial.C : S →+* LaurentPolynomial S).comp f) (laurentVarUnit S)

theorem laurentVarUnit_zpow (S : Type) [CommRing S] (n : ℤ) :
    ((laurentVarUnit S ^ n : (LaurentPolynomial S)ˣ) : LaurentPolynomial S) = LaurentPolynomial.T n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, ih, LaurentPolynomial.T_add]; rfl
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul, ih, sub_eq_add_neg, LaurentPolynomial.T_add]; rfl

theorem laurentMap_C_mul_T {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : R) (n : ℤ) :
    lmap f (LaurentPolynomial.C a * LaurentPolynomial.T n) = LaurentPolynomial.C (f a) * LaurentPolynomial.T n := by
  simp [lmap, laurentVarUnit_zpow]

theorem lext {R : Type} [CommRing R] {p p' : LaurentPolynomial R} (h : ∀ n, p.coeff n = p'.coeff n) : p = p' :=
  AddMonoidAlgebra.ext (Finsupp.ext h)

theorem lmap_apply {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : LaurentPolynomial R) (n : ℤ) :
    (lmap f p).coeff n = f (p.coeff n) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Finsupp.add_apply, hp, hq,
      map_add]
  | C_mul_T k a =>
    rw [laurentMap_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp

theorem lmap_injective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (lmap f) := by
  intro p p' h
  refine lext fun n => ?_
  apply hf
  rw [← lmap_apply, ← lmap_apply, h]

theorem lmap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    lmap (g.comp f) = (lmap g).comp (lmap f) := by
  refine RingHom.ext fun p => lext fun n => ?_
  rw [RingHom.comp_apply, lmap_apply, lmap_apply, lmap_apply, RingHom.comp_apply]

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (F : R →+* S) (G : S →+* T) :
    spMap (G.comp F) = spMap G ≫ spMap F := by
  show sch.map (Spec.map (CommRingCat.ofHom (G.comp F))) = sch.map (Spec.map (CommRingCat.ofHom G)) ≫ sch.map (Spec.map (CommRingCat.ofHom F))
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

attribute [local instance] Classical.propDecidable

variable {A : Type} [CommRing A]

def sub (u : A) (s : Finset A) : Subalgebra ℤ A := Algebra.adjoin ℤ (↑(insert u s) : Set A)

theorem sub_mono (u : A) : Monotone (sub u) := fun _ _ h =>
  Algebra.adjoin_mono (Finset.coe_subset.2 (Finset.insert_subset_insert u h))

theorem mem_sub (u : A) (s : Finset A) {a : A} (ha : a ∈ insert u s) : a ∈ sub u s :=
  Algebra.subset_adjoin (Finset.mem_coe.2 ha)

theorem lmap_val_comp (u : A) {s t : Finset A} (hst : s ≤ t) :
    (lmap (sub u t).val.toRingHom).comp (lmap (Subalgebra.inclusion (sub_mono u hst)).toRingHom) =
      lmap (sub u s).val.toRingHom := by
  rw [← lmap_comp]; rfl

def diag (u : A) : Finset A ⥤ CommRingCat.{0} where
  obj s := CommRingCat.of (LaurentPolynomial (sub u s))
  map {s t} h := CommRingCat.ofHom (lmap (Subalgebra.inclusion (sub_mono u (leOfHom h))).toRingHom)
  map_id s := CommRingCat.hom_ext (RingHom.ext fun p => lext fun n => by
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply, lmap_apply]; rfl)
  map_comp f g := CommRingCat.hom_ext (RingHom.ext fun p => lext fun n => by
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, lmap_apply]; rfl)

def cocone (u : A) : Cocone (diag u) where
  pt := CommRingCat.of (LaurentPolynomial A)
  ι := { app := fun s => CommRingCat.ofHom (lmap (sub u s).val.toRingHom)
         naturality := fun s t h => by
           simp only [Functor.const_obj_map, Category.comp_id]
           exact CommRingCat.hom_ext (lmap_val_comp u (leOfHom h)) }

theorem exists_preimage (u : A) (x : LaurentPolynomial A) : ∃ s y, lmap (sub u s).val.toRingHom y = x := by
  induction x using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨s, y, rfl⟩ := hp
    obtain ⟨t, z, rfl⟩ := hq
    refine ⟨s ∪ t, lmap (Subalgebra.inclusion (sub_mono u Finset.subset_union_left)).toRingHom y +
      lmap (Subalgebra.inclusion (sub_mono u Finset.subset_union_right)).toRingHom z, ?_⟩
    rw [map_add, ← RingHom.comp_apply, ← RingHom.comp_apply, ← lmap_comp, ← lmap_comp]
    rfl
  | C_mul_T k a =>
    refine ⟨{a}, LaurentPolynomial.C ⟨a, mem_sub u _ (by simp)⟩ * LaurentPolynomial.T k, ?_⟩
    rw [laurentMap_C_mul_T]
    rfl

theorem cocone_isColimit (u : A) : Nonempty (IsColimit (cocone u)) := by
  haveI : ReflectsColimitsOfShape (Finset A) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    change LaurentPolynomial A at x
    obtain ⟨s, y, hy⟩ := exists_preimage u x
    exact ⟨s, y, hy.symm⟩
  · intro s t xs xt h
    refine ⟨s ∪ t, homOfLE Finset.subset_union_left, homOfLE Finset.subset_union_right, ?_⟩
    apply lmap_injective (sub u (s ∪ t)).val.toRingHom (fun a b hab => Subtype.ext hab)
    · change (lmap (sub u (s ∪ t)).val.toRingHom).comp (lmap _) xs = (lmap (sub u (s ∪ t)).val.toRingHom).comp (lmap _) xt
      rw [← lmap_comp, ← lmap_comp]
      exact h

theorem sub_fg (u : A) (s : Finset A) : (sub u s).FG := ⟨insert u s, rfl⟩

end GlobalTheory.EtC.LaurentNoeth

open GlobalTheory.EtC.LaurentNoeth in

theorem GlobalTheory.EtC.laurent_vanishing_of_noetherian : ∀ (q : ℕ) [NeZero q], (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) → ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  classical
  intro q _ hN A _ hA hq n i hn
  refine ⟨fun x y => ?_⟩
  suffices key : ∀ x : Ht q (sp (LaurentPolynomial A)) n i, x = 0 by rw [key x, key y]
  intro x
  set u : A := ((hq.unit⁻¹ : Aˣ) : A)
  obtain ⟨hc⟩ := cocone_isColimit u
  have hqL : IsUnit (q : LaurentPolynomial A) := by
    have := hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A); simpa using this
  obtain ⟨j, y, hy⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (diag u) (cocone u) hc n i).1 x hqL
  haveI : Algebra.FiniteType ℤ (sub u j) := (Subalgebra.fg_iff_finiteType _).1 (sub_fg u j)
  haveI : IsNoetherianRing (sub u j) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨C, _, hCn, hCsh, f, g, hfg⟩ := GlobalTheory.T.exists_noetherian_sh_factorization (sub u j) A hA (sub u j).val.toRingHom
  haveI := hCn
  have hqS : IsUnit (q : sub u j) := by
    refine isUnit_iff_exists_inv.2 ⟨⟨u, mem_sub u j (Finset.mem_insert_self u j)⟩, ?_⟩
    apply Subtype.ext
    simp [u]
  have hqC : IsUnit (q : C) := by have := hqS.map f; simpa using this
  haveI := hN C hCsh hqC n i hn
  have e : (cocone u).ι.app j = CommRingCat.ofHom ((lmap g).comp (lmap f)) := by
    rw [← lmap_comp, hfg]; rfl
  rw [← hy, e]
  change pull _ (spMap ((lmap g).comp (lmap f))) _ _ y = 0
  rw [spMap_comp']
  refine (pull_comp (ZMod q) (spMap (lmap g)) (spMap (lmap f)) (tw q i) n y).trans ?_
  have : pull _ (spMap (lmap f)) (tw q i) n y = 0 := Subsingleton.elim _ _
  rw [this, map_zero]
