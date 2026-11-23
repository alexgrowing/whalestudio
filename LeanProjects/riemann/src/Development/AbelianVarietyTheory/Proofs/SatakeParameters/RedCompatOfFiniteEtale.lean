import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsZeroFreeSchOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodSemilinear

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.Tr

open GlobalTheory.EtC.CupSpec

section CyclicComplexMaps

variable {R : Type} [CommRing R]

theorem chainMap_f {X Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Z) (p : ℕ) :
    (chainsXIso R (sch.obj X) p).inv ≫ (chainMap R t).f (-(p : ℤ)) = t ≫ (chainsXIso R (sch.obj Z) p).inv := by
  have h1 : (chainMap R t).f (-(p : ℤ)) =
      (chainsXIso R (sch.obj X) p).hom ≫ ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (simpMap R t)).f p ≫
        (chainsXIso R (sch.obj Z) p).inv :=
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := p) rfl
  rw [h1, Iso.inv_hom_id_assoc]
  rfl

theorem ev_chainMap {X Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Z) {I : Cx R} {n : ℤ}
    (α : Cochain ((chains R).obj (sch.obj Z)) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (y : Sx (sch.obj X) p U) :
    ev ((Cochain.ofHom (chainMap R t)).comp α (zero_add n)) p s h U y =
      Sec.map ((chainsXIso R (sch.obj Z) p).inv ≫ α.v _ _ h) (Sec.map t (freeGen R (yoneda.obj X) U y)) := by
  rw [ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chainMap_f]
  rfl

end CyclicComplexMaps

section Key

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

theorem secMap_sum {F G : Shv R} {ι : Type*} (s : Finset ι) (g : ι → (F ⟶ G)) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (∑ j ∈ s, g j) a = ∑ j ∈ s, Sec.map (g j) a :=
  map_sum (mapHom F G a) g s

theorem exists_free_restr (P : PSh) : ∃ ι : (free R).obj P ⟶ (restr φ).obj ((free S).obj P),
    ∀ U x, Sec.map ι (freeGen R P U x) = (show Sec ((restr φ).obj ((free S).obj P)) U from freeGen S P U x) :=
  free_exists P _ (fun U x => show Sec ((restr φ).obj ((free S).obj P)) U from freeGen S P U x)
    (fun V U g x => freeGen_res P g x)

theorem isTransfer_reduce {Z X : Scheme.{0}} {f : Z ⟶ X} {t : freeSch R X ⟶ freeSch R Z} (ht : IsTransfer R f t)
    (ι : freeSch R Z ⟶ (restr φ).obj (freeSch S Z))
    (hι : ∀ U x, Sec.map ι (freeGen R (yoneda.obj Z) U x) =
      (show Sec ((restr φ).obj (freeSch S Z)) U from freeGen S (yoneda.obj Z) U x))
    (t' : freeSch S X ⟶ freeSch S Z)
    (ht' : ∀ U x, Sec.map t' (freeGen S (yoneda.obj X) U x) =
      (show Sec (freeSch S Z) U from Sec.map ι (Sec.map t (freeGen R (yoneda.obj X) U x)))) :
    IsTransfer S f t' := by
  intro T x m s hs hiso
  apply free_ext
  intro V w
  have e := congrArg (fun g => Sec.map ι (Sec.map g (freeGen R (yoneda.obj T) V w))) (ht T x m s hs hiso)
  change Sec.map ι (Sec.map t (Sec.map ((free R).map (yoneda.map x)) (freeGen R (yoneda.obj T) V w))) =
    Sec.map ι (Sec.map (∑ j, (free R).map (yoneda.map (s j))) (freeGen R (yoneda.obj T) V w)) at e
  change Sec.map t' (Sec.map ((free S).map (yoneda.map x)) (freeGen S (yoneda.obj T) V w)) =
    Sec.map (∑ j, (free S).map (yoneda.map (s j))) (freeGen S (yoneda.obj T) V w)
  rw [freeGen_map, ht']
  rw [freeGen_map] at e
  refine e.trans ?_
  rw [secMap_sum, secMap_sum]
  refine (map_sum (ι.hom.app (op V)).hom _ Finset.univ).trans (Finset.sum_congr rfl fun j _ => ?_)
  change Sec.map ι (Sec.map ((free R).map (yoneda.map (s j))) (freeGen R (yoneda.obj T) V w)) = _
  rw [freeGen_map, freeGen_map, hι]

theorem key_free {Z X : Scheme.{0}} {f : Z ⟶ X} {I : Shv R} {J : Shv S} (A : freeSch R Z ⟶ I) (B : freeSch S Z ⟶ J)
    (ρ' : I ⟶ (restr φ).obj J)
    (hAB : ∀ V z, Sec.map B (freeGen S (yoneda.obj Z) V z) = Sec.map ρ' (Sec.map A (freeGen R (yoneda.obj Z) V z)))
    {tR : freeSch R X ⟶ freeSch R Z} (htR : IsTransfer R f tR) {tS : freeSch S X ⟶ freeSch S Z}
    (huniq : ∀ t, IsTransfer S f t → t = tS) (U : Scheme.{0}) (y : U ⟶ X) :
    Sec.map B (Sec.map tS (freeGen S (yoneda.obj X) U y)) =
      Sec.map ρ' (Sec.map A (Sec.map tR (freeGen R (yoneda.obj X) U y))) := by
  obtain ⟨ι, hι⟩ := exists_free_restr φ (yoneda.obj Z)
  obtain ⟨t', ht'⟩ := free_exists (R := S) (yoneda.obj X) (freeSch S Z)
    (fun U y => show Sec (freeSch S Z) U from Sec.map ι (Sec.map tR (freeGen R (yoneda.obj X) U y)))
    (fun V U g y => by
      refine (map_res ι g _).trans ?_
      change Sec.map ι (Sec.res g (Sec.map tR (freeGen R (yoneda.obj X) U y))) = _
      rw [map_res, freeGen_res])
  have hT := huniq t' (isTransfer_reduce φ htR ι hι t' ht')
  subst hT
  rw [ht']
  have hm : ι ≫ (restr φ).map B = A ≫ ρ' := free_ext _ _ (fun V z => by
    change Sec.map B (Sec.map ι (freeGen R (yoneda.obj Z) V z)) = Sec.map ρ' (Sec.map A (freeGen R (yoneda.obj Z) V z))
    rw [hι]
    exact hAB V z)
  exact congrArg (fun g => Sec.map g (Sec.map tR (freeGen R (yoneda.obj X) U y))) hm

end Key

theorem redCompat_of_finite_etale (l : ℕ) [Fact l.Prime] {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f]
    (hex : ∀ (R : Type) [CommRing R], ∃! t, IsTransfer R f t) (n i : ℤ) : RedCompat l f n i := by
  intro k x
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl⟩
  have hd : l ^ k ∣ l ^ (k + 1) := pow_dvd_pow l (Nat.le_succ k)
  obtain ⟨t0, ht0, -⟩ := hex (ZMod (l ^ (k + 1)))
  have htQ := transfer_spec (ZMod (l ^ (k + 1))) ⟨t0, ht0⟩
  obtain ⟨t1, ht1, hu1⟩ := hex (ZMod (l ^ k))
  have huniq : ∀ t, IsTransfer (ZMod (l ^ k)) f t → t = transfer (ZMod (l ^ k)) f := fun t ht =>
    (hu1 t ht).trans (hu1 _ (transfer_spec _ ⟨t1, ht1⟩)).symm
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (redMap (l ^ (k + 1)) (l ^ k) i).image_exists (sch.obj Z) n α
  have h1 : red (l ^ (k + 1)) (l ^ k) (sch.obj Z) n i (CohomologyClass.mk α) = CohomologyClass.mk β :=
    (redMap (l ^ (k + 1)) (l ^ k) i).op_spec _ n α β hβ
  rw [h1]
  have key := (redMap (l ^ (k + 1)) (l ^ k) i).op_spec (sch.obj X) n
    (zcomp (Cocycle.ofHom (chainMap _ (transfer _ f))) α (zero_add n))
    (zcomp (Cocycle.ofHom (chainMap _ (transfer _ f))) β (zero_add n)) (by
      intro p s h U y
      change ev ((Cochain.ofHom (chainMap _ (transfer _ f))).comp β.1 (zero_add n)) p s h U y =
        (redMap (l ^ (k + 1)) (l ^ k) i).app U s
          (ev ((Cochain.ofHom (chainMap _ (transfer _ f))).comp α.1 (zero_add n)) p s h U y)
      rw [ev_chainMap, ev_chainMap]
      exact key_free (ZMod.castHom hd (ZMod (l ^ k))) _ _
        (ScalarExt.semiHom (redMap (l ^ (k + 1)) (l ^ k) i) (ScalarExt.zmod_semilinear hd _) s)
        (fun V z => (ev_def β.1 p s h V z).symm.trans ((hβ p s h V z).trans (congrArg _ (ev_def α.1 p s h V z))))
        htQ huniq U y)
  exact key

end GlobalTheory.EtC.Tr
