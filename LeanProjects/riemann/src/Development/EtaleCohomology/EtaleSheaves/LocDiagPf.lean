import Development.EtaleCohomology.EtaleSheaves.ZarLocalPf

noncomputable section
open CategoryTheory Limits Opposite

namespace LateralTheory.E.LocDiagPf

open Classical in

def g {S : Type} [CommRing S] (p : PrimeSpectrum S) (s : Finset p.asIdeal.primeCompl) : S :=
  ∏ x ∈ s, (x : S)

variable {S : Type} [CommRing S] (p : PrimeSpectrum S)

theorem g_mem (s : Finset p.asIdeal.primeCompl) : g p s ∈ p.asIdeal.primeCompl := by
  classical
  unfold g
  convert Submonoid.prod_mem _ (fun (x : p.asIdeal.primeCompl) _ => x.2)

theorem g_dvd {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) : g p s ∣ g p t := by
  classical
  unfold g
  convert Finset.prod_dvd_prod_of_subset s t (fun x : p.asIdeal.primeCompl => (x : S)) h

theorem g_single (y : p.asIdeal.primeCompl) : g p {y} = (y : S) := by
  classical
  unfold g
  convert Finset.prod_singleton (fun x : p.asIdeal.primeCompl => (x : S)) y

theorem unitAway {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) :
    IsUnit (algebraMap S (Localization.Away (g p t)) (g p s)) :=
  isUnit_of_dvd_unit (map_dvd _ (g_dvd p h)) (IsLocalization.Away.algebraMap_isUnit _)

def tr {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) :
    Localization.Away (g p s) →+* Localization.Away (g p t) :=
  IsLocalization.Away.lift (g p s) (unitAway p h)

theorem tr_comp {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) :
    (tr p h).comp (algebraMap S _) = algebraMap S _ :=
  IsLocalization.Away.lift_comp _ _

theorem tr_apply {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) (x : S) :
    tr p h (algebraMap S _ x) = algebraMap S _ x :=
  IsLocalization.Away.lift_eq _ _ _

theorem away_ext {s : Finset p.asIdeal.primeCompl} {P : Type} [CommRing P]
    {u v : Localization.Away (g p s) →+* P}
    (h : u.comp (algebraMap S _) = v.comp (algebraMap S _)) : u = v :=
  IsLocalization.ringHom_ext (Submonoid.powers (g p s)) h

def Dg : Finset p.asIdeal.primeCompl ⥤ CommRingCat.{0} where
  obj s := CommRingCat.of (Localization.Away (g p s))
  map {s t} h := CommRingCat.ofHom (tr p (leOfHom h))
  map_id s := by
    ext1
    apply away_ext
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id, tr_comp]
    rfl
  map_comp {s t u} a b := by
    ext1
    apply away_ext
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp]
    rw [RingHom.comp_assoc, tr_comp, tr_comp, tr_comp]

theorem unitLoc (s : Finset p.asIdeal.primeCompl) :
    IsUnit (algebraMap S (Localization.AtPrime p.asIdeal) (g p s)) :=
  IsLocalization.map_units _ (⟨g p s, g_mem p s⟩ : p.asIdeal.primeCompl)

def toLoc (s : Finset p.asIdeal.primeCompl) :
    Localization.Away (g p s) →+* Localization.AtPrime p.asIdeal :=
  IsLocalization.Away.lift (g p s) (unitLoc p s)

theorem toLoc_comp (s : Finset p.asIdeal.primeCompl) :
    (toLoc p s).comp (algebraMap S _) = algebraMap S _ :=
  IsLocalization.Away.lift_comp _ _

theorem toLoc_apply (s : Finset p.asIdeal.primeCompl) (x : S) :
    toLoc p s (algebraMap S _ x) = algebraMap S _ x :=
  IsLocalization.Away.lift_eq _ _ _

def Cc : Cocone (Dg p) where
  pt := CommRingCat.of (Localization.AtPrime p.asIdeal)
  ι :=
    { app := fun s => (CommRingCat.ofHom (toLoc p s) : (Dg p).obj s ⟶ CommRingCat.of (Localization.AtPrime p.asIdeal))
      naturality := fun s t h => by
        ext1
        apply away_ext
        simp only [Functor.const_obj_map, CommRingCat.hom_comp, CommRingCat.hom_ofHom, Dg]
        rw [RingHom.comp_assoc, tr_comp, toLoc_comp, RingHom.comp_assoc, toLoc_comp]
        rfl }

theorem Cc_ι (s : Finset p.asIdeal.primeCompl) : ((Cc p).ι.app s).hom = toLoc p s := rfl

def phi (c : Cocone (Dg p)) : S →+* c.pt :=
  (c.ι.app ∅).hom.comp (algebraMap S (Localization.Away (g p ∅)))

theorem cocone_comp (c : Cocone (Dg p)) (s : Finset p.asIdeal.primeCompl) :
    (c.ι.app s).hom.comp (algebraMap S (Localization.Away (g p s))) = phi p c := by
  have hw := c.w (homOfLE (Finset.empty_subset s))
  unfold phi
  rw [← hw]
  ext x
  exact congrArg (c.ι.app s).hom (tr_apply p (Finset.empty_subset s) x).symm

theorem phi_unit (c : Cocone (Dg p)) (y : p.asIdeal.primeCompl) : IsUnit (phi p c y) := by
  rw [← DFunLike.congr_fun (cocone_comp p c {y}) (y : S)]
  have hy : IsUnit (algebraMap S (Localization.Away (g p {y})) y) := by
    rw [show (y : S) = g p {y} from (g_single p y).symm]
    exact IsLocalization.Away.algebraMap_isUnit _
  exact IsUnit.map (c.ι.app {y}).hom hy

def isColim : IsColimit (Cc p) where
  desc c := CommRingCat.ofHom (IsLocalization.lift (M := p.asIdeal.primeCompl)
    (S := Localization.AtPrime p.asIdeal) (phi_unit p c))
  fac c s := by
    ext1
    apply away_ext
    ext x
    change (IsLocalization.lift (M := p.asIdeal.primeCompl) (S := Localization.AtPrime p.asIdeal)
      (phi_unit p c)) (toLoc p s (algebraMap S _ x)) =
      (c.ι.app s).hom (algebraMap S (Localization.Away (g p s)) x)
    rw [toLoc_apply, IsLocalization.lift_eq]
    exact (DFunLike.congr_fun (cocone_comp p c s) x).symm
  uniq c m hm := by
    ext1
    refine IsLocalization.ringHom_ext (S := Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl ?_
    ext x
    have hx := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (hm ∅))
      (algebraMap S (Localization.Away (g p ∅)) x)
    change m.hom (algebraMap S (Localization.AtPrime p.asIdeal) x) =
      (IsLocalization.lift (M := p.asIdeal.primeCompl) (S := Localization.AtPrime p.asIdeal)
      (phi_unit p c)) (algebraMap S _ x)
    rw [IsLocalization.lift_eq]
    refine Eq.trans ?_ hx
    change _ = m.hom (toLoc p ∅ (algebraMap S _ x))
    rw [toLoc_apply]

theorem LocDiag_of : LateralTheory.E.ZarLocalPf.LocDiag := by
  intro S _ p
  refine ⟨Finset p.asIdeal.primeCompl, inferInstance, inferInstance, Dg p, Cc p,
    ⟨isColim p⟩, id, ∅, algebraMap S (Localization.Away (g p ∅)), ?_⟩
  intro k m
  refine ⟨g p k, g_mem p k, RingHom.id _, ?_⟩
  ext x
  exact tr_apply p (leOfHom m) x

end LateralTheory.E.LocDiagPf
