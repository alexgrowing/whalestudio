import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StrictlyHenselianIsColimit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfEtaleOfIsIndEtale
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC.GmPhiNoeth

theorem coeff_laurentMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : LaurentPolynomial R) (n : ℤ) :
    (laurentMap f p).coeff n = f (p.coeff n) := by
  simp [laurentMap]

theorem laurentMap_id (R : Type) [CommRing R] : laurentMap (RingHom.id R) = RingHom.id _ :=
  RingHom.ext fun p => AddMonoidAlgebra.ext (Finsupp.ext fun n => by rw [coeff_laurentMap]; rfl)

def laurentFunctor : CommRingCat.{0} ⥤ CommRingCat.{0} where
  obj R := CommRingCat.of (LaurentPolynomial R)
  map f := CommRingCat.ofHom (laurentMap f.hom)
  map_id R := by
    change CommRingCat.ofHom (laurentMap (RingHom.id R)) = _
    rw [laurentMap_id]; rfl
  map_comp f g := by
    change CommRingCat.ofHom (laurentMap (g.hom.comp f.hom)) = _
    rw [GmPhiNat.laurentMap_comp]; rfl

def isColimit_laurent {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}
    (hc : IsColimit c) : IsColimit (laurentFunctor.mapCocone c) := by
  haveI : ReflectsColimitsOfShape J (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have hc' : IsColimit ((forget CommRingCat.{0}).mapCocone c) := isColimitOfPreserves _ hc

  have hsurj : ∀ a : c.pt, ∃ j, ∃ b : D.obj j, (c.ι.app j).hom b = a := fun a =>
    Types.jointly_surjective_of_isColimit hc' a

  have hker : ∀ j (b : D.obj j), (c.ι.app j).hom b = 0 → ∃ k, ∃ f : j ⟶ k, (D.map f).hom b = 0 := by
    intro j b hb
    have h := (Types.FilteredColimit.isColimit_eq_iff' hc' b 0).1 (by
      change (c.ι.app j).hom b = (c.ι.app j).hom 0
      rw [hb, map_zero])
    obtain ⟨k, f, hf⟩ := h
    refine ⟨k, f, ?_⟩
    change (D.map f).hom b = (D.map f).hom 0 at hf
    rw [hf, map_zero]
  have hw : ∀ {j k : J} (f : j ⟶ k) (y : LaurentPolynomial (D.obj j)),
      laurentMap (c.ι.app k).hom (laurentMap (D.map f).hom y) = laurentMap (c.ι.app j).hom y := by
    intro j k f y
    rw [← RingHom.comp_apply, ← GmPhiNat.laurentMap_comp, ← CommRingCat.hom_comp, c.w f]
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (laurentFunctor.mapCocone c)) ?_ ?_)
  · intro (x : LaurentPolynomial c.pt)
    suffices h : ∃ j, ∃ y : LaurentPolynomial (D.obj j), laurentMap (c.ι.app j).hom y = x by
      obtain ⟨j, y, hy⟩ := h
      exact ⟨j, y, hy.symm⟩
    induction x using LaurentPolynomial.induction_on' with
    | add p p' hp hp' =>
      obtain ⟨j, y, rfl⟩ := hp
      obtain ⟨j', y', rfl⟩ := hp'
      refine ⟨IsFiltered.max j j', laurentMap (D.map (IsFiltered.leftToMax j j')).hom y +
        laurentMap (D.map (IsFiltered.rightToMax j j')).hom y', ?_⟩
      rw [map_add, hw, hw]
    | C_mul_T n a =>
      obtain ⟨j, b, rfl⟩ := hsurj a
      refine ⟨j, LaurentPolynomial.C b * LaurentPolynomial.T n, ?_⟩
      rw [map_mul, GmPhiNat.laurentMap_T, ← RingHom.comp_apply, GmPhiNat.laurentMap_C, RingHom.comp_apply]
  · intro i j (xi : LaurentPolynomial (D.obj i)) (xj : LaurentPolynomial (D.obj j)) h
    change laurentMap (c.ι.app i).hom xi = laurentMap (c.ι.app j).hom xj at h
    let m := IsFiltered.max i j
    let fi := IsFiltered.leftToMax i j
    let fj := IsFiltered.rightToMax i j
    let z : LaurentPolynomial (D.obj m) := laurentMap (D.map fi).hom xi - laurentMap (D.map fj).hom xj
    have hz : laurentMap (c.ι.app m).hom z = 0 := by
      simp only [z, map_sub, hw, h, sub_self]

    have hfin : ∀ s : Finset ℤ, ∃ k, ∃ h : m ⟶ k, ∀ n ∈ s, (D.map h).hom (z.coeff n) = 0 := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty => exact ⟨m, 𝟙 m, fun n hn => absurd hn (Finset.notMem_empty n)⟩
      | insert n s _ ih =>
        obtain ⟨k₁, h₁, hk₁⟩ := ih
        have hn : (c.ι.app m).hom (z.coeff n) = 0 := by
          rw [← coeff_laurentMap, hz]; rfl
        obtain ⟨k₂, h₂, hk₂⟩ := hker m _ hn
        obtain ⟨k, g₁, g₂, hg⟩ := IsFiltered.span h₁ h₂
        refine ⟨k, h₁ ≫ g₁, fun n' hn' => ?_⟩
        rcases Finset.mem_insert.1 hn' with rfl | hn'
        · rw [hg, D.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, hk₂, map_zero]
        · rw [D.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, hk₁ n' hn', map_zero]
    obtain ⟨k, hmk, hk⟩ := hfin z.coeff.support
    have hz0 : laurentMap (D.map hmk).hom z = 0 := by
      refine AddMonoidAlgebra.ext (Finsupp.ext fun n => ?_)
      rw [coeff_laurentMap]
      by_cases hn : n ∈ z.coeff.support
      · exact hk n hn
      · rw [Finsupp.notMem_support_iff.1 hn, map_zero]; rfl
    refine ⟨k, fi ≫ hmk, fj ≫ hmk, ?_⟩
    change laurentMap (D.map (fi ≫ hmk)).hom xi = laurentMap (D.map (fj ≫ hmk)).hom xj
    rw [D.map_comp, D.map_comp, CommRingCat.hom_comp, CommRingCat.hom_comp, GmPhiNat.laurentMap_comp,
      GmPhiNat.laurentMap_comp, RingHom.comp_apply, RingHom.comp_apply, ← sub_eq_zero, ← map_sub]
    exact hz0

end GlobalTheory.EtC.GmPhiNoeth

open GlobalTheory.EtC.GmPhiNoeth in

theorem GlobalTheory.EtC.gmPhi_surjective_of_noetherian : ∀ (q : ℕ) [NeZero q],
    (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
      Function.Surjective (gmPhi q A i)) →
    ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i) := by
  intro q _ hN A _ hSH hq i x
  obtain ⟨hH, hsep⟩ := hSH
  obtain ⟨J, _, _, D, ι, hc, hl, hst, hqj, -, -⟩ :=
    GlobalTheory.SHColim.strictlyHenselian_isColimit q A ⟨hH, hsep⟩ hq
  have hqL : IsUnit (q : LaurentPolynomial A) := by
    simpa using hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)
  obtain ⟨j, y, hy⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (D ⋙ laurentFunctor) _ (isColimit_laurent hc) 1 i).1 x hqL
  obtain ⟨B, _, _, s, hs⟩ := hst j
  haveI := hl j
  haveI : IsNoetherianRing (D.obj j) := GlobalTheory.StalkNoeth.isNoetherianRing_of_isStalk B (D.obj j) s hs
  obtain ⟨b, hb⟩ := hN (D.obj j) hs.1 (hqj j) i y
  have hn := gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q (A := D.obj j) (B := A) (ι.app j).hom (hqj j) i b
  rw [hb] at hn
  exact ⟨_, hn.symm.trans hy⟩
