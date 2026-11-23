import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleSurjectiveProj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem exists_sigma_point {W : Scheme.{0}} {I : Type} (K : Type) [Field K]
    (y : Spec (CommRingCat.of K) ⟶ ∐ fun _ : I => W) :
    ∃ (i : I) (y' : Spec (CommRingCat.of K) ⟶ W), y' ≫ Sigma.ι (fun _ : I => W) i = y := by
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨⟨i, w⟩, hw⟩ := (sigmaMk (fun _ : I => W)).surjective (y pt)
  rw [sigmaMk_mk] at hw
  refine ⟨i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => W) i) y ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨q, rfl⟩
  rw [Subsingleton.elim q pt]
  exact ⟨w, hw⟩

private theorem card_sigma_fibre {Y Z : Scheme.{0}} (s : Y ⟶ Z) (I : Type) (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ Z) :
    Nat.card {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y) // y ≫ (Sigma.desc fun _ : I => s) = x} =
      Nat.card I * Nat.card {y' : Spec (CommRingCat.of K) ⟶ Y // y' ≫ s = x} := by
  let F : I × {y' : Spec (CommRingCat.of K) ⟶ Y // y' ≫ s = x} →
      {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y) // y ≫ (Sigma.desc fun _ : I => s) = x} :=
    fun q => ⟨q.2.1 ≫ Sigma.ι (fun _ : I => Y) q.1, by
      rw [Category.assoc, Sigma.ι_desc]
      exact q.2.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, a, ha⟩ ⟨j, b, hb⟩ h
      have h' : a ≫ Sigma.ι (fun _ : I => Y) i = b ≫ Sigma.ι (fun _ : I => Y) j :=
        congrArg Subtype.val h
      by_cases hij : i = j
      · subst hij
        have hab : a = b := (cancel_mono _).mp h'
        subst hab
        rfl
      · exfalso
        have hE := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : I => Y) ⟨h'⟩ hij
        obtain ⟨p⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K)))
        exact hE.false p
    · rintro ⟨y, hy⟩
      obtain ⟨i, y', rfl⟩ := exists_sigma_point K y
      refine ⟨⟨i, y', ?_⟩, rfl⟩
      rw [Category.assoc, Sigma.ι_desc] at hy
      exact hy
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod]

theorem UpperTheory.Gal.G3.pSigmaFEt :
    SigmaFEt := by
  intro Y Z s d I _ hs
  obtain ⟨hfin, het, hcard⟩ := hs
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hid : IsFinite (Sigma.desc fun _ : I => 𝟙 Y) := by
    have h1 := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y n
    have h2 : IsFinite ((Sigma.reindex e (fun _ : Fin n => Y)).hom ≫
        Sigma.desc fun _ : Fin n => 𝟙 Y) := inferInstance
    have h3 : (Sigma.desc fun _ : I => 𝟙 Y) =
        (Sigma.reindex e (fun _ : Fin n => Y)).hom ≫ Sigma.desc fun _ : Fin n => 𝟙 Y := by
      refine Sigma.hom_ext (f := fun _ : I => Y) _ _ fun i => ?_
      rw [Sigma.ι_desc, ← Category.assoc]
      erw [Sigma.ι_reindex_hom (f := fun _ : Fin n => Y) e i]
      rw [Sigma.ι_desc]
    rw [h3]
    exact h2
  have hfac : (Sigma.desc fun _ : I => s) = (Sigma.desc fun _ : I => 𝟙 Y) ≫ s := by
    refine Sigma.hom_ext (f := fun _ : I => Y) _ _ fun i => ?_
    simp
  have hloc : IsZariskiLocalAtSource @Etale.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine ⟨?_, ?_, ?_⟩
  · rw [hfac]
    infer_instance
  · exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{0}) fun _ => het
  · intro K _ _ x
    rw [card_sigma_fibre, hcard]
