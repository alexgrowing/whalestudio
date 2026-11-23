import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCoverStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

private theorem exists_algHom_of_etale (k B : Type) [Field k] [IsSepClosed k] [CommRing B]
    [Nontrivial B] [Algebra k B] [Algebra.Etale k B] : Nonempty (B →ₐ[k] k) := by
  obtain ⟨I, _, Ai, _, _, e, hA⟩ := (Algebra.Etale.iff_exists_algEquiv_prod k B).mp inferInstance
  have hI : Nonempty I := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : Subsingleton (Π i, Ai i) := inferInstance
    exact not_subsingleton B e.toEquiv.subsingleton
  obtain ⟨i⟩ := hI
  haveI := (hA i).1
  haveI := (hA i).2
  let u : k ≃ₐ[k] Ai i := AlgEquiv.ofBijective (Algebra.ofId k (Ai i))
    ⟨(algebraMap k (Ai i)).injective, IsSepClosed.algebraMap_surjective k (Ai i)⟩
  exact ⟨(u.symm.toAlgHom.comp (Pi.evalAlgHom k Ai i)).comp e.toAlgHom⟩

private theorem exists_section_of_etale_field {k : Type} [Field k] [IsSepClosed k] {P : Scheme.{0}}
    (q : P ⟶ Spec (CommRingCat.of k)) [Etale q] [Surjective q] :
    ∃ g : Spec (CommRingCat.of k) ⟶ P, g ≫ q = 𝟙 _ := by
  obtain ⟨x0⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
  obtain ⟨p, -⟩ := q.surjective x0
  let U := P.affineOpenCover
  let j := U.idx p
  haveI : IsOpenImmersion (U.f j) := U.map_prop j
  let φ : CommRingCat.of k ⟶ U.X j := Spec.preimage (U.f j ≫ q)
  have hφ : Spec.map φ = U.f j ≫ q := Spec.map_preimage _
  have hE : Etale (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have het : φ.hom.Etale := HasRingHomProperty.Spec_iff.mp hE
  letI : Algebra k (U.X j) := φ.hom.toAlgebra
  haveI : Algebra.Etale k (U.X j) := het
  obtain ⟨y, -⟩ := U.covers p
  haveI : Nontrivial (U.X j) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact y.isPrime.ne_top (Subsingleton.elim _ _)
  obtain ⟨ψ⟩ := exists_algHom_of_etale k (U.X j)
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ U.f j, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  conv_rhs => rw [← Spec.map_id]
  congr 1
  ext c
  exact ψ.commutes c

private theorem exists_section_of_etale_henselian (A : Type) [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of A))
    [Etale f] [Surjective f] : ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _ := by
  let κ := IsLocalRing.ResidueField A
  let i : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  have hb := GlobalTheory.bijective_restrictPoints_of_etale_of_henselian f A (𝟙 _)
  obtain ⟨σ, hσ⟩ := exists_section_of_etale_field (pullback.snd f i)
  have hg : (σ ≫ pullback.fst f i) ≫ f = i ≫ 𝟙 _ := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp,
      Category.comp_id]
  obtain ⟨⟨s, hs⟩, _⟩ := hb.2 ⟨σ ≫ pullback.fst f i, hg⟩
  exact ⟨s, hs⟩

theorem UpperTheory.etaleCohomology_functorialityAxioms_hold_of_sheafAxioms :
    GlobalTheory.EtC.B2 := by
  intro R _ A _ hA F n hn
  obtain ⟨hHen, hSep⟩ := hA
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : H R (sp A) F n, z = 0 := by
    intro z
    obtain ⟨Y, f, hE, hS, hz⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover R (Spec (CommRingCat.of A)) F n hn z
    obtain ⟨s, hs⟩ := exists_section_of_etale_henselian A f
    calc z = pull R (𝟙 _) F n z := (pull_id R _ F n z).symm
      _ = pull R (sch.map (s ≫ f)) F n z := by rw [hs, CategoryTheory.Functor.map_id]
      _ = pull R (sch.map s) F n (pull R (sch.map f) F n z) := by
        rw [CategoryTheory.Functor.map_comp, pull_comp]
      _ = 0 := by rw [hz, map_zero]
  rw [key x, key y]
