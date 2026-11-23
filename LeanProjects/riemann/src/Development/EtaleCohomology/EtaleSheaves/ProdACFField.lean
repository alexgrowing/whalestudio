import Development.EtaleCohomology.EtaleSheaves.BuildCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut

namespace LateralTheory.E.PtsPf

attribute [local instance] PrimeSpectrum.isPrime

lemma prodACF_field (K : Type) [Field K] [IsAlgClosed K] : ProdACF K := by
  refine ⟨fun p hp hd => ?_, fun a => ?_⟩
  · obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p (by
      rw [Polynomial.degree_eq_natDegree hp.ne_zero]; exact_mod_cast hd.ne')
    exact ⟨x, hx⟩
  · by_cases ha : a = 0
    · exact ⟨0, 1, IsIdempotentElem.zero, isUnit_one, by simp [ha]⟩
    · exact ⟨1, a, IsIdempotentElem.one, isUnit_iff_ne_zero.mpr ha, by simp⟩

lemma prodACF_pi {ι : Type} (W : ι → Type) [∀ i, CommRing (W i)] (h : ∀ i, ProdACF (W i)) :
    ProdACF (∀ i, W i) := by
  refine ⟨fun p hp hd => ?_, fun a => ?_⟩
  · have hr : ∀ i, ∃ x, (p.map (Pi.evalRingHom W i)).eval x = 0 := by
      intro i
      rcases subsingleton_or_nontrivial (W i) with hs | hs
      · exact ⟨0, Subsingleton.elim _ _⟩
      · exact (h i).1 _ (hp.map _) (by rw [hp.natDegree_map]; exact hd)
    choose x hx using hr
    refine ⟨x, funext fun i => ?_⟩
    have := Polynomial.hom_eval₂ p (RingHom.id _) (Pi.evalRingHom W i) x
    simp only [RingHom.comp_id] at this
    simp only [Polynomial.eval_map] at hx
    change (Pi.evalRingHom W i) (Polynomial.eval₂ (RingHom.id _) x p) = 0
    rw [this]
    exact hx i
  · have hr := fun i => (h i).2 (a i)
    choose e u he hu hau using hr
    refine ⟨e, u, ?_, Pi.isUnit_iff.mpr hu, funext hau⟩
    exact funext fun i => he i

abbrev WA (R : CommRingCat.{0}) : Type :=
  ∀ p : PrimeSpectrum R, AlgebraicClosure p.asIdeal.ResidueField

def phiA (R : CommRingCat.{0}) : R →+* WA R :=
  RingHom.pi fun p => (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
    (algebraMap R p.asIdeal.ResidueField)

lemma surj_phiA (R : CommRingCat.{0}) : Surjective (Spec.map (CommRingCat.ofHom (phiA R))) := by
  refine ⟨fun p' => ?_⟩
  obtain ⟨p, rfl⟩ : ∃ p : PrimeSpectrum R, (p : Spec R) = p' := ⟨p', rfl⟩
  let ev : WA R →+* AlgebraicClosure p.asIdeal.ResidueField := Pi.evalRingHom _ p
  have hq : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  refine ⟨⟨RingHom.ker ev, hq⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (phiA R) (RingHom.ker ev) = p.asIdeal
  rw [RingHom.comap_ker]
  have : ev.comp (phiA R) = (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
    (algebraMap R p.asIdeal.ResidueField) := rfl
  rw [this, RingHom.ker_comp_of_injective _ (RingHom.injective (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField))), Ideal.ker_algebraMap_residueField]

theorem Pts_of : Pts := by
  intro P _ _
  let 𝒰 := P.affineCover.finiteSubcover
  let I := 𝒰.I₀
  have hA : ∀ i : I, IsAffine (𝒰.X i) := fun i => by
    change IsAffine (P.affineCover.X _); infer_instance
  let R : I → CommRingCat.{0} := fun i => Γ(𝒰.X i, ⊤)
  let f : ∀ i, Spec (R i) ⟶ P := fun i => (𝒰.X i).isoSpec.inv ≫ 𝒰.f i
  let S : I → CommRingCat.{0} := fun i => CommRingCat.of (WA (R i))
  let g : ∀ i, Spec (S i) ⟶ P := fun i => Spec.map (CommRingCat.ofHom (phiA (R i))) ≫ f i
  refine ⟨∀ i, S i, inferInstance, inv (sigmaSpec S) ≫ Sigma.desc g, ?_, ?_⟩
  · exact prodACF_pi _ fun i => prodACF_pi _ fun p => prodACF_field _
  · have : Surjective (Sigma.desc g) := by
      apply Surjective.sigmaDesc_of_union_range_eq_univ
      have hr : ∀ i, Set.range (g i) = Set.range (𝒰.f i) := fun i => by
        have := surj_phiA (R i)
        rw [range_eq_range_of_surjective (g i) (𝒰.f i) (Spec.map (CommRingCat.ofHom (phiA (R i))) ≫ (𝒰.X i).isoSpec.inv)
          (by simp [g, f])]
      simp_rw [hr]
      exact 𝒰.iUnion_range
    infer_instance

end LateralTheory.E.PtsPf
