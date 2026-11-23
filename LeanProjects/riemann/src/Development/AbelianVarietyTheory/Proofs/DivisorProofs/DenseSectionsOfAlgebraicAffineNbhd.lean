import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.DenseAff

theorem chart (R : Type) [CommRing R] [IsLocalRing R] (U : Over (Sp R)) (hU : Smooth U.hom)
    (e : Sp R ⟶ U.left) (he : e ≫ U.hom = 𝟙 _) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (j : Spec (CommRingCat.of A) ⟶ U.left)
      (_ : IsOpenImmersion j) (_ : A →ₐ[R] R), Algebra.Smooth R A ∧
      j ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hcV, -⟩ := U.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e (closedPoint R))) isOpen_univ
  have hV : IsAffineOpen V := hV
  haveI : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  have hrange : Set.range e ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨y, rfl⟩
    rw [hV.range_fromSpec]
    exact ((specializes_closedPoint y).map e.continuous).mem_open V.isOpen hcV
  have he' : IsOpenImmersion.lift hV.fromSpec e hrange ≫ hV.fromSpec = e := IsOpenImmersion.lift_fac _ _ _
  let φA : CommRingCat.of R ⟶ Γ(U.left, V) := Spec.preimage (hV.fromSpec ≫ U.hom)
  have hφA : Spec.map φA = hV.fromSpec ≫ U.hom := Spec.map_preimage _
  let εr : Γ(U.left, V) ⟶ CommRingCat.of R := Spec.preimage (IsOpenImmersion.lift hV.fromSpec e hrange)
  have hεr : Spec.map εr = IsOpenImmersion.lift hV.fromSpec e hrange := Spec.map_preimage _
  letI : Algebra R Γ(U.left, V) := φA.hom.toAlgebra
  haveI := hU
  have hsm : Smooth (hV.fromSpec ≫ U.hom) := inferInstance
  rw [← hφA, HasRingHomProperty.Spec_iff (P := @Smooth)] at hsm
  have hcomp : φA ≫ εr = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hεr, hφA, ← Category.assoc, he', he, Spec.map_id]
  let ε : Γ(U.left, V) →ₐ[R] R :=
    { toRingHom := εr.hom
      commutes' := by
        intro r
        show εr.hom (φA.hom r) = r
        rw [← CommRingCat.comp_apply, hcomp]
        rfl }
  exact ⟨Γ(U.left, V), inferInstance, inferInstance, hV.fromSpec, inferInstance, ε,
    RingHom.smooth_algebraMap.mp hsm, hφA.symm⟩

def psi (R A Ω : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing Ω] [Algebra R Ω]
    (U : Over (Sp R)) (j : Spec (CommRingCat.of A) ⟶ U.left)
    (hj : j ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Spec (CommRingCat.of (TensorProduct R Ω A)) ⟶ pullback U.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) :=
  (pullbackSpecIso R Ω A).inv ≫ (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ j (𝟙 _) (𝟙 _) (by simp [hj]) (by simp)

section
variable (R A Ω : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing Ω] [Algebra R Ω]
    (U : Over (Sp R)) (j : Spec (CommRingCat.of A) ⟶ U.left)
    (hj : j ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap R A)))

instance [IsOpenImmersion j] : IsOpenImmersion (psi R A Ω U j hj) := by
  unfold psi; infer_instance

theorem psi_fst : psi R A Ω U j hj ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R Ω A).toRingHom) ≫ j := by
  unfold psi
  rw [Category.assoc, Category.assoc, pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackSpecIso_inv_snd_assoc]
  rfl

theorem psi_snd : psi R A Ω U j hj ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
  unfold psi
  rw [Category.assoc, Category.assoc, pullback.lift_snd, pullbackSymmetry_hom_comp_snd_assoc,
    Category.comp_id, pullbackSpecIso_inv_fst]
end

theorem core (KEY : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R) (Ω : Type) [Field Ω] [Algebra R Ω], RingHom.ker (algebraMap R Ω) ≠ maximalIdeal R → IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ a : A →ₐ[R] R, GlobalTheory.DenseSec.pt ((Algebra.ofId R Ω).comp a) f ≠ 0)
    (R : Type) [CommRing R] [IsLocalRing R] (hR : IsAdicComplete (maximalIdeal R) R)
    (U : Over (Sp R)) (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A]
    (j : Spec (CommRingCat.of A) ⟶ U.left) [IsOpenImmersion j]
    (hj : j ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap R A))) (ε : A →ₐ[R] R)
    (Ω : Type) [Field Ω] [Algebra R Ω] (hker : RingHom.ker (algebraMap R Ω) ≠ maximalIdeal R)
    (hirr : IrreducibleSpace (pullback U.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) : Scheme.{0}))
    (O : (pullback U.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).Opens)
    (hO : (O : Set (pullback U.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) : Scheme.{0})).Nonempty) :
    ∃ (a : Sp R ⟶ U.left) (aΩ : Sp Ω ⟶ pullback U.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))),
      a ≫ U.hom = 𝟙 _ ∧ aΩ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ a ∧
      aΩ ≫ pullback.snd _ _ = 𝟙 _ ∧ Set.range aΩ ⊆ O := by

  have hirrA : IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) := by
    haveI : Nontrivial (TensorProduct R Ω A) :=
      (GlobalTheory.DenseSec.pt ((Algebra.ofId R Ω).comp ε)).toRingHom.domain_nontrivial
    have hpre := (PreirreducibleSpace.isPreirreducible_univ
      (X := ↥(pullback U.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))))).preimage
      (psi R A Ω U j hj).isOpenEmbedding
    rw [Set.preimage_univ] at hpre
    exact { isPreirreducible_univ := hpre, toNonempty := inferInstance }
  have hmeet : ((Set.range (psi R A Ω U j hj)) ∩ (O : Set _)).Nonempty := by
    obtain ⟨p⟩ := hirrA.toNonempty
    exact nonempty_preirreducible_inter (psi R A Ω U j hj).isOpenEmbedding.isOpen_range O.isOpen
      ⟨_, p, rfl⟩ hO
  obtain ⟨_, ⟨y, rfl⟩, hyO⟩ := hmeet
  obtain ⟨_, ⟨f, rfl⟩, hyf, hfO⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show y ∈ (psi R A Ω U j hj) ⁻¹' (O : Set _) from hyO) (O.isOpen.preimage (psi R A Ω U j hj).continuous)
  have hf : ¬ IsNilpotent f := by
    intro h
    dsimp only at hyf
    rw [(PrimeSpectrum.basicOpen_eq_bot_iff f).2 h] at hyf
    exact hyf
  obtain ⟨a, ha⟩ := KEY R hR A ε Ω hker hirrA f hf
  let sec : Sp R ⟶ U.left := Spec.map (CommRingCat.ofHom a.toRingHom) ≫ j
  have hsec : sec ≫ U.hom = 𝟙 _ := by
    simp only [sec, Category.assoc, hj, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    simp
  refine ⟨sec, pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ sec) (𝟙 _)
    (by rw [Category.assoc, hsec, Category.comp_id, Category.id_comp]), hsec, pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _, ?_⟩
  have hfac : pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ sec) (𝟙 _)
      (by rw [Category.assoc, hsec, Category.comp_id, Category.id_comp]) =
      Spec.map (CommRingCat.ofHom (GlobalTheory.DenseSec.pt ((Algebra.ofId R Ω).comp a)).toRingHom) ≫
        psi R A Ω U j hj := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, psi_fst, ← Category.assoc, ← Spec.map_comp]
      simp only [sec, ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext r
      simp [GlobalTheory.DenseSec.pt]
    · rw [pullback.lift_snd, Category.assoc, psi_snd, ← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext r
      simp [GlobalTheory.DenseSec.pt]
  rw [hfac, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  apply hfO
  show _ ∈ ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens _) : Set (PrimeSpectrum (TensorProduct R Ω A)))
  apply (PrimeSpectrum.mem_basicOpen _ _).2
  rw [Spec.map_apply]
  intro hmem
  have hz : PrimeSpectrum.asIdeal (z : PrimeSpectrum Ω) = ⊥ :=
    @Ideal.eq_bot_of_prime Ω _ _ (PrimeSpectrum.isPrime (z : PrimeSpectrum Ω))
  have h2 : (GlobalTheory.DenseSec.pt ((Algebra.ofId R Ω).comp a)) f ∈ PrimeSpectrum.asIdeal (z : PrimeSpectrum Ω) := hmem
  rw [hz, Ideal.mem_bot] at h2
  exact ha h2

theorem denseSections_of_algebraic : (∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R) (Ω : Type) [Field Ω] [Algebra R Ω], RingHom.ker (algebraMap R Ω) ≠ maximalIdeal R → IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ a : A →ₐ[R] R, GlobalTheory.DenseSec.pt ((Algebra.ofId R Ω).comp a) f ≠ 0) → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (U : Over (Sp R)), Smooth U.hom → ∀ (e : Sp R ⟶ U.left), e ≫ U.hom = 𝟙 _ → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Sp R), closedPoint R ∉ Set.range x → IrreducibleSpace (pullback U.hom x : Scheme.{0}) → ∀ O : (pullback U.hom x).Opens, (O : Set (pullback U.hom x : Scheme.{0})).Nonempty → ∃ (a : Sp R ⟶ U.left) (aΩ : Sp Ω ⟶ pullback U.hom x), a ≫ U.hom = 𝟙 _ ∧ aΩ ≫ pullback.fst _ _ = x ≫ a ∧ aΩ ≫ pullback.snd _ _ = 𝟙 _ ∧ Set.range aΩ ⊆ O := by
  intro KEY R _ _ _ hR U hU e he Ω _ x hx hirr O hO
  obtain ⟨A, _, _, j, _, ε, hsm, hj⟩ := chart R U hU e he
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = x := ⟨_, Spec.map_preimage x⟩
  letI : Algebra R Ω := φ.hom.toAlgebra
  have hker : RingHom.ker (algebraMap R Ω) ≠ maximalIdeal R := by
    intro h
    apply hx
    refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω), ?_⟩
    have hp := Spec.map_apply φ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)
    refine hp.trans (PrimeSpectrum.ext ?_)
    rw [PrimeSpectrum.comap_asIdeal, ← RingHom.ker_eq_comap_bot]
    exact h
  exact core KEY R hR U A j hj ε Ω hker hirr O hO

end GlobalTheory.DenseAff
