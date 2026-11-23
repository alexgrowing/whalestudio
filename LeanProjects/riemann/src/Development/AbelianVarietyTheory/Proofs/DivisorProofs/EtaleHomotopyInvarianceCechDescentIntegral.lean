import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PiTensorLiftCompSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsoWidePullbackYonedaStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.CechDescHInv

theorem yoneda_spec_widePullback (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ)
    (ι : Fin (k + 1) → (B →+* T)) (hι : ∀ j, (ι j).comp a = (ι 0).comp a)
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) →
      ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j) :
    ∃ e : yoneda.obj (Spec (CommRingCat.of T)) ≅ widePullback (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))),
      ∀ j, e.hom ≫ WidePullback.π _ j = yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) :=
  GlobalTheory.T.spec_widePushout_iso_widePullback_yoneda A B T a k ι hι hu

theorem tensor_univ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) (R : Type) [CommRing R]
    (g : Fin (k + 1) → (B →+* R)) (hg : ∀ j, (g j).comp (algebraMap A B) = (g 0).comp (algebraMap A B)) :
    ∃! φ : PiTensorProduct A (fun _ : Fin (k + 1) => B) →+* R,
      ∀ j, φ.comp (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) j).toRingHom = g j := by
  classical
  letI : Algebra A R := ((g 0).comp (algebraMap A B)).toAlgebra
  let g' : Fin (k + 1) → (B →ₐ[A] R) := fun j => ⟨g j, fun r => RingHom.congr_fun (hg j) r⟩
  refine ⟨(GlobalTheory.piTensorLift g').toRingHom, fun j => ?_, fun ψ hψ => ?_⟩
  · ext x
    exact GlobalTheory.piTensorLift_single g' j x
  · have hc : ∀ r : A, ψ (algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r) = algebraMap A R r := by
      intro r
      have h1 : algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r =
          PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0 (algebraMap A B r) :=
        ((PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0).commutes r).symm
      rw [h1]
      exact RingHom.congr_fun (hψ 0) (algebraMap A B r)
    let ψ' : PiTensorProduct A (fun _ : Fin (k + 1) => B) →ₐ[A] R := ⟨ψ, hc⟩
    have : ψ' = GlobalTheory.piTensorLift g' := PiTensorProduct.algHom_ext fun j => by
      ext x
      change ψ _ = _
      rw [AlgHom.comp_apply, GlobalTheory.piTensorLift_single]
      exact RingHom.congr_fun (hψ j) x
    exact congrArg AlgHom.toRingHom this

theorem poly_univ (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ)
    (ι : Fin (k + 1) → (B →+* T))
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) →
      ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j)
    (R : Type) [CommRing R] (g : Fin (k + 1) → (Polynomial B →+* R))
    (hg : ∀ j, (g j).comp (Polynomial.mapRingHom a) = (g 0).comp (Polynomial.mapRingHom a)) :
    ∃! φ : Polynomial T →+* R, ∀ j, φ.comp (Polynomial.mapRingHom (ι j)) = g j := by
  have hX : ∀ j, g j Polynomial.X = g 0 Polynomial.X := fun j => by
    have := RingHom.congr_fun (hg j) Polynomial.X
    simpa using this
  obtain ⟨ψ, hψ, hψu⟩ := hu R (fun j => (g j).comp Polynomial.C) (fun j => by
    ext x
    have := RingHom.congr_fun (hg j) (Polynomial.C x)
    simpa using this)
  refine ⟨Polynomial.eval₂RingHom ψ (g 0 Polynomial.X), fun j => ?_, fun φ hφ => ?_⟩
  · apply Polynomial.ringHom_ext
    · intro b
      simpa using RingHom.congr_fun (hψ j) b
    · simp [hX j]
  · have hC : φ.comp Polynomial.C = ψ := hψu _ (fun j => by
      ext b
      simpa using RingHom.congr_fun (hφ j) (Polynomial.C b))
    apply Polynomial.ringHom_ext
    · intro t
      simpa using RingHom.congr_fun hC t
    · simpa using RingHom.congr_fun (hφ 0) Polynomial.X

theorem spec_integral_surj (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (hi : φ.IsIntegral)
    (hk : RingHom.ker φ ≤ nilradical A) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨IsIntegralHom.SpecMap_iff.2 hi, ⟨fun (x : PrimeSpectrum A) => ?_⟩⟩
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hi⟩
  have hle : (⊥ : Ideal B).comap (algebraMap A B) ≤ x.asIdeal := by
    rw [← RingHom.ker_eq_comap_bot]
    exact hk.trans (nilradical_le_prime x.asIdeal)
  obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal ⊥ hle
  have : x ∈ Set.range (PrimeSpectrum.comap φ) := ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQx⟩
  exact this

theorem poly_isIntegral (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (hi : φ.IsIntegral) :
    (Polynomial.mapRingHom φ).IsIntegral := by
  letI := (Polynomial.mapRingHom φ).toAlgebra
  have hC : ∀ b : B, IsIntegral (Polynomial A) (Polynomial.C b) := by
    intro b
    obtain ⟨f, hf, hfb⟩ := hi b
    refine ⟨f.map Polynomial.C, hf.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (Polynomial A) (Polynomial B)).comp Polynomial.C = Polynomial.C.comp φ := by
      ext x <;> simp [RingHom.algebraMap_toAlgebra]
    rw [e, ← Polynomial.hom_eval₂, hfb, map_zero]
  have hXi : IsIntegral (Polynomial A) (Polynomial.X : Polynomial B) := by
    have : (Polynomial.X : Polynomial B) = algebraMap (Polynomial A) (Polynomial B) Polynomial.X := by
      simp [RingHom.algebraMap_toAlgebra]
    rw [this]; exact isIntegral_algebraMap
  intro p
  change IsIntegral (Polynomial A) p
  induction p using Polynomial.induction_on with
  | C b => exact hC b
  | add p r hp hr => exact hp.add hr
  | monomial n b _ => exact (hC b).mul (hXi.pow _)

theorem poly_ker (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (hk : RingHom.ker φ ≤ nilradical A) :
    RingHom.ker (Polynomial.mapRingHom φ) ≤ nilradical (Polynomial A) := by
  intro p hp
  rw [mem_nilradical, Polynomial.isNilpotent_iff]
  intro n
  rw [← mem_nilradical]
  apply hk
  rw [RingHom.mem_ker] at hp ⊢
  have := congrArg (fun r => Polynomial.coeff r n) hp
  simpa using this

theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  have := hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using this

theorem hInv_of_integral (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Algebra.IsIntegral A B → RingHom.ker (algebraMap A B) ≤ nilradical A → IsUnit (q : A) →
    (∀ k : ℕ, HInv q (PiTensorProduct A (fun _ : Fin (k + 1) => B))) → HInv q A := by
  intro hint hker hq hT i
  have hi : (algebraMap A B).IsIntegral := fun x => hint.isIntegral x
  obtain ⟨hf1, hf2⟩ := spec_integral_surj A B (algebraMap A B) hi hker
  obtain ⟨hf1', hf2'⟩ := spec_integral_surj _ _ (Polynomial.mapRingHom (algebraMap A B))
    (poly_isIntegral A B _ hi) (poly_ker A B _ hker)
  have hq' : IsUnit (q : Polynomial A) := by simpa using hq.map (Polynomial.C : A →+* Polynomial A)
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have h1 := GlobalTheory.EtC.b4 q (Spec.map (CommRingCat.ofHom (algebraMap A B))) (isUnit_gamma q A hq) i
  have h1' := GlobalTheory.EtC.b4 q (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))
    (isUnit_gamma q _ hq') i
  let F : Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))) ⟶
      Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :=
    Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B))))
      (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))) (by
        simp only [Arrow.mk_hom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 3
        ext x <;> simp)
  let m : cech (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ⟶
      cech (Spec.map (CommRingCat.ofHom (algebraMap A B))) := Arrow.mapCechNerve F
  have hsq : m ≫ cechAug (Spec.map (CommRingCat.ofHom (algebraMap A B))) =
      cechAug (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ≫
        spMap (Polynomial.C : A →+* Polynomial A) := by
    clear E h1 h1' hT hf1 hf2 hf1' hf2' hint hker hq hq' hi
    refine NatTrans.ext (funext fun n => ?_)
    change WidePullback.lift _ _ _ ≫ WidePullback.base _ = WidePullback.base _ ≫ yoneda.map (Spec.map _)
    apply WidePullback.lift_base
  have hm : Eqv _ m (tw q i) := by
    refine GlobalTheory.T.levelwiseEquivalence_isEquivalence _ m _ (fun n => ?_)
    clear h1 h1' hf1 hf2 hf1' hf2' hint hker hq hq' hi hsq
    set k := n.unop.len
    let T := PiTensorProduct A (fun _ : Fin (k + 1) => B)
    let ι : Fin (k + 1) → (B →+* T) := fun j =>
      (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) j).toRingHom
    have hι : ∀ j, (ι j).comp (algebraMap A B) = (ι 0).comp (algebraMap A B) := by
      intro j; ext x; simp [ι]
    have hu := tensor_univ A B k
    obtain ⟨e, he⟩ := yoneda_spec_widePullback A B T (algebraMap A B) k ι hι hu
    have hι' : ∀ j, (Polynomial.mapRingHom (ι j)).comp (Polynomial.mapRingHom (algebraMap A B)) =
        (Polynomial.mapRingHom (ι 0)).comp (Polynomial.mapRingHom (algebraMap A B)) := by
      intro j; rw [Polynomial.mapRingHom_comp, Polynomial.mapRingHom_comp, hι j]
    obtain ⟨e', he'⟩ := yoneda_spec_widePullback (Polynomial A) (Polynomial B) (Polynomial T)
      (Polynomial.mapRingHom (algebraMap A B)) k (fun j => Polynomial.mapRingHom (ι j)) hι'
      (poly_univ A B T (algebraMap A B) k ι (fun R _ g hg => hu R g hg))
    let mn : widePullback (yoneda.obj (Spec (CommRingCat.of (Polynomial A))))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of (Polynomial B))))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))) ⟶
        widePullback (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :=
      WidePullback.lift (WidePullback.base _ ≫ yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))))
        (fun j => WidePullback.π _ j ≫ yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B))))
        (fun j => by
          rw [Category.assoc, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← WidePullback.π_arrow _ j, Category.assoc, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 4
          ext x <;> simp)
    have hmn : m.app n = mn := rfl
    have hπ : ∀ j, (e'.hom ≫ mn) ≫ WidePullback.π _ j =
        (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : T →+* Polynomial T))) ≫ e.hom) ≫ WidePullback.π _ j := by
      intro j
      rw [Category.assoc, WidePullback.lift_π, ← Category.assoc, he' j, Category.assoc, he j,
        ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Functor.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      congr 3
      ext x <;> simp
    have key : e'.hom ≫ mn = yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : T →+* Polynomial T))) ≫ e.hom := by
      apply WidePullback.hom_ext
      · exact hπ
      · rw [← WidePullback.π_arrow _ 0, ← Category.assoc, ← Category.assoc, hπ 0]
    have h3 : Eqv _ (disc.map e'.hom ≫ disc.map mn) (tw q i) := by
      rw [← Functor.map_comp, key, Functor.map_comp]
      exact (E.2.1 _ _ _ _ _).1 (hT k i) (E.1 _ _ _ (disc.mapIso e).isIso_hom)
    rw [hmn]
    exact (E.2.1 _ _ _ _ _).2.1 (E.1 _ _ _ (disc.mapIso e').isIso_hom) h3
  have h2 : Eqv _ (cechAug (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ≫
      spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := by
    rw [← hsq]; exact (E.2.1 _ _ _ _ _).1 hm h1
  exact (E.2.1 _ _ _ _ _).2.1 h1' h2

end GlobalTheory.EtC.CechDescHInv
