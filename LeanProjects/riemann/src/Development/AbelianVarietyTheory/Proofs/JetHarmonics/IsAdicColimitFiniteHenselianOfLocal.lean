import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory.AdicColimit

theorem smodEq_smul_top_map {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (J : Ideal A) (f : M →ₗ[A] N) {x y : M} (h : x ≡ y [SMOD (J • ⊤ : Submodule A M)]) :
    f x ≡ f y [SMOD (J • ⊤ : Submodule A N)] := by
  rw [SModEq.sub_mem] at h ⊢
  rw [← map_sub]
  have : (J • ⊤ : Submodule A M).map f ≤ J • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact this ⟨_, h, rfl⟩

theorem isAdicComplete_of_retract {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (J : Ideal A) (s : N →ₗ[A] M) (p : M →ₗ[A] N) (hps : ∀ x, p (s x) = x)
    (h : IsAdicComplete J M) : IsAdicComplete J N where
  haus' x hx := by
    have : s x = 0 := IsHausdorff.haus h.toIsHausdorff (s x) fun n => by
      simpa using smodEq_smul_top_map _ s (hx n)
    rw [← hps x, this, map_zero]
  prec' f hf := by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := fun n => s (f n)) fun {m n} hmn =>
      smodEq_smul_top_map _ s (hf hmn)
    exact ⟨p L, fun n => by simpa [hps] using smodEq_smul_top_map _ p (hL n)⟩

theorem isAdicComplete_map_eval {A ι : Type} [CommRing A] (T : ι → Type) [∀ i, CommRing (T i)]
    (e : A ≃+* Π i, T i) (J : Ideal A) (h : IsAdicComplete J A) (i : ι) :
    IsAdicComplete (J.map ((Pi.evalRingHom T i).comp e.toRingHom)) (T i) := by
  classical
  letI : Algebra A (T i) := ((Pi.evalRingHom T i).comp e.toRingHom).toAlgebra
  let s : T i →ₗ[A] A :=
    { toFun t := e.symm (Pi.single i t)
      map_add' x y := by rw [Pi.single_add, map_add]
      map_smul' a t := by
        apply e.injective
        rw [RingHom.id_apply, smul_eq_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply,
          ← Pi.single_mul_right]
        rfl }
  refine (IsAdicComplete.map_algebraMap_iff J (T i)).2
    (isAdicComplete_of_retract J s (Algebra.linearMap A (T i)) (fun t => ?_) h)
  change e (e.symm (Pi.single i t)) i = t
  rw [e.apply_symm_apply, Pi.single_eq_same]

theorem isAdicColimit_finite_henselian_of_local :
    (∀ (R : Type) [CommRing R] (I : Ideal R) (A : Type) [CommRing A] [IsLocalRing A] (φ : R →+* A), IsAdicComplete (I.map φ) A → IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ)))) → (∀ (R : Type) [CommRing R] (I : Ideal R) (T : Over (Spec (CommRingCat.of R))) (𝒰 : T.left.OpenCover.{0}), (∀ i j, i ≠ j → Disjoint (Set.range (𝒰.f i)) (Set.range (𝒰.f j))) → (∀ i, IsAdicColimit I (Over.mk (𝒰.f i ≫ T.hom))) → IsAdicColimit I T) → ∀ (R : Type) [CommRing R] (I : Ideal R) (O : Type) [CommRing O] [HenselianLocalRing O] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] (φ : R →+* A), IsAdicComplete (I.map φ) A → IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
  intro hloc hcov R _ I O _ _ A _ _ _ φ hc
  classical
  obtain ⟨ι, _, T, _, _, e, hT⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing O A
  let π (i : ι) : A →+* T i := (Pi.evalRingHom T i).comp e.toRingEquiv.toRingHom
  have hopen (i : ι) : IsOpenImmersion (Spec.map (CommRingCat.ofHom (π i))) := by
    have : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom) :=
      inferInstanceAs (IsIso e.toRingEquiv.toCommRingCatIso.hom)
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    infer_instance
  let 𝒰 : (Spec (CommRingCat.of A)).OpenCover := Scheme.Cover.mkOfCovers ι
    (fun i => Spec (CommRingCat.of (T i))) (fun i => Spec.map (CommRingCat.ofHom (π i))) (fun x => by
      obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
        (PrimeSpectrum.comap e.toRingEquiv.symm.toRingHom x)
      refine ⟨i, q, ?_⟩
      change PrimeSpectrum.comap e.toRingEquiv.toRingHom (PrimeSpectrum.comap (Pi.evalRingHom T i) q) = x
      rw [hq]
      ext a
      change e.symm (e a) ∈ x.asIdeal ↔ _
      rw [e.symm_apply_apply]) hopen
  refine hcov R I (Over.mk (Spec.map (CommRingCat.ofHom φ))) 𝒰 (fun i j hij => ?_) fun i => ?_
  · rw [Set.disjoint_left]
    rintro x ⟨p, rfl⟩ ⟨q, hq⟩
    change ι at i j
    change PrimeSpectrum (T i) at p
    change PrimeSpectrum (T j) at q
    change PrimeSpectrum.comap (π j) q = PrimeSpectrum.comap (π i) p at hq
    have h1 : e.symm (Pi.single i 1) ∈ (PrimeSpectrum.comap (π j) q).asIdeal := by
      change e (e.symm (Pi.single i 1)) j ∈ q.asIdeal
      rw [e.apply_symm_apply, Pi.single_eq_of_ne (i := i) (i' := j) (fun h => hij h.symm)]
      exact zero_mem _
    rw [hq] at h1
    change e (e.symm (Pi.single i 1)) i ∈ p.asIdeal at h1
    rw [e.apply_symm_apply, Pi.single_eq_same] at h1
    exact p.isPrime.one_notMem h1
  · change ι at i
    have := (hT i).1
    have key := hloc R I (T i) ((π i).comp φ) (by
      rw [← Ideal.map_map]
      exact isAdicComplete_map_eval T e.toRingEquiv _ hc i)
    rw [CommRingCat.ofHom_comp, Spec.map_comp] at key
    exact key

end GlobalTheory.AdicColimit
