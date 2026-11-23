import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.DiscElt

variable (R : Type) [CommRing R]

theorem hkpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem hkpull_single {X Y : Shv R} (g : X ⟶ Y) (F : Shv R) (n : ℤ) (t : Y ⟶ (res R F).X n)
    (ht : t ≫ (res R F).d n (n + 1) = 0) :
    HK.pull R ((CochainComplex.singleFunctor (Shv R) 0).map g) F n
      (CohomologyClass.mk (Cocycle.fromSingleMk t (zero_add n) (n + 1) rfl ht)) =
      CohomologyClass.mk (Cocycle.fromSingleMk (g ≫ t) (zero_add n) (n + 1) rfl (by simp [ht])) := by
  rw [Cocycle.fromSingleMk_precomp g t (zero_add n) (n + 1) rfl ht]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cocycle.precomp]

end GlobalTheory.EtC.DiscElt

namespace GlobalTheory.EtC

open GlobalTheory.EtC.DiscElt in

theorem disc_elt_cls : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ cl : ∀ (P : PSh) (n : ℤ) (t : (free R).obj P ⟶ (res R F).X n), t ≫ (res R F).d n (n + 1) = 0 → H R (disc.obj P) F n, (∀ P n x, ∃ t ht, cl P n t ht = x) ∧ (∀ P n t ht t' ht', cl P n t ht = cl P n t' ht' ↔ ∃ y : (free R).obj P ⟶ (res R F).X (n - 1), t = t' + y ≫ (res R F).d (n - 1) n) ∧ (∀ P n, cl P n 0 zero_comp = 0) ∧ ∀ (P P' : PSh) (f : P ⟶ P') n t ht, ∃ h, pull R (disc.map f) F n (cl P' n t ht) = cl P n ((free R).map f ≫ t) h := by
  intro R _ F
  obtain ⟨e, -, hnat⟩ := chains_disc_homotopyEquiv R
  have hb : ∀ (P : PSh) (n : ℤ), Function.Bijective (HK.pull R (e P).hom F n) := fun P n => by
    haveI : QuasiIso (e P).hom := (e P).quasiIso_hom
    exact quasiIso_hypercohomology_bijective' R (e P).hom F n
  let E : ∀ (P : PSh) (n : ℤ), H R (disc.obj P) F n ≃ HK R (sgl ((free R).obj P)) F n :=
    fun P n => Equiv.ofBijective _ (hb P n)
  have hE : ∀ P n x, E P n x = HK.pull R (e P).hom F n x := fun _ _ _ => rfl
  let c : ∀ (P : PSh) (n : ℤ) (t : (free R).obj P ⟶ (res R F).X n), t ≫ (res R F).d n (n + 1) = 0 →
      HK R (sgl ((free R).obj P)) F n :=
    fun P n t ht => CohomologyClass.mk (Cocycle.fromSingleMk t (zero_add n) (n + 1) rfl ht)
  refine ⟨fun P n t ht => (E P n).symm (c P n t ht), ?_, ?_, ?_, ?_⟩
  · intro P n x
    obtain ⟨z, hz⟩ := (E P n x).mk_surjective
    obtain ⟨t, ht, rfl⟩ := Cocycle.fromSingleMk_surjective z n (zero_add n) (n + 1) rfl
    exact ⟨t, ht, by rw [Equiv.symm_apply_eq]; exact hz⟩
  · intro P n t ht t' ht'
    rw [(E P n).symm.injective.eq_iff]
    change CohomologyClass.mk _ = CohomologyClass.mk _ ↔ _
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, ← Cocycle.fromSingleMk_sub _ _ _ _ _ ht ht',
      CohomologyClass.mk_eq_zero_iff,
      Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (n - 1) (by omega)]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; abel⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; abel⟩
  · intro P n
    change (E P n).symm (CohomologyClass.mk _) = 0
    rw [Equiv.symm_apply_eq, hE, map_zero, Cocycle.fromSingleMk_zero, CohomologyClass.mk_zero]
  · intro P P' f n t ht
    refine ⟨by simp [ht], ?_⟩
    rw [Equiv.eq_symm_apply, hE]
    change HK.pull R (e P).hom F n (HK.pull R ((chains R).map (disc.map f)) F n _) = _
    rw [← hkpull_comp, hnat f, hkpull_comp]
    have h1 : HK.pull R (e P').hom F n ((E P' n).symm (c P' n t ht)) = c P' n t ht := by
      rw [← hE, Equiv.apply_symm_apply]
    rw [h1]
    exact hkpull_single R ((free R).map f) F n t ht

end GlobalTheory.EtC
