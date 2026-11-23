import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafMapMonoEpiIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsIsoOfFreeIsoStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff
open CochainComplex CochainComplex.HomComplex

namespace UpperTheory.EquivOfAffineBijective₂

private lemma hk_id (R : Type) [CommRing R] (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) :
    HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

private lemma hk_comp (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

private lemma loc_of_affine (U : Scheme.{0}) (p : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ (A : Scheme.{0}), IsAffine A → ∀ (c : A ⟶ U) (W : Scheme.{0}) (k : W ⟶ A), p W (k ≫ c)) : Loc U p := by
  refine ⟨Sieve.ofArrows _ U.affineCover.f,
    Scheme.zariskiTopology_le_etaleTopology _ U.affineCover.mem_grothendieckTopology, ?_⟩
  rintro V g ⟨A, k, c, ⟨i⟩, rfl⟩
  exact h _ (by dsimp [Scheme.affineCover]; infer_instance) _ _ _

end UpperTheory.EquivOfAffineBijective₂

open UpperTheory.EquivOfAffineBijective₂ in
theorem UpperTheory.equiv_of_affine_bijective :
    ∀ (R : Type) [CommRing R] (F : Shv R) {P Q : PSh} (f : P ⟶ Q), (∀ T : Scheme.{0}, IsAffine T → Function.Bijective (f.app (op T))) → Eqv R (disc.map f) F := by
  intro R _ F P Q f hf
  have hiso : IsIso ((free R).map f) := by
    refine (GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R f).2.2 (fun U y => ?_) (fun U x x' hxx => ?_)
    · refine loc_of_affine U _ fun A hA c W k => ?_
      obtain ⟨x, hx⟩ := (hf A hA).2 (Q.map c.op y)
      refine ⟨P.map k.op x, ?_⟩
      rw [FunctorToTypes.naturality, hx, op_comp, FunctorToTypes.map_comp_apply]
    · refine loc_of_affine U _ fun A hA c W k => ?_
      have h1 : P.map c.op x = P.map c.op x' := by
        apply (hf A hA).1
        rw [FunctorToTypes.naturality, FunctorToTypes.naturality, hxx]
      rw [op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply, h1]
  have hc : IsIso ((chains R).map (disc.map f)) := GlobalTheory.T.chains_iso_of_free_iso R _ fun _ => hiso
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨HK.pull R (inv ((chains R).map (disc.map f))) F n, fun x => ?_, fun x => ?_⟩
  · change HK.pull R (inv ((chains R).map (disc.map f))) F n (HK.pull R ((chains R).map (disc.map f)) F n x) = x
    rw [← hk_comp, IsIso.inv_hom_id, hk_id]
  · change HK.pull R ((chains R).map (disc.map f)) F n (HK.pull R (inv ((chains R).map (disc.map f))) F n x) = x
    rw [← hk_comp, IsIso.hom_inv_id, hk_id]
