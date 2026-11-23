import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

attribute [local instance 2000] Rep.hV2

section CompLinear

variable {n : ℕ} {R : Type*} [CommRing R]

theorem bijective_of_bijective_comp_linear {X X' Y Y' : Type*} {_ : AddCommGroup Y} {_ : AddCommGroup Y'}
    {_ : Module R Y} {_ : Module R Y'} {F : X → (Y →+ ZMod n)} (hF : Function.Bijective F) {α : X' → X}
    (hα : Function.Bijective α) {γ : Y' →ₗ[R] Y} (hγ : Function.Bijective γ) {F' : X' → (Y' →+ ZMod n)}
    (hF' : ∀ x' y', F' x' y' = F (α x') (γ y')) : Function.Bijective F' :=
  bijective_of_bijective_comp hF hα (γ := γ.toAddMonoidHom) hγ hF'

theorem neg_apply_bilin_eq {X X₀ Y Z : Type*} [AddCommGroup X] [AddCommGroup X₀] [AddCommGroup Y] [AddCommGroup Z]
    {_ : Module R X} {_ : Module R Y} {_ : Module R Z} {_ : Module R X₀} (t : Z →+ ZMod n)
    (B : X →ₗ[R] Y →ₗ[R] Z) (f : X₀ →ₗ[R] X) (x : X₀) (y : Y) :
    -t (B (f x) y) = (t.comp (bilinAddHom B (f (-x)))) y := by
  rw [AddMonoidHom.comp_apply, bilinAddHom_apply, map_neg, map_neg, LinearMap.neg_apply, map_neg]

end CompLinear

section LocalZMod

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TotallyDisconnectedSpace H] {m : ℕ} [NeZero m] {Dl : Rep.{0} (ULift.{0} ℤ) H} [IsDiscreteRep Dl]
  (Hd : DualityHypotheses m Dl) (hDl : ∀ d : Dl, m • d = 0)

theorem bijective_zmodMulPairing_tTop {r s : ℕ} (h : r + s = 2) :
    Function.Bijective fun x : cohomology (zmodRep.{0} H m) r =>
      Hd.tTop.comp (bilinAddHom (cupPairing (zmodMulPairing m Dl hDl) h) x) := by
  have hM : ∀ a : zmodRep.{0} H m, m • a = 0 := nsmul_zmodRep_eq_zero H m
  have : Finite (zmodRep.{0} H m) := inferInstanceAs (Finite (ULift.{0} (ZMod m)))
  have : IsDiscreteRep (dualRep Dl (zmodRep.{0} H m)) := isDiscreteRep_dualRep _ _
  refine bijective_of_bijective_comp (Hd.bijective_dualityMap_of_group (zmodRep.{0} H m) hM h)
    Function.bijective_id (γ := (cohomologyMap (zmodDualIso m Dl hDl).inv s).hom.toAddMonoidHom)
    (bijective_cohomologyMap_of_comp_eq_id _ _ (zmodDualIso m Dl hDl).inv_hom_id
      (zmodDualIso m Dl hDl).hom_inv_id s) fun x ω => ?_
  change Hd.tTop (cupPairing (zmodMulPairing m Dl hDl) h x ω) =
    Hd.tTop (cupPairing (evalPairing Dl (zmodRep.{0} H m)) h x ((cohomologyMap (zmodDualIso m Dl hDl).inv s).hom ω))
  congr 1
  have e := cupPairing_cohomologyMap (evalPairing Dl (zmodRep.{0} H m)) (𝟙 _) (zmodDualIso m Dl hDl).inv h x ω
  rw [cohomologyMap_id] at e
  refine Eq.trans ?_ e.symm
  rw [← tensorHom_zmodDualIso_zmodMulPairing m Dl hDl, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.id_comp, Iso.inv_hom_id, MonoidalCategory.id_tensorHom_id, Category.id_comp]

omit [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] [IsDiscreteRep Dl]
  [NeZero m] in

theorem comp_eq_tensorHom_zmodMulPairing {M Dm : Rep.{0} (ULift.{0} ℤ) H} (μ : M ⊗ Dm ⟶ Dm) (ρ : Dm ⟶ Dl)
    (ι : M ⟶ zmodRep.{0} H m)
    (hμ : ∀ (a : M) (d : Dm), μ.hom (a ⊗ₜ[ULift.{0} ℤ] d) = (ZMod.cast (ι.hom a).down : ℤ) • d) :
    μ ≫ ρ = (ι ⊗ₘ ρ) ≫ zmodMulPairing m Dl hDl := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun a d => ?_))
  change ρ.hom (μ.hom (a ⊗ₜ[ULift.{0} ℤ] d)) = (zmodMulPairing m Dl hDl).hom (ι.hom a ⊗ₜ[ULift.{0} ℤ] ρ.hom d)
  rw [hμ, map_zsmul]
  obtain ⟨b⟩ := ι.hom a
  rw [zmodMulPairing_tmul]

omit [CompactSpace H] [TotallyDisconnectedSpace H] [NeZero m] in

theorem cohomologyMap_cupPairing_of_comp_eq {M Dm M' : Rep.{0} (ULift.{0} ℤ) H} [IsDiscreteRep M]
    [IsDiscreteRep Dm] [IsDiscreteRep M'] (μ : M ⊗ Dm ⟶ Dm) (μ' : M' ⊗ Dl ⟶ Dl) (ρ : Dm ⟶ Dl) (ι : M ⟶ M')
    (hμ : μ ≫ ρ = (ι ⊗ₘ ρ) ≫ μ') {r s q : ℕ} (h : r + s = q) (x : cohomology M r) (y : cohomology Dm s) :
    (cohomologyMap ρ q).hom (cupPairing μ h x y) =
      cupPairing μ' h ((cohomologyMap ι r).hom x) ((cohomologyMap ρ s).hom y) := by
  rw [cupPairing_cohomologyMap, ← hμ, ← cohomologyMap_cupPairing]

end LocalZMod

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n]

omit [NeZero n] in

theorem nsmul_galRootsOfUnity_local (v : S)
    (ω : galRootsOfUnity.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) : n • ω = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((Additive.toMul ω : rootsOfUnity n
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) :
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))ˣ) ^ n = 1
  exact (mem_rootsOfUnity n _).1 (Additive.toMul ω).2

def zmodResToLocal (v : S) :
    Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) ⟶
      zmodRep.{0} (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

omit [NeZero n] in
theorem bijective_zmodResToLocal (v : S) : Function.Bijective (zmodResToLocal S ιs n v).hom :=
  Function.bijective_id

omit [NeZero n] in

theorem pairingRes_zmodMulPairing_comp_gsRootsLocalMor (v : S) :
    pairingRes (gsFinFamily S ιs v).toMonoidHom (zmodMulPairing n (gsRoots S n) (nsmul_gsRoots S n)) ≫
        gsRootsLocalMor S ιs n v =
      (zmodResToLocal S ιs n v ⊗ₘ gsRootsLocalMor S ιs n v) ≫
        zmodMulPairing n (galRootsOfUnity.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
          (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (nsmul_galRootsOfUnity_local S n v) := by
  refine comp_eq_tensorHom_zmodMulPairing (nsmul_galRootsOfUnity_local S n v) _ _ _ fun a d => ?_
  obtain ⟨a⟩ := a
  exact zmodMulPairing_tmul n (gsRoots S n) (nsmul_gsRoots S n) a d

set_option maxHeartbeats 1600000 in

theorem gsLocalInvRoots_cupPairing (v : S) {r s : ℕ} (h : r + s = 2)
    (ξ : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) r)
    (η : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) s) :
    gsLocalInvRoots S ιs n v (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
        (zmodMulPairing n (gsRoots S n) (nsmul_gsRoots S n))) h ξ η) =
      (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
        (natCast_ne_zero_adicCompletion S n v)).tTop
        (cupPairing (zmodMulPairing n (galRootsOfUnity.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
          (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (nsmul_galRootsOfUnity_local S n v)) h
          ((cohomologyMap (zmodResToLocal S ιs n v) r).hom ξ) ((cohomologyMap (gsRootsLocalMor S ιs n v) s).hom η)) := by
  refine (gsLocalInvRoots_eq S ιs n v _).trans (congrArg
    (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
      (natCast_ne_zero_adicCompletion S n v)).tTop ?_)
  exact cohomologyMap_cupPairing_of_comp_eq _ _ _ _
    (pairingRes_zmodMulPairing_comp_gsRootsLocalMor S ιs n v) h ξ η

variable (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1)
include hμ

theorem bijective_gsLocalPairing_two (v : S) :
    Function.Bijective fun ξ : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom
        (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) 2 =>
      (gsLocalInvRoots S ιs n v).comp ((bilinAddHom (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))) (show 0 + 2 = 2 from rfl))).flip ξ) := by
  refine bijective_of_bijective_comp_linear (bijective_zmodMulPairing_tTop
    (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
      (natCast_ne_zero_adicCompletion S n v)) (nsmul_galRootsOfUnity_local S n v) (show 2 + 0 = 2 from rfl))
    (bijective_cohomologyMap_of_bijective _ (bijective_zmodResToLocal S ιs n v) 2)
    (γ := (cohomologyMap (gsRootsLocalMor S ιs n v) 0).hom)
    (bijective_cohomologyMap_of_bijective _ (bijective_gsRootsLocalMor S ιs n hμ v) 0) fun ξ η => ?_
  change gsLocalInvRoots S ιs n v (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
    (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))) (show 0 + 2 = 2 from rfl) η ξ) = _
  refine (congrArg (gsLocalInvRoots S ιs n v) (cupPairing_pairingRes_zmodMulPairing_two_zero
    (gsFinFamily S ιs v).toMonoidHom (gsRoots S n) (nsmul_gsRoots S n) (show 2 + 0 = 2 from rfl)
    (show 0 + 2 = 2 from rfl) ξ η).symm).trans ?_
  exact gsLocalInvRoots_cupPairing S ιs n v _ ξ η

theorem bijective_gsLocalPairing_one (v : S) :
    Function.Bijective fun ξ : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom
        (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) 1 =>
      (gsLocalInvRoots S ιs n v).comp ((bilinAddHom (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))) (show 1 + 1 = 2 from rfl))).flip ξ) := by
  refine bijective_of_bijective_comp_linear (bijective_zmodMulPairing_tTop
    (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
      (natCast_ne_zero_adicCompletion S n v)) (nsmul_galRootsOfUnity_local S n v) (show 1 + 1 = 2 from rfl))
    ((bijective_cohomologyMap_of_bijective _ (bijective_zmodResToLocal S ιs n v) 1).comp neg_bijective)
    (γ := (cohomologyMap (gsRootsLocalMor S ιs n v) 1).hom)
    (bijective_cohomologyMap_of_bijective _ (bijective_gsRootsLocalMor S ιs n hμ v) 1) fun ξ η => ?_
  change gsLocalInvRoots S ιs n v (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
    (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))) (show 1 + 1 = 2 from rfl) η ξ) = _
  have e := cupPairing_pairingRes_zmodMulPairing_one (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)
    (nsmul_gsRoots S n) (show 1 + 1 = 2 from rfl) ξ η
  refine (congrArg (gsLocalInvRoots S ιs n v) (neg_eq_iff_eq_neg.2 e).symm).trans ?_
  refine (map_neg _ _).trans ?_
  refine (congrArg Neg.neg (gsLocalInvRoots_cupPairing S ιs n v _ ξ η)).trans ?_
  exact neg_apply_bilin_eq _ _ _ _ _

end

end GroundTheory.ProfCoh
