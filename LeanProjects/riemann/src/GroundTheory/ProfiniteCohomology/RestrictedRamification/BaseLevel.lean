import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BijectiveGsCompactZmodDualityMap
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseTransportGS
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Algebra

variable {n : ℕ} [NeZero n]

theorem exists_isUnit_mul_of_surjective_of_bijective {Y : Type*} [AddCommGroup Y] (f g : Y →+ ZMod n)
    (hf : Function.Surjective f) (hg : Function.Bijective g) :
    ∃ c : ZMod n, IsUnit c ∧ ∀ y, f y = c * g y := by
  obtain ⟨y₁, hy₁⟩ := hg.2 1
  have hy : ∀ y, y = (g y).val • y₁ := fun y => hg.1 (by
    rw [map_nsmul, hy₁, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val])
  have hfy : ∀ y, f y = f y₁ * g y := fun y => by
    conv_lhs => rw [hy y]
    rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  refine ⟨f y₁, ?_, hfy⟩
  obtain ⟨y, hy1⟩ := hf 1
  exact IsUnit.of_mul_eq_one (g y) ((hfy y).symm.trans hy1)

omit [NeZero n] in

theorem bijective_of_transport {X X' Y Y' W W' : Type*} [AddCommGroup X] [AddCommGroup X'] [AddCommGroup Y]
    [AddCommGroup Y'] [AddCommGroup W] [AddCommGroup W'] (B : Y →+ X →+ W) (B' : Y' →+ X' →+ W')
    (T : W →+ ZMod n) (f : W' →+ ZMod n) (eX : X ≃+ X') (eY : Y ≃+ Y') (eW : W ≃+ W')
    (hcup : ∀ y x, B' (eY y) (eX x) = eW (B y x)) (c : ZMod n) (hc : IsUnit c)
    (hf : ∀ w, f (eW w) = c * T w) (hbij : Function.Bijective fun x => T.comp (B.flip x)) :
    Function.Bijective fun x' => f.comp (B'.flip x') := by
  have hF : Function.Bijective fun x => (c • T).comp (B.flip x) := by
    refine ⟨fun x x' h => hbij.1 (AddMonoidHom.ext fun y => ?_), fun χ => ?_⟩
    · have e := DFunLike.congr_fun h y
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, AddMonoidHom.smul_apply, smul_eq_mul] at e ⊢
      exact hc.mul_left_cancel e
    · obtain ⟨x, hx⟩ := hbij.2 ((hc.unit⁻¹ : (ZMod n)ˣ) • χ)
      refine ⟨x, AddMonoidHom.ext fun y => ?_⟩
      have e := DFunLike.congr_fun hx y
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, AddMonoidHom.smul_apply, smul_eq_mul,
        Units.smul_def] at e ⊢
      rw [e, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  refine bijective_of_bijective_comp hF eX.symm.bijective (γ := eY.symm.toAddMonoidHom) eY.symm.bijective
    fun x' y' => ?_
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, AddMonoidHom.smul_apply, smul_eq_mul,
    AddEquiv.coe_toAddMonoidHom]
  conv_lhs => rw [← eX.apply_symm_apply x', ← eY.apply_symm_apply y']
  rw [hcup, hf]

end Algebra

section Level

variable {K L : FiniteSubfield} [Fact (K ≤ L)] (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) (n : ℕ) [NeZero n]

def GsBaseBijective (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (t : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 3 →+ ZMod n) : Prop :=
  ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective (zmodCompactDualityMap (gsFinFamily S ιs) (gsRoots S n)
    (nsmul_gsRoots S n) U h t)

def GsCoresSurjective (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (t : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 3 →+ ZMod n) : Prop :=
  Function.Surjective (t.comp (compactCores (gsFinFamily S ιs) U (gsRoots S n) 3).hom.toAddMonoidHom)

variable {S ιs n} in

def GsLevelBijective (T : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 3 →+ ZMod n) : Prop :=
  Function.Bijective T ∧ ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective (compactZmodDualityMap (gsFinFamily S ιs)
    (gsRoots S n) (nsmul_gsRoots S n) T h)

set_option maxHeartbeats 3200000 in

theorem bijective_zmodCompactDualityMap_gsOpenSubgroup
    (t : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 3 →+ ZMod n)
    (TL : compactCohomologyRes (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
      (gsRoots (K := L) (placesOver S) n) 3 →+ ZMod n) (hLev : GsLevelBijective TL)
    (hsurj : GsCoresSurjective S ιs n (gsOpenSubgroup S hL) t) :
    GsBaseBijective S ιs n (gsOpenSubgroup S hL) t := by
  intro r s h
  have hTL := hLev.1
  let f := (gsRootsOfUnityIso S hL n).symm
  let eW := (gsMackeyCompactIso hL ιs f 3).toLinearEquiv.toAddEquiv
  let eY := (gsMackeyCompactIso hL ιs f s).toLinearEquiv.toAddEquiv
  let eX := (cohomologyIsoOfContinuousMulEquiv (gsBaseChange S hL) (zmodRepResIso (gsBaseChange S hL) n) r).toLinearEquiv.toAddEquiv
  have hex := exists_isUnit_mul_of_surjective_of_bijective
    (t.comp (compactCores (gsFinFamily S ιs) (gsOpenSubgroup S hL) (gsRoots S n) 3).hom.toAddMonoidHom)
    (TL.comp eW.symm.toAddMonoidHom) hsurj (hTL.comp eW.symm.bijective)
  exact hex.elim fun c hcf => hcf.elim fun hc hfc => bijective_of_transport
    (bilinAddHom (compactCupRes (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
      (zmodMulPairingRight n (gsRoots (K := L) (placesOver S) n) (nsmul_gsRoots (K := L) (placesOver S) n))
      ((Nat.add_comm s r).trans h)))
    (bilinAddHom (compactCupRes (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
      (zmodMulPairingRight n (Rep.res (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (gsRoots S n)) (nsmul_gsRoots S n)) ((Nat.add_comm s r).trans h)))
    TL _ eX eY eW
    (fun y x => (gsMackeyCompactIso_compactCupRes_zmod hL ιs n (nsmul_gsRoots (K := L) (placesOver S) n)
      (nsmul_gsRoots S n) f ((Nat.add_comm s r).trans h) y x).symm)
    c hc (fun w => (hfc _).trans (congrArg (c * TL ·) (eW.symm_apply_apply w))) (hLev.2 h)

end Level

end

end GroundTheory.ProfCoh
