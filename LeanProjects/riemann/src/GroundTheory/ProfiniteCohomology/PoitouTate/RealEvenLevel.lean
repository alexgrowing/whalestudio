import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
import GroundTheory.ProfiniteCohomology.PoitouTate.RealAbstract
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLevel
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

attribute [local instance 2000] Rep.hV2

section Algebra

theorem bijective_of_surjective_of_surjective_dual {A : Type*} [AddCommGroup A] {n : ℕ} [NeZero n]
    (hA : ∀ a : A, n • a = 0) (T : A →+ ZMod n) (hT : Function.Surjective T)
    (e : ZMod n → (A →+ ZMod n)) (he : Function.Surjective e) : Function.Bijective T := by
  have : Finite (A →+ ZMod n) := Finite.of_surjective e he
  have : Finite A := finite_of_finite_addMonoidHom_zmod hA
  let ev : A → ((A →+ ZMod n) →+ ZMod n) := fun a =>
    { toFun := fun χ => χ a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    intro a b hab
    by_contra hne
    obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero hA (sub_ne_zero.2 hne)
    apply hχ
    rw [map_sub, sub_eq_zero]
    exact DFunLike.congr_fun hab χ
  have h1 : Nat.card A ≤ Nat.card ((A →+ ZMod n) →+ ZMod n) := Nat.card_le_card_of_injective ev hev
  have h2 : Nat.card ((A →+ ZMod n) →+ ZMod n) ≤ Nat.card (A →+ ZMod n) :=
    card_addMonoidHom_zmod_le (n := n) (A := A →+ ZMod n)
  have h3 : Nat.card (A →+ ZMod n) ≤ Nat.card (ZMod n) := Nat.card_le_card_of_surjective e he
  exact hT.bijective_of_nat_card_le (h1.trans (h2.trans h3))

end Algebra

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {n : ℕ} [NeZero n] {D : Rep (ULift.{0} ℤ) G} [IsDiscreteRep D] (hD : ∀ d : D, n • d = 0)
  [IsDiscreteRep (dualRep D (zmodRep.{0} G n))]

omit [TopologicalSpace G] [IsTopologicalGroup G] [NeZero n] [IsDiscreteRep D]
  [IsDiscreteRep (dualRep D (zmodRep.{0} G n))] in

theorem tensorHom_zmodDualIso_inv_dualEvalPairing :
    ((zmodDualIso n D hD).inv ⊗ₘ 𝟙 (zmodRep.{0} G n)) ≫ dualEvalPairing D (zmodRep.{0} G n) =
      (𝟙 D ⊗ₘ 𝟙 (zmodRep.{0} G n)) ≫ zmodMulPairingRight n D hD := by
  rw [← tensorHom_zmodDualIso_zmodMulPairingRight D hD, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, Iso.inv_hom_id, Category.comp_id]

omit [NeZero n] in

theorem compactZmodDualityMap_eq_compactDualityMap {m r s : ℕ}
    (T : compactCohomologyRes φ D m →+ ZMod n) (h : r + s = m) (x : cohomology (zmodRep.{0} G n) r)
    (y : compactCohomologyRes φ D s) :
    compactZmodDualityMap φ D hD T h x y =
      compactDualityMap φ D h T (zmodRep.{0} G n) x
        ((compactCohomologyResMap φ (zmodDualIso n D hD).inv s).hom y) := by
  have e := compactCupRes_compactCohomologyResMap φ (dualEvalPairing D (zmodRep.{0} G n))
    (zmodMulPairingRight n D hD) (zmodDualIso n D hD).inv (𝟙 _)
    (tensorHom_zmodDualIso_inv_dualEvalPairing hD) ((Nat.add_comm s r).trans h) y x
  rw [cohomologyMap_id, ModuleCat.hom_id, LinearMap.id_apply] at e
  rw [compactZmodDualityMap_apply, compactDualityMap_apply, e]

theorem bijective_compactZmodDualityMap_of_compactDualityMap {m r s : ℕ}
    (T : compactCohomologyRes φ D m →+ ZMod n) (h : r + s = m)
    (hb : Function.Bijective (compactDualityMap φ D h T (zmodRep.{0} G n))) :
    Function.Bijective (compactZmodDualityMap φ D hD T h) :=
  bijective_of_bijective_comp hb Function.bijective_id
    (bijective_compactCohomologyResMap_of_comp_eq_id φ (zmodDualIso n D hD).inv (zmodDualIso n D hD).hom
      (Iso.inv_hom_id _) (Iso.hom_inv_id _) s)
    (γ := (compactCohomologyResMap φ (zmodDualIso n D hD).inv s).hom.toAddMonoidHom)
    fun x y => compactZmodDualityMap_eq_compactDualityMap φ hD T h x y

end Generic

section Level

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {N : ℕ} [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hK : Odd N ∨ IsTotallyComplex K.1)

set_option synthInstance.maxHeartbeats 400000 in
include hS in

theorem bijective_gs_compactZmodDualityMap_of_duality {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactZmodDualityMap (gsFinFamily S ιs) (gsRoots S N) (nsmul_gsRoots S N)
      (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) h) := by
  have : IsDiscreteRep (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) N) := isDiscreteRep_of_isTrivial _
  have : IsDiscreteRep (dualRep (gsRoots S N) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) N)) :=
    isDiscreteRep_dualRep _ _
  exact bijective_compactZmodDualityMap_of_compactDualityMap (gsFinFamily S ιs) (nsmul_gsRoots S N) _ h
    (poitouTate_duality_gs S ιs hS hK (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) N)
      (nsmul_zmodRep_eq_zero _ N) h)

include hS in

theorem bijective_gsCompactInv_of_duality [Nonempty S] :
    Function.Bijective (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) :=
  bijective_of_surjective_of_surjective_dual
    (nsmul_compactCohomologyRes_eq_zero (gsFinFamily S ιs) (nsmul_gsRoots S N) 3) _
    (surjective_gsCompactInv S N ιs hK (subsingleton_cohomology_three_gsRoots S hS hK) fun v =>
      (bijective_gsLocalInvRoots_of_places S ιs N (fun v hv h => hv (hS v h)) v).2)
    (fun a => compactZmodDualityMap (gsFinFamily S ιs) (gsRoots S N) (nsmul_gsRoots S N)
      (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) (show 0 + 3 = 3 from rfl)
      (zmodH0Class a))
    ((bijective_gs_compactZmodDualityMap_of_duality S ιs hS hK (show 0 + 3 = 3 from rfl)).2.comp
      (zmodH0Class_surjective (H := galUnramifiedOutside K.1 ℚ̄ S) (n := N)))

include hS in

theorem gsLevelBijective_gsCompactInv [Nonempty S] :
    GsLevelBijective (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) :=
  ⟨bijective_gsCompactInv_of_duality S ιs hS hK, fun h => bijective_gs_compactZmodDualityMap_of_duality S ιs hS hK h⟩

end Level

section OpenSubgroup

variable {K L : FiniteSubfield} [Fact (K ≤ L)] (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) (n : ℕ) [NeZero n]

set_option maxHeartbeats 3200000 in

theorem bijective_compactZmodDualityMap_gsOpenSubgroup_of_surjective
    (τ : compactCohomologyRes (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
      (Rep.res (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S n)) 3 →+ ZMod n)
    (hτ : Function.Surjective τ)
    (TL : compactCohomologyRes (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
      (gsRoots (K := L) (placesOver S) n) 3 →+ ZMod n) (hLev : GsLevelBijective TL) {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactZmodDualityMap (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
      (Rep.res (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S n))
      (nsmul_gsRoots S n) τ h) := by
  have hTL := hLev.1
  let f := (gsRootsOfUnityIso S hL n).symm
  let eW := (gsMackeyCompactIso hL ιs f 3).toLinearEquiv.toAddEquiv
  let eY := (gsMackeyCompactIso hL ιs f s).toLinearEquiv.toAddEquiv
  let eX := (cohomologyIsoOfContinuousMulEquiv (gsBaseChange S hL) (zmodRepResIso (gsBaseChange S hL) n) r).toLinearEquiv.toAddEquiv
  have hex := exists_isUnit_mul_of_surjective_of_bijective τ (TL.comp eW.symm.toAddMonoidHom) hτ
    (hTL.comp eW.symm.bijective)
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

end OpenSubgroup

end

end GroundTheory.ProfCoh
