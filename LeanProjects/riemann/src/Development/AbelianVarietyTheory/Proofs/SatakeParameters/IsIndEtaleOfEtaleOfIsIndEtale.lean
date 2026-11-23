import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIndEtaleAlgebraOfStrictlyHenselianEtaleStalkAf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatMapMaximalIdealIsSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsNoetherianRingOfDirectedPureUnionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOverEtaleOfIsIndEtaleStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC IsLocalRing

namespace GlobalTheory.StalkNoeth

theorem noeth_of_directed_subrings : ∀ (S : Type) [CommRing S] [IsLocalRing S] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S), Monotone R → (∀ x : S, ∃ i, x ∈ R i) → (∀ i, IsNoetherianRing (R i)) → (∀ i, ((maximalIdeal S).comap (R i).subtype).map (R i).subtype = maximalIdeal S) → (∀ i (J : Ideal (R i)), (J.map (R i).subtype).comap (R i).subtype = J) → IsNoetherianRing S :=
  GlobalTheory.T.isNoetherianRing_of_directed_pure_union'

theorem isIndEtale_of_etale_of_isIndEtale : ∀ (A W O : Type) [CommRing A] [CommRing W] [CommRing O] [Algebra A W] [Algebra A O] [Algebra W O] [IsScalarTower A W O] [Algebra.Etale A W], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O) → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) :=
  GlobalTheory.T.isIndEtale_over_etale_of_isIndEtale

noncomputable def stageHom {A W O : Type} [CommRing A] [CommRing W] [CommRing O] [IsLocalRing O] [Algebra A W] [Algebra A O]
    (v : W →ₐ[A] O) : Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O)) →+* O :=
  IsLocalization.lift (M := ((maximalIdeal O).comap (v : W →+* O)).primeCompl) (g := (v : W →+* O))
    (fun y => by by_contra hy; exact y.2 hy)

theorem stageHom_algebraMap {A W O : Type} [CommRing A] [CommRing W] [CommRing O] [IsLocalRing O] [Algebra A W] [Algebra A O]
    (v : W →ₐ[A] O) (w : W) : stageHom v (algebraMap W _ w) = v w :=
  IsLocalization.lift_eq _ _

theorem stage_props {A W O : Type} [CommRing A] [CommRing W] [CommRing O] [IsLocalRing O] [Algebra A W] [Algebra A O]
    [Algebra.Etale A W] (hO : IndEt A O) (v : W →ₐ[A] O) :
    (∀ J : Ideal (Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))), (J.map (stageHom v)).comap (stageHom v) = J) ∧
      (maximalIdeal (Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O)))).map (stageHom v) = maximalIdeal O := by
  set q := (maximalIdeal O).comap (v : W →+* O) with hq
  letI : Algebra W O := (v : W →+* O).toAlgebra
  haveI : IsScalarTower A W O := IsScalarTower.of_algebraMap_eq (fun a => (v.commutes a).symm)
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) := isIndEtale_of_etale_of_isIndEtale A W O hO
  letI : Algebra (Localization.AtPrime q) O := (stageHom v).toAlgebra
  haveI : IsScalarTower W (Localization.AtPrime q) O :=
    IsScalarTower.of_algebraMap_eq (fun w => (stageHom_algebraMap v w).symm)
  have h2 : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Localization.AtPrime q) O) :=
    GlobalTheory.StrictHensUnion.indEtale_over_localization W (Localization.AtPrime q) O q.primeCompl h1
  haveI : IsLocalHom (algebraMap (Localization.AtPrime q) O) := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨⟨w, y⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl a
    rw [IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime q) q]
    have hu : IsUnit (v (y : W)) := by
      by_contra hy
      exact y.2 hy
    have h3 : algebraMap (Localization.AtPrime q) O (IsLocalization.mk' (Localization.AtPrime q) w y) * v y = v w := by
      rw [← stageHom_algebraMap v (y : W), ← stageHom_algebraMap v w]
      change stageHom v _ * stageHom v _ = stageHom v _
      rw [← map_mul, IsLocalization.mk'_spec]
    have h4 : IsUnit (v w) := h3 ▸ ha.mul hu
    intro hw
    exact hw h4
  obtain ⟨hfl, hmax, -⟩ := GlobalTheory.IndEtaleLocal.flat_map_maximalIdeal_isSeparable (Localization.AtPrime q) O h2
  haveI : Module.FaithfullyFlat (Localization.AtPrime q) O := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨fun J => Ideal.comap_map_eq_self_of_faithfullyFlat J, hmax⟩

theorem stage_le {A W W' O : Type} [CommRing A] [CommRing W] [CommRing W'] [CommRing O] [IsLocalRing O] [Algebra A W]
    [Algebra A W'] [Algebra A O] (v : W →ₐ[A] O) (v' : W' →ₐ[A] O) (k : W →ₐ[A] W') (hk : v'.comp k = v) :
    (stageHom v).range ≤ (stageHom v').range := by
  have hle : ((maximalIdeal O).comap (v : W →+* O)).primeCompl ≤
      ((maximalIdeal O).comap (v' : W' →+* O)).primeCompl.comap (k : W →+* W') := by
    intro y hy
    change v' (k y) ∉ maximalIdeal O
    rw [← AlgHom.comp_apply, hk]
    exact hy
  let ψ := IsLocalization.map (S := Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))) (Localization.AtPrime ((maximalIdeal O).comap (v' : W' →+* O))) (k : W →+* W') hle
  have hψ : (stageHom v').comp ψ = stageHom v := by
    refine IsLocalization.ringHom_ext (S := Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))) ((maximalIdeal O).comap (v : W →+* O)).primeCompl ?_
    ext w
    simp only [RingHom.comp_apply, ψ, IsLocalization.map_eq, stageHom_algebraMap]
    rw [← hk]
    rfl
  rw [← hψ]
  rintro _ ⟨x, rfl⟩
  exact ⟨ψ x, rfl⟩

theorem isNoetherianRing_of_indEt : ∀ (A O : Type) [CommRing A] [IsNoetherianRing A] [CommRing O] [IsLocalRing O]
    [Algebra A O], IndEt A O → IsNoetherianRing O := by
  intro A O _ _ _ _ _ hO
  let ι := {T : Subring O // ∃ (W : Type) (_ : CommRing W) (_ : Algebra A W) (_ : Algebra.Etale A W) (v : W →ₐ[A] O),
    T = (stageHom v).range}
  have fac : ∀ (Z : Type) [CommRing Z] [Algebra A Z] [Algebra.FinitePresentation A Z] (g : Z →ₐ[A] O),
      ∃ (W : Type) (_ : CommRing W) (_ : Algebra A W) (_ : Algebra.Etale A W) (u : Z →ₐ[A] W) (v : W →ₐ[A] O),
        v.comp u = g := fun Z _ _ _ g => GlobalTheory.IndEtaleLocal.exists_etale_factor hO g
  have mem : ∀ x : O, ∃ T : ι, x ∈ T.1 := by
    intro x
    obtain ⟨W, _, _, _, u, v, huv⟩ := fac (Polynomial A) (Polynomial.aeval x)
    refine ⟨⟨_, W, inferInstance, inferInstance, inferInstance, v, rfl⟩, algebraMap W _ (u Polynomial.X), ?_⟩
    rw [stageHom_algebraMap]
    have := DFunLike.congr_fun huv Polynomial.X
    simpa using this
  haveI : Nonempty ι := ⟨(mem 0).choose⟩
  haveI : IsDirected ι (· ≤ ·) := by
    refine ⟨fun T1 T2 => ?_⟩
    obtain ⟨T1, W1, _, _, _, v1, rfl⟩ := T1
    obtain ⟨T2, W2, _, _, _, v2, rfl⟩ := T2
    haveI : Algebra.FinitePresentation A (TensorProduct A W1 W2) := Algebra.FinitePresentation.trans A W1 _
    obtain ⟨W3, _, _, _, u, v3, huv⟩ := fac (TensorProduct A W1 W2) (Algebra.TensorProduct.productMap v1 v2)
    refine ⟨⟨_, W3, inferInstance, inferInstance, inferInstance, v3, rfl⟩, ?_, ?_⟩
    · exact stage_le v1 v3 (u.comp Algebra.TensorProduct.includeLeft) (by
        rw [← AlgHom.comp_assoc, huv]; exact Algebra.TensorProduct.productMap_left v1 v2)
    · exact stage_le v2 v3 (u.comp Algebra.TensorProduct.includeRight) (by
        rw [← AlgHom.comp_assoc, huv]; exact Algebra.TensorProduct.productMap_right v1 v2)
  refine noeth_of_directed_subrings O ι (fun T => T.1) (fun _ _ h => h) mem ?_ ?_ ?_
  · rintro ⟨T, W, _, _, _, v, rfl⟩
    haveI : IsNoetherianRing W := Algebra.FiniteType.isNoetherianRing A W
    haveI : IsNoetherianRing (Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))) :=
      IsLocalization.isNoetherianRing ((maximalIdeal O).comap (v : W →+* O)).primeCompl _ inferInstance
    exact isNoetherianRing_range (stageHom v)
  · rintro ⟨T, W, _, _, _, v, rfl⟩
    obtain ⟨-, hmax⟩ := stage_props hO v
    refine le_antisymm Ideal.map_comap_le ?_
    conv_lhs => rw [← hmax]
    rw [Ideal.map_le_iff_le_comap]
    intro l hl
    have h1 : stageHom v l ∈ maximalIdeal O := hmax.le (Ideal.mem_map_of_mem _ hl)
    have h2 : (⟨stageHom v l, l, rfl⟩ : (stageHom v).range) ∈ (maximalIdeal O).comap (stageHom v).range.subtype := h1
    exact Ideal.mem_map_of_mem _ h2
  · rintro ⟨T, W, _, _, _, v, rfl⟩ J
    obtain ⟨hc, -⟩ := stage_props hO v
    refine le_antisymm ?_ Ideal.le_comap_map
    intro x hx
    obtain ⟨y, rfl⟩ := (stageHom v).rangeRestrict_surjective x
    have hJ : J = (J.comap (stageHom v).rangeRestrict).map (stageHom v).rangeRestrict :=
      (Ideal.map_comap_of_surjective _ (stageHom v).rangeRestrict_surjective J).symm
    have h2 : stageHom v y ∈ (J.comap (stageHom v).rangeRestrict).map (stageHom v) := by
      rw [hJ, Ideal.map_map] at hx
      exact hx
    have h3 := (hc (J.comap (stageHom v).rangeRestrict)).le h2
    exact h3

theorem isNoetherianRing_of_isStalk : ∀ (B : Type) [CommRing B] [Algebra.FiniteType ℤ B] (O : Type) [CommRing O]
    [IsLocalRing O] (s : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of B)), IsStalk O s → IsNoetherianRing O := by
  intro B _ _ O _ _ s hs
  obtain ⟨_, -, hind, -⟩ := isStalk_affine B O s hs
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  exact isNoetherianRing_of_indEt B O hind

end GlobalTheory.StalkNoeth
