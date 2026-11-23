import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateCondCongr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSepClosedResidueFieldOfModuleFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsLift

theorem surjective_algebraMap_of_finite_unramified : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra R T] [Module.Finite R T]
    [Algebra.FormallyUnramified R T], Function.Surjective (algebraMap R T) := by
  intro R _ _ _ T _ _ _ _ _
  haveI := GlobalTheory.isLocalHom_algebraMap_of_moduleFinite R T
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := T)
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T) :=
    inferInstance
  have hk : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  let N : Submodule R T := LinearMap.range (Algebra.linearMap R T)
  have hNN : (⊤ : Submodule R T) ≤ N ⊔ IsLocalRing.maximalIdeal R • ⊤ := by
    intro x _
    obtain ⟨c, hc⟩ := hk (IsLocalRing.residue T x)
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
    have hr : IsLocalRing.residue T (algebraMap R T r) = IsLocalRing.residue T x := by
      rw [← hc, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsLocalRing.ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R)]
    have hx : x - algebraMap R T r ∈ IsLocalRing.maximalIdeal T := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hr, sub_self]
    rw [← hm] at hx
    have hx' : x - algebraMap R T r ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R T) := by
      rw [Ideal.smul_top_eq_map]; exact hx
    have : x = algebraMap R T r + (x - algebraMap R T r) := by ring
    rw [this]
    exact Submodule.add_mem_sup ⟨r, rfl⟩ hx'
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hNN
  intro y
  obtain ⟨r, hr⟩ := hle (Submodule.mem_top (x := y))
  exact ⟨r, hr⟩

theorem nonempty_algHom_residueField : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra R T] [Module.Finite R T],
    Nonempty (T →ₐ[R] IsLocalRing.ResidueField R) := by
  intro R _ _ _ T _ _ _ _
  haveI := GlobalTheory.isLocalHom_algebraMap_of_moduleFinite R T
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T) :=
    inferInstance
  let l : IsLocalRing.ResidueField T →ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R :=
    IsAlgClosed.lift
  exact ⟨(l.restrictScalars R).comp (IsScalarTower.toAlgHom R T (IsLocalRing.ResidueField T))⟩

theorem exists_section_of_point : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (B : Type) [CommRing B] [Algebra R B] [Algebra.Etale R B] [Module.Finite R B]
    (K : Type) [Field K] (φ : R →+* K) (χ : B →+* K), χ.comp (algebraMap R B) = φ →
    ∃ ψ : B →+* R, ψ.comp (algebraMap R B) = RingHom.id R ∧ φ.comp ψ = χ := by
  intro R _ _ _ B _ _ _ _ K _ φ χ hχ
  classical
  obtain ⟨J, hJ, T, _, _, e, hT, hT'⟩ := GlobalTheory.finite_algebra_strictly_henselian_pi R B
  haveI := Fintype.ofFinite J
  let ε : J → B := fun i => e.symm (Pi.single i 1)
  have hεsum : ∑ i, ε i = 1 := by
    simp only [ε, ← map_sum, Finset.univ_sum_single]
    exact map_one e.symm
  have hεid : ∀ i, IsIdempotentElem (ε i) := fun i => by
    show e.symm _ * e.symm _ = e.symm _
    rw [← map_mul, ← Pi.single_mul, _root_.one_mul]

  have hfac : ∀ (L : Type) [CommRing L] (ω : B →+* L) (i : J), ω (ε i) = 1 →
      ∀ (x : B) (r : R), e x i = algebraMap R (T i) r → ω x = ω (algebraMap R B r) := by
    intro L _ ω i hωi x r hr
    have hx : x * ε i = algebraMap R B r * ε i := by
      apply e.injective
      funext j
      simp only [ε, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, Pi.mul_apply,
        Pi.algebraMap_apply]
      by_cases h : j = i
      · subst h; simp [hr]
      · simp [Pi.single_eq_of_ne h]
    have := congrArg ω hx
    rwa [map_mul, map_mul, hωi, _root_.mul_one, _root_.mul_one] at this
  obtain ⟨i, hi⟩ : ∃ i, χ (ε i) ≠ 0 := by
    by_contra h
    push_neg at h
    have := congrArg χ hεsum
    simp [map_sum, h] at this
  have hi1 : χ (ε i) = 1 := (IsIdempotentElem.iff_eq_zero_or_one.1 ((hεid i).map χ)).resolve_left hi
  haveI : IsLocalRing (T i) := inferInstance
  haveI : Module.Finite R (T i) := (hT' i).2
  let π : B →ₐ[R] T i := (Pi.evalAlgHom R T i).comp e.toAlgHom
  have hπ : Function.Surjective π := fun y => ⟨e.symm (Pi.single i y), by simp [π]⟩
  haveI : Algebra.FormallyUnramified R (T i) := Algebra.FormallyUnramified.of_surjective π hπ
  have hsurj : Function.Surjective (algebraMap R (T i)) := surjective_algebraMap_of_finite_unramified R (T i)
  obtain ⟨β⟩ := nonempty_algHom_residueField R (T i)
  obtain ⟨ψ₀, hψ₀⟩ := (GlobalTheory.EtaleHensel.bijective_residue_comp R B R).2 (β.comp π)
  have hψi : ψ₀ (ε i) = 1 := by
    have h1 : IsLocalRing.residue R (ψ₀ (ε i)) = 1 := by
      have := congrArg (fun g : B →ₐ[R] IsLocalRing.ResidueField R => g (ε i)) hψ₀
      simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] at this
      rw [← IsLocalRing.ResidueField.algebraMap_eq, this]
      simp [π, ε]
    have hloc : ∀ a : R, IsIdempotentElem a → a = 0 ∨ a = 1 := fun a ha => by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
      · right; exact h.mul_left_cancel (by rw [ha.eq, _root_.mul_one])
      · left
        have h0 : (1 - a) * a = 0 := by rw [sub_mul, _root_.one_mul, ha.eq, sub_self]
        exact h.mul_right_eq_zero.1 h0
    rcases hloc _ ((hεid i).map ψ₀) with h | h
    · rw [h, map_zero] at h1; exact absurd h1.symm one_ne_zero
    · exact h
  refine ⟨ψ₀.toRingHom, ?_, ?_⟩
  · ext r; simp
  · ext x
    obtain ⟨r, hr⟩ := hsurj (e x i)
    have h1 : χ x = φ r := by
      rw [hfac K χ i hi1 x r hr.symm]
      show (χ.comp (algebraMap R B)) r = φ r
      rw [hχ]
    have h2 : ψ₀ x = r := by
      have := hfac R ψ₀.toRingHom i hψi x r hr.symm
      simpa using this
    show φ (ψ₀ x) = χ x
    rw [h1, h2]

theorem exists_iso_sp_of_finite_etale : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsFinite f → Etale f →
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B), Algebra.Etale R B ∧ Module.Finite R B ∧
      ∃ e : X ≅ Sp B, e.hom ≫ spMap (algebraMap R B) = f := by
  intro R _ X f hf hfe
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let ρ : R →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom
  letI : Algebra R Γ(X, ⊤) := ρ.toAlgebra
  have key : X.isoSpec.hom ≫ spMap (algebraMap R Γ(X, ⊤)) = f := by
    have h := Scheme.isoSpec_hom_naturality f
    rw [Scheme.isoSpec_Spec_hom] at h
    show X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ρ) = f
    rw [show CommRingCat.ofHom ρ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop from rfl,
      Spec.map_comp, ← Category.assoc, h, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  have hsp : spMap (algebraMap R Γ(X, ⊤)) = X.isoSpec.inv ≫ f := by
    rw [← key, Iso.inv_hom_id_assoc]
  have het : Etale (spMap (algebraMap R Γ(X, ⊤))) := by rw [hsp]; infer_instance
  have hfi : IsFinite (spMap (algebraMap R Γ(X, ⊤))) := by rw [hsp]; infer_instance
  refine ⟨Γ(X, ⊤), inferInstance, inferInstance, ?_, ?_, X.isoSpec, key⟩
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).1 het
  · exact (IsFinite.SpecMap_iff _).1 hfi

theorem preconnectedSpace_sp (R : Type) [CommRing R] [IsLocalRing R] : PreconnectedSpace (Sp R) := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  have key : ∀ z : Sp R, z ⤳ (IsLocalRing.closedPoint R : PrimeSpectrum R) := fun z =>
    IsLocalRing.specializes_closedPoint (R := R) z
  by_cases h : (IsLocalRing.closedPoint R : PrimeSpectrum R) ∈ s
  · right; ext z; simp only [Set.mem_univ, iff_true]; exact (key z).mem_open hs.isOpen h
  · left; ext z; simp only [Set.mem_empty_iff_false, iff_false]
    exact fun hz => h ((key z).mem_closed hs.isClosed hz)

theorem torsion_points_restrict_bijective : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A],
    IsAbelianScheme A → ∀ (n : ℕ), 0 < n → IsUnit (n : Γ(S, ⊤)) →
    ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (t : Sp R ⟶ S)
    (K : Type) [Field K] (φ : R →+* K),
    (∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 →
      (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ g =
        (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ h → g = h) ∧
    ∀ x : Over.mk (spMap φ ≫ t) ⟶ A, x ^ n = 1 → ∃ g : Over.mk t ⟶ A, g ^ n = 1 ∧
      (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ g = x := by
  intro S A _ _ hA n _ hn R _ _ _ t K _ φ
  haveI := hA
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A hn
  haveI := hfin
  haveI := het
  haveI := preconnectedSpace_sp R
  let ψK : Over.mk (spMap φ ≫ t) ⟶ Over.mk t := Over.homMk (spMap φ) rfl
  let E := GlobalTheory.TorsionUnram.torsionEquiv A n
  refine ⟨fun g h hg hh hgh => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := (E _).surjective ⟨g, hg⟩
    obtain ⟨b, hb⟩ := (E _).surjective ⟨h, hh⟩
    have ga : a ≫ torsion.ι A n = g := congrArg Subtype.val ha
    have gb : b ≫ torsion.ι A n = h := congrArg Subtype.val hb
    have hab : ψK ≫ a = ψK ≫ b := by
      apply (E _).injective
      apply Subtype.ext
      show (ψK ≫ a) ≫ torsion.ι A n = (ψK ≫ b) ≫ torsion.ι A n
      rw [Category.assoc, Category.assoc, ga, gb]
      exact hgh
    have hab' : spMap φ ≫ a.left = spMap φ ≫ b.left := congrArg (fun u => u.left) hab
    haveI : PreconnectedSpace (Over.mk t).left := preconnectedSpace_sp R
    have : a = b := GlobalTheory.over_eq_of_preconnected_of_unramified (spMap φ) hab'
    rw [← ga, ← gb, this]
  · obtain ⟨y, hy⟩ := (E _).surjective ⟨x, hx⟩
    have yx : y ≫ torsion.ι A n = x := congrArg Subtype.val hy
    obtain ⟨B, _, _, _, _, e, he⟩ :=
      exists_iso_sp_of_finite_etale R _ (pullback.snd (torsion A n).hom t) inferInstance inferInstance
    let q : Sp K ⟶ Sp B := pullback.lift y.left (spMap φ) (Over.w y) ≫ e.hom
    obtain ⟨χ', hχ'⟩ := Spec.map_surjective q
    have hq : q ≫ spMap (algebraMap R B) = spMap φ := by
      simp only [q, Category.assoc, he, pullback.lift_snd]
    have hχ : χ'.hom.comp (algebraMap R B) = φ := by
      have h0 : Spec.map (CommRingCat.ofHom (algebraMap R B) ≫ χ') =
          Spec.map (CommRingCat.ofHom φ) := by
        rw [Spec.map_comp, hχ']
        exact hq
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h0)
    obtain ⟨ψ, hψ1, hψ2⟩ := exists_section_of_point R B K φ χ'.hom hχ
    let s : Sp R ⟶ (torsion A n).left := spMap ψ ≫ e.inv ≫ pullback.fst _ _
    have h1 : e.inv ≫ pullback.snd (torsion A n).hom t = spMap (algebraMap R B) := by
      rw [← he, Iso.inv_hom_id_assoc]
    have hs : s ≫ (torsion A n).hom = t := by
      simp only [s, Category.assoc, pullback.condition]
      rw [reassoc_of% h1, ← Category.assoc, ← GlobalTheory.TorsionUnram.spMap_comp', hψ1]
      show Spec.map (CommRingCat.ofHom (RingHom.id R)) ≫ t = t
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    let gs : Over.mk t ⟶ torsion A n := Over.homMk s hs
    refine ⟨gs ≫ torsion.ι A n, ((E _) gs).2, ?_⟩
    have h2 : spMap φ ≫ spMap ψ = q := by
      rw [← GlobalTheory.TorsionUnram.spMap_comp', hψ2, ← hχ']
      rfl
    have hy' : ψK ≫ gs = y := by
      apply Over.OverMorphism.ext
      show spMap φ ≫ s = y.left
      simp only [s, ← Category.assoc]
      rw [h2]
      simp only [q, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]
    rw [← Category.assoc, hy', yx]

end GlobalTheory.TorsLift
