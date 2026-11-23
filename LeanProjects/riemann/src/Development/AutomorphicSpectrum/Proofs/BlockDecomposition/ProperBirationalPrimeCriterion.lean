import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Krull

theorem stalkMap_germ_appLE {Y Z : Scheme.{0}} (ψ : Z ⟶ Y) (W : Y.Opens) (U : Z.Opens)
    (h : U ≤ ψ ⁻¹ᵁ W) (z : Z) (hz : z ∈ U) (hy : ψ z ∈ W) (a : Γ(Y, W)) :
    ψ.stalkMap z (Y.presheaf.germ W (ψ z) hy a) = Z.presheaf.germ U z hz (ψ.appLE W U h a) := by
  simp [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, TopCat.Presheaf.germ_res_apply]

theorem isUnit_germ_fromSpec {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(Z, U)) (hz : hU.fromSpec q ∈ U) (c : Γ(Z, U)) :
    IsUnit (Z.presheaf.germ U _ hz c) ↔ c ∉ q.asIdeal := by
  letI : Algebra Γ(Z, U) (Z.presheaf.stalk (hU.fromSpec q)) := (Z.presheaf.germ U _ hz).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Z.presheaf.stalk (hU.fromSpec q)) q.asIdeal := hU.isLocalization_stalk' q hz
  rw [← Ideal.mem_primeCompl_iff]
  exact IsLocalization.AtPrime.isUnit_to_map_iff (Z.presheaf.stalk (hU.fromSpec q)) q.asIdeal c

theorem exists_mul_eq_of_germ_eq {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(Z, U)) (hz : hU.fromSpec q ∈ U) (c d : Γ(Z, U))
    (e : Z.presheaf.germ U _ hz c = Z.presheaf.germ U _ hz d) :
    ∃ v : Γ(Z, U), v ∉ q.asIdeal ∧ v * c = v * d := by
  letI : Algebra Γ(Z, U) (Z.presheaf.stalk (hU.fromSpec q)) := (Z.presheaf.germ U _ hz).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Z.presheaf.stalk (hU.fromSpec q)) q.asIdeal := hU.isLocalization_stalk' q hz
  obtain ⟨⟨v, hv⟩, hvcd⟩ :=
    (IsLocalization.eq_iff_exists q.asIdeal.primeCompl (Z.presheaf.stalk (hU.fromSpec q))).mp e
  exact ⟨v, hv, hvcd⟩

theorem exists_frac_stalk {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) (y : Y) (hy : y ∈ W)
    (s : Y.presheaf.stalk y) :
    ∃ a u : Γ(Y, W), IsUnit (Y.presheaf.germ W y hy u) ∧
      s * Y.presheaf.germ W y hy u = Y.presheaf.germ W y hy a := by
  letI : Algebra Γ(Y, W) (Y.presheaf.stalk y) := (Y.presheaf.germ W y hy).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hW.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨⟨a, u⟩, hs⟩ := IsLocalization.surj (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl s
  exact ⟨a, u.1, IsLocalization.map_units (Y.presheaf.stalk y) u, hs⟩

theorem exists_mul_eq_zero_of_germ {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) (y : Y)
    (hy : y ∈ W) (a : Γ(Y, W)) (e : Y.presheaf.germ W y hy a = 0) :
    ∃ u : Γ(Y, W), IsUnit (Y.presheaf.germ W y hy u) ∧ u * a = 0 := by
  letI : Algebra Γ(Y, W) (Y.presheaf.stalk y) := (Y.presheaf.germ W y hy).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hW.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨⟨u, hu⟩, hua⟩ :=
    (IsLocalization.map_eq_zero_iff (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y) a).mp e
  exact ⟨u, IsLocalization.map_units (Y.presheaf.stalk y) (⟨u, hu⟩ : (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl), hua⟩

theorem isIso_stalkMap_of_isIso_restrict {Y Z : Scheme.{0}} (ψ : Z ⟶ Y) (W : Y.Opens)
    (h : IsIso (ψ ∣_ W)) (z : Z) (hz : z ∈ ψ ⁻¹ᵁ W) : IsIso (ψ.stalkMap z) := by
  haveI : IsIso ((ψ ∣_ W).stalkMap ⟨z, hz⟩) := by
    first
    | infer_instance
    | (haveI : IsOpenImmersion (ψ ∣_ W) := inferInstance; infer_instance)
    | (haveI : IsOpenImmersion (ψ ∣_ W) := IsOpenImmersion.of_isIso _; infer_instance)
    | exact PresheafedSpace.IsOpenImmersion.stalk_iso (ψ ∣_ W).toPshHom ⟨z, hz⟩
  have e := morphismRestrictStalkMap ψ W ⟨z, hz⟩
  show IsIso (ψ.stalkMap (⟨z, hz⟩ : (ψ ⁻¹ᵁ W : Z.Opens)).1)
  rw [Arrow.iso_w' e]
  infer_instance

theorem chart_fractions_of_isIso_stalkMap {Y Z : Scheme.{0}} (ψ : Z ⟶ Y) {W : Y.Opens}
    (hW : IsAffineOpen W) {U : Z.Opens} (hU : IsAffineOpen U) (h : U ≤ ψ ⁻¹ᵁ W)
    (q : PrimeSpectrum Γ(Z, U)) (hz : hU.fromSpec q ∈ U) (hiso : IsIso (ψ.stalkMap (hU.fromSpec q))) :
    (∀ c : Γ(Z, U), ∃ a u : Γ(Y, W), ψ.appLE W U h u ∉ q.asIdeal ∧
      ∃ v : Γ(Z, U), v ∉ q.asIdeal ∧ v * (ψ.appLE W U h u * c) = v * ψ.appLE W U h a) ∧
    (∀ a : Γ(Y, W), (∃ v : Γ(Z, U), v ∉ q.asIdeal ∧ v * ψ.appLE W U h a = 0) →
      ∃ u : Γ(Y, W), ψ.appLE W U h u ∉ q.asIdeal ∧ u * a = 0) := by
  have hy : ψ (hU.fromSpec q) ∈ W := h hz
  have hbij := (ConcreteCategory.isIso_iff_bijective (ψ.stalkMap (hU.fromSpec q))).mp hiso
  constructor
  · intro c
    obtain ⟨s, hs0⟩ := hbij.2 (Z.presheaf.germ U _ hz c)
    obtain ⟨a, u, hu, hs⟩ := exists_frac_stalk hW (ψ (hU.fromSpec q)) hy s
    have hs' := congrArg (ψ.stalkMap (hU.fromSpec q)) hs
    rw [map_mul, hs0, stalkMap_germ_appLE ψ W U h _ hz hy u, stalkMap_germ_appLE ψ W U h _ hz hy a] at hs'
    have hu' : IsUnit (Z.presheaf.germ U _ hz (ψ.appLE W U h u)) := by
      rw [← stalkMap_germ_appLE ψ W U h _ hz hy u]
      exact hu.map _
    rw [isUnit_germ_fromSpec hU q hz] at hu'
    refine ⟨a, u, hu', ?_⟩
    apply exists_mul_eq_of_germ_eq hU q hz
    rw [map_mul, mul_comm, hs']
  · rintro a ⟨v, hv, hva⟩
    have h0 : Z.presheaf.germ U _ hz (ψ.appLE W U h a) = 0 := by
      have hvu : IsUnit (Z.presheaf.germ U _ hz v) := (isUnit_germ_fromSpec hU q hz v).mpr hv
      have hh := congrArg (Z.presheaf.germ U _ hz) hva
      rw [map_mul, map_zero] at hh
      exact hvu.mul_right_eq_zero.mp hh
    have h1 : Y.presheaf.germ W _ hy a = 0 := by
      apply hbij.1
      rw [map_zero, stalkMap_germ_appLE ψ W U h _ hz hy a, h0]
    obtain ⟨u, hu, hua⟩ := exists_mul_eq_zero_of_germ hW _ hy a h1
    refine ⟨u, ?_, hua⟩
    rw [← isUnit_germ_fromSpec hU q hz, ← stalkMap_germ_appLE ψ W U h _ hz hy u]
    exact hu.map _

theorem chart_fractions_subscheme {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}}
    (ψ : Z ⟶ J.subscheme) (V : X.Opens) (hV : IsAffineOpen V) (f : Γ(X, V))
    (hiso : IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f))) (U : Z.Opens) (hU : IsAffineOpen U)
    (h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V) (q : Ideal Γ(Z, U)) (hq : q.IsPrime)
    (hf : (ψ ≫ J.subschemeι).appLE V U h f ∉ q) :
    (∀ c : Γ(Z, U), ∃ b t : Γ(X, V), (ψ ≫ J.subschemeι).appLE V U h t ∉ q ∧
      ∃ v : Γ(Z, U), v ∉ q ∧ v * ((ψ ≫ J.subschemeι).appLE V U h t * c) =
        v * (ψ ≫ J.subschemeι).appLE V U h b) ∧
    (∀ b : Γ(X, V), (∃ v : Γ(Z, U), v ∉ q ∧ v * (ψ ≫ J.subschemeι).appLE V U h b = 0) →
      ∃ t : Γ(X, V), (ψ ≫ J.subschemeι).appLE V U h t ∉ q ∧ t * b ∈ J.ideal ⟨V, hV⟩) := by
  let p : PrimeSpectrum Γ(Z, U) := ⟨q, hq⟩
  have hz : hU.fromSpec p ∈ (U : Set Z) := by
    rw [← hU.range_fromSpec]
    exact Set.mem_range_self _
  have hunit : IsUnit (Z.presheaf.germ U _ hz ((ψ ≫ J.subschemeι).appLE V U h f)) :=
    (isUnit_germ_fromSpec hU p hz _).mpr hf
  have hb : hU.fromSpec p ∈ Z.basicOpen ((ψ ≫ J.subschemeι).appLE V U h f) :=
    (Z.mem_basicOpen _ _ hz).mpr hunit
  have e1 : Z.basicOpen ((ψ ≫ J.subschemeι).appLE V U h f) =
      U ⊓ Z.basicOpen ((ψ ≫ J.subschemeι).app V f) := Z.basicOpen_res _ (homOfLE h).op
  have hb2 : hU.fromSpec p ∈ Z.basicOpen ((ψ ≫ J.subschemeι).app V f) :=
    (TopologicalSpace.Opens.mem_inf.mp (e1 ▸ hb)).2
  have e2 := Scheme.preimage_basicOpen (ψ ≫ J.subschemeι) f
  have hmem : hU.fromSpec p ∈ ψ ⁻¹ᵁ (J.subschemeι ⁻¹ᵁ X.basicOpen f) := by
    have hh : hU.fromSpec p ∈ (ψ ≫ J.subschemeι) ⁻¹ᵁ X.basicOpen f := e2 ▸ hb2
    exact hh
  have hist : IsIso (ψ.stalkMap (hU.fromSpec p)) := isIso_stalkMap_of_isIso_restrict ψ _ hiso _ hmem
  have hW' : IsAffineOpen (J.subschemeι ⁻¹ᵁ V) := hV.preimage J.subschemeι
  obtain ⟨H1, H2⟩ := chart_fractions_of_isIso_stalkMap ψ hW' hU h p hz hist
  have hce : ∀ t : Γ(X, V), (ψ ≫ J.subschemeι).appLE V U h t =
      ψ.appLE (J.subschemeι ⁻¹ᵁ V) U h (J.subschemeι.app V t) := by
    intro t
    rw [Scheme.Hom.comp_appLE]
    rfl
  have hsurj := J.subschemeι_app_surjective ⟨V, hV⟩
  constructor
  · intro c
    obtain ⟨a, u, hu, v, hv, hvc⟩ := H1 c
    obtain ⟨b, rfl⟩ := hsurj a
    obtain ⟨t, rfl⟩ := hsurj u
    refine ⟨b, t, ?_, v, hv, ?_⟩
    · rw [hce]
      exact hu
    · rw [hce, hce]
      exact hvc
  · rintro b ⟨v, hv, hvb⟩
    rw [hce] at hvb
    obtain ⟨u, hu, hub⟩ := H2 (J.subschemeι.app V b) ⟨v, hv, hvb⟩
    obtain ⟨t, rfl⟩ := hsurj u
    refine ⟨t, ?_, ?_⟩
    · rw [hce]
      exact hu
    · rw [← J.ker_subschemeι_app ⟨V, hV⟩, RingHom.mem_ker, map_mul]
      exact hub

theorem stalk_over_isoLocus : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme) (V : X.Opens) (hV : IsAffineOpen V) (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ q : Ideal Γ(Z, U), q.IsPrime → f ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) → (∀ c : Γ(Z, U), ∃ b t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ ∃ v : Γ(Z, U), v ∉ q ∧ v * (algebraMap Γ(X, V) Γ(Z, U) t * c) = v * algebraMap Γ(X, V) Γ(Z, U) b) ∧ (∀ b : Γ(X, V), (∃ v : Γ(Z, U), v ∉ q ∧ v * algebraMap Γ(X, V) Γ(Z, U) b = 0) → ∃ t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ t * b ∈ J.ideal ⟨V, hV⟩) := by
  intro X J Z ψ V hV f hiso U hU h q hq hf
  exact chart_fractions_subscheme J ψ V hV f hiso U hU h q hq hf

end GlobalTheory.CompanionTheory.GE.Krull
