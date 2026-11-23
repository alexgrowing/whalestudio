import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKummerEqOfPicardTorsionFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayOfIsUnitModStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonPicEtaleLocalizationUnitsModuloStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyClassDiesOnLocalizationAwayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationDescendAwayStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.KummerLoc

noncomputable abbrev gU (R : Type) [CommRing R] : Rˣ →* (Γ(Spec (CommRingCat.of R), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom

theorem pull_spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T)
    {q : ℕ} {n i : ℤ} (x : Ht q (sp R) n i) :
    pull _ (spMap (ψ.comp φ)) _ _ x = pull _ (spMap ψ) _ _ (pull _ (spMap φ) _ _ x) := by
  rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp]; rfl

theorem pull_kum_gU (hnat : DivisorNaturality) (q : ℕ) [NeZero q] {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hq : IsUnit (q : R)) (v : Rˣ) :
    pull _ (spMap φ) _ _ (kum q (gU R v)) = kum q (gU S (Units.map φ.toMonoidHom v)) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of R), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  rw [(hnat q).2.2.2 _ _ hq']
  congr 1
  ext
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have h2 := congrArg (fun g => g.hom (v : R)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  simpa using h2.symm

set_option maxHeartbeats 1000000 in

theorem exists_kummer_on_finer_nbhd : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c := by
  intro q _ k B _ _ _ _ _ _ hq f _ A' _ _ hA' w
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  have hqA : IsUnit (q : A') := by simpa using hqB.map (algebraMap B A')
  haveI : Algebra.Etale B A' := hA'.1
  set SB : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
    (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hSB
  set M : Submonoid A' := Algebra.algebraMapSubmonoid A' SB with hM
  have hfM : (algebraMap B A' f) ∈ M := ⟨f, Submonoid.mem_sup_right (Submonoid.mem_powers f), rfl⟩
  let φf : Localization.Away (algebraMap B A' f) →+* Localization M :=
    IsLocalization.Away.lift (algebraMap B A' f) (IsLocalization.map_units (Localization M) (⟨(algebraMap B A' f), hfM⟩ : M))
  have hφf : φf.comp (algebraMap A' _) = algebraMap A' (Localization M) := IsLocalization.Away.lift_comp _ _
  haveI := GlobalTheory.T.subsingleton_pic_etale_localization_unitsModulo B f A'
  have hqL : IsUnit (q : Localization M) := by simpa using hqA.map (algebraMap A' (Localization M))
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_kummer_eq_of_picard_torsionFree q (Localization M) hqL (fun c _ => Subsingleton.elim _ _) (pull _ (spMap φf) _ _ w)
  let u₀ : (Localization M)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (Localization M))).hom.hom.toMonoidHom u
  have hu₀ : gU _ u₀ = u := by ext; simp [u₀]
  obtain ⟨m₀, hm₀, v, hv⟩ := GlobalTheory.T.exists_away_unit_map_eq A' M u₀
  have hm₁ : (algebraMap B A' f) * m₀ ∈ M := M.mul_mem hfM hm₀
  have hunit1 : IsUnit (algebraMap A' (Localization.Away ((algebraMap B A' f) * m₀)) ((algebraMap B A' f) * m₀)) := IsLocalization.Away.algebraMap_isUnit _
  let α : Localization.Away (algebraMap B A' f) →+* Localization.Away ((algebraMap B A' f) * m₀) :=
    IsLocalization.Away.lift (algebraMap B A' f) (isUnit_of_mul_isUnit_left (by simpa using hunit1))
  let β : Localization.Away m₀ →+* Localization.Away ((algebraMap B A' f) * m₀) :=
    IsLocalization.Away.lift m₀ (isUnit_of_mul_isUnit_right (by simpa using hunit1))
  let φ₁ : Localization.Away ((algebraMap B A' f) * m₀) →+* Localization M :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀) (IsLocalization.map_units (Localization M) (⟨_, hm₁⟩ : M))
  have hα : α.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hβ : β.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hφ₁ : φ₁.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hqm₀ : IsUnit (q : Localization.Away m₀) := by simpa using hqA.map (algebraMap A' _)
  have hqm₁ : IsUnit (q : Localization.Away ((algebraMap B A' f) * m₀)) := by simpa using hqA.map (algebraMap A' _)
  have hnat := GlobalTheory.T.cup_chern_kummer_pullback_naturality
  set y := pull _ (spMap α) _ _ w - kum q (gU _ (Units.map β.toMonoidHom v)) with hy
  have hy0 : pull _ (spMap φ₁) _ _ y = 0 := by
    rw [hy, map_sub, ← pull_spMap_comp, pull_kum_gU hnat q _ hqm₁]
    have e1 : φ₁.comp α = φf := IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f)) (by rw [RingHom.comp_assoc, hα, hφ₁, hφf])
    have e2 : Units.map φ₁.toMonoidHom (Units.map β.toMonoidHom v) = u₀ := by
      rw [← hv (φ₁.comp β) (by rw [RingHom.comp_assoc, hβ, hφ₁])]; ext; rfl
    rw [e1, e2, hu₀, hu, sub_self]
  obtain ⟨m', hm', hψ⟩ := GlobalTheory.T.tateTwistCohomology_class_dies_on_localizationAway GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q A' M 1 1 hqA ((algebraMap B A' f) * m₀) hm₁ y φ₁ hφ₁ hy0
  obtain ⟨b, hb, hbm⟩ := M.mul_mem hm₁ hm'
  obtain ⟨s, hs, t, ht, rfl⟩ := Submonoid.mem_sup.1 hb
  obtain ⟨n, rfl⟩ := ht
  have hs' : IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) := hs
  refine ⟨Localization.Away (algebraMap B A' s), inferInstance, inferInstance, inferInstance, inferInstance,
    GlobalTheory.T.isExcisionNbhd_away_of_isUnit_mod' B A' f s hA' hs', ?_⟩
  set A₂ := Localization.Away (algebraMap B A' s)
  set g : A' →+* Localization.Away (algebraMap B A₂ f) := (algebraMap A₂ _).comp (algebraMap A' A₂) with hg
  have hgu : IsUnit (g ((algebraMap B A' f) * m₀ * m')) := by
    rw [← hbm]
    simp only [map_mul, map_pow]
    refine IsUnit.mul ?_ (IsUnit.pow _ ?_)
    · exact (IsLocalization.Away.algebraMap_isUnit (algebraMap B A' s)).map (algebraMap A₂ _)
    · have : g (algebraMap B A' f) = algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f) := by
        rw [hg, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A' A₂ f]
      rw [this]
      exact IsLocalization.Away.algebraMap_isUnit _
  let χ : Localization.Away ((algebraMap B A' f) * m₀ * m') →+* Localization.Away (algebraMap B A₂ f) :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀ * m') hgu
  have hχ : χ.comp (algebraMap A' _) = g := IsLocalization.Away.lift_comp _ _
  have hunit2 : IsUnit (algebraMap A' (Localization.Away ((algebraMap B A' f) * m₀ * m')) ((algebraMap B A' f) * m₀ * m')) :=
    IsLocalization.Away.algebraMap_isUnit _
  let ψ : Localization.Away ((algebraMap B A' f) * m₀) →+* Localization.Away ((algebraMap B A' f) * m₀ * m') :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀) (isUnit_of_mul_isUnit_left (by simpa using hunit2))
  have hψc : ψ.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hqm₂ : IsUnit (q : Localization.Away ((algebraMap B A' f) * m₀ * m')) := by simpa using hqA.map (algebraMap A' _)
  clear_value χ ψ β α
  refine ⟨gU _ (Units.map (χ.comp (ψ.comp β)).toMonoidHom v), fun φ hφ => ?_⟩
  have e3 : φ = χ.comp (ψ.comp α) := IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f))
    (by rw [hφ, RingHom.comp_assoc, RingHom.comp_assoc, hα, hψc, hχ])
  have hw : pull _ (spMap α) _ _ w = y + kum q (gU _ (Units.map β.toMonoidHom v)) := by
    rw [hy, sub_add_cancel]
  subst e3
  rw [pull_spMap_comp, pull_spMap_comp, hw]
  have hψy := hψ ψ hψc
  rw [map_add (pull _ (spMap ψ) _ _)]
  rw [hψy, zero_add]
  rw [pull_kum_gU hnat q ψ hqm₁]
  have key : pull _ (spMap χ) _ _ (kum q (gU _ (Units.map ψ.toMonoidHom (Units.map β.toMonoidHom v)))) =
      kum q (gU _ (Units.map χ.toMonoidHom (Units.map ψ.toMonoidHom (Units.map β.toMonoidHom v)))) :=
    pull_kum_gU hnat q χ hqm₂ _
  refine key.trans ?_
  exact congrArg (kum q) (congrArg (gU _) (Units.ext rfl))

end GlobalTheory.EtC.KummerLoc

end
