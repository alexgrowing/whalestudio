import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupCyclotomicAwayProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIdlAlong
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoNearNormalPointOfFiniteBirational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCartierOnNormalizedBlowup
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoMorphismRestrictFiniteOfIsNormalDenseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PoincCov

theorem isProper_of_blowup {n : ℕ} {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (hz : IsProjOver z)
    {J : Z.IdealSheafData} {S₀ : Scheme.{0}} {π₀ : S₀ ⟶ Z} (hB : FinalTheorems.Blowup π₀ J) : IsProper π₀ := by
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨X', b, hb, hbs, -⟩ := GlobalTheory.ProjBlowup.exists_blowup z hz J
  obtain ⟨f, hf, -⟩ := hb.2 S₀ π₀ hB.1
  obtain ⟨f', hf', -⟩ := hB.2 X' b hb.1
  have e1 : f ≫ f' = 𝟙 S₀ := (hB.2 S₀ π₀ hB.1).unique (by simp [hf', hf]) (by simp)
  have e2 : f' ≫ f = 𝟙 X' := (hb.2 X' b hb.1).unique (by simp [hf, hf']) (by simp)
  haveI : IsIso f := ⟨f', e1, e2⟩
  haveI : IsSeparated z := by
    obtain ⟨m, e, he, rfl⟩ := hz
    have := isProper_str (cycAway n) m
    infer_instance
  haveI : IsProper (b ≫ z) := by
    obtain ⟨m, e, he, he'⟩ := hbs
    have := isProper_str (cycAway n) m
    rw [← he']
    infer_instance
  haveI : IsProper b := IsProper.of_comp b z
  rw [← hf]
  infer_instance

theorem isProper_of_isNormBl {n : ℕ} {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (hz : IsProjOver z)
    {J : Z.IdealSheafData} {S : Scheme.{0}} {π : S ⟶ Z} (h : IsNormBl π J) : IsProper π := by
  obtain ⟨-, S₀, π₀, ν, U, hB, rfl, hfin, -, -, -⟩ := h
  haveI := isProper_of_blowup z hz hB
  infer_instance

theorem isIso_restrict_of_isNormBl {n : ℕ} {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (hz : IsProjOver z)
    (hZ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) {J : Z.IdealSheafData} {S : Scheme.{0}} {π : S ⟶ Z} (h : IsNormBl π J)
    (V : Z.Opens) (hV : ∀ x ∈ V, x ∉ J.support) : IsIso (π ∣_ V) := by
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨hS, S₀, π₀, ν, U, hB, rfl, hfin, hUd, hνd, hνU⟩ := h
  haveI hπ₀V : IsIso (π₀ ∣_ V) := GlobalTheory.Principalise.isIso_restrict_of_blowup hB V hV
  haveI := isProper_of_blowup z hz hB
  haveI : LocallyOfFiniteType z := by
    obtain ⟨m, e, he, rfl⟩ := hz
    have := isProper_str (cycAway n) m
    infer_instance
  haveI : IsLocallyNoetherian S₀ := LocallyOfFiniteType.isLocallyNoetherian (π₀ ≫ z)
  haveI : GlobalTheory.IsNormalScheme Z := .of_pred hZ
  haveI hoi : IsOpenImmersion ((π₀ ⁻¹ᵁ V).ι ≫ π₀) := by
    rw [← morphismRestrict_ι]; infer_instance
  haveI : GlobalTheory.IsNormalScheme (π₀ ⁻¹ᵁ V).toScheme := .of_isOpenImmersion ((π₀ ⁻¹ᵁ V).ι ≫ π₀)
  haveI : IsIso (ν ∣_ (π₀ ⁻¹ᵁ V)) :=
    GlobalTheory.T.isIso_morphismRestrict_finite_of_isNormal_dense ν U (π₀ ⁻¹ᵁ V) ((GlobalTheory.isNormalScheme_iff_pred S).mp hS) (GlobalTheory.IsNormalScheme.pred _) hUd hνd hνU
  rw [morphismRestrict_comp]
  exact IsIso.comp_isIso' (by assumption) hπ₀V

end GlobalTheory.PoincCov

namespace GlobalTheory.PoincCov

theorem exists_normalisation_cover : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, ∀ (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z), (∀ x ∈ J.support, x ∉ Set.range i) → IsNormBl π J → ∀ X₁ : Setup F W i, ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ X₁.M.Z) (ν : S₁ ⟶ S), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsDominant p₁ ∧ IsFinite ν ∧ ν ≫ π = p₁ ≫ X₁.π ∧ IsIso (p₁ ∣_ (X₁.π ⁻¹ᵁ i.opensRange)) ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ X₁.π)) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ S) (b : Sp R ⟶ X₁.M.Z), a ≫ π = b ≫ X₁.π → Set.range (jK R ≫ b ≫ X₁.π) ⊆ Set.range i → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ ν = a ∧ ξ₁ ≫ p₁ = b := by
  intro g _ n _ _ F Z z i _ hz hZ hiz hdense W J S π hJi hNB X₁
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  haveI : Algebra.FiniteType ℤ (CommRingCat.of (cycAway n)) := ‹Algebra.FiniteType ℤ (cycAway n)›
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI : LocallyOfFiniteType z := by
    obtain ⟨m, e, he, rfl⟩ := hz
    have := isProper_str (cycAway n) m
    infer_instance
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
  haveI hπP : IsProper π := isProper_of_isNormBl z hz hNB
  let Vi : Z.Opens := i.opensRange
  haveI hπV : IsIso (π ∣_ Vi) := isIso_restrict_of_isNormBl z hz hZ hNB Vi (fun x hx hJ => hJi x hJ hx)
  have monoV : ∀ {T : Scheme.{0}} (u v : T ⟶ S), u ≫ π = v ≫ π → Set.range (u ≫ π) ⊆ (Vi : Set Z) → u = v := by
    intro T u v huv hr
    have hu : Set.range u ⊆ ((π ⁻¹ᵁ Vi : S.Opens) : Set S) := by
      rintro _ ⟨w, rfl⟩
      exact hr ⟨w, rfl⟩
    have hv : Set.range v ⊆ ((π ⁻¹ᵁ Vi : S.Opens) : Set S) := by
      rintro _ ⟨w, rfl⟩
      have := hr ⟨w, rfl⟩
      rw [huv] at this
      exact this
    have hm : Mono ((π ⁻¹ᵁ Vi).ι ≫ π) := by
      rw [← morphismRestrict_ι]; infer_instance
    rw [← Scheme.Opens.range_ι] at hu hv
    rw [← IsOpenImmersion.lift_fac _ u hu, ← IsOpenImmersion.lift_fac _ v hv]
    congr 1
    rw [← cancel_mono ((π ⁻¹ᵁ Vi).ι ≫ π)]
    simp only [← Category.assoc, IsOpenImmersion.lift_fac]
    exact huv
  let U : X₁.M.Z.Opens := X₁.π ⁻¹ᵁ Vi
  have hUne : (U : Set X₁.M.Z).Nonempty := by
    refine ⟨X₁.M.pt (show Sp X₁.Ω₁ from IsLocalRing.closedPoint X₁.Ω₁), ?_⟩
    show X₁.π (X₁.M.pt _) ∈ Vi
    rw [← Scheme.Hom.comp_apply, X₁.comp]
    exact ⟨_, rfl⟩
  haveI : Nonempty U := hUne.to_subtype
  let c : (U : Scheme.{0}) ⟶ S := X₁.π ∣_ Vi ≫ inv (π ∣_ Vi) ≫ (π ⁻¹ᵁ Vi).ι
  have hc : c ≫ π = U.ι ≫ X₁.π := by
    simp only [c, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, morphismRestrict_ι]
  let j : (U : Scheme.{0}) ⟶ pullback π X₁.π := pullback.lift c U.ι hc
  haveI := X₁.fin
  haveI : LocallyOfFiniteType (X₁.π ≫ z) := inferInstance
  haveI : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian (X₁.π ≫ z)
  haveI : IsLocallyNoetherian (pullback π X₁.π) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst π X₁.π ≫ π ≫ z)
  have hjs : j ≫ pullback.snd π X₁.π = U.ι := pullback.lift_snd _ _ _
  haveI : QuasiCompact (j ≫ pullback.snd π X₁.π) := by rw [hjs]; infer_instance
  haveI : QuasiCompact j := QuasiCompact.of_comp j (pullback.snd π X₁.π)
  haveI : QuasiSeparated (j ≫ pullback.snd π X₁.π) := by rw [hjs]; infer_instance
  haveI : QuasiSeparated j := QuasiSeparated.of_comp j (pullback.snd π X₁.π)
  haveI : LocallyOfFiniteType (j ≫ pullback.snd π X₁.π) := by rw [hjs]; infer_instance
  haveI : LocallyOfFiniteType j := locallyOfFiniteType_of_comp j (pullback.snd π X₁.π)
  haveI hfin : IsFinite j.fromNormalization :=
    GlobalTheory.NormBlowupInt.isFinite_fromNormalization_int_of_isReduced (o := CommRingCat.of (cycAway n)) j
      (pullback.fst π X₁.π ≫ π ≫ z) fun x _ => (LocallyOfFiniteType.stalkMap j x).residueFieldMap
  haveI : GlobalTheory.IsNormalScheme X₁.M.Z := X₁.normal
  haveI : GlobalTheory.IsNormalScheme (U : Scheme.{0}) := .of_isOpenImmersion U.ι
  let p₁ : j.normalization ⟶ X₁.M.Z := j.fromNormalization ≫ pullback.snd π X₁.π
  let ν : j.normalization ⟶ S := j.fromNormalization ≫ pullback.fst π X₁.π
  have hp₁ : j.toNormalization ≫ p₁ = U.ι := by
    show j.toNormalization ≫ j.fromNormalization ≫ pullback.snd π X₁.π = U.ι
    rw [Scheme.Hom.toNormalization_fromNormalization_assoc, pullback.lift_snd]
  have hcomm : ν ≫ π = p₁ ≫ X₁.π := by simp [ν, p₁, pullback.condition]
  refine ⟨j.normalization, inferInstance, p₁, ν, GlobalTheory.IsNormalScheme.pred _, ?_, ?_, ?_, hcomm, ?_, ?_, ?_⟩
  · show IsProper (j.fromNormalization ≫ pullback.snd π X₁.π)
    infer_instance
  · constructor
    have hUd : Dense (U : Set X₁.M.Z) := U.isOpen.dense hUne
    refine hUd.mono ?_
    intro x hx
    refine ⟨j.toNormalization ⟨x, hx⟩, ?_⟩
    rw [show p₁ (j.toNormalization ⟨x, hx⟩) = (j.toNormalization ≫ p₁) ⟨x, hx⟩ from rfl, hp₁]
    rfl
  · show IsFinite (j.fromNormalization ≫ pullback.fst π X₁.π)
    infer_instance
  · let O : (pullback π X₁.π).Opens := pullback.snd π X₁.π ⁻¹ᵁ U
    have hjO : Set.range j ⊆ Set.range O.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      show pullback.snd π X₁.π (j x) ∈ U
      rw [← Scheme.Hom.comp_apply, hjs]
      exact x.2
    let f0 : (U : Scheme.{0}) ⟶ O := IsOpenImmersion.lift O.ι j hjO
    have hf0 : f0 ≫ O.ι = j := IsOpenImmersion.lift_fac _ _ _
    let s' := pullback.snd π X₁.π ∣_ U
    have hs' : s' ≫ U.ι = O.ι ≫ pullback.snd π X₁.π := morphismRestrict_ι _ _
    have e1 : f0 ≫ s' = 𝟙 _ := by
      rw [← cancel_mono U.ι, Category.assoc, hs', ← Category.assoc, hf0, hjs, Category.id_comp]
    have e2 : s' ≫ f0 = 𝟙 _ := by
      rw [← cancel_mono O.ι, Category.assoc, hf0, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst]
        apply monoV
        · rw [Category.assoc, hc, ← Category.assoc, hs', Category.assoc, Category.assoc, pullback.condition]
        · rw [Category.assoc, hc, ← Category.assoc]
          rintro _ ⟨w, rfl⟩
          rw [Scheme.Hom.comp_apply]
          exact (s' w).2
      · rw [Category.assoc, pullback.lift_snd, hs']
    haveI : IsIso s' := ⟨f0, e2, e1⟩
    haveI : IsIso f0 := ⟨s', e1, e2⟩
    have H := GlobalTheory.isPullback_toNormalization_of_mono f0 O.ι j hf0.symm
    have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict j.fromNormalization O) H.flip
    haveI : IsIso (j.fromNormalization ∣_ O) := by rw [← e]; infer_instance
    show IsIso ((j.fromNormalization ≫ pullback.snd π X₁.π) ∣_ U)
    rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' (by assumption) (by assumption)
  · obtain ⟨-, S₀, π₀, ν₀, U₀, hB, hνπ, -, -, -, -⟩ := hNB
    obtain ⟨D, hD⟩ := GlobalTheory.EffCartierData.exists_idealSheaf_eq hB.1
    have hpe : p₁ ≫ X₁.π = (ν ≫ ν₀) ≫ π₀ := by rw [← hcomm, Category.assoc ν ν₀ π₀, hνπ]
    have hK : D.KeepsRegular (ν ≫ ν₀) := by
      refine D.keepsRegular_of_dense _ (fun y => inferInstance) ((j.toNormalization.denseRange).mono ?_)
      rintro _ ⟨x, rfl⟩
      show (ν ≫ ν₀) (j.toNormalization x) ∉ D.idealSheaf.support
      rw [hD, GlobalTheory.ProjBlowup.mem_support_comap]
      intro h
      apply hJi _ h
      have : j.toNormalization ≫ (ν ≫ ν₀) ≫ π₀ = U.ι ≫ X₁.π := by rw [← hpe, ← Category.assoc, hp₁]
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, this]
      exact x.2
    have e : J.comap (p₁ ≫ X₁.π) = (D.pull (ν ≫ ν₀) hK).idealSheaf := by
      rw [GlobalTheory.EffCartierData.idealSheaf_pull, hD, hpe, Scheme.IdealSheafData.comap_comp]
    rw [e]
    exact GlobalTheory.EffCartierData.effCartier_idealSheaf _
  · intro R _ _ _ _ a b hab hgen
    let d : Sp R ⟶ pullback π X₁.π := pullback.lift a b hab
    have hr : Set.range (jK R ≫ b) ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      show X₁.π ((jK R ≫ b) w) ∈ Vi
      rw [← Scheme.Hom.comp_apply, Category.assoc]
      exact hgen ⟨w, rfl⟩
    let y := IsOpenImmersion.lift U.ι (jK R ≫ b) hr
    have hy : y ≫ U.ι = jK R ≫ b := IsOpenImmersion.lift_fac _ _ _
    have hyj : y ≫ j = jK R ≫ d := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst]
        apply monoV
        · rw [Category.assoc, hc, ← Category.assoc, hy, Category.assoc, Category.assoc, hab]
        · rw [Category.assoc, hc, ← Category.assoc, hy, Category.assoc]
          exact hgen
      · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, hy]
    obtain ⟨ξ, ⟨-, hξ⟩, -⟩ := GlobalTheory.existsUnique_lift_spec_of_isLocalization (R := R) (R' := FractionRing R)
      (nonZeroDivisors R) le_rfl j.fromNormalization (y ≫ j.toNormalization) d
      (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hyj])
    refine ⟨ξ, ?_, ?_⟩
    · show ξ ≫ j.fromNormalization ≫ pullback.fst π X₁.π = a
      rw [← Category.assoc, hξ, pullback.lift_fst]
    · show ξ ≫ j.fromNormalization ≫ pullback.snd π X₁.π = b
      rw [← Category.assoc, hξ, pullback.lift_snd]

end GlobalTheory.PoincCov
