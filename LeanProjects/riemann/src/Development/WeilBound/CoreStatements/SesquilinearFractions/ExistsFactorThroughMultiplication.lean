import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenyRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsEqPowOfTorsionCompEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

theorem etale_hom_ext_complex_points {K : Type} [Field K] (σ : K →+* ℂ) {X Y : Over (Sp K)} [Etale X.hom] [IsSeparated Y.hom]
    (f g : X ⟶ Y) (h : ∀ x : Over.mk (spMap σ) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have hflat : Flat (spMap σ) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := σ.toAlgebra
    exact (inferInstance : Module.Flat K ℂ)
  have hsurj : Surjective (spMap σ) := by
    constructor
    intro y
    refine ⟨IsLocalRing.closedPoint ℂ, ?_⟩
    exact Subsingleton.elim _ _
  have : Flat (pullback.fst X.hom (spMap σ)) := inferInstance
  have : Surjective (pullback.fst X.hom (spMap σ)) := inferInstance
  have : Epi (pullback.fst X.hom (spMap σ)) := Flat.epi_of_flat_of_surjective _
  have : Etale (pullback.snd X.hom (spMap σ)) := inferInstance
  have : IsReduced (pullback X.hom (spMap σ)) := isReduced_of_smooth_of_isReduced (pullback.snd X.hom (spMap σ))
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst X.hom (spMap σ))]
  refine GlobalTheory.ComplexPoints.hom_ext_of_points (pullback.snd X.hom (spMap σ)) Y.hom ?_ ?_
  · simp only [Category.assoc, Over.w]
  · intro x hx
    have hx' : (x ≫ pullback.fst X.hom (spMap σ)) ≫ X.hom = spMap σ := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hx, Category.id_comp]
    have := congrArg (fun q => q.left) (h (Over.homMk (x ≫ pullback.fst X.hom (spMap σ)) hx'))
    simpa only [Over.comp_left, Over.homMk_left, Category.assoc] using this

theorem exists_factor_through_multiplication {K : Type} [Field K] [CharZero K] (σ : K →+* ℂ) (n : ℕ) (hn : 0 < n) (Q Q' : Out.PolAV (Sp K))
    (f₀ : Q.A ⟶ Q'.A) [IsMonHom f₀] (hpt : ∀ y : Over.mk (spMap σ) ⟶ Q.A, y ^ n = 1 → y ≫ f₀ = 1) :
    ∃ g₀ : Q.A ⟶ Q'.A, IsMonHom g₀ ∧ Out.mulA Q.A n ≫ g₀ = f₀ := by
  have hB := Q.isAb
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have hB' := Q'.isAb
  have := hB'.proper
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hnK).map (Scheme.ΓSpecIso (.of K)).inv.hom
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := GrpTangent.finiteEtale_mulN_torsion Q.A hu
  have : ConnectedSpace Q.A.left := GeometricallyConnected.connectedSpace_of_subsingleton Q.A.hom
  have hc : IsClopen (Set.range (mulN Q.A n).left) :=
    ⟨(mulN Q.A n).left.isClosedMap.isClosed_range, (mulN Q.A n).left.isOpenMap.isOpen_range⟩
  have h5 : Surjective (mulN Q.A n).left :=
    ⟨Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty _))⟩
  have hι : torsion.ι Q.A n ≫ mulN Q.A n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ η[Q.A]) (toUnit_unique _ _))
  have h6 : torsion.ι Q.A n ≫ f₀ = 1 := etale_hom_ext_complex_points σ _ _ fun x => by
    rw [← Category.assoc, MonObj.comp_one]
    refine hpt _ ?_
    rw [← GrpTangent.comp_mulN, Category.assoc, hι, MonObj.comp_one]
  have h7 : ∀ (T : Over (Sp K)) (x : T ⟶ Q.A), x ^ n = 1 → x ≫ f₀ = 1 := fun T x hx => by
    have e : x ≫ mulN Q.A n = toUnit T ≫ η[Q.A] := by rw [GrpTangent.comp_mulN, hx, Hom.one_def]
    obtain ⟨y, e'⟩ : ∃ y : T ⟶ torsion Q.A n, y ≫ torsion.ι Q.A n = x :=
      ⟨pullback.lift x (toUnit T) e, pullback.lift_fst _ _ _⟩
    rw [← e', Category.assoc, h6, MonObj.comp_one]
  have hm : Out.mulA Q.A n = mulN Q.A n := (GrpTangent.mulN_eq_pow Q.A n).symm
  have : Etale (Out.mulA Q.A n).left := hm ▸ h2
  have : IsFinite (Out.mulA Q.A n).left := hm ▸ h1
  have : Surjective (Out.mulA Q.A n).left := hm ▸ h5
  obtain ⟨g₀, hg₀⟩ := DivisibleHom.exists_factor n f₀ h7
  have : IsMonHom (Out.mulA Q.A n ≫ g₀) := hg₀ ▸ inferInstance
  exact ⟨g₀, DivisibleHom.isMonHom_of_factor n g₀, hg₀⟩

theorem spMap_comp_integers {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) :
    spMap (σ.comp (algebraMap (𝓞 K) K)) = spMap σ ≫ spMap (algebraMap (𝓞 K) K) := by
  simp only [spMap]
  rw [← Spec.map_comp]
  rfl

theorem isogeny_points_kernel_descent {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (n : ℕ) (A B : Out.PolAV (Sp (𝓞 K)))
    (f : A.A ⟶ B.A) (Q Q' : Out.PolAV (Sp K)) (φ : Q.A.left ⟶ A.A.left) (φ' : Q'.A.left ⟶ B.A.left)
    (hφ : IsGrpPullback Q.A A.A (spMap (algebraMap (𝓞 K) K)) φ) (hφ' : IsGrpPullback Q'.A B.A (spMap (algebraMap (𝓞 K) K)) φ')
    (f₀ : Q.A ⟶ Q'.A) (hf₀ : f₀.left ≫ φ' = φ ≫ f.left)
    (hker : ∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A, x ^ n = 1 → x ≫ f = 1) :
    ∀ y : Over.mk (spMap σ) ⟶ Q.A, y ^ n = 1 → y ≫ f₀ = 1 := by
  intro y hy
  obtain ⟨E, hE⟩ := LamF.exists_mulEquiv_points_of_isGrpPullback _ _ _ A.A Q.A φ hφ (Over.mk (spMap σ))
  obtain ⟨E', hE'⟩ := LamF.exists_mulEquiv_points_of_isGrpPullback _ _ _ B.A Q'.A φ' hφ' (Over.mk (spMap σ))
  let e : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ Over.mk ((Over.mk (spMap σ)).hom ≫ spMap (algebraMap (𝓞 K) K)) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans (spMap_comp_integers σ).symm)
  let e' : Over.mk ((Over.mk (spMap σ)).hom ≫ spMap (algebraMap (𝓞 K) K)) ⟶ Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans (spMap_comp_integers σ))
  have hee : e' ≫ e = 𝟙 _ := Over.OverMorphism.ext (Category.id_comp _)
  have hz : (e ≫ E y) ^ n = 1 := by
    rw [← MonObj.comp_pow, ← map_pow, hy, map_one, MonObj.comp_one]
  have h₂ : E y ≫ f = 1 := by
    have h₁ := congrArg (fun q => e' ≫ q) (hker _ hz)
    rw [← Category.assoc, ← Category.assoc, hee, Category.id_comp, MonObj.comp_one] at h₁
    exact h₁
  have h₃ : E' (y ≫ f₀) = E y ≫ f := by
    apply Over.OverMorphism.ext
    rw [hE', Over.comp_left, Over.comp_left, hE, Category.assoc, Category.assoc, hf₀]
  exact E'.injective (by rw [h₃, h₂, map_one])

theorem exists_nth_root_homomorphism : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (n : ℕ) (A B : Out.PolAV (Sp (𝓞 K))) (f : A.A ⟶ B.A), IsMonHom f → 0 < n → (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A, x ^ n = 1 → x ≫ f = 1) → ∃ f' : A.A ⟶ B.A, IsMonHom f' ∧ f' ^ n = f := by
  intro K _ _ σ n A B f hf hn hker
  have hE := GlobalTheory.existsUnique_hom_extension_semiAbelian
  have hL : Out.Laws := GlobalTheory.allSixLaws.1
  obtain ⟨Q, φ, -, hφ⟩ := LamF.exists_isGrpPullback_polAV hL.polBaseChange (spMap (algebraMap (𝓞 K) K)) A
  obtain ⟨Q', φ', -, hφ'⟩ := LamF.exists_isGrpPullback_polAV hL.polBaseChange (spMap (algebraMap (𝓞 K) K)) B
  obtain ⟨⟨f₀, hf₀, -⟩, hmon⟩ := LamF.existsUnique_hom_of_isGrpPullback _ _ _ A.A B.A Q.A Q'.A φ φ' hφ hφ' f
  have hm₀ : IsMonHom f₀ := hmon f₀ hf₀ hf
  obtain ⟨g₀, hg₀, e₀⟩ := exists_factor_through_multiplication σ n hn Q Q' f₀ (isogeny_points_kernel_descent σ n A B f Q Q' φ φ' hφ hφ' f₀ hf₀ hker)
  obtain ⟨g, hg, eg, -⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hE (𝓞 K) K A.A B.A Q.A Q'.A φ φ'
    A.isAb B.isAb hφ hφ' g₀ hg₀
  obtain ⟨F, -, -, hF⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hE (𝓞 K) K A.A B.A Q.A Q'.A φ φ'
    A.isAb B.isAb hφ hφ' f₀ hm₀
  refine ⟨g, hg, (hF _ ?_).trans (hF f hf₀).symm⟩
  have e₁ : g ^ n = (𝟙 A.A ^ n) ≫ g := by rw [MonObj.pow_comp, Category.id_comp]
  have e₂ : f₀ = (𝟙 Q.A ^ n) ≫ g₀ := e₀.symm
  rw [e₁, e₂, Over.comp_left, Over.comp_left, Category.assoc, eg, ← Category.assoc,
    LamF.IsGrpPullback.id_pow_left hφ n, Category.assoc]

end PositivityTheory.Xgf
