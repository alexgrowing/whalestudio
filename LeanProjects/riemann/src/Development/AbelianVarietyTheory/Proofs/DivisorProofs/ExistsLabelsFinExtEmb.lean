import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem exists_labels_finExt_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (hD : IsPullDeg ρ D.toPre D₁.toPre) (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left), IsFib ρ A A₁ a → ∃ (_ : Algebra (FractionRing R) (Kb R₁)) (em : Kb R →ₐ[FractionRing R] Kb R₁) (lab₁ : Labels D₁.toPre A₁), (∀ r, algebraMap (FractionRing R) (Kb R₁) (algebraMap R _ r) = algebraMap (FractionRing R₁) (Kb R₁) (algebraMap R₁ _ (ρ r))) ∧ OneTrait D₁.toPre A₁ lab₁ ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre (Kb R) k) (p₁ : QkPt D.toPre (Kb R₁) k) (p' : QkPt D₁.toPre (Kb R₁) k), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF ρ hD (Kb R₁) p₁.g p'.g → (lab₁ k p').left ≫ a = spMap em.toRingHom ≫ (lab k p).left := by
  intro R _ _ _ hR D A lab hT R₁ _ _ _ ρ hρ D₁ hD A₁ a ⟨ga, hga, gpa, la⟩
  obtain ⟨W₀, _, _, _, φ₀, G, _, _, D₀, A₀, U₀, h₀, a₀, _, em₀, hW₀, i₀, l₀, hG, ⟨g₀, hg₀, gp₀, lb₀⟩, c₀, H₀⟩ := hT
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have hGF := hL.globalFns
  have := hR.2
  have hB := D.tau_bimult
  obtain rfl := eq_fracMap hρ.2.1 hga
  obtain rfl := eq_fracMap i₀ hg₀
  letI : Algebra (FractionRing R) (Kb R₁) := ((algebraMap (FractionRing R₁) (Kb R₁)).comp (fracMap hρ.2.1)).toAlgebra
  have c' : Compat ρ (Kb R₁) := fun r => congrArg (algebraMap (FractionRing R₁) (Kb R₁)) (hga r)

  obtain ⟨W, _, _, _, io, φ, hW, iio, lio, lφ, hc⟩ :=
    GlobalTheory.LocExt.exists_cDvr_ext_of_finite R R₁ ρ hρ.2.1 hρ.2.2 W₀ hW₀ φ₀ l₀
  have iφ : Function.Injective φ := by
    letI := ρ.toAlgebra
    haveI : Module.Finite R R₁ := hρ.2.2
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := R) ?_
    change Ideal.comap ρ (RingHom.ker φ) = ⊥
    rw [RingHom.comap_ker, hc, ← RingHom.injective_iff_ker_eq_bot]
    exact iio.comp i₀
  have := hW₀.1
  have := hW₀.2.2
  have := hW.1
  have b₀ : AdmBase W₀ (maximalIdeal W₀) := ⟨inferInstance, inferInstance, inferInstance, hW₀.2.1⟩
  have b₁ : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨D₂, h₁, A₂, U₂, b, hP, gpb, lb, hb⟩ := exists_pull_fib hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    b₀ b₁ io iio (map_maximalIdeal_le io) hG U₀
  obtain ⟨hc₀, T₀⟩ := exists_comp i₀ iio h₀ h₁
  obtain ⟨h', T'⟩ : ∃ h' : IsPullDeg φ D₁.toPre D₂.toPre, Tower hD h' hc₀ := by
    revert hc₀
    rw [← hc]
    exact fun hc₀ _ => exists_cancel hρ.2.1 iφ hD hc₀
  have fr : (fracMap iφ).comp (fracMap hρ.2.1) = (fracMap iio).comp (fracMap i₀) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by
      simp only [RingHom.comp_apply, fracMap_algebraMap]
      exact congrArg _ (RingHom.congr_fun hc r))
  obtain ⟨a₁, e₁, gp₁, lb₁⟩ := exists_fib_cancel (g' := spMap (fracMap iφ))
    ((Geo.Tor.spMap_comp _ _).symm.trans ((congrArg spMap fr).trans (Geo.Tor.spMap_comp _ _))) gpa la gp₀ lb₀ gpb lb
  letI : Algebra (FractionRing R₁) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp (fracMap iφ)).toAlgebra
  letI : Algebra (FractionRing W₀) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp (fracMap iio)).toAlgebra
  letI : Algebra (FractionRing R) (Kb W) :=
    ((algebraMap (FractionRing W) (Kb W)).comp ((fracMap iφ).comp (fracMap hρ.2.1))).toAlgebra
  have cφ : Compat φ (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (fracMap_algebraMap iφ r)
  have cio : Compat io (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (fracMap_algebraMap iio r)
  have cρ : Compat ρ (Kb W) := fun r =>
    congrArg (fun t => algebraMap (FractionRing W) (Kb W) (fracMap iφ t)) (fracMap_algebraMap hρ.2.1 r)
  have cc : Compat (io.comp φ₀) (Kb W) := fun r => (cρ r).trans ((cφ _).trans
    (congrArg (fun t => algebraMap (FractionRing W) (Kb W) (algebraMap W _ t)) (RingHom.congr_fun hc r)))
  have cφ₀ : Compat φ₀ (Kb W) := fun r => (cc r).trans (cio _).symm
  obtain ⟨em⟩ := nonempty_lift (FractionRing R₁) (Kb W)
  obtain ⟨j⟩ := nonempty_lift (FractionRing W₀) (Kb W)
  let emR : Kb R₁ →ₐ[FractionRing R] Kb W := ⟨em.toRingHom, fun t => em.commutes (fracMap hρ.2.1 t)⟩
  have a₀K : algebraMap (FractionRing R) (Kb W₀) = (algebraMap (FractionRing W₀) (Kb W₀)).comp (fracMap i₀) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c₀ r).trans
      (congrArg (algebraMap (FractionRing W₀) (Kb W₀)) (fracMap_algebraMap i₀ r).symm))
  let jR : Kb W₀ →ₐ[FractionRing R] Kb W := ⟨j.toRingHom, fun t => by
    rw [a₀K]
    exact (j.commutes (fracMap i₀ t)).trans
      (congrArg (algebraMap (FractionRing W) (Kb W)) (RingHom.congr_fun fr t).symm)⟩

  obtain ⟨em'⟩ := nonempty_lift (FractionRing R) (Kb R₁)
  letI : Algebra (Kb R) (Kb W) := (emR.comp em').toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) (Kb W) :=
    IsScalarTower.of_algebraMap_eq fun x => ((emR.comp em').commutes x).symm
  let emK : Kb R →ₐ[FractionRing R] Kb R₁ := em'.comp ((jR.comp em₀).restrictNormal (Kb R))
  have hK : (emR.comp emK).toRingHom = (jR.comp em₀).toRingHom :=
    RingHom.ext fun x => (jR.comp em₀).restrictNormal_commutes (Kb R) x

  have ex : ∀ (k : ℕ) (p' : QkPt D₁.toPre (Kb R₁) k), ∃ x : TFK (R := R₁) (Kb R₁) ⟶ A₁.A, 1 ≤ k →
      ∃ (p : QkPt D.toPre (Kb R) k) (p₁ : QkPt D.toPre (Kb R₁) k), QkExt emK.toRingHom p p₁ ∧ p'.y = hD.xe.symm p₁.y ∧
        IsPullGtF ρ hD (Kb R₁) p₁.g p'.g ∧ x.left ≫ a = spMap emK.toRingHom ≫ (lab k p).left := by
    intro k p'
    by_cases hk : 1 ≤ k
    · obtain ⟨p₁, rfl⟩ := pullQk_surjective hD hGF c' hB D₁.tau_bimult p'
      obtain ⟨p, hp⟩ := exists_of_ext hB emK hk p₁
      obtain ⟨x, hx⟩ := exists_lift_pt gpa.1 emK.toRingHom emK.comp_algebraMap (lab k p)
      exact ⟨x, fun _ => ⟨p, p₁, hp, rfl, isPullGtF_pullGt hD hGF c' _, hx⟩⟩
    · exact ⟨η[A₁.A] |> fun e => toUnit _ ≫ e, fun h => absurd h hk⟩
  choose lab₁ hlab₁ using ex
  refine ⟨inferInstance, emK, lab₁, c', ?_, ?_⟩
  ·
    refine ⟨W, _, inferInstance, inferInstance, φ, (Over.pullback (specOf io)).obj G, inferInstance, inferInstance, D₂, A₂,
      U₂, h', a₁, inferInstance, em, hW, iφ, lφ, IsSemiAbelian.pullback _ G hG,
      ⟨fracMap iφ, fracMap_algebraMap iφ, gp₁, lb₁⟩, cφ, ?_⟩
    intro k hk p' p₁' p'' x₁ y₁ y₂ y₃ y₄
    obtain ⟨p, p₁, z₁, z₂, z₃, z₄⟩ := hlab₁ k p' hk
    obtain ⟨r, hr⟩ := exists_ext hB emR p₁
    have r₁ : IsPullGtF ρ hD (Kb W) r.g p₁'.g := isPullGtF_ext hD cρ em.toRingHom em.comp_algebraMap z₃ hr y₁
    have r₂ := T'.isPullGtF cc r₁ y₃
    have hq : QkExt (jR.comp em₀).toRingHom p r := by
      rw [← hK]
      exact qkExt_trans z₁ hr
    have key : spMap (emR.comp emK).toRingHom ≫ (lab k p).left = spMap (jR.comp em₀).toRingHom ≫ (lab k p).left := by
      rw [hK]
    obtain ⟨q₁, hq₁⟩ := exists_ext hB em₀ p
    obtain ⟨r', hr'⟩ := exists_ext hB jR q₁
    obtain rfl : r = r' := ext_unique hB (jR.comp em₀) hq (qkExt_trans hq₁ hr')
    let q₀ := pullQk h₀ hGF c₀ hB D₀.tau_bimult q₁
    obtain ⟨x₀, hx₀⟩ := exists_lift_pt gp₀.1 em₀.toRingHom (em₀.comp_algebraMap.trans a₀K) (lab k p)
    have t₀ := H₀ k hk p q₁ q₀ x₀ hq₁ rfl (isPullGtF_pullGt h₀ hGF c₀ _) hx₀
    obtain ⟨⟨q₀', hq₀'⟩, hx, hgal⟩ := GlobalTheory.UT.Cl.galois_holds W₀ _ b₀ D₀ A₀ G hG U₀ _ (Kb W) j k hk q₀
    obtain ⟨x₀', hx₀'⟩ := hx x₀
    have t₁ := (hgal q₀' x₀ x₀' hq₀' hx₀').1 t₀
    have s₁ : IsPullGtF φ₀ h₀ (Kb W) r.g q₀'.g :=
      isPullGtF_ext h₀ cφ₀ j.toRingHom j.comp_algebraMap (isPullGtF_pullGt h₀ hGF c₀ _) hr' hq₀'
    have s₂ := isPullGtF_pullGt h₁ hGF cio q₀'.g
    rw [← pullGt_unique hc₀ cc r₂ (T₀.isPullGtF cc s₁ s₂)] at s₂
    have ey : p''.y = h₁.xe.symm q₀'.y := by
      apply hc₀.xe.injective
      have u₁ : hc₀.xe p''.y = r.y := by
        rw [← T'.xe_eq, y₂, AddEquiv.apply_symm_apply, y₁.1, z₂, AddEquiv.apply_symm_apply, hr.1]
      rw [u₁, ← T₀.xe_eq, AddEquiv.apply_symm_apply, hq₀'.1, hr'.1]
      exact (h₀.xe.apply_symm_apply _).symm
    have ex₁ : x₁.left ≫ b = x₀'.left := by
      apply gp₀.1.hom_ext
      · rw [Category.assoc, ← e₁, ← Category.assoc, y₄, Category.assoc, z₄, hx₀', Category.assoc, hx₀, ← Category.assoc,
          ← Category.assoc, ← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp]
        exact key
      · rw [Category.assoc, gpb.1.w, ← Category.assoc, Over.w x₁, Over.w x₀']
        exact (Geo.Tor.spMap_comp _ _).symm
    refine h5.qkBaseChange W₀ W _ _ b₀ b₁ io D₀ A₀ G U₀ _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) A₂ D₂ h₁
      U₂ hP (Kb W) cio k hk q₀' x₀' p'' x₁ ey s₂ ?_ t₁
    rw [hb, ← Category.assoc, ex₁]
  ·
    intro k hk p p₁ p' e₁' e₂' e₃'
    obtain ⟨q, q₁, z₁, z₂, z₃, z₄⟩ := hlab₁ k p' hk
    obtain rfl : q₁ = p₁ := qk_ext (hD.xe.symm.injective (by rw [← z₂]; exact e₂')) (pullGt_unique' hD z₃ e₃')
    obtain rfl := qkExt_inj hB emK z₁ e₁'
    exact z₄

end GlobalTheory.Mum
