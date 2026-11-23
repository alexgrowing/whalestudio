import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricSqrtPrincipalSiegelFiniteEtaleStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsTwoTorsionTranslateSameLambdaBundleStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyComplexPointEqOfSamePeriodMatrixStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsLocalPeriodMatrix
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSeparatingPairs
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SameCompOfIsHolTo
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNhdsSubsetImage
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SqOfCalculus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegelNearby
open GlobalTheory.ZM.SiegPull GlobalTheory.RigidTranslate

theorem toUnit_left {S : Scheme.{0}} (T : Over S) : (toUnit T).left = T.hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit T))

theorem exists_polPB (hB : Out.PolBaseChangeSt) {S S' : Scheme.{0}} (P : Out.PolAV S) (f : S' ⟶ S) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), PolPB P' P f φ := by
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := hB _ _ f P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, hg, LBIso.symm ⟨t, ht⟩⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

theorem transl_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (t : 𝟙_ (Over S) ⟶ G) (t' : 𝟙_ (Over S') ⟶ G')
    (e : t'.left ≫ φ = f ≫ t.left) :
    ((toUnit G' ≫ t') * 𝟙 G').left ≫ φ = φ ≫ ((toUnit G ≫ t) * 𝟙 G).left := by
  have h₁ := h.2 G' (toUnit G' ≫ t') (𝟙 G') (toUnit _ ≫ t) (pushPt h.1.w (𝟙 G')) (by
    rw [Over.comp_left, Over.comp_left, toUnit_left, toUnit_left, Category.assoc, e]
    exact Category.assoc _ _ _) rfl
  have h₂ : pushPt h.1.w (𝟙 G') ≫ ((toUnit G ≫ t) * 𝟙 G) = (toUnit _ ≫ t) * pushPt h.1.w (𝟙 G') := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  rw [← h₁, ← h₂, Over.comp_left]
  exact congrArg (· ≫ _) (Category.id_comp φ)

theorem exists_section_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (t : 𝟙_ (Over S) ⟶ G) (n : ℕ) (ht : t ^ n = 1) :
    ∃ t' : 𝟙_ (Over S') ⟶ G', t' ^ n = 1 ∧ t'.left ≫ φ = f ≫ t.left := by
  have w : (f ≫ t.left) ≫ G.hom = 𝟙 S' ≫ f := by
    rw [Category.assoc, Over.w t]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  let t' : 𝟙_ (Over S') ⟶ G' := Over.homMk (h.1.lift (f ≫ t.left) (𝟙 S') w) (h.1.lift_snd _ _ _)
  have e : t'.left ≫ φ = f ≫ t.left := h.1.lift_fst _ _ _
  have e₁ : pushHom h _ t' = toUnit _ ≫ t := Over.OverMorphism.ext (by
    rw [Over.comp_left, toUnit_left]
    exact e.trans (congrArg (· ≫ t.left) (Category.id_comp f).symm))
  have e₂ : pushHom h _ (t' ^ n) = pushHom h _ 1 := by
    rw [map_pow, e₁, map_one, ← MonObj.comp_pow, ht, MonObj.comp_one]
  refine ⟨t', Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e₂) ?_), e⟩
  exact (Over.w _).trans (Over.w _).symm

variable {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}

theorem exists_sqOf_polPB (hL : Out.Laws) {R : Type} [CommRing R] {c : SiegPre h k ζ s} {f : Sp R ⟶ S}
    {Q : Out.PolAV (Sp R)} {φ : Q.A.left ⟶ c.A.left} (hQ : SqOf Q c f φ) (hT : TorsConst Q.A 2) (p : Sp ℂ ⟶ Sp R)
    {P₀ : Out.PolAV (Sp ℂ)} {φ₀ : P₀.A.left ⟶ c.A.left} (hP : SqOf P₀ c (p ≫ f) φ₀) :
    ∃ (Q' : Out.PolAV (Sp R)) (φ' : Q'.A.left ⟶ c.A.left) (ψ : P₀.A.left ⟶ Q'.A.left),
      SqOf Q' c f φ' ∧ PolPB P₀ Q' p ψ ∧ ψ ≫ φ' = φ₀ := by
  obtain ⟨Q₀, ψ₀, hpb⟩ := exists_polPB hL.polBaseChange Q p
  have h₀ := (sqOf_calculus h k o ζ S _ _ s c f).1 p Q Q₀ φ ψ₀ hQ hpb
  obtain ⟨e, he, heφ, hlam⟩ := (sqOf_calculus h k o ζ S _ S s c (p ≫ f)).2.1 Q₀ P₀ _ _ h₀ hP
  obtain ⟨t₀, ht₀, i₀⟩ := GlobalTheory.T.exists_twoTorsion_translate_same_lambdaBundle hL ℂ Q₀ P₀ e he hlam
  obtain ⟨t, ht, hy⟩ := hT ℂ ((𝟙_ (Over (Sp ℂ))).hom ≫ p) (pushHom hpb.1 _ t₀) (by rw [← map_pow, ht₀, map_one])
  have et : t₀.left ≫ ψ₀ = p ≫ t.left := by
    refine (congrArg (fun q => q.left) hy).trans ?_
    rw [Over.comp_left, toUnit_left]
    exact congrArg (· ≫ t.left) (Category.id_comp p)
  obtain ⟨Q', e', he', hg', hlam', i'⟩ := exists_rigid_translate hL R Q t ht
  have ee : e'.inv.left ≫ e'.hom.left = 𝟙 _ := by rw [← Over.comp_left, e'.inv_hom_id, Over.id_left]
  have : IsMonHom e'.symm.hom := inferInstanceAs (IsMonHom e'.inv)
  have gp : IsGrpPullback P₀.A Q'.A p (e.hom.left ≫ ψ₀ ≫ e'.inv.left) :=
    ((isGrpPullback_of_iso e).comp (hpb.1.comp (isGrpPullback_of_iso e'.symm))).congr
      ((Category.id_comp _).trans (Category.comp_id _)) rfl
  have hQ' := (sqOf_calculus h k o ζ S _ S s c f).2.2 Q Q' φ e' he' hg' hlam' hQ
  refine ⟨Q', e'.hom.left ≫ φ, e.hom.left ≫ ψ₀ ≫ e'.inv.left, hQ', ⟨gp, hP.2.1.trans hQ'.2.1.symm, ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart Q.isLB ((p ≫ t.left) (default : PrimeSpectrum ℂ))
    have j₁ := lbIso_diff_pull Q.isLB (e'.hom ≫ ((toUnit Q.A ≫ t) * 𝟙 Q.A)).left (toUnit Q'.A ≫ t).left
      (e.hom.left ≫ ψ₀ ≫ e'.inv.left) i fun z => by
        have : (e.hom.left ≫ ψ₀ ≫ e'.inv.left) ≫ (toUnit Q'.A ≫ t).left = P₀.A.hom ≫ p ≫ t.left := by
          rw [Over.comp_left, toUnit_left, ← Category.assoc, gp.1.w, Category.assoc]
        rw [this, Scheme.Hom.comp_apply, Subsingleton.elim (α := PrimeSpectrum ℂ) (P₀.A.hom z) default]
        exact hi
    have E : (e.hom.left ≫ ψ₀ ≫ e'.inv.left) ≫ (e'.hom ≫ ((toUnit Q.A ≫ t) * 𝟙 Q.A)).left =
        (e.hom ≫ ((toUnit Q₀.A ≫ t₀) * 𝟙 Q₀.A)).left ≫ ψ₀ := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, Category.assoc,
        transl_comm hpb.1 t t₀ et, ← Category.assoc e'.inv.left, ee, Category.id_comp]
    rw [E] at j₁
    have j₂ := LBIso.chartPull (Geo.Tor.chartPullPull _ _ (e.hom.left ≫ ψ₀ ≫ e'.inv.left) rfl)
      (Geo.Tor.chartPullPull _ _ _ rfl) i'
    have j₃ := LBIso.trans P₀.isLB (pull_isLB Q₀.isLB _) (pull_isLB Q.isLB _) i₀ (lbIso_pull_comp hpb.2.2 _)
    exact LBIso.trans P₀.isLB (pull_isLB Q.isLB _) (pull_isLB Q'.isLB _) j₃
      (LBIso.trans (pull_isLB Q'.isLB _) (pull_isLB (DVR.linComb_isLB _ Q.isLB _ _) _) (pull_isLB Q.isLB _) j₂ j₁).symm
  · rw [Category.assoc, Category.assoc, ← Category.assoc e'.inv.left, ee, Category.id_comp, heφ]

theorem exists_point_lift {F : Type} [Field F] [IsAlgClosed F] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f]
    [Surjective f] (x : Sp F ⟶ Y) : ∃ b : Sp F ⟶ X, b ≫ f = x := by
  have : CompactSpace ↥(pullback f x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f x)
  obtain ⟨p, -⟩ := (pullback.snd f x).surjective (default : PrimeSpectrum F)
  obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback f x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd f x) q hq ≫ pullback.fst f x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

theorem exists_etale_sqrt (hL : Out.Laws) {K : Type} [Field K] {ζ : K} (σ : K →+* ℂ) (F : SFam h k ζ) (hk : 2 ≤ k)
    (hζ : IsUnit ζ) (p₀ : Sp ℂ ⟶ F.X) :
    ∃ (R : Type) (_ : CommRing R) (π : Sp R ⟶ F.X) (p : Sp ℂ ⟶ Sp R) (Q : Out.PolAV (Sp R))
      (φ : Q.A.left ⟶ F.univ.A.left), Etale π ∧ p ≫ π = p₀ ∧ SqOf Q F.univ π φ ∧ TorsConst Q.A 2 := by
  have := F.smooth
  have : Smooth F.s := SmoothOfRelativeDimension.smooth (h * (h + 1) / 2) F.s
  have : IsLocallyNoetherian F.X := LocallyOfFiniteType.isLocallyNoetherian F.s
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := F.X) (x := p₀ (default : PrimeSpectrum ℂ))
    (U := ⊤) trivial
  have : IsNoetherianRing Γ(F.X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : CharZero K := σ.charZero
  let f : Sp Γ(F.X, U) ⟶ F.X := hU.fromSpec
  have : IsOpenImmersion f := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  obtain ⟨β, -⟩ := Spec.map_surjective (f ≫ F.s)
  letI : Algebra ℚ Γ(F.X, U) := (β.hom.comp (algebraMap ℚ K)).toAlgebra
  obtain ⟨R, _, _, Q, φ, ⟨h₁, h₂, h₃⟩, hQ, hT⟩ := GlobalTheory.T.exists_symmetric_sqrt_principal_siegel_finite_etale hL h k K ζ Γ(F.X, U) F.X F.s F.univ f hk hζ F.princ
  have : IsFinite (spMap (algebraMap Γ(F.X, U) R)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 h₁)
  have : Surjective (spMap (algebraMap Γ(F.X, U) R)) := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  have : Etale (spMap (algebraMap Γ(F.X, U) R)) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.etale_algebraMap.2 h₂)
  have hr : Set.range p₀ ⊆ Set.range f := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum ℂ) z default]
    exact hU.range_fromSpec.ge hp
  obtain ⟨p, hp⟩ := exists_point_lift (spMap (algebraMap Γ(F.X, U) R)) (IsOpenImmersion.lift f p₀ hr)
  exact ⟨R, _, _, p, Q, φ, inferInstance, by rw [← Category.assoc, hp, IsOpenImmersion.lift_fac], hQ, hT⟩

theorem exists_nhds_sameComp : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ (τ₀ : Matrix (Fin h) (Fin h) ℂ) (p₀ : Sp ℂ ⟶ F.X), p₀ ≫ F.s = spMap σ → PtAt F.univ p₀ τ₀ → ∃ N ∈ nhds τ₀, ∀ τ ∈ N, ∀ p : Sp ℂ ⟶ F.X, p ≫ F.s = spMap σ → PtAt F.univ p τ → SameComp F.s σ p p₀ := by
  intro hL _ hU h k K _ ζ σ F hh hk ho hζ τ₀ p₀ hs ⟨P₀, lev₀, φ₀, hper, hsq, hlev⟩
  have hζ' : IsUnit ζ := IsUnit.mk0 _ fun e => Complex.exp_ne_zero _ (by rw [← hζ, e, map_zero])
  obtain ⟨R, _, π, p₁, Q₁, φ₁, het, rfl, hQ₁, hT⟩ := exists_etale_sqrt hL σ F (by omega) hζ' p₀
  obtain ⟨Q, φ, ψ, hQ, hpb, rfl⟩ := exists_sqOf_polPB hL hQ₁ hT p₁ hsq
  choose l hl hl' using fun a => exists_section_pull hQ.1 (F.univ.lev a) k (F.univ.lev_tors a)
  have := F.smooth
  have sm : SmoothOfRelativeDimension (h * (h + 1) / 2) (π ≫ F.s) := by
    have := smoothOfRelativeDimension_comp 0 (h * (h + 1) / 2) π F.s
    rwa [zero_add] at this
  have : Smooth (π ≫ F.s) := SmoothOfRelativeDimension.smooth (h * (h + 1) / 2) _
  obtain ⟨B, y, -, -, -, -, hB, hB0, hy0, hys, hyh, hyi, -⟩ :=
    SubfieldChart.exists_holomorphic_chart K σ _ (π ≫ F.s) _ p₁ sm (by rw [← Category.assoc, hs])
  subst hy0
  obtain ⟨B₁, τ, hB₁, hB₁0, hB₁B, hτ0, hτd, hτ⟩ := PeriodLift.exists_local_period_matrix hL hU K σ _ (π ≫ F.s) Q h k _ l
    B y 0 P₀ ψ τ₀ lev₀ inferInstance (by omega) hl hB hB0 hys hyh hpb hper fun a => by
      apply hQ.1.1.hom_ext
      · rw [Category.assoc, hlev, Category.assoc, Category.assoc, hl']
      · rw [Category.assoc, hpb.1.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hpt : ∀ b ∈ B₁, PtAt F.univ (y b ≫ π) (τ b) := fun b hb => by
    obtain ⟨P, χ, lev, h₁, h₂, h₃⟩ := hτ b hb
    exact ⟨P, lev, χ ≫ φ, h₂, (sqOf_calculus h k K ζ _ _ _ F.s F.univ π).1 _ Q P φ χ hQ h₁, fun a => by
      rw [← Category.assoc, h₃, Category.assoc, hl', Category.assoc]⟩
  have hys' : ∀ b ∈ B, (y b ≫ π) ≫ F.s = spMap σ := fun b hb => by rw [Category.assoc, hys b hb]
  obtain ⟨B₂, hB₂, hB₂0, hB₂B, hinj⟩ := EtaleLocInj.exists_open_injOn _ _ π _ B y 0 het hB hB0 hyh
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hB₁.inter hB₂) 0 ⟨hB₁0, hB₂0⟩
  have hbB : Metric.ball 0 ε ⊆ B := fun b hb => hB₁B (hball hb).1
  obtain ⟨N, hN, hNτ⟩ := SiegelOpen.exists_nhds_subset_image h (Metric.ball 0 ε) τ 0 Metric.isOpen_ball
    (Metric.mem_ball_self hε) (fun i j => (hτd i j).mono fun b hb => (hball hb).1)
    (fun b hb => let ⟨_, _, _, H, _⟩ := hpt b (hball hb).1; ⟨H.2.1, H.2.2.1⟩) fun b hb b' hb' e =>
      hyi (hbB hb) (hbB hb') (hinj b (hball hb).2 b' (hball hb').2
        (GlobalTheory.T.siegelFamily_complexPoint_eq_of_same_periodMatrix hL hU h k K ζ σ F hh hk ho hζ (τ b) _ _ (hys' b (hbB hb)) (hys' b' (hbB hb'))
          (hpt b (hball hb).1) (e ▸ hpt b' (hball hb').1)))
  refine ⟨N, hτ0 ▸ hN, fun t ht p hp hpt' => ?_⟩
  have H := hpt'
  obtain ⟨_, _, _, H, _⟩ := H
  obtain ⟨b, hb, rfl⟩ := hNτ t ht H.2.1 H.2.2.1
  rw [GlobalTheory.T.siegelFamily_complexPoint_eq_of_same_periodMatrix hL hU h k K ζ σ F hh hk ho hζ (τ b) p _ hp (hys' b (hbB hb)) hpt' (hpt b (hball hb).1)]
  exact sameComp_of_isHolTo K σ _ F.s _ (Metric.ball 0 ε) (fun b => y b ≫ π) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (fun b hb => hys' b (hbB hb))
    (LocLift.isHolTo_comp_hom (LocLift.isHolTo_mono hyh Metric.isOpen_ball hbB) π) b hb 0 (Metric.mem_ball_self hε)

end GlobalTheory.SiegelNearby
